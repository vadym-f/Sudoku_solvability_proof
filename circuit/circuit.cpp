/* Sudoku solution characteristic polynomial, ciruit for proving polynomial evaluation
 * Vadym Fedyukovych 2018,2019
 * This research was not paid by Samsung Research SRK, 2018
 */
#include <libsnark/common/default_types/r1cs_ppzksnark_pp.hpp>
#include <libsnark/gadgetlib1/protoboard.hpp>
#include <libsnark/zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp>
#include <libsnark/gadgetlib1/gadgets/verifiers/r1cs_ppzksnark_verifier_gadget.hpp>  //?

using namespace std;

#define N  3  // solution size is  N^2 * N^2

// http://elmo.sbs.arizona.edu/sandiway/sudoku/examples.html
vector <vector<int>> sudoku_9x9_initial_position = {
  {0, 0, 0,  6, 0, 0,  4, 0, 0},
  {7, 0, 0,  0, 0, 3,  6, 0, 0},
  {0, 0, 0,  0, 9, 1,  0, 8, 0},

  {0, 0, 0,  0, 0, 0,  0, 0, 0},
  {0, 5, 0,  1, 8, 0,  0, 0, 3},
  {0, 0, 0,  3, 0, 6,  0, 4, 5},

  {0, 4, 0,  2, 0, 0,  0, 6, 0},
  {9, 0, 3,  0, 0, 0,  0, 0, 0},
  {0, 2, 0,  0, 0, 0,  1, 0, 0}
};

vector <vector<int>> sudoku_9x9_solution = {
  {5, 8, 1,  6, 7, 2,  4, 3, 9},
  {7, 9, 2,  8, 4, 3,  6, 5, 1},
  {3, 6, 4,  5, 9, 1,  7, 8, 2},

  {4, 3, 8,  9, 5, 7,  2, 1, 6},
  {2, 5, 6,  1, 8, 4,  9, 7, 3},
  {1, 7, 9,  3, 2, 6,  8, 4, 5},

  {8, 4, 5,  2, 1, 9,  3, 6, 7},
  {9, 1, 3,  7, 6, 8,  5, 2, 4},
  {6, 2, 7,  4, 3, 5,  1, 9, 8}
};

int sudoku_is_consistent(const int n, const vector <vector<int>>& solution, const vector <vector <int>>& initial_position) {
  int result = 1;

  for(int y=0; y < N*N; y++) {
    for(int x=0; x < N*N; x++) {
      if(initial_position[y][x] != 0 &&
	 initial_position[y][x] != solution[y][x]) {
	cout << "Mismatch at (" << x+1 << ", " << y+1 << ")" << endl;
	result = 0;
      }
    }
  }

  if(result == 1)
    cout << "Consistent" << endl;
  return result;
}

void sudoku_print_position(const int n, const vector <vector <int>>& initial_position) {
  cout << "Initial position:" << endl;
  for(int y=0; y < n*n; y++) {
    for(int x=0; x < n*n; x++) {
      cout << initial_position[y][x];
      if(x == n*n-1) {
	cout << endl;
	if((y+1)%n == 0)
	  cout << "-" << endl;
      } else {
	if((x+1)%n == 0)
	  cout << "|";
	else
	  cout << " ";
      }
    }
  }
}

void sudoku_print_solution(const int n, const vector <vector<int>>& solution) {
  cout << "Solution:" << endl;
  for(int y=0; y < n*n; y++) {
    for(int x=0; x < n*n; x++) {
      cout << solution[y][x];
      if(x == n*n-1) {
	cout << endl;
	if((y+1)%n == 0)
	  cout << "-" << endl;
      } else {
	if((x+1)%n == 0)
	  cout << "|";
	else
	  cout << " ";
      }
    }
  }
}

template<typename ppT, typename FieldT>
class sudoku_check_poly_gadget : libsnark::gadget<FieldT> {
private:
  libsnark::pb_variable_array<FieldT> sv, sudoku_solution, sudoku_initial_position,
                                      prows, pcolumns, pblocks;
  libsnark::pb_variable<FieldT> s, fvs;
  int n;

public:
  sudoku_check_poly_gadget(libsnark::protoboard<FieldT>& pb,
                           const int n,
                           const std::string& annotation_prefix="sudoku_poly_proof"):
    libsnark::gadget<FieldT>(pb, annotation_prefix), n(n)
  {
    sudoku_initial_position.allocate(pb, n*n*n*n, "initial_pos");
    s.allocate(pb, "s"); // the challenge
    fvs.allocate(pb, "fvs"); // set characteristic polynomial evaluated at challenge

    // public-witness boundary

    sudoku_solution.allocate(pb, n*n*n*n, "solution");
    sv.allocate(pb, n*n*n*n, "sv");

    prows.allocate(pb, n*n*n*n, "p-rows");
    pcolumns.allocate(pb, n*n*n*n, "p-columns");
    pblocks.allocate(pb, n*n*n*n, "p-blocks");

    //    pb.set_input_sizes(n*n*n*n + 2);
  };

  void generate_r1cs_constraints()
  {
    int x, y, z, bx, by, bz; // starting from 0 here

    // solution - challenge product layer
    for(y=0; y < n*n; y++)
      for(x=0; x < n*n; x++)
        // sv[] - 1 = s * solution[]
        this->pb.add_r1cs_constraint(
          libsnark::r1cs_constraint<FieldT>(s, sudoku_solution[x + y*n*n], sv[x + y*n*n] - 1),
          "s*sol=sv-1");

    // "product accumulator" layers
    // row characteristic polynomial f_r(y,s)
    for(y=0; y < n*n; y++) {
      // loop-start, x=0
      this->pb.add_r1cs_constraint(
        libsnark::r1cs_constraint<FieldT>(1, sv[0 + y*n*n], prows[0 + y*n*n]),
        "first in row");
      for(x=1; x < n*n; x++)
	this->pb.add_r1cs_constraint(
          libsnark::r1cs_constraint<FieldT>(prows[x-1 + y*n*n], sv[x + y*n*n], prows[x + y*n*n]),
          "rows");
      // compare characteristic polynomial circuit output with with f_v(s)
      this->pb.add_r1cs_constraint(
        libsnark::r1cs_constraint<FieldT>(prows[n*n-1 + y*n*n], 1, fvs),
        "last in row");
    } // rows

    for(x=0; x < n*n; x++) {
      // loop-start, y=0
      this->pb.add_r1cs_constraint(
        libsnark::r1cs_constraint<FieldT>(1, sv[x + 0*n*n], pcolumns[x + 0*n*n]),
        "first in column");
      for(y=1; y < n*n; y++)
	this->pb.add_r1cs_constraint(
          libsnark::r1cs_constraint<FieldT>(pcolumns[x + (y-1)*n*n], sv[x + y*n*n], pcolumns[x + y*n*n]),
          "columns");
      this->pb.add_r1cs_constraint(
        libsnark::r1cs_constraint<FieldT>(pcolumns[x + (n*n - 1)*n*n], 1, fvs),
        "last in column");
    } // columns

    for(bz=0; bz < n*n; bz++) {
      bx = bz%n; by = bz/n;
      this->pb.add_r1cs_constraint(
        libsnark::r1cs_constraint<FieldT>(1, sv[(0 + bx*n) + (0 + by*n)*n*n], pblocks[0  +  bz*n*n]),
        "first in block");
      for(z=1; z < n*n; z++) {
	x = z%n; y = z/n;
	this->pb.add_r1cs_constraint(
          libsnark::r1cs_constraint<FieldT>(pblocks[z - 1 + bz*n*n], sv[(x + bx*n) + (y + by*n)*n*n], pblocks[z + bz*n*n]),
          "blocks");
      }
      this->pb.add_r1cs_constraint(
        libsnark::r1cs_constraint<FieldT>(pblocks[(n*n - 1) + bz*n*n], 1, fvs),
        "last in block");
    } // blocks

    // compare solution with initial position: 
    for(y=0; y < n*n; y++)
      for(x=0; x < n*n; x++)
	this->pb.add_r1cs_constraint(
          libsnark::r1cs_constraint<FieldT>(sudoku_solution[x + y*n*n] - sudoku_initial_position[x + y*n*n],
                                            sudoku_initial_position[x + y*n*n], 0),
          "solution=position");
  };

  void generate_r1cs_witness(const vector <vector<int>>& solution,
                             const vector <vector <int>>& initial_position)
  {
    int x, y, z, bx, by, bz; // starting from 0 here
    FieldT partial;

#ifdef DEBUG_17
    FieldT val_s = 17;
#else
    FieldT val_s = FieldT::random_element();
#endif
    this->pb.lc_val(s) = val_s;

#ifdef DEBUG_17
    //  ((1 + 17*4)*(1 + 17*3)*(1 + 17*8)*(1 + 17*9)*(1 + 17*5)*(1 + 17*7)*(1 + 17*2)*(1 + 17*1)*(1 + 17*6))
    FieldT val_fvs = libff::alt_bn128_Fr("50693373566035200");
#else
    FieldT val_fvs = FieldT::one();
    for(int j=0; j < n*n; j++)
      val_fvs = val_fvs * (FieldT::one() + val_s * (j+1));
#endif
    this->pb.lc_val(fvs) = val_fvs;

    for(y=0; y < n*n; y++)
      for(x=0; x < n*n; x++) {
	sudoku_solution[x + y*n*n] = solution[y][x];
	sudoku_initial_position[x + y*n*n] = initial_position[y][x];
      }

    for(y=0; y < n*n; y++)
      for(x=0; x < n*n; x++)
	this->pb.val(sv[x + y*n*n]) = val_s * this->pb.val(sudoku_solution[x + y*n*n]) + FieldT::one();
    
    for(y=0; y < n*n; y++) {
      partial = FieldT::one();
      for(x=0; x < n*n; x++) {
	partial *= this->pb.val(sv[x + y*n*n]);
	this->pb.val(prows[x + y*n*n]) = partial;
      } // for(x)
    } // for(y)

    for(x=0; x < n*n; x++) {
      partial = FieldT::one();
      for(y=0; y < n*n; y++) {
	partial *= this->pb.val(sv[x + y*n*n]); 
	this->pb.val(pcolumns[x + y*n*n]) = partial;
      } // for(y)
    } // for(x)

    for(bz=0; bz < n*n; bz++) {
      bx = bz%n; by = bz/n;
      partial = FieldT::one();
      for(z=0; z < n*n; z++) {
	x = z%n; y = z/n;
	partial *= this->pb.val(sv[(x + bx*n) + (y + by*n)*n*n]);
	this->pb.val(pblocks[z + bz*n*n]) = partial;
      }
    } // blocks
  }; // generate_r1cs_witness()
}; // class sudoku_check_poly_gadget

typedef libff::alt_bn128_pp ppT;
typedef libff::Fr<ppT> FieldT;

int main() {
  ppT::init_public_params();
  libsnark::protoboard<FieldT> pb;

  sudoku_check_poly_gadget<ppT, FieldT> poly_check(pb, N);
  poly_check.generate_r1cs_constraints();
  poly_check.generate_r1cs_witness(sudoku_9x9_solution, sudoku_9x9_initial_position);

  sudoku_print_position(N, sudoku_9x9_initial_position);
  sudoku_print_solution(N, sudoku_9x9_solution);
  sudoku_is_consistent(N, sudoku_9x9_solution, sudoku_9x9_initial_position);

  //? N^4 sv; (N^4 + N^2)*3 rows, cols, blocks; N^4 initial = 5*N^4 + 3*N^2
  //? 5*81+3*9 = 432
  cout << "Number of constraints: " << pb.get_constraint_system().num_constraints() << endl;

  libsnark::r1cs_ppzksnark_keypair<ppT> keypair =
    libsnark::r1cs_ppzksnark_generator<ppT>(pb.get_constraint_system());

  libsnark::r1cs_ppzksnark_primary_input<ppT> primary_input;
  libsnark::r1cs_ppzksnark_auxiliary_input<ppT> auxiliary_input;
  libsnark::r1cs_ppzksnark_proof<ppT> proof =
    libsnark::r1cs_ppzksnark_prover<ppT>(keypair.pk, primary_input, auxiliary_input);
  bool is_ok = libsnark::r1cs_ppzksnark_verifier_weak_IC(keypair.vk, primary_input, proof);

  if(pb.is_satisfied()) {
    cout << "SAT" << endl;
  } else {
    cout << "UNSAT" << endl;
  };
  return 0;
}

/* Sudoku solution characteristic polynomial, ciruit for proving polynomial evaluation
 * Vadym Fedyukovych 2018
 * report rejected and this research was not paid by Samsung Research SRK, 2018
 */
#include "relations/constraint_satisfaction_problems/r1cs/r1cs.hpp"
#include "common/default_types/r1cs_ppzksnark_pp.hpp"
#include "gadgetlib1/protoboard.hpp"
#include "zk_proof_systems/ppzksnark/r1cs_ppzksnark/r1cs_ppzksnark.hpp"

using namespace libsnark;
using namespace std;

typedef Fr<default_ec_pp> FieldT;

#define N  3  // solution size is  n^2 * n^2

// http://elmo.sbs.arizona.edu/sandiway/sudoku/examples.html
int sudoku_initial_position[N*N][N*N] = {  // difficult
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

int sudoku_solution[N*N][N*N] = {
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

int sudoku_consistent() {
  int result = 1;

  for(int y=0; y < N*N; y++) {
    for(int x=0; x < N*N; x++) {
      if(sudoku_initial_position[y][x] != 0 &&
	 sudoku_initial_position[y][x] != sudoku_solution[y][x]) {
	cout << "Mismatch at (" << x+1 << ", " << y+1 << ")" << endl;
	result = 0;
      }
    }
  }
  if(result == 1)
    cout << "Consistent" << endl;
  return result;
}

void sudoku_print_position() {
  cout << "Initial position:" << endl;
  for(int y=0; y < N*N; y++) {
    for(int x=0; x < N*N; x++) {
      cout << sudoku_initial_position[y][x];
      if(x == N*N-1) {
	cout << endl;
	if((y+1)%N == 0)
	  cout << "-" << endl;
      } else {
	if((x+1)%N == 0)
	  cout << "|";
	else
	  cout << " ";
      }
    }
  }
}

void sudoku_print_solution() {
  cout << "Solution:" << endl;
  for(int y=0; y < N*N; y++) {
    for(int x=0; x < N*N; x++) {
      cout << sudoku_solution[y][x];
      if(x == N*N-1) {
	cout << endl;
	if((y+1)%N == 0)
	  cout << "-" << endl;
      } else {
	if((x+1)%N == 0)
	  cout << "|";
	else
	  cout << " ";
      }
    }
  }
}

int main() {
  sudoku_print_position();
  sudoku_print_solution();
  sudoku_consistent();

  default_r1cs_ppzksnark_pp::init_public_params();

  protoboard<FieldT> pb;

  pb_variable<FieldT> s;
  s.allocate(pb, "s");

  pb_variable_array<FieldT> sv, prows, pcolumns, pblocks, frows, fcolumns, fblocks;

  sv.allocate(pb, N*N*N*N, "sv");

  prows.allocate(pb, N*N*N*N, "p-rows");
  pcolumns.allocate(pb, N*N*N*N, "p-columns");
  pblocks.allocate(pb, N*N*N*N, "p-blocks");

  frows.allocate(pb, N*N, "f-out-rows");
  fcolumns.allocate(pb, N*N, "f-out-columns");
  fblocks.allocate(pb, N*N, "f-out-blocks");

  int x, y, z, bx, by, bz; // starting from 0 here

  // --------------- circuit
  // solution - challenge product layer
  for(y=0; y < N*N; y++)
    for(x=0; x < N*N; x++)
      // sv[] - 1 = s * solution[]
      pb.add_r1cs_constraint(r1cs_constraint<FieldT>(s, sudoku_solution[y][x], sv[x + y*N*N] - 1), "");

  // "product accumulator" layers
  // row characteristic polynomial f_r(y,s)
  for(y=0; y < N*N; y++) {
    // loop-start, x=0
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, sv[0 + y*N*N], prows[0 + y*N*N]), "");
    for(x=1; x < N*N; x++)
      pb.add_r1cs_constraint(r1cs_constraint<FieldT>(prows[x-1 + y*N*N], sv[x + y*N*N], prows[x + y*N*N]), "");
    // compare characteristic polynomial circuit output with with f_v(s)
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(prows[N*N-1 + y*N*N], 1, frows[y]), "");
  } // rows

  for(x=0; x < N*N; x++) {
    // loop-start, y=0
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, sv[x + 0*N*N], pcolumns[x + 0*N*N]), "");
    for(y=1; y < N*N; y++)
      pb.add_r1cs_constraint(r1cs_constraint<FieldT>(pcolumns[x + (y-1)*N*N], sv[x + y*N*N], pcolumns[x + y*N*N]), "");
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(pcolumns[x + (N*N - 1)*N*N], 1, fcolumns[x]), "");
  } // columns

  for(bz=0; bz < N*N; bz++) {
    bx = bz%N; by = bz/N;
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(1, sv[(0 + bx*N) + (0 + by*N)*N*N], pblocks[0  +  bz*N*N]), "");
    for(z=1; z < N*N; z++) {
      x = z%N; y = z/N;
      pb.add_r1cs_constraint(r1cs_constraint<FieldT>(pblocks[z - 1 + bz*N*N], sv[(x + bx*N) + (y + by*N)*N*N], pblocks[z + bz*N*N]), "");
    }
    pb.add_r1cs_constraint(r1cs_constraint<FieldT>(pblocks[(N*N - 1) + bz*N*N], 1, fblocks[bz]), "");
  } // blocks

  // compare solution with initial position: 
  for(y=0; y < N*N; y++)
    for(x=0; x < N*N; x++)
      pb.add_r1cs_constraint(r1cs_constraint<FieldT>(sudoku_solution[y][x] - sudoku_initial_position[y][x], sudoku_initial_position[y][x], 0), "");

  // N^4 sv; (N^4 + N^2)*3 rows, cols, blocks; N^4 initial = 5*N^4 + 3*N^2
  // 5*81+3*9 = 432
  cout << "Number of constraints: " << pb.get_constraint_system().num_constraints() << endl;

  // common/default_types/r1cs_ppzksnark_pp.hpp:typedef default_ec_pp default_r1cs_ppzksnark_pp;
  r1cs_ppzksnark_keypair<default_r1cs_ppzksnark_pp> keypair = r1cs_ppzksnark_generator<default_r1cs_ppzksnark_pp>(pb.get_constraint_system());
  // --------------- witness assignment
  pb.lc_val(s) = 17;
  FieldT prod_sv, partial; // , fvs=1

  //  ((1 + 17*4)*(1 + 17*3)*(1 + 17*8)*(1 + 17*9)*(1 + 17*5)*(1 + 17*7)*(1 + 17*2)*(1 + 17*1)*(1 + 17*6))
  FieldT fvs = alt_bn128_Fr("50693373566035200");

  for(z=0; z < N*N; z++) {
  //    fvs = fvs * (s * (z+1) + FieldT::one());
    pb.val(frows[z]) = fvs;
    pb.val(fcolumns[z]) = fvs;
    pb.val(fblocks[z]) = fvs;
  }

  for(y=0; y < N*N; y++)
    for(x=0; x < N*N; x++)
      pb.val(sv[x + y*N*N]) = pb.val(s) * sudoku_solution[y][x] + FieldT::one();

  for(y=0; y < N*N; y++) {
    partial=1;
    for(x=0; x < N*N; x++) {
      partial *= pb.val(sv[x + y*N*N]);
      pb.val(prows[x + y*N*N]) = partial;
    } // for(x)
  } // for(y)

  for(x=0; x < N*N; x++) {
    partial=1;
    for(y=0; y < N*N; y++) {
      // do it
      partial *= pb.val(sv[x + y*N*N]); 
      pb.val(pcolumns[x + y*N*N]) = partial;
    } // for(y)
  } // for(x)

  for(bz=0; bz < N*N; bz++) {
    bx = bz%N; by = bz/N;
    partial=1;
    for(z=0; z < N*N; z++) {
      x = z%N; y = z/N;
      partial *= pb.val(sv[(x + bx*N) + (y + by*N)*N*N]);
      pb.val(pblocks[z + bz*N*N]) = partial;
    }
  } // blocks
/*
  r1cs_ppzksnark_primary_input<default_r1cs_ppzksnark_pp> primary_input;
  r1cs_ppzksnark_auxiliary_input<default_r1cs_ppzksnark_pp> auxiliary_input;
  r1cs_ppzksnark_proof<default_r1cs_ppzksnark_pp> proof = r1cs_ppzksnark_prover<default_r1cs_ppzksnark_pp>(keypair.pk, primary_input, auxiliary_input, pb.get_constraint_system());
  bool is_ok = r1cs_ppzksnark_verifier_weak_IC(keypair.vk, primary_input, proof);
*/
  // --------------- 
  if(pb.is_satisfied()) {
    cout << "SAT" << endl;
  } else {
    cout << "UNSAT" << endl;
  };
  return 0;
}

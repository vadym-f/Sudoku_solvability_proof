# Private verification of Sudoku solution

Sudoku solution verification was introduced in the context of atomic Bitcoin transction:

[Bitcoincore article](https://bitcoincore.org/en/2016/02/26/zero-knowledge-contingent-payments-announcement/) --
[Financial Crypto 2016 talk](https://github.com/zcash-hackworks/pay-to-sudoku) --
[QED-it meetup](https://www.youtube.com/watch?v=bD-xTQ0_2nA)

Informally, a chicken-and-egg problem was resolved this way:
if solution is sent first then why pay for it, and
if payment is made first then nothing prevents from sending just random bytes.
It was shown how to create a hashlock transaction such that
payment can be claimed with a hash preimage,
and that preimages is verified to be a valid encryption key for a valid solution to the given Sudoku puzzle.

This verification idea could be best demonstrated with a few photos that are "worth a thousand words":

[Sudoku verification idea](http://www.wisdom.weizmann.ac.il/~naor/PAPERS/SUDOKU_DEMO/)

Actual solution verification was implemented as producing and verifying a zk-SNARK proof.

An alternative verification is introduced with this project,
starting from the idea of polynomial set representation.
We expect a circuit of reduced complexity, in terms of multiplication gates count.

Polynomial set representation was introduced in the context of communication-efficient
"set reconciliation" problem solved by Minsky, Trachtenberg, and Zippel, 2003:

[Set reconciliation sourcecode](https://github.com/trachten/cpisync)

It was extended into bivariate polynomial representation of graphs,
leading to a Schnorr-like proof systems for graph isomorhism and hamiltonicity with "large" non-binary challenges.

In this project, we experiment with a SNARK circuit for set characteristic polynomials
as shown on the photos referenced earlier.
In particular, we are interested in exact circuit complexity.
For other practical purposes, this is a work-in-progress:
we need to reorganise by introducing a gadget
implementing methods to construct the circuit and assign the witness.

We plan to experiment with SNARK proofs for statements about graphs.
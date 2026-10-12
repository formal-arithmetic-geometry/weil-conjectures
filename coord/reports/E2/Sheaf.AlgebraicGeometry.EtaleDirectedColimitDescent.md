## What changed

Proved `AlgebraicGeometry.Etale.exists_stage_of_directedColimit` with its signature
unchanged. The proof chooses uniform finite relations, converts colimit etaleness
to a polynomial inverse certificate, descends the certificate, and applies the
reverse characterization at the resulting stage. Two independent statements
isolate finite-presentation/conormal characterization and descent of polynomial
identities. Neither is a restatement of the original theorem.

Added the concrete predicate `Algebra.EtalePolynomialCertificate`, with no sorry.
Its first family checks the right inverse modulo the relation ideal; the second
checks the left inverse on generating relation classes modulo the ideal square.

All four delivery modules compile locally without warnings. Scratch examples
compiled for n=m=0, arbitrary relations over the zero ring, the single relation
X in one variable, and relation 1 (the zero quotient). No nontriviality assumption
was added. The characterization allows every T in the universe of the base ring,
which includes both the stages and the colimit; tensor rings have universe max u v.
The proof was checked directly at https://stacks.math.columbia.edu/tag/07RI.
LeanSearch returned Internal Server Error, recorded as unavailable. LeanFinder,
Loogle and grep found individual ingredients but no exact descent theorem.

## Proved and sorry left

Proved `AlgebraicGeometry.Etale.exists_stage_of_directedColimit`: one of one
original sorries closed, conditional on two named intermediate statements.
No sorry remains in the original module. No target signature was changed.

Exactly two sorries are added, each the entire proof of a public theorem in its
own module, with its source, full proof in words and matching node:

- `AlgebraicGeometry.exists_etale_baseChange_polynomialCertificate`, node
  `lem-weil-pbc-etale-base-change-polynomial-certificate`, module
  `Sheaf.AlgebraicGeometry.EtaleBaseChangePolynomialCertificate`.
- `Algebra.exists_stage_etalePolynomialCertificate`, node
  `lem-weil-pbc-etale-polynomial-certificate-colimit`, module
  `Sheaf.RingTheory.EtalePolynomialCertificateColimit`.

The new certificate definition contains no sorry.

## No longer needed

Removed direct proof imports `Sheaf.Paper.DirectedColimitBaseChangeElementwise`
and `Sheaf.RingTheory.EtaleRingMapConormalCriterion` from the original module.
Their dependencies remain: the former is imported by the new certificate descent
module, the latter by the new characterization module. Tensor cancellation,
polynomial scalar extension and tensor-quotient base change remain in the new
nodes' plans. No original mathematical dependency is pruned outright; no realized
statement or step of the unit is bypassed. The certificate uses existing Mathlib
polynomial, derivative and ideal definitions.

## Where the brief, the DAG or earlier work was wrong

No statement dispute. The old imports state the conormal criterion and
single-element tensor descent, but do not state finite inverse certificate
extraction, its inverse check, or simultaneous descent of its ideal membership
witnesses. These are now two independent items instead of unstated glue in the
main proof. The local Stacks source is absent; the public Tag 07RI proof was read.

## New nodes

`def-weil-pbc-etale-polynomial-certificate` defines the two finite families of
inverse identities, implemented by `Algebra.EtalePolynomialCertificate` in
`Sheaf.RingTheory.EtalePolynomialCertificate`.

`lem-weil-pbc-etale-base-change-polynomial-certificate` groups original steps
1, 2, 3 and 5. It has no colimit or directed-system hypothesis and identifies
etaleness with a concrete certificate for uniform finite relations.

`lem-weil-pbc-etale-polynomial-certificate-colimit` is original step 4 for fixed
relations. It has no target algebra C₀, no etaleness hypothesis or conclusion,
and no finite-presentation assumption on B₀.

## Second reading by E2

1. Compared the delivered main module with the repository version. The theorem
   signature is byte-for-byte unchanged; the new modules and declarations are
   recorded in the report and matching DAG nodes.
2. Compiled all four delivered modules with `lcompile.py --all`; compilation
   succeeds. The only remaining `sorry`s are the two named split-off theorems,
   and there are no forbidden declarations.
3. Checked the split statements and edge cases described in the report. The
   certificate definition is concrete, and both split-off statements are strict
   reductions of the original proof rather than restatements; their sources,
   docstrings, and DAG nodes match.
4. The main proof uses the shortest available assembly from the two split
   reductions. Proof-only imports are plain imports, and the removed direct
   imports are listed under `No longer needed`; no unit statement or realized
   step is bypassed.
5. The DAG proof, proof dependencies, origins, Lean declarations, and module
   paths agree with the delivered code. No statement or definition change was
   made.

Changed nothing during second reading; the delivery is ready for `deliver3.py`.

All three nodes retain chapter sec-proper-base-change and unit sk-thm-p1. The
original node's proof, proof_deps and proof_origin now match the Lean assembly.
No existing public interface changed, so no change record is needed.

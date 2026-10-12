## What changed

Proved the algebraic finite quotient reduction in
`Sheaf.AlgebraicGeometry.FiniteCoefficientOfFiniteStalks`. The proof introduces a private
finite quotient lemma using the injective ring-homomorphism kernel lift into the finite additive
endomorphism ring of a finite module. It uses one new intermediate theorem module for the finite
geometric stalk detection step.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.finite_quotient_section_annihilator_of_finite_stalks` modulo the
strictly simpler intermediate theorem
`AlgebraicGeometry.Scheme.exists_finite_stalk_annihilator_detection`, which remains `sorry` and
is recorded by node `lem-weil-pbc-constructible-finite-stalk-annihilator-detection`.

This is a decomposition: one upper hole closed, one strictly simpler geometric hole added.
The private algebraic lemma is proved without sorry. No sorry remains in the assigned module.
Both delivered modules compile without warnings. The empty-index product is a singleton;
the proof also covers the zero coefficient ring, zero sheaf and empty scheme.

## No longer needed

No imports or stated proof dependencies were removed. The proof does not directly use the
constructibility definitions or stalk conservativity after the detection theorem is applied;
they remain dependencies of that theorem's module.

## Where the brief, the DAG or earlier work was wrong

The existing dependency declarations do not state the finite-selection and stalk-chart
argument needed to produce finitely many detecting stalks. This delivery exposes that argument as a strictly simpler
intermediate theorem rather than leaving a `sorry` inside the target proof.

## New nodes

`lem-weil-pbc-constructible-finite-stalk-annihilator-detection` records the finite geometric
stalk detection theorem and its source, searches, and Lean declaration. It does not assume
finite stalks and does not conclude a finite coefficient quotient; it isolates steps 1 and 3,
while the delivered proof completes step 2 and the quotient comparison. No change records.
The source blueprint was read from the launcher’s read-only blueprint-tree copy; the
repository’s literature path is not populated on this machine.

## Second reading by C1

1. I compared both delivered modules with the repository versions. The existing target
   declaration is byte-for-byte unchanged; the added declaration is a separate theorem,
   and no definitions or target statements were altered. Verdict: pass.
2. I compiled both modules with `lcompile.py --all`. The target has no `sorry`, while the
   split-off detection theorem has exactly its named `sorry`; no forbidden declarations or
   extra axioms were introduced. Verdict: pass.
3. I checked the split-off detection statement and node. It is strictly weaker than the
   finite-quotient target (it only gives finite stalk detection), has a source, proof
   description, and searches, and is not duplicated in the existing library. Verdict: pass.
4. The target proof follows the detection node and then the finite endomorphism-ring
   injection. The unit route is retained; no old proof dependency or import became unused.
   Verdict: pass.
5. The target node records the detection theorem as its sole proof dependency, and the
   new node records the theorem, module, declaration, proof route, and source consistently
   with the Lean files. Verdict: pass.

I changed only the report by adding this second-reading record. The proof modules and DAG
nodes required no repair after compilation and static inspection.

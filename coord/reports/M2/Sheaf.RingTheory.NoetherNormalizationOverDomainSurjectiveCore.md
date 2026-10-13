## What changed

Proved `Algebra.FiniteType.exists_finite_subalgebra_away_core` in
`Sheaf.RingTheory.NoetherNormalizationOverDomainSurjectiveCore`, without changing its
signature or public imports. Added proof-only Mathlib imports for localization integrality,
polynomial localization, field Noether normalization, and finite ring maps.

The generic-fibre and two-stage denominator-clearing proof is adapted from the already
proved `Algebra.FiniteType.exists_finite_aeval_away` in
`WeilConjectures.Mathlib.RingTheory.NoetherNormalization`. We prove generic-fibre finite
generation directly from `g`, so `R : Type u` and `S : Type v` retain independent universes.
The final subalgebra is constructed as the adjoin over the evaluation range of the finite
set of scaled generators, then restricted to `R`. Its finite-module structure agrees with
the requested inclusion algebra by definitional equality.

Updated the item's DAG proof and proof origin to describe the actual unit rescaling,
localization integrality lemmas, common product, and final finite adjoin construction.
The three existing proof dependencies remain used. No definitions or statements changed.

## Proved and sorry left

Closed the sole hole: `Algebra.FiniteType.exists_finite_subalgebra_away_core`
(node `new-noether-normalization-over-domain-surjective-core`). Added no holes and no
intermediate statements. No `sorry` remains in the delivered module.

Local single-file compilation succeeds without warnings. The delivery dry run also runs
the project's declaration axiom probe and preflight. The proof uses Mathlib's proved
field normalization and localization integrality results, not any Sheaf theorem with a hole.

## No longer needed

No original imports, nodes, or modules are pruned: field normalization, finite implies
integral, and finite integral adjoin are all used. No import of the source normalization
module is needed, since its conclusion concerns localized finiteness rather than the
finite subalgebra required here. Removed the exploratory proof import
`Mathlib.RingTheory.RingHom.FiniteType`, replacing it with the narrower
`Mathlib.RingTheory.RingHom.Finite`; removed redundant
`Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic` and the unused finite-type instance
for `R → S`. These were sandbox-only explorations, not imports removed from the library.

## Where the brief, the DAG or earlier work was wrong

The DAG suggested lifting coordinates by the triangular construction of Stacks 00OY.
Individual nonzero scalar rescaling of field normalization coordinates suffices instead:
rescaling is a polynomial automorphism over the fraction field. This follows the same
unit route and retains every existing proof dependency.

The source proof's `RingHom.finiteType_localizationPreserves` requires equal universes
for the rings. Using it verbatim would fail the item's independent-universe signature.
Direct generation of the generic fibre by the images of the given finset resolves this
without modifying any interface or adapting another module.

The empty finset has common product 1, the zero-coordinate case uses the same uniform
argument, and no domain or torsion-free assumption on S is used. The localization-zero
clearing lemma handles R-torsion in S. Injectivity of R → S guarantees the generic fibre
is nonzero.

## Second reading by M2

1. PASS: Compared the sole delivered module and existing node with their repository
   versions. The theorem signature is byte for byte identical (checked by extraction);
   no definition, visibility, public import, target or other module changes. The node
   changes only proof and proof_origin; proof_deps stays identical.
2. PASS: Local compilation is clean. A scratch copy with `#print axioms` reports only
   `propext`, `Classical.choice`, and `Quot.sound` for
   `Algebra.FiniteType.exists_finite_subalgebra_away_core`. No sorry or prohibited
   declaration occurs. All choices use proved Mathlib results inside a theorem proof;
   S' is the actual finite adjoin, not an object chosen from an unproved existence result.
3. PASS: No statement is split off and no hole is added. Checked empty g (product 1),
   zero coordinates, independent universes, and R-torsion in S: the second clearing
   lemma handles relations that vanish only after localization. Injectivity ensures
   a nontrivial generic fibre.
4. PASS: Read the upstream `Algebra.FiniteType.exists_finite_aeval_away` proof and
   searched Sheaf and Mathlib for finite subalgebra and scaled-generator alternatives.
   The upstream conclusion is localized finiteness, not the finite subalgebra here,
   and has a shared-universe signature; adapting its relevant argument is justified.
   Each added proof-only import supplies used declarations or localization instances,
   and none is transitively supplied by the other added imports. Both public imports
   supply signature notions. All three original proof dependencies remain used, so
   the No longer needed list is complete. Read dag/units/sk-thm-p1.json: this node is
   below its realized steps; its route and all realized entries remain untouched.
5. PASS: Read the existing node and all three dependency records. Its three steps
   match field normalization with unit rescaling, finite-implies-integral plus both
   denominator-clearing lemmas, and finite integral adjoin respectively. Its source
   attribution identifies the proved upstream argument. No new node is needed.

Changed the theorem docstring to describe individual denominator lifts and unit
rescaling, replacing the obsolete triangular-coordinate sentence. The proof itself
is correct and unchanged. Added this review record; closed 1 hole, added 0 holes.

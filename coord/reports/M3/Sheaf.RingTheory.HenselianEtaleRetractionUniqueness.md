## What changed

Proved `algHom_eq_of_henselianLocalRing_etale` in
`Sheaf.RingTheory.HenselianEtaleRetractionUniqueness`. Added the proof-only import
`Sheaf.RingTheory.RootLiftingEtaleRetraction`, whose main theorem is already proved.
Converted ideal residue-field bijectivity to scheme residue-field bijectivity by the affine
residue-field isomorphisms and naturality of global evaluation; applied the unique-retraction
theorem and transitivity. Updated the DAG proof and dependencies to match.

Corrected the independent algebra instance to `phi.toAlgebra` (see
`coord/changes/henselian-etale-retraction-uniqueness-algebra.md`). The natural-language node
already asks for retractions of phi. No target statement or definition changed.

Validation: the module compiles cleanly; its sole caller
`Sheaf.RingTheory.HenselianEtaleRetraction` compiles unchanged against the new module.
The imported root-lifting theorem follows the same standard-etale/simple-root route;
no unit-level step is bypassed.

## Proved and sorry left

Closed the sole hole: `algHom_eq_of_henselianLocalRing_etale`
(node `lem-weil-pbc-henselian-etale-retraction-uniqueness`). No sorry remains in this module;
no holes were added or split off. This is a proof using an already proved theorem, with a
necessary correction of the original Lean signature, not a decomposition.

## No longer needed

No imports removed: the three public Mathlib imports still support the signature.
The direct proof dependencies `lem-weil-pbc-simple-root-uniqueness` and
`lem-weil-pbc-standard-etale-pair-maps` are replaced by
`lem-weil-pbc-root-lifting-etale-retraction`. They remain needed inside that proved theorem,
so no modules are globally pruned. No new module besides the item's copy.

## Where the brief, the DAG or earlier work was wrong

The original signature allowed an algebra structure unrelated to the étale map phi.
Counterexample: S=B=k⊕V with V square-zero and countable basis e_n, phi=id, q'=V.
This local ring is henselian (its maximal ideal is nilpotent). Choose the independent
algebra structure e_n↦e_(n+1), fixing k. Two algebra retractions send e_(n+1)↦e_n but
send e_0 respectively to 0 and e_0; both pull back V to V. The identity phi is étale
and its residue-field map is bijective, yet these retractions are distinct.
Binding the algebra to phi restores
exactly the retraction statement in Stacks Tag 04GG(8). The unchanged caller already uses
that algebra structure. The unchanged natural-language DAG statement needs no correction.

Search: LeanFinder via msearch for uniqueness of étale sections found standard-etale hom_ext
and SpecToEquivOfLocalRing but no direct uniqueness theorem. Grep of Mathlib unramified and
étale files found formal-unramified ext lemmas requiring nilpotent ideals, which do not apply
here. Grep and reading the project found the already proved
`IsLocalRing.existsUnique_algHom_of_monic_simple_root_lifting_etale`; the existing existence
module provides the residue-field comparison argument. Stacks Tag 04GG was checked at
https://stacks.math.columbia.edu/tag/04GG because the local literature copy is absent.

## Second reading by M3

1. Compared the complete delivered module and existing node against the repository with
   diff. The sole signature change binds Algebra S B to phi.toAlgebra, as explicitly
   declared in the report and change record. The square-zero counterexample is valid:
   the shift has two distinct left inverses preserving the maximal-ideal preimage.
   Stacks Tag 04GG(8) specifies retractions of the given ring map, so the correction
   matches the unchanged natural-language node. No target or definition changed.
   Searched all Lean sources for uses; the sole caller installs this same algebra
   instance and compiled unchanged against the freshly compiled delivered module. PASS.
2. Compiled the module without errors or warnings using lcompile.py. Inspected the
   whole proof and checked for forbidden declarations and hollow definitions: none.
   Scratch #print axioms for algHom_eq_of_henselianLocalRing_etale and for the imported
   IsLocalRing.existsUnique_algHom_of_monic_simple_root_lifting_etale both list exactly
   propext, Classical.choice and Quot.sound. No sorry remains or is introduced. PASS.
3. There are no split-off statements or new nodes. The sole hole closed is
   algHom_eq_of_henselianLocalRing_etale, with zero holes added. Checked the corrected
   statement for the identity map, field base, and product etale algebra with a chosen
   factor prime; it asserts the expected unique retraction. The zero-ring case is
   excluded by the prime and local-ring assumptions. No arbitrary data is chosen from
   an unproved existence theorem. PASS.
4. Read RootLiftingEtaleRetraction in full and checked the unit sk-thm-p1 realized
   record. Reusing its proved unique-retraction theorem keeps the standard-etale
   presentation and simple-root uniqueness argument and bypasses no unit step.
   A fresh Loogle query HenselianLocalRing, AlgHom found only HenselianLocalRing.TFAE;
   project and Mathlib searches found no shorter direct uniqueness theorem or public
   affine residue-field conversion lemma. The added import is proof-only; all three
   public Mathlib imports support the signature. No longer needed lists both old
   direct proof dependencies; they remain dependencies of the imported theorem, so
   no module is globally pruned. PASS.
5. Compared node proof steps, their uses, proof_deps, proof_origin and lean.statement
   against the code. The affine evaluation naturality and residue surjectivity step
   precedes the existing unique-retraction theorem exactly as written. No new nodes
   require metadata. PASS.

Second reading changed no Lean proof or signature. Made the Old and New signatures
in the change record verbatim multiline Lean and added the complete downstream-module
inventory, with recorded claim groups and effects. Added this independent review.

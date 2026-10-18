## What changed

Implemented the closed-support comparison from the ordinary Hom sequence on injective
sheaves, the published functorial K-injective resolution, and the existing kernel-to-cone
quasi-isomorphism. The cone inclusion is explicit, and its naturality and the naturality
of the concrete derived-functor comparison are proved in Lean. The original public
signature is unchanged.

Repair of returned head `9cef3f555`: removed the duplicate private
`CochainComplex.prev_rel` and `CochainComplex.next_rel` declarations. Every use now
applies Mathlib’s public `ComplexShape.up_mk`; the predecessor index equation is
integer arithmetic and the successor equation is reflexive. The matching source-library
helpers are private, so they cannot be referred to through an ordinary import.
The existing imported kernel-to-shifted-cone theorem remains the quasi-isomorphism input.
No source-library change or consumer adaptation is required.

Repair of returned head `0f7d9008b`: removed the duplicate private
`AlgebraicGeometry.Etale.ofNatIsoRight_unit_app`. The cited source-library copies
are all private and cannot be imported by name. The only call site now uses
Mathlib's existing public `Adjunction.ofNatIsoRight_unit`, followed by
`NatTrans.comp_app` and `Functor.whiskerLeft_app`. No replacement declaration is
introduced. This directly reuses the existing adjunction API.

The new ordinary sequence lemma isolates the sheaf argument from complexes and derived
categories. It uses the open–closed sequence, the constant-sheaf adjunction, evaluation at
1, and the extension-by-zero adjunction. Private helpers carry elementary calculations.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.closedSupportHom` (the original one of one holes).
Added holes: none. Remaining holes in the two delivered modules: none.
`AlgebraicGeometry.Etale.closedSupportHomSequence` is proved completely, including the
actual restriction-map identification and exactness. This is a proof, not a decomposition.

The two files are compiled together in import order. The original theorem's normalized
signature was compared with its existing DAG record and is identical. The new import
direction was checked and has no cycle. Final delivery checks are recorded by deliver3.py.

## No longer needed

Removed the duplicate local relation lemmas `CochainComplex.prev_rel` and
`CochainComplex.next_rel`; Mathlib’s `ComplexShape.up_mk` supplies the relation proof
at each call site. Also removed the duplicate private `AlgebraicGeometry.Etale.ofNatIsoRight_unit_app`;
its use is replaced by the existing public Mathlib unit formula. No additional
modules or DAG nodes are pruned by this repair.

The proof does not use the following former proof dependencies:

- `prop-weil-pbc-inverse-image-modules-exact`: the constant-sheaf pullback isomorphisms
  already exist for the fixed-coefficient sheaf category. This concrete cone statement
  does not need exactness of inverse image on a different ringed-module category.
- `lem-weil-pbc-module-sheaves-grothendieck-abelian`: the fixed `ModuleCat A`-valued sheaf
  category has the Mathlib Grothendieck instance already imported by the resolution API.
  The stated project lemma instead discusses `SheafOfModules` and abelian sheaves.
- `lem-weil-pbc-extension-by-zero-exact` and
  `lem-weil-pbc-right-adjoint-preserves-kinjective`: the concrete statement uses
  restriction applied to the resolution on T. It needs no separate proof that this
  restricted complex is K-injective.
- `lem-weil-pbc-kinjective-total-derived`: the existing concrete
  `Functor.rightDerivedFunctorObjQIso` computes exactly the functor in this signature;
  the generic existential derived-functor theorem is unnecessary.
- `lem-weil-pbc-kinjective-hom-derived`: naturality follows from the actual derived
  functor unit and the actual quotient and shift isomorphisms. There is no separate
  homotopy-equivalence descent argument to prove.

Removed from the main module the proof imports
`Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`,
`Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`,
`Sheaf.CategoryTheory.KInjectiveTotalDerived`, and
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
The original direct imports `WeilConjectures.SixFunctors.OpenClosed.Exact` and
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` are replaced in the
main module by the underived sequence. Their mathematical inputs remain used in the
underived proof, so those two dependencies are not pruned.

No target statement or blueprint unit statement or realized proof step is bypassed.
The unit record `sk-prop-sf-cbc` has empty `realized.statement` and `realized.steps` lists.

## Where the brief, the DAG or earlier work was wrong

The returned head `0f7d9008b` also redundantly stated the unit formula for an
adjunction transported along a right natural isomorphism. Although the three
cited source copies are private, Mathlib already exposes the natural-transformation
formula `Adjunction.ofNatIsoRight_unit`, so no extra lemma is needed.

The earlier returned implementation redundantly stated two arithmetic relation lemmas already
private in `WeilConjectures.Algebra.Homology.KernelShiftedMappingCone`. This repair
removes both declarations and reuses the public Mathlib relation constructor instead.

The old plan included a separate computation of the open term as a derived functor.
The actual Lean signature already specifies that term as restriction applied to the
published resolution of K on T, so that extra computation is unnecessary. The generic
existential total-derived declaration also does not directly compute the particular
`rightDerivedFunctor` in the signature; the source library already supplies its concrete
comparison.

Compiler diagnostics exposed expensive unfolding in first drafts of the private
rank-one section identification and the concrete derived calculation. General private
lemmas over arbitrary categories keep those proofs from unfolding the concrete sheaf
constructions repeatedly. The file boundary was not used to evade a compiler limit;
no existing public definition, signature, or consumer is changed.

## New nodes

`new-lem-amb-closed-support-hom-sequence`, realized by
`AlgebraicGeometry.Etale.closedSupportHomSequence` in
`Sheaf.AlgebraicGeometry.ClosedSupportHomSequence`. It is an ordinary sheaf-level
sequence, with no complexes, resolutions, cones, or derived categories. The node records
the sources, complete argument, and actual leansearch, loogle, and grep searches.

The whole-blueprint search `blueprint_refs.py search 'closed support Hom'` returned
no node. A DAG search found related supported-Hom and pro-etale kernel statements;
these concern derived transport, supported products, or intrinsic ringed pro-etale
categories, rather than this ordinary fixed-coefficient etale injective Hom sequence.
The ancestor check returned `lem-amb-closed-support-hom`, as recorded in the new node.

Change record: `coord/changes/K4-closed-support-hom-proof-context.md`. It records the
new private proof context and public helper required by the surface checker. The consumer
scan reports zero downstream modules; no consumer adaptation is needed.

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

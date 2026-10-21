# AlgebraicGeometry.Scheme.strictHenselizationRing_divisor_quotient_presentation

## Reason

Complete the retirement assigned in `coord/retire-items.tsv`, row
`retire:Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation`.
The item has zero holes. Its mathematical result is already proved upstream, but
that theorem uses the full affine-neighbourhood colimit while the Sheaf consumer
uses the small representative colimit. These rings are canonically isomorphic,
rather than definitionally equal.

Retire the duplicate public theorem and preserve the sole consumer's exact statement.
Inside its proof, identify the two structural morphisms on a representative colimit
leg and apply the upstream divisor presentation to `b` followed by the comparison.
Use `Ideal.quotientEquiv` for the inverse comparison to identify the two principal
quotients. Pull the local-base algebra action back by this quotient isomorphism and
compose the universal pointed-etale cocone isomorphism with the algebra isomorphism.
The existing regularity and localization argument then applies unchanged.

No source-library file, target statement, or definition changes. The mathematical
presentation node remains used and is attached to its upstream owner. No new public
compatibility declaration or unfinished lemma is introduced.

## Old

The retired Sheaf module publicly declared:

```lean
theorem strictHenselizationRing_divisor_quotient_presentation
    (R : CommRingCat.{u}) (f : R)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hg : ¬ IsUnit (b.hom f)) :
    ∃ (p : Ideal (R ⧸ Ideal.span {f})) (_ : p.IsPrime)
      (K : Type u) (_ : Field K)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime p)) K)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime p)) K)
      (_ : Algebra (Localization.AtPrime p) K)
      (_ : IsScalarTower (Localization.AtPrime p)
        (IsLocalRing.ResidueField (Localization.AtPrime p)) K)
      (_ : Algebra (Localization.AtPrime p)
        (strictHenselizationRing barY ⧸ Ideal.span {b.hom f})),
      Algebra.IsStrictHenselization (Localization.AtPrime p) K
        (strictHenselizationRing barY ⧸ Ideal.span {b.hom f})
```

The sole consumer privately imported that module and applied this theorem directly.
It publicly imported `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`.

## New

Withdraw the item through `deleted.txt`; the delivery tool creates the standard
empty module. Its DAG attachment is the retained upstream module
`WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation`,
whose complete theorem has the following signature:

```lean
theorem strictHenselizationRing_divisor_quotient_presentation
    (R : CommRingCat.{u}) (f : R)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY)
    (hg : ¬ IsUnit (b.hom f)) :
    ∃ (p : Ideal (R ⧸ Ideal.span {f})) (_ : p.IsPrime)
      (K : Type u) (_ : Field K)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime p)) K)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime p)) K)
      (_ : Algebra (Localization.AtPrime p) K)
      (_ : IsScalarTower (Localization.AtPrime p)
        (IsLocalRing.ResidueField (Localization.AtPrime p)) K)
      (_ : Algebra (Localization.AtPrime p)
        (strictHenselization barY ⧸ Ideal.span {b.hom f})),
      Algebra.IsStrictHenselization (Localization.AtPrime p) K
        (strictHenselization barY ⧸ Ideal.span {b.hom f})
```

The consumer privately imports the upstream presentation module. Its public
structural-map import changes to the upstream owner, since the original Sheaf import
and the upstream presentation's extension module both declare
`strictHenselizationStructuralMap_eq`. Loading them together fails with an existing
identifier error. The replacement import provides the same definitions in the
consumer's unchanged public signature.

The consumer's theorem signature, visibility, and existing docstring stay verbatim.
The new private `comparison_base` helper is the proved canonical comparison previously
inside the retired item. The quotient action is explicitly the old algebra map followed
by the quotient ring equivalence. The resulting algebra isomorphism transports the
universal cocone. The only witness selection is from fully proved upstream theorems;
no object is selected from an unproved existence theorem.

Validation: the adapted consumer compiles without warnings (8.8 seconds). Its sole
direct importer, `StrictHenselRegularDivisorQuotientRegularPart`, compiles unchanged
against the sandbox artifact (2.9 seconds). Axiom probes of the retained upstream
presentation, the adapted consumer, and that direct importer each list exactly
`propext`, `Classical.choice`, and `Quot.sound`. All delivered Lean lines have at most
100 characters. The original consumer compiled against an empty item fails at its
line 38 with `Unknown identifier strictHenselizationRing_divisor_quotient_presentation`;
the adapted consumer succeeds.

## Users

`tools/downstream.py` finds the following thirteen downstream modules. The only actual
caller of the retired theorem is the adapted `RegularAux` module. Source searches
found no additional consumer in quarantine.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed | Indirect importer only. Public theorem signatures and all definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit | unclaimed | Indirect importer only. Public theorem signatures and all definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient | unclaimed | Indirect importer only. Public theorem signatures and all definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientDomainPart | unclaimed | Indirect importer only. Public theorem signatures and all definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian | unclaimed | Indirect importer only. Public theorem signatures and all definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegular | unclaimed | Indirect importer only. Public theorem signatures and all definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularAux | unclaimed | Only direct importer and caller. Switch imports and transport the upstream presentation through the canonical quotient ring isomorphism. Exact signature and visibility preserved. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientRegularPart | unclaimed | Direct importer of the adapted consumer; compiled unchanged against the adapted module. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | unclaimed | Indirect importer only. Public theorem signatures and all definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite | unclaimed | Indirect importer only. Public theorem signatures and all definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale | unclaimed | Indirect importer only. Public theorem signatures and all definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData | unclaimed | Indirect importer only. Public theorem signatures and all definitions used here are unchanged; no source edit. |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization | unclaimed | Indirect importer only. Public theorem signatures and all definitions used here are unchanged; no source edit. |

The node's sole mathematical parent is
`lem-sbc-strict-hensel-regular-divisor-quotient-regular-part-aux`; its dependency edge
is retained and its proof record now includes the canonical transport. References
in older nodes' `created` or `blueprint.from` fields are provenance, not live proof
requirements for the old module. The unit `sk-prop-input-spreading` is unchanged.
No mathematical node is withdrawn, including unfinished-parent dependencies.
No target definition changes, so no target-statement review is reopened.

Edge cases are unchanged. The quotient equivalence works when `f = 0`, with nilpotents,
and over a field. A unit is excluded by the original nonunit hypothesis. No
nonzerodivisor, regularity, or Noetherianity hypothesis is added to the presentation.

## Status

landed 20261021T011048-L-2034534 2026-10-21 (merge of deliver/W2/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselDivisorQuotientPresentation)

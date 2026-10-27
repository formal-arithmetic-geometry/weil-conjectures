# PushNormalized

## Reason

Avoid repeatedly elaborating the same ringed direct-image pure-tensor predicate
through the concrete section-module equivalence. Reuse its existing named
predicate. Both formulas are definitionally equal: the coefficient map, site map,
tensor generators and section action are the same. This changes representation
only, with no additional hypothesis or weakened conclusion. The selected lax
structure is still the unique structure satisfying that identical predicate.

## Old

```lean
def PushNormalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (pushforward Λ f).LaxMonoidal) : Prop :=
  ∀ (M N : modules Λ X) (U : Y.ProEtᵒᵖ)
    (x : ((pushforward Λ f).obj M).val.obj U)
    (y : ((pushforward Λ f).obj N).val.obj U),
    ((m.μ M N).val.app U)
        (sectionPureTensor Λ Y _ _ U x y) =
      sectionPureTensor Λ X M N
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).op.obj U) x y
```

## New

```lean
def PushNormalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (pushforward Λ f).LaxMonoidal) : Prop :=
  SheafOfModules.RingedPushforwardPureTensor (InternalModuleOperations.siteMap f)
    (ring Λ Y) (ring Λ X) (coefficientMap Λ f) m


private theorem existsUnique_of_normalized_pairing {A : Sort*} {P Q : A → Prop}
    (h : ∃ a, P a ∧ Q a ∧ ∀ b, P b → b = a) : ∃! a, P a := by
  obtain ⟨a, ha, _, hu⟩ := h
  exact ⟨a, ha, hu⟩
```

The import of
`Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax`
is added as a public import because the definition now uses
its public predicate. Chosen data remain the same; the definitionally equal
total-comparison proposition is documented separately in
K9-total-comparison-functor-alias.md. Other public signatures are unchanged.
Private proof helpers are optimized and the two private tensor interfaces
used by SectionOrdinaryOplaxNormalization are retained with their original types.
The proved private `pullTensor_sectionTmul_eq` identifies the two generator
formulas over an arbitrary site, so applications avoid repeatedly expanding
concrete coefficients. No consumer requires a source adaptation.

## Users

Obtained using `tools/downstream.py Sheaf.Paper.ProEtaleSectionModuleFunctors
--uses PushNormalized`, with a source check of the two results.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProEtaleSectionModuleFunctors | K9 | Same predicate and unique lax structure; proofs use the shared normalization API. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed | Search matches a different locally defined PushNormalized; unaffected. |

Because target statements may depend on this definition, their semantic review
is reopened. The old and new definitions have exactly the same mathematical
meaning and are kernel-convertible. No target statement changes. No module under
WeilConjectures is modified.

## Status

landed 20261026T070233-L-3486174 2026-10-26 (merge of deliver/K9/Sheaf.Paper.ProEtaleSectionModuleFunctors)

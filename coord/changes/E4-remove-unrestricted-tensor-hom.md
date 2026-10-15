# AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_derivedTensor_obj

## Reason

Reviewer X-78da5 (head 78da571da), return E2, requires removal or a human-approved
coefficient correction of the generic tensor and internal-Hom preservation assertions.
This repair chooses removal for these two unused assertions and their dependent restrictions.

Over the discrete condensed coefficient ring Z/4, take both inputs to be the constant
Z/2-module in degree zero on a geometric point of characteristic 3, with ell = 2.
The free resolution with multiplication by 2 in every positive degree is exact over Z/4.
Tensoring it with Z/2, or applying Hom(-,Z/2), makes every differential zero.
Thus Tor and Ext are nonzero in every nonnegative degree; boundedness fails in the
asserted outputs. The geometric assumptions do not restrict the coefficient ring.
These assertions are removed, not proved or weakened.

## Old

```lean
lemma boundedConstructible_derivedTensor_obj
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hK : boundedConstructible (condensedRingObj Λ X) K)
    (hL : boundedConstructible (condensedRingObj Λ X) L) :
    boundedConstructible (condensedRingObj Λ X) (((-⊗ᴸ-(X)⟦Λ⟧).obj K).obj L) :=
  sorry

/-- The derived hom of module objects over `Λ` preserves bounded constructible
complexes. -/
lemma boundedConstructible_derivedHom_obj
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (hK : boundedConstructible (condensedRingObj Λ X) K)
    (hL : boundedConstructible (condensedRingObj Λ X) L) :
    boundedConstructible (condensedRingObj Λ X) (((RHom(X)⟦Λ⟧).obj (op K)).obj L) :=
  sorry

/-- The derived tensor product `- ⊗ᴸ - : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded
constructible complexes: the restriction of `-⊗ᴸ-(X)⟦Λ⟧` in both variables. -/
noncomputable def boundedConstructibleTensor : Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ :=
  Functor.curry.obj ((boundedConstructible _).lift
    (((boundedConstructible _).ι.prod (boundedConstructible _).ι) ⋙
      Functor.uncurry.obj -⊗ᴸ-(X)⟦Λ⟧)
    fun KL ↦ boundedConstructible_derivedTensor_obj Λ ℓ k X KL.1.property KL.2.property)

/-- The derived hom `RHom(-, -) : Dᵇc(X)⟦Λ⟧ᵒᵖ ⥤ Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧` on bounded constructible
complexes: the restriction of `RHom(X)⟦Λ⟧` in both variables. -/
noncomputable def boundedConstructibleHom : (Dᵇc(X)⟦Λ⟧)ᵒᵖ ⥤ Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(X)⟦Λ⟧ :=
  Functor.curry.obj ((boundedConstructible _).lift
    (((boundedConstructible _).ι.op.prod (boundedConstructible _).ι) ⋙
      Functor.uncurry.obj RHom(X)⟦Λ⟧)
    fun KL ↦ boundedConstructible_derivedHom_obj Λ ℓ k X KL.1.unop.property KL.2.property)

variable {X}

/-- For a fixed `K ∈ Dᵇc(X)⟦Λ⟧`, the restricted functor `K ⊗ᴸ -` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleTensorObjCompatibility (K : Dᵇc(X)⟦Λ⟧) :
    (boundedConstructibleTensor Λ ℓ k X).obj K ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (-⊗ᴸ-(X)⟦Λ⟧).obj K.obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleTensor]

/-- For a fixed `K ∈ Dᵇc(X)⟦Λ⟧`, the restricted functor `RHom(K, -)` is compatible with the
inclusions. -/
noncomputable def boundedConstructibleHomObjCompatibility (K : Dᵇc(X)⟦Λ⟧) :
    (boundedConstructibleHom Λ ℓ k X).obj (op K) ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (RHom(X)⟦Λ⟧).obj (op K.obj) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun g ↦ by
    simp [boundedConstructibleHom]

/-- For a fixed `K ∈ Dᵇc(X)⟦Λ⟧`, the adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` on bounded constructible
complexes: the restriction of `ProEtale.CondensedRing.derivedTensorHomAdjunction` along the
fully faithful inclusions. -/
noncomputable def boundedConstructibleTensorHomAdjunction (K : Dᵇc(X)⟦Λ⟧) :
    (boundedConstructibleTensor Λ ℓ k X).obj K ⊣ (boundedConstructibleHom Λ ℓ k X).obj (op K) :=
  Adjunction.restrictFullyFaithful (derivedTensorHomAdjunction Λ K.obj)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    (boundedConstructibleTensorObjCompatibility Λ ℓ k K).symm
    (boundedConstructibleHomObjCompatibility Λ ℓ k K).symm

```

## New

The seven declarations above are removed, with no replacement assertion or new hole.
The public import of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`
is removed; the ambient tensor and Hom implementations remain available in their own modules.
The module documentation no longer advertises these unsupported restrictions.

## Users

`tools/downstream.py` and a whole-library textual search find no caller of any of the
seven removed declarations outside the item module. There is no forced adaptation for
these removals. The remaining original pushforward assertion is a separate repair obligation.

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | E4 | Remove seven declarations and the unused Hom import. |
| Sheaf.AlgebraicGeometry.CondensedConstructibleSerre | B3 | No removed declaration used; no source adaptation. |
| Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality | B3 | No removed declaration used; no source adaptation. |
| Sheaf.Paper.CondensedCoefficientComparisons | unclaimed | No removed declaration used; no source adaptation. |
| Sheaf.Paper.CondensedFinitePresentationDescent | B3 | No removed declaration used; no source adaptation. |
| Sheaf.Paper.CondensedFlatCoefficientCalculus | A4 | No removed declaration used; no source adaptation. |
| Sheaf.Paper.CondensedOpenClosedRecollement | D3 | No removed declaration used; no source adaptation. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | No removed declaration used; no source adaptation. |
| Sheaf.Paper.CondensedQbarComparisons | unclaimed | No removed declaration used; no source adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | No removed declaration used; no source adaptation. |
| Sheaf.Paper.CondensedQbarLfpLocalTriviality | C2 | No removed declaration used; no source adaptation. |
| Sheaf.Paper.CondensedSheafExtContinuity | C4 | No removed declaration used; no source adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | A2 | No removed declaration used; no source adaptation. |
| TargetsCheck | unclaimed | No removed declaration used; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No removed declaration used; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriekDefs | unclaimed | No removed declaration used; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs | unclaimed | No removed declaration used; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No removed declaration used; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit | B2 | No removed declaration used; no source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek | unclaimed | No removed declaration used; no source adaptation. |

Neither these declarations nor the removed Hom import realizes a unit statement or
unit proof step in `dag/units/sk-thm-properbasechange.json`. No target statement uses
the removed declarations. The retained pullback and extension-by-zero proofs compile.

The second reader also changes the proof-only Nagata import from
`public import WeilConjectures.Compactification.NagataCompactification` to
`import WeilConjectures.Compactification.NagataCompactification`. Only the proof of
`HasCompactification.of_isOver` uses Nagata. Both direct importers, `Derived.UpperShriek`
and `BaseChangeTheorems.MorphismDefs` under the same module-object root, compile unchanged
against the delivered module. The exported theorem and all retained definition bodies stay
unchanged.

## Status

landed 20261015T181522-L-748402 2026-10-15 (merge of deliver/E4/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible)

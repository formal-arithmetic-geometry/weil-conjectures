/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence
public import WeilConjectures.TraceFormula.WeilIdentityStructure
public import WeilConjectures.WeilSheaf.CondensedModelCompactSupport
public import WeilConjectures.ZetaFunction.WeilObjectOfLisse
public import WeilConjectures.ZetaFunction.WeilObjectOfLisseSpecTrace

/-!
# The cohomology sheaves of `RΓ_c` of the Weil object of a lisse sheaf

For a lisse `ℓ`-adic sheaf `H` on `X₀`, the Weil object `(H, 1)` of `Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧`
(`AlgebraicGeometry.WeilComplex.weilObjectOfLisse`) has the identity Weil structure, and so have
its compactly supported cohomology `RΓ_c(X₀, H)` and the cohomology sheaves of the latter
(`ProEtale.CondensedRing.weilCompactSupportCohomology_obj_str_hom_of_id`,
`ProEtale.CondensedRing.WeilBoundedConstructible.homologyFunctor_obj_str_hom_of_id`). Hence
these cohomology sheaves are the Weil sheaves `Hⁱ(Ra_! H)` on `Spec k₀` with the identity
structure (`ProEtale.CondensedRing.WeilSheaf.ofId`), where `Ra_!` may be computed with the
compactification `WeilComplex.structureMorphismCompactification X` of the structure morphism
`a : X₀ ⟶ Spec k₀` chosen by `WeilComplex.derivedLowerShriek`, by the independence of the
compactification
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl`).

## Main definitions

- `AlgebraicGeometry.WeilComplex.homologyWeilCompactSupportCohomologyWeilObjectOfLisseIso`:
  `Hⁱ(RΓ_c(X₀, (H, 1))) ≅ (Hⁱ(Ra_! H), 𝟙)`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale ProEtale.CondensedRing

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

attribute [local instance] fact_ringChar_prime_of_finite

/-- The Weil object `(H, 1)` has the identity Weil structure `L(𝟙)^* H ≅ H`. -/
lemma weilObjectOfLisse_one_str_hom {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) :
    (weilObjectOfLisse (k₀ := k₀) hH 1).str.hom =
      (boundedConstructibleUpperStarId (Profinite.padicAlgClRingObj l) l (overSpec X)).hom.app
        (weilObjectOfLisse (k₀ := k₀) hH 1).carrier := by
  rw [weilObjectOfLisse, Endofunctor.IsoAlgebra.mk_str, Iso.trans_hom, Iso.app_hom]
  refine (congrArg _ ?_).trans (Category.comp_id _)
  rw [boundedConstructibleOfLisseSMulIso, ObjectProperty.isoMk_hom, Functor.mapIso_hom,
    Functor.mapIso_hom]
  have h : (WeilCoefficients.smulIso (1 : (PadicAlgCl l)ˣ) H).hom = 𝟙 H :=
    (congrArg (AdicSheaf.smul · H) (congrArg ULift.up Units.val_one)).trans
      (AdicSheaf.smul_one H)
  rw [h, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

/-- The underlying complex of `RΓ_c(X₀, (H, 1))` is `Ra_!(H[0])`, computed with the
compactification `structureMorphismCompactification X`. -/
noncomputable def weilCompactSupportCohomologyWeilObjectOfLisseCarrierIso
    {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) :
    ((weilCompactSupportCohomology l (Iso.refl (overSpec X))).obj
        (weilObjectOfLisse (k₀ := k₀) hH 1)).carrier.obj ≅
      (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l)
          (structureMorphismCompactification (k₀ := k₀) X)).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((adicSheafEquivCondensedMod l X).functor.obj H)) :=
  (ObjectProperty.ι (boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj l) (point k₀).left))).mapIso
      ((boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl l
        (compactificationOverField (toPoint (overSpec X)))
        ((structureMorphismCompactification (k₀ := k₀) X).copy (toPoint_left _))).app
        (boundedConstructibleOfLisse hH)) ≪≫
    ((boundedConstructibleLowerShriekOfCompactificationCompatibility l
      ((structureMorphismCompactification (k₀ := k₀) X).copy (toPoint_left (overSpec X)))).app
      (boundedConstructibleOfLisse hH) :
        ((boundedConstructibleLowerShriekOfCompactification l
          ((structureMorphismCompactification (k₀ := k₀) X).copy
            (toPoint_left (overSpec X)))).obj (boundedConstructibleOfLisse hH)).obj ≅
      (rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l)
          ((structureMorphismCompactification (k₀ := k₀) X).copy (toPoint_left (overSpec X)))).obj
        (boundedConstructibleOfLisse hH).obj)

/-- **The cohomology sheaves of `RΓ_c` of the Weil object of a lisse sheaf**:
`Hⁱ(RΓ_c(X₀, (H, 1)))` is the Weil sheaf `Hⁱ(Ra_! H)` on `Spec k₀` with the identity structure,
`Ra_!` computed with the compactification `structureMorphismCompactification X`. -/
noncomputable def homologyWeilCompactSupportCohomologyWeilObjectOfLisseIso
    {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) (i : ℤ) :
    (WeilBoundedConstructible.homologyFunctor l (Iso.refl (point k₀)) i).obj
        ((weilCompactSupportCohomology l (Iso.refl (overSpec X))).obj
          (weilObjectOfLisse (k₀ := k₀) hH 1)) ≅
      ProEtale.CondensedRing.WeilSheaf.ofId l (X := point k₀)
        ((_root_.DerivedCategory.homologyFunctor _ i).obj
          ((rightDerivedLowerShriekOfCompactification (Profinite.padicAlgClRingObj l)
              (structureMorphismCompactification (k₀ := k₀) X)).obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              ((adicSheafEquivCondensedMod l X).functor.obj H)))) :=
  WeilSheaf.isoOfId l
    (WeilBoundedConstructible.homologyFunctor_obj_str_hom_of_id l _
      (weilCompactSupportCohomology_obj_str_hom_of_id l _ (weilObjectOfLisse_one_str_hom hH)) i)
    (WeilSheaf.ofId_str_hom l _)
    ((_root_.DerivedCategory.homologyFunctor _ i).mapIso
      (weilCompactSupportCohomologyWeilObjectOfLisseCarrierIso hH))

end AlgebraicGeometry.WeilComplex

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Module.FinitePresentation
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
public import Sheaf.CategoryTheory.SiteConstantModuleHom
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.LinearAlgebra.Pi
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Internal Hom and automorphisms of finite constant pro-etale modules

Source: current blueprint, sec-proetale-coefficients/sk-prop-pe-finite-local-systems,
`sk-prop-pe-finite-local-systems-hom.md`, clauses (1)--(3)
(blueprint: det-pe-finite-local-systems-hom).

Constant modules use the recorded module sheafification functor with its canonical
commutative-ring transport. The kernel is described sectionwise, including both
restriction naturality and naturality in the arbitrary target module sheaf.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Register Mathlib's explicitly constructed filtered group colimits.
Source: Mathlib, GrpCat.FilteredColimits.colimitCoconeIsColimit, used in the current
blueprint finite-local-systems Hom proof, paragraph (3)
(blueprint: det-pe-finite-local-systems-hom). -/
instance finiteConstantHomGrpFilteredColimits :
    HasFilteredColimitsOfSize.{u + 1, u + 1} GrpCat.{u + 1} where
  HasColimitsOfShape _I _ _ :=
    { has_colimit F := ⟨⟨⟨GrpCat.FilteredColimits.colimitCocone.{u + 1, u + 1} F,
        GrpCat.FilteredColimits.colimitCoconeIsColimit.{u + 1, u + 1} F⟩⟩⟩ }

/-- The same filtered colimits with the original site's smaller arrow universe.
Source: Mathlib's filtered-colimit universe transport, used in the current blueprint
finite-local-systems Hom proof, paragraph (3)
(blueprint: det-pe-finite-local-systems-hom). -/
instance finiteConstantHomGrpFilteredColimitsSite :
    HasFilteredColimitsOfSize.{u, u + 1} GrpCat.{u + 1} :=
  hasFilteredColimitsOfSize_of_univLE.{u, u + 1, u + 1, u + 1}

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ]

/-- The comparison comma categories are filtered because the inclusion is flat.
Source: the existing representably flat site comparison, used in the current blueprint
finite-local-systems Hom proof, opening paragraph
(blueprint: det-pe-finite-local-systems-hom). -/
instance finiteConstantHomComparisonFiltered (V : X.ProEtᵒᵖ) :
    IsFiltered (CostructuredArrow (Scheme.toProEt X).op V) :=
  IsFiltered.of_equivalence (structuredArrowOpEquivalence (Scheme.toProEt X) V.unop)

/-- The genuine group-valued Kan extension exists by the filtered comma construction.
Source: Mathlib's pointwise Kan extension and filtered group colimits, used in the
current blueprint finite-local-systems Hom proof, paragraph (3)
(blueprint: det-pe-finite-local-systems-hom). -/
instance finiteConstantHomGrpPointwiseKan (F : X.Etaleᵒᵖ ⥤ GrpCat.{u + 1}) :
    (Scheme.toProEt X).op.HasPointwiseLeftKanExtension F :=
  fun _ ↦ inferInstance

/-- The constant commutative coefficient ring on the original small pro-etale site.
Source: current blueprint, finite-local-systems Hom detail, opening paragraph
(blueprint: det-pe-finite-local-systems-hom). -/
abbrev finiteConstantHomRing :=
  (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj (CommRingCat.of Λ)

/-- The existing intrinsic category over the constant coefficient ring.
Source: current blueprint, finite-local-systems Hom detail, opening paragraph
(blueprint: det-pe-finite-local-systems-hom). -/
abbrev FiniteConstantHomModules :=
  ringedSiteModules.{u + 1}
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (finiteConstantHomRing X Λ))

/-- The recorded constant-module functor; no second constant-module construction is made.
Source: current blueprint, finite-local-systems Hom detail, opening paragraph
(blueprint: det-pe-finite-local-systems-hom). -/
abbrev finiteConstantHomFunctor := constantModuleHomFunctor (Scheme.ProEt.topology X) Λ

/-- The scalar constant-section map, used for the coefficients of the transpose matrix.
Source: current blueprint, finite-local-systems Hom proof, paragraph (1)
(blueprint: det-pe-finite-local-systems-hom). -/
def finiteConstantHomScalar (U : X.ProEtᵒᵖ) : Λ →+* (finiteConstantHomRing X Λ).obj.obj U :=
  ((toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of Λ))).app U).hom

/-- On sections the transpose sends `(x_i)` to `(sum_i a_ik x_i)_k`.
Source: current blueprint, finite-local-systems Hom detail, clause (1)
(blueprint: det-pe-finite-local-systems-hom). -/
def finiteConstantHomTranspose {m n : ℕ}
    (a : (Fin m → Λ) →ₗ[Λ] (Fin n → Λ))
    (N : FiniteConstantHomModules X Λ) (U : X.ProEtᵒᵖ) :
    (Fin n → N.val.obj U) →ₗ[(finiteConstantHomRing X Λ).obj.obj U] (Fin m → N.val.obj U) :=
  LinearMap.pi fun k ↦ ∑ i : Fin n,
    finiteConstantHomScalar X Λ U (a (Pi.single k 1) i) • LinearMap.proj i

/-- The underlying set sheaf of an intrinsic module, using the existing forgetful functors.
Source: current blueprint, finite-local-systems Hom proof, opening paragraph
(blueprint: det-pe-finite-local-systems-hom). -/
abbrev finiteConstantHomUnderlying :
    FiniteConstantHomModules X Λ ⥤ Sheaf (Scheme.ProEt.topology X) (Type (u + 1)) :=
  SheafOfModules.toSheaf _ ⋙ sheafCompose _ (forget AddCommGrpCat.{u + 1})

/-- The canonical composition map on constant set sheaves, obtained from the inverse
finite-product comparison and the ordinary composition function.
Source: current blueprint, finite-local-systems Hom proof, paragraph (2)
(blueprint: det-pe-finite-local-systems-hom). -/
def finiteConstantSetComposition (P Q T : ModuleCat.{u + 1} Λ) :
    (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj (P →ₗ[Λ] Q) ⨯
      (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj (Q →ₗ[Λ] T) ⟶
        (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj (P →ₗ[Λ] T) := by
  letI : PreservesFiniteLimits
      (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))) :=
    inferInstanceAs (PreservesFiniteLimits
      (Functor.const X.ProEtᵒᵖ ⋙ presheafToSheaf (Scheme.ProEt.topology X) (Type (u + 1))))
  exact inv (prodComparison (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1)))
    (P →ₗ[Λ] Q) (Q →ₗ[Λ] T)) ≫
      (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).map
        ((Types.binaryProductIso (P →ₗ[Λ] Q) (Q →ₗ[Λ] T)).hom ≫
          (↾fun fg ↦ fg.2.comp fg.1))

/-- Pair two sections using the evaluation functor's finite-product comparison.
Source: current blueprint, finite-local-systems Hom proof, paragraph (2)
(blueprint: det-pe-finite-local-systems-hom). -/
def finiteConstantHomPair
    (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (U : X.ProEtᵒᵖ)
    (x : F.obj.obj U) (y : G.obj.obj U) : (F ⨯ G).obj.obj U :=
  (PreservesLimitPair.iso
    (sheafToPresheaf (Scheme.ProEt.topology X) (Type (u + 1)) ⋙
      (evaluation X.ProEtᵒᵖ (Type (u + 1))).obj U) F G).inv
        ((Types.binaryProductIso (F.obj.obj U) (G.obj.obj U)).inv (x, y))

/-- Composition of constant-module Hom sections, transported from composition of
constant set sections. The supplied set comparisons are characterized by their units
in the theorem below; they cannot be arbitrary maps.
Source: current blueprint, finite-local-systems Hom proof, paragraph (2)
(blueprint: det-pe-finite-local-systems-hom). -/
def finiteConstantModuleComposition
    (σ : ∀ M : ModuleCat.{u + 1} Λ,
      (finiteConstantHomUnderlying X Λ).obj ((finiteConstantHomFunctor X Λ).obj M) ≅
        (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj M)
    (P Q T : ModuleCat.{u + 1} Λ) (U : X.ProEtᵒᵖ)
    (f : ((finiteConstantHomFunctor X Λ).obj (ModuleCat.of Λ (P →ₗ[Λ] Q))).val.obj U)
    (g : ((finiteConstantHomFunctor X Λ).obj (ModuleCat.of Λ (Q →ₗ[Λ] T))).val.obj U) :
    ((finiteConstantHomFunctor X Λ).obj (ModuleCat.of Λ (P →ₗ[Λ] T))).val.obj U :=
  (σ (ModuleCat.of Λ (P →ₗ[Λ] T))).inv.hom.app U
    ((finiteConstantSetComposition X Λ P Q T).hom.app U
      (finiteConstantHomPair X _ _ U
        ((σ (ModuleCat.of Λ (P →ₗ[Λ] Q))).hom.hom.app U f)
        ((σ (ModuleCat.of Λ (Q →ₗ[Λ] T))).hom.hom.app U g)))

private theorem finiteConstantHom_unit_smul
    (M : ModuleCat.{u + 1} Λ) (U : X.ProEtᵒᵖ) (r : Λ) (x : M) :
    (constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U (r • x) =
      finiteConstantHomScalar X Λ U r •
        (show ((finiteConstantHomFunctor X Λ).obj M).val.obj U from
          (constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U x) := by
  let J := Scheme.ProEt.topology X
  let α := toSheafify J ((Functor.const X.ProEtᵒᵖ).obj (RingCat.of Λ))
  let η := (PresheafOfModules.sheafificationAdjunction α).unit.app
    ((siteConstantModulePresheafGeneral (C := X.ProEt) Λ).obj M)
  let : J.PreservesSheafification (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification J
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
      (FD := fun A B : CommRingCat.{u + 1} ↦ A →+* B)
      (CD := fun A : CommRingCat.{u + 1} ↦ A)
      (FE := fun A B : RingCat.{u + 1} ↦ A →+* B)
      (CE := fun A : RingCat.{u + 1} ↦ A)
  have hr : ((constantModuleHomRingIso J Λ).inv.hom.app U)
      (finiteConstantHomScalar X Λ U r) = (α.app U) r := by
    exact ConcreteCategory.congr_hom (congr_app
      (sheafComposeIso_inv_fac J (forget₂ CommRingCat RingCat)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of Λ))) U) r
  change (η.app U) (r • x) =
    ((constantModuleHomRingIso J Λ).inv.hom.app U)
      (finiteConstantHomScalar X Λ U r) •
        (show ((siteConstantModuleFunctorGeneral J Λ).obj M).val.obj U from (η.app U) x)
  rw [hr]
  exact (η.app U).hom.map_smul r x

private def finiteConstantHom_scalarNat :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of Λ) ⟶
      (finiteConstantHomRing X Λ).obj ⋙ forget₂ CommRingCat RingCat :=
  Functor.whiskerRight (toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of Λ))) (forget₂ CommRingCat RingCat)

private def finiteConstantHom_unitNat (M : ModuleCat.{u + 1} Λ) :
    (siteConstantModulePresheafGeneral (C := X.ProEt) Λ).obj M ⟶
      (PresheafOfModules.restrictScalars (finiteConstantHom_scalarNat X Λ)).obj
        ((finiteConstantHomFunctor X Λ).obj M).val where
  app U := ModuleCat.ofHom
    (Y := ((PresheafOfModules.restrictScalars (finiteConstantHom_scalarNat X Λ)).obj
      ((finiteConstantHomFunctor X Λ).obj M).val).obj U)
    { toFun := (constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U
      map_add' x y := map_add _ x y
      map_smul' r x := finiteConstantHom_unit_smul X Λ M U r x }
  naturality f := by
    ext x
    exact NatTrans.naturality_apply
      (constantModuleHomUnit (Scheme.ProEt.topology X) Λ M) f x

set_option backward.isDefEq.respectTransparency false in
private theorem finiteConstantHom_extend
    (M : ModuleCat.{u + 1} Λ) (N : FiniteConstantHomModules X Λ) (U : X.ProEtᵒᵖ)
    (l : M → N.val.obj U) (hadd : ∀ x y, l (x + y) = l x + l y)
    (hsmul : ∀ r x, l (r • x) = finiteConstantHomScalar X Λ U r • l x) :
    ∃ φ : (SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
        ((finiteConstantHomFunctor X Λ).obj M) N).val.obj U,
      ∀ x : M, φ.app (op (Over.mk (𝟙 U.unop)))
        ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U x) = l x := by
  let J := Scheme.ProEt.topology X
  let R := finiteConstantHomRing X Λ
  let α := finiteConstantHom_scalarNat X Λ
  let αU := Functor.whiskerLeft (Over.forget U.unop).op α
  let η := finiteConstantHom_unitNat X Λ M
  let ηU := (PresheafOfModules.pushforward₀ (Over.forget U.unop) _).map η
  have hN : Presheaf.IsSheaf (J.over U.unop)
      ((PresheafOfModules.restrictOver R.obj U.unop).obj N.val).presheaf :=
    (N.over U.unop).isSheaf
  have : Presheaf.IsLocallySurjective J α := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget J α).2
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight (toSheafify J
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of Λ))) (forget CommRingCat))
    infer_instance
  have : Presheaf.IsLocallySurjective (J.over U.unop) αU :=
    Presheaf.isLocallySurjective_whisker (J.over U.unop) J (Over.forget U.unop) α
  have hi : PresheafOfModules.IsLocallyInjective J η := by
    change Presheaf.IsLocallyInjective J
      (toSheafify J ((siteConstantModulePresheafGeneral (C := X.ProEt) Λ).obj M).presheaf)
    infer_instance
  have hs : PresheafOfModules.IsLocallySurjective J η := by
    change Presheaf.IsLocallySurjective J
      (toSheafify J ((siteConstantModulePresheafGeneral (C := X.ProEt) Λ).obj M).presheaf)
    infer_instance
  have : PresheafOfModules.IsLocallyInjective (J.over U.unop) ηU :=
    Presheaf.isLocallyInjective_whisker (J.over U.unop) J (Over.forget U.unop)
      ((PresheafOfModules.toPresheaf _).map η)
  have : PresheafOfModules.IsLocallySurjective (J.over U.unop) ηU :=
    Presheaf.isLocallySurjective_whisker (J.over U.unop) J (Over.forget U.unop)
      ((PresheafOfModules.toPresheaf _).map η)
  let k : (PresheafOfModules.pushforward₀ (Over.forget U.unop) _).obj
        ((siteConstantModulePresheafGeneral (C := X.ProEt) Λ).obj M) ⟶
      (PresheafOfModules.restrictScalars αU).obj
        ((PresheafOfModules.restrictOver R.obj U.unop).obj N.val) :=
    { app W := ModuleCat.ofHom
        (Y := ((PresheafOfModules.restrictScalars αU).obj
          ((PresheafOfModules.restrictOver R.obj U.unop).obj N.val)).obj W)
        { toFun x := N.val.map W.unop.hom.op (l x)
          map_add' x y := by rw [hadd, map_add]
          map_smul' r x := by
            change N.val.map W.unop.hom.op (l (r • x)) =
              finiteConstantHomScalar X Λ (op W.unop.left) r •
                N.val.map W.unop.hom.op (l x)
            rw [hsmul, N.val.map_smul]
            have h := NatTrans.naturality_apply α W.unop.hom.op r
            change finiteConstantHomScalar X Λ (op W.unop.left) r =
              R.obj.map W.unop.hom.op (finiteConstantHomScalar X Λ U r) at h
            exact congrArg (fun t : R.obj.obj (op W.unop.left) ↦
              t • N.val.map W.unop.hom.op (l x)) h.symm }
      naturality {W W'} f := by
        ext x
        change N.val.map W'.unop.hom.op (l x) =
          N.val.map f.unop.left.op (N.val.map W.unop.hom.op (l x))
        rw [← N.val.map_comp_apply, ← op_comp, Over.w] }
  let e₁ := PresheafOfModules.restrictHomEquivOfIsLocallySurjective αU
    (M₁ := (PresheafOfModules.restrictOver R.obj U.unop).obj
      ((finiteConstantHomFunctor X Λ).obj M).val) hN
  let e₂ := PresheafOfModules.homEquivOfIsLocallyBijective (f := ηU)
    (N := (PresheafOfModules.restrictScalars αU).obj
      ((PresheafOfModules.restrictOver R.obj U.unop).obj N.val)) hN
  let φ := e₁.symm (e₂.symm k)
  refine ⟨φ, ?_⟩
  intro x
  have he : ηU ≫ (PresheafOfModules.restrictScalars αU).map φ = k :=
    e₂.apply_symm_apply k
  have hh := ConcreteCategory.congr_hom
    (congrArg (fun t ↦ t.app (op (Over.mk (𝟙 U.unop)))) he) x
  change φ.app (op (Over.mk (𝟙 U.unop)))
    ((constantModuleHomUnit J Λ M).app U x) = N.val.map (𝟙 U) (l x) at hh
  simpa using hh

private def finiteConstantHom_basisMap {n : ℕ}
    (M : ModuleCat.{u + 1} Λ) (b : (Fin n → Λ) →ₗ[Λ] M)
    (N : FiniteConstantHomModules X Λ) (U : X.ProEtᵒᵖ) :
    (SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
      ((finiteConstantHomFunctor X Λ).obj M) N).val.obj U →ₗ[
        (finiteConstantHomRing X Λ).obj.obj U] (Fin n → N.val.obj U) where
  toFun φ i := (φ.app (op (Over.mk (𝟙 U.unop))))
    ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U (b (Pi.single i 1)))
  map_add' φ ψ := by ext i; rfl
  map_smul' r φ := by
    ext i
    change (r • φ).app (op (Over.mk (𝟙 U.unop)))
      ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U (b (Pi.single i 1))) =
        r • φ.app (op (Over.mk (𝟙 U.unop)))
          ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U (b (Pi.single i 1)))
    rw [PresheafOfModules.smul_app]
    let v : N.val.obj U := φ.app (op (Over.mk (𝟙 U.unop)))
      ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U (b (Pi.single i 1)))
    change (finiteConstantHomRing X Λ).obj.map (𝟙 U) r • v = r • v
    exact congrArg (fun t : (finiteConstantHomRing X Λ).obj.obj U ↦ t • v)
      (ConcreteCategory.congr_hom ((finiteConstantHomRing X Λ).obj.map_id U) r)

private theorem finiteConstantHom_basis_relations {m n : ℕ}
    (M : ModuleCat.{u + 1} Λ)
    (a : (Fin m → Λ) →ₗ[Λ] (Fin n → Λ)) (b : (Fin n → Λ) →ₗ[Λ] M)
    (hexact : Function.Exact a b)
    (N : FiniteConstantHomModules X Λ) (U : X.ProEtᵒᵖ)
    (φ : (SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
      ((finiteConstantHomFunctor X Λ).obj M) N).val.obj U) :
    finiteConstantHomTranspose X Λ a N U (finiteConstantHom_basisMap X Λ M b N U φ) = 0 := by
  classical
  ext k
  simp only [finiteConstantHomTranspose, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, Pi.zero_apply]
  let η : M →+ ((finiteConstantHomFunctor X Λ).obj M).val.obj U :=
    ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U).hom
  let ψ := (φ.app (op (Over.mk (𝟙 U.unop))))
  change (∑ i : Fin n, finiteConstantHomScalar X Λ U (a (Pi.single k 1) i) •
    ψ (η (b (Pi.single i 1)))) = 0
  have hsum : b (a (Pi.single k 1)) =
      ∑ i : Fin n, a (Pi.single k 1) i • b (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ (a (Pi.single k 1)), map_sum]
    congr 1
    funext i
    rw [map_smul]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  have hz : b (a (Pi.single k 1)) = 0 := hexact.apply_apply_eq_zero _
  have he : (∑ i : Fin n, finiteConstantHomScalar X Λ U (a (Pi.single k 1) i) •
      η (b (Pi.single i 1))) = η (b (a (Pi.single k 1))) := by
    rw [hsum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (finiteConstantHom_unit_smul X Λ M U _ _).symm
  calc
    _ = ψ (∑ i : Fin n, finiteConstantHomScalar X Λ U (a (Pi.single k 1) i) •
        η (b (Pi.single i 1))) := by simp only [map_sum, map_smul]
    _ = 0 := by rw [he, hz, map_zero, map_zero]

private theorem finiteConstantHom_unit_ext
    (M : ModuleCat.{u + 1} Λ) (N : FiniteConstantHomModules X Λ) (U : X.ProEtᵒᵖ)
    (a b : (SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
      ((finiteConstantHomFunctor X Λ).obj M) N).val.obj U)
    (h : ∀ x : M,
      a.app (op (Over.mk (𝟙 U.unop)))
          ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U x) =
      b.app (op (Over.mk (𝟙 U.unop)))
          ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U x)) : a = b := by
  let J := Scheme.ProEt.topology X
  let FM := (finiteConstantHomFunctor X Λ).obj M
  let η := constantModuleHomUnit J Λ M
  have hlocal (V : Over U.unop) (x : M) :
      a.app (op V) (η.app (op V.left) x) = b.app (op V) (η.app (op V.left) x) := by
    have ha := PresheafOfModules.naturality_apply a
      (Over.homMk V.hom : V ⟶ Over.mk (𝟙 U.unop)).op (η.app U x)
    have hb := PresheafOfModules.naturality_apply b
      (Over.homMk V.hom : V ⟶ Over.mk (𝟙 U.unop)).op (η.app U x)
    have hn := NatTrans.naturality_apply η V.hom.op x
    change η.app (op V.left) x = FM.val.map V.hom.op (η.app U x) at hn
    change a.app (op V) (FM.val.map V.hom.op (η.app U x)) =
      N.val.map V.hom.op (a.app (op (Over.mk (𝟙 U.unop))) (η.app U x)) at ha
    change b.app (op V) (FM.val.map V.hom.op (η.app U x)) =
      N.val.map V.hom.op (b.app (op (Over.mk (𝟙 U.unop))) (η.app U x)) at hb
    rw [hn, ha, hb, h x]
  have : Presheaf.IsLocallySurjective J η :=
    inferInstanceAs (Presheaf.IsLocallySurjective J
      (toSheafify J ((siteConstantModulePresheafGeneral (C := X.ProEt) Λ).obj M).presheaf))
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply N.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J η s)
  intro W f hf
  obtain ⟨x, hx⟩ := hf
  let V' : Over U.unop := Over.mk (f ≫ V.unop.hom)
  have ha := PresheafOfModules.naturality_apply a
    (Over.homMk f : V' ⟶ V.unop).op s
  have hb := PresheafOfModules.naturality_apply b
    (Over.homMk f : V' ⟶ V.unop).op s
  change a.app (op V') (FM.val.map f.op s) = N.val.map f.op (a.app V s) at ha
  change b.app (op V') (FM.val.map f.op s) = N.val.map f.op (b.app V s) at hb
  change η.app (op W) x = FM.val.map f.op s at hx
  change N.val.map f.op (a.app V s) = N.val.map f.op (b.app V s)
  rw [← ha, ← hb, ← hx]
  exact hlocal V' x

private theorem finiteConstantHom_basis_injective {n : ℕ}
    (M : ModuleCat.{u + 1} Λ) (b : (Fin n → Λ) →ₗ[Λ] M)
    (hb : Function.Surjective b) (N : FiniteConstantHomModules X Λ) (U : X.ProEtᵒᵖ) :
    Function.Injective (finiteConstantHom_basisMap X Λ M b N U) := by
  classical
  intro φ ψ h
  apply finiteConstantHom_unit_ext X Λ M N U φ ψ
  intro y
  obtain ⟨x, rfl⟩ := hb y
  have hx : b x = ∑ i : Fin n, x i • b (Pi.single i 1) := by
    conv_lhs => rw [pi_eq_sum_univ x, map_sum]
    congr 1
    funext i
    rw [map_smul]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [hx, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteConstantHom_unit_smul, map_smul, map_smul]
  exact congrArg (finiteConstantHomScalar X Λ U (x i) • ·) (congrFun h i)

private theorem finiteConstantHom_basis_surjective {m n : ℕ}
    (M : ModuleCat.{u + 1} Λ)
    (a : (Fin m → Λ) →ₗ[Λ] (Fin n → Λ)) (b : (Fin n → Λ) →ₗ[Λ] M)
    (hexact : Function.Exact a b) (hb : Function.Surjective b)
    (N : FiniteConstantHomModules X Λ) (U : X.ProEtᵒᵖ)
    (y : Fin n → N.val.obj U) (hy : finiteConstantHomTranspose X Λ a N U y = 0) :
    ∃ φ, finiteConstantHom_basisMap X Λ M b N U φ = y := by
  classical
  let : Module Λ (N.val.obj U) :=
    Module.compHom (N.val.obj U) (finiteConstantHomScalar X Λ U)
  let f : (Fin n → Λ) →ₗ[Λ] N.val.obj U :=
    { toFun x := ∑ i : Fin n, x i • y i
      map_add' x x' := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' r x := by
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hf (k : Fin m) : f (a (Pi.single k 1)) = 0 := by
    change (∑ i : Fin n, finiteConstantHomScalar X Λ U (a (Pi.single k 1) i) • y i) = 0
    simpa only [finiteConstantHomTranspose, LinearMap.pi_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.proj_apply, Pi.zero_apply] using congrFun hy k
  have hfa (z : Fin m → Λ) : f (a z) = 0 := by
    rw [a.pi_apply_eq_sum_univ z, map_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [map_smul]
    have hk : (fun j ↦ if k = j then (1 : Λ) else 0) = Pi.single k 1 := by
      funext j
      simp [Pi.single_apply, eq_comm]
    rw [hk, hf, smul_zero]
  have hker : LinearMap.range a ≤ LinearMap.ker f := by
    rintro _ ⟨z, rfl⟩
    exact hfa z
  let q := (LinearMap.range a).liftQ f hker
  let e := hexact.linearEquivOfSurjective hb
  let l := q.comp e.symm.toLinearMap
  obtain ⟨φ, hφ⟩ := finiteConstantHom_extend X Λ M N U l
    (fun x y ↦ l.map_add x y) (fun r x ↦ l.map_smul r x)
  refine ⟨φ, funext fun i ↦ ?_⟩
  change φ.app (op (Over.mk (𝟙 U.unop)))
    ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U (b (Pi.single i 1))) = y i
  rw [hφ]
  change q (e.symm (b (Pi.single i 1))) = y i
  rw [Function.Exact.linearEquivOfSurjective_symm_apply]
  change f (Pi.single i 1) = y i
  simp [f, Pi.single_apply]

private theorem finiteConstantHom_basis_restrict
    (M : ModuleCat.{u + 1} Λ) (N : FiniteConstantHomModules X Λ)
    (U V : X.ProEtᵒᵖ) (f : U ⟶ V)
    (φ : (SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
      ((finiteConstantHomFunctor X Λ).obj M) N).val.obj U) (x : M) :
    (((SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
      ((finiteConstantHomFunctor X Λ).obj M) N).val.map f φ).app
        (op (Over.mk (𝟙 V.unop))))
          ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app V x) =
      N.val.map f ((φ.app (op (Over.mk (𝟙 U.unop))))
        ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U x)) := by
  let η := constantModuleHomUnit (Scheme.ProEt.topology X) Λ M
  have hn := NatTrans.naturality_apply η f x
  have hφ := PresheafOfModules.naturality_apply φ
    (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 U.unop)).op (η.app U x)
  change η.app V x = ((finiteConstantHomFunctor X Λ).obj M).val.map f
    (η.app U x) at hn
  change φ.app (op (Over.mk (𝟙 V.unop ≫ f.unop))) (η.app V x) = _
  rw [PresheafOfModules.restrictOver_hom_app_congr φ (Category.id_comp f.unop)]
  rw [hn]
  exact hφ

/-- A finite presentation gives the natural sectionwise kernel description of internal Hom.
The displayed basis-value formula specifies the canonical isomorphism. The following two
identities are its naturality for restriction and for every map of target sheaves.
Source: current blueprint, finite-local-systems Hom detail, clause (1)
(blueprint: det-pe-finite-local-systems-hom).
Proof, following the finite-presentation argument of clause (1):
1. The commutative-ring and ring sheafification units agree through the canonical
   coefficient transport. Thus the constant module unit is linear over constant scalars.
2. Evaluate a slice morphism on the images of the standard basis. Linearity and
   exactness of the ordinary module presentation put its tuple in the transpose kernel.
3. Constant sections locally generate the source. Two morphisms with the same basis
   values agree on all constant sections, then on every section by separatedness.
4. A tuple in the kernel defines a linear map from the ordinary free module. It kills
   the image of a, so factors through M. On the slice, extend its restricted values
   across the locally bijective module unit, then recover linearity over the sheafified
   ring from local surjectivity of its scalar unit. These are Mathlib's sheafification
   Hom equivalences. No exactness assertion about the sections of N is used.
5. The resulting bijective linear map is the required linear equivalence. Naturality
   of the unit and of slice morphisms proves restriction compatibility; postcomposition
   proves naturality in N. The same formulas include rank zero. -/
theorem finiteConstantHom_presentation {m n : ℕ}
    (M : ModuleCat.{u + 1} Λ)
    (a : (Fin m → Λ) →ₗ[Λ] (Fin n → Λ)) (b : (Fin n → Λ) →ₗ[Λ] M)
    (hexact : Function.Exact a b) (hsurjective : Function.Surjective b) :
    ∃ e : ∀ (N : FiniteConstantHomModules X Λ) (U : X.ProEtᵒᵖ),
      (SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
        ((finiteConstantHomFunctor X Λ).obj M) N).val.obj U ≃ₗ[
          (finiteConstantHomRing X Λ).obj.obj U]
            LinearMap.ker (finiteConstantHomTranspose X Λ a N U),
      (∀ (N : FiniteConstantHomModules X Λ) (U : X.ProEtᵒᵖ)
          (φ : (SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
            ((finiteConstantHomFunctor X Λ).obj M) N).val.obj U) (i : Fin n),
        (e N U φ).1 i = (φ.app (op (Over.mk (𝟙 U.unop))))
          ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U
            (b (Pi.single i 1)))) ∧
      (∀ (N : FiniteConstantHomModules X Λ) (U V : X.ProEtᵒᵖ) (f : U ⟶ V)
          (φ : (SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
            ((finiteConstantHomFunctor X Λ).obj M) N).val.obj U) (i : Fin n),
        (e N V ((SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
          ((finiteConstantHomFunctor X Λ).obj M) N).val.map f φ)).1 i =
            N.val.map f ((e N U φ).1 i)) ∧
      (∀ (N N' : FiniteConstantHomModules X Λ) (g : N ⟶ N') (U : X.ProEtᵒᵖ)
          (φ : (SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
            ((finiteConstantHomFunctor X Λ).obj M) N).val.obj U) (i : Fin n),
        (e N' U ((SheafOfModules.homObjMap (R := finiteConstantHomRing X Λ)
          (𝟙 ((finiteConstantHomFunctor X Λ).obj M)) g).val.app U φ)).1 i =
            g.val.app U ((e N U φ).1 i)) := by
  let d (N : FiniteConstantHomModules X Λ) (U : X.ProEtᵒᵖ) :=
    (finiteConstantHom_basisMap X Λ M b N U).codRestrict
      (LinearMap.ker (finiteConstantHomTranspose X Λ a N U))
      (fun φ ↦ finiteConstantHom_basis_relations X Λ M a b hexact N U φ)
  have hd (N : FiniteConstantHomModules X Λ) (U : X.ProEtᵒᵖ) :
      Function.Bijective (d N U) := by
    constructor
    · intro φ ψ h
      exact finiteConstantHom_basis_injective X Λ M b hsurjective N U
        (congrArg Subtype.val h)
    · intro y
      obtain ⟨φ, hφ⟩ := finiteConstantHom_basis_surjective X Λ M a b hexact
        hsurjective N U y.val y.property
      exact ⟨φ, Subtype.ext hφ⟩
  refine ⟨fun N U ↦ LinearEquiv.ofBijective (d N U) (hd N U), ?_, ?_, ?_⟩
  · intro N U φ i
    rfl
  · intro N U V f φ i
    exact finiteConstantHom_basis_restrict X Λ M N U V f φ (b (Pi.single i 1))
  · intro N N' g U φ i
    rfl

/-- The canonical constant Hom comparison is invertible for two finitely presented
modules, and preserves composition on all sections and identity. The set comparisons
are fixed by their constant-section units, as is the linear comparison.
Source: current blueprint, finite-local-systems Hom detail, clause (2)
(blueprint: det-pe-finite-local-systems-hom).
Proof, following steps 1 and 4--6 of the node:
1. Abelian module sheafification and set sheafification agree on underlying sets by
   lem-pc-sites-sheafification-underlying-sets; their units give the displayed σ.
2. Apply the finite-product-preserving constant set functor to evaluation. Its
   linearity identities give the comparison, sending a constant f to C(f) on slices.
3. The presentation calculation identifies ordinary Hom with the finite kernel
   Q^n → Q^m. Exactness and finite-limit preservation of constant modules identify
   its sheafification with the kernel in clause (1). The coordinates agree by
   evaluation at b(e_i), proving invertibility. This is also the recorded
   lem-pur-site-constant-module-hom comparison.
4. Apply the constant set functor to ev(g comp f,x) = ev(g,ev(f,x)). Equality on
   every slice gives the displayed composition equation for arbitrary sections.
   The identity follows by applying it to ev(id,x) = x. -/
theorem finiteConstantHom_constant :
    ∃ σ : ∀ M : ModuleCat.{u + 1} Λ,
      (finiteConstantHomUnderlying X Λ).obj ((finiteConstantHomFunctor X Λ).obj M) ≅
        (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj M,
      (∀ (M : ModuleCat.{u + 1} Λ) (U : X.ProEtᵒᵖ) (x : M),
        (σ M).hom.hom.app U
          ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ M).app U x) =
            (toSheafify (Scheme.ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (M : Type (u + 1)))).app U x) ∧
      ∃ c : ∀ P Q : ModuleCat.{u + 1} Λ,
        (finiteConstantHomFunctor X Λ).obj (ModuleCat.of Λ (P →ₗ[Λ] Q)) ⟶
          SheafOfModules.homObj (R := finiteConstantHomRing X Λ)
            ((finiteConstantHomFunctor X Λ).obj P) ((finiteConstantHomFunctor X Λ).obj Q),
        (∀ (P Q : ModuleCat.{u + 1} Λ) (U : X.ProEtᵒᵖ) (f : P →ₗ[Λ] Q),
          (c P Q).val.app U
            ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ
              (ModuleCat.of Λ (P →ₗ[Λ] Q))).app U f) =
                (PresheafOfModules.restrictOver (finiteConstantHomRing X Λ).obj U.unop).map
                  (((finiteConstantHomFunctor X Λ).map (ModuleCat.ofHom f)).val)) ∧
        (∀ (P Q : ModuleCat.{u + 1} Λ) [Module.FinitePresentation Λ P]
          [Module.FinitePresentation Λ Q], IsIso (c P Q)) ∧
        (∀ (P Q T : ModuleCat.{u + 1} Λ) [Module.FinitePresentation Λ P]
          [Module.FinitePresentation Λ Q] [Module.FinitePresentation Λ T]
          (U : X.ProEtᵒᵖ)
          (f : ((finiteConstantHomFunctor X Λ).obj (ModuleCat.of Λ (P →ₗ[Λ] Q))).val.obj U)
          (g : ((finiteConstantHomFunctor X Λ).obj (ModuleCat.of Λ (Q →ₗ[Λ] T))).val.obj U),
          (c P T).val.app U (finiteConstantModuleComposition X Λ σ P Q T U f g) =
            (c P Q).val.app U f ≫ (c Q T).val.app U g) ∧
        (∀ (P : ModuleCat.{u + 1} Λ) [Module.FinitePresentation Λ P] (U : X.ProEtᵒᵖ),
          (c P P).val.app U
            ((constantModuleHomUnit (Scheme.ProEt.topology X) Λ
              (ModuleCat.of Λ (P →ₗ[Λ] P))).app U LinearMap.id) = 𝟙 _) := by
  sorry

/-- The automorphism sheaf is characterized by the actual groups of automorphisms on
slices and their restriction maps. Its constant group comparison is specified on every
constant automorphism, and it is the inverse image of the constant etale group sheaf.
Classicality is the recorded continuity predicate on the underlying set sheaf.
Source: current blueprint, finite-local-systems Hom detail, clause (3)
(blueprint: det-pe-finite-local-systems-hom).
Proof, following steps 1 and 7--8 of the node:
1. In End(M) squared take pairs (f,g) with fg = gf = 1. This is a finite equalizer
   of sets, not a submodule. By lem-weil-pbc-site-sheaf-sets-limits-sectionwise the
   same equalizer for local sheaf endomorphisms is a sheaf; it is precisely the
   groups of automorphisms on slices. Restriction acts on both inverse maps.
2. The Hom comparison of clause (2), including composition and identity, identifies
   this equalizer with the constant inverse-pair set. Projection identifies it with
   Aut(M). Multiplication is (f,g)(h,k) = (fh,kg), so the comparison preserves the
   group law and has the stated formula on constant automorphisms.
3. Constant etale sheaves pull back to constant pro-etale sheaves: both constant
   functors are left adjoint to global sections, since the inclusion of sites
   preserves their terminal object. The same statement holds for groups, giving
   the displayed group-sheaf isomorphism with the actual comparison inverse image.
4. Apply det-pe-classical-sheaves-image to its underlying sheaf of sets: this is in
   the comparison essential image, hence every affine-presentation continuity map
   is bijective. No finiteness or commutativity of Aut(M) is required. -/
theorem finiteConstantHom_automorphisms (M : ModuleCat.{u + 1} Λ)
    [Module.FinitePresentation Λ M] :
    ∃ A : Sheaf (Scheme.ProEt.topology X) GrpCat.{u + 1},
      ∃ e : ∀ U : X.ProEtᵒᵖ, A.obj.obj U ≃*
        Aut ((PresheafOfModules.restrictOver (finiteConstantHomRing X Λ).obj U.unop).obj
          ((finiteConstantHomFunctor X Λ).obj M).val),
        (∀ (U V : X.ProEtᵒᵖ) (f : U ⟶ V) (x : A.obj.obj U) (W : (Over V.unop)ᵒᵖ),
          (e V (A.obj.map f x)).hom.app W =
            (e U x).hom.app (op ((Over.map f.unop).obj W.unop))) ∧
        (∃ α : A ≅ (constantSheaf (Scheme.ProEt.topology X) GrpCat.{u + 1}).obj
            (GrpCat.of (Aut M)),
          ∀ (U : X.ProEtᵒᵖ) (a : Aut M),
            e U (α.inv.hom.app U
              ((toSheafify (Scheme.ProEt.topology X)
                ((Functor.const X.ProEtᵒᵖ).obj (GrpCat.of (Aut M)))).app U a)) =
              (PresheafOfModules.restrictOver (finiteConstantHomRing X Λ).obj U.unop).mapIso
                ((SheafOfModules.forget _).mapIso ((finiteConstantHomFunctor X Λ).mapIso a))) ∧
        Nonempty (A ≅
          (Functor.sheafPullbackConstruction.sheafPullback (Scheme.toProEt X) GrpCat.{u + 1}
            X.smallEtaleTopology (Scheme.ProEt.topology X)).obj
              ((constantSheaf X.smallEtaleTopology GrpCat.{u + 1}).obj (GrpCat.of (Aut M)))) ∧
        IsClassical ((sheafCompose (Scheme.ProEt.topology X) (forget GrpCat.{u + 1})).obj A) := by
  sorry

end AlgebraicGeometry.ProEtale

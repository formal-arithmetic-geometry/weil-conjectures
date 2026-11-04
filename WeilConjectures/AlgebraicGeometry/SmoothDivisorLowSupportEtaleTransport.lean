/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.SixFunctors.Etale.Derived.LisseFieldDual
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyRestriction
public import WeilConjectures.SixFunctors.OpenClosed.SupportedSections
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.AlgebraicGeometry.SmoothDivisorEtaleChart
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local

/-!
# Étale chart transport for smooth-divisor support vanishing

This module isolates Step 4 of `lem-pur-smooth-divisor-low-support` from the standard-pair
calculation.  Its input is the already established standard-pair assertion, universally in
finite coefficients and in the relative affine-line base.  The conclusion is the support
vanishing for a smooth codimension-one pair.

## Main statements

- `AlgebraicGeometry.Etale.rightDerivedSectionsWithSupportIsoLowerShriekUpperShriek`:
  `RΓ_Z ≅ Ri_! ∘ Ri^!` on `D(X_ét, Λ)`.
- `isZero_homology_rightDerivedSectionsWithSupport_of_smooth_divisor_of_standard_pair`
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section Transport

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- `RΓ_Z ≅ Ri_! ∘ Ri^!` on `D(X_ét, Λ)` for a closed immersion `i : Z ⟶ X`: the sheaf of
sections with support in `Z` is `i_* i^!`, the exact functor `i_*` derives to `Ri_!`, and the
derived functor of the sheaf functor `i^!` is the exceptional inverse image `Ri^!`. -/
noncomputable def rightDerivedSectionsWithSupportIsoLowerShriekUpperShriek {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (sectionsWithSupport (ModuleCat.{u + 1} Λ) i.openComplement.ι).rightDerivedFunctor ≅
      R(i)^![Λ] ⋙ R(i)_![ModuleCat.{u + 1} Λ] :=
  (Functor.rightDerivedFunctorCompIso' _ _ (closedUpperShriekCompLowerStarIso
      (ModuleCat.{u + 1} Λ) i i.openComplement.ι
      i.range_eq_compl_range_openComplement_ι)).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedClosedUpperShriekIso Λ i) _ ≪≫
    Functor.isoWhiskerLeft _
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ) i).symm

/-- The open complement of a closed immersion only depends on its range. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.openComplement_eq_of_range_eq {Z₁ Z₂ X : Scheme.{u}}
    (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X) [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (h : Set.range i₁ = Set.range i₂) : i₁.openComplement = i₂.openComplement := by
  ext1
  rw [Scheme.Hom.coe_openComplement, Scheme.Hom.coe_openComplement, h]

omit [Finite Λ] in
/-- Equal opens have the same derived sections with support in their complements. -/
noncomputable def rightDerivedSectionsWithSupportCongr {X : Scheme.{u}} {O₁ O₂ : X.Opens}
    (h : O₁ = O₂) (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (sectionsWithSupport (ModuleCat.{u + 1} Λ) O₁.ι).rightDerivedFunctor.obj K ≅
      (sectionsWithSupport (ModuleCat.{u + 1} Λ) O₂.ι).rightDerivedFunctor.obj K :=
  eqToIso (by subst h; rfl)

end Transport

/-- A natural number invertible in the field `k` is invertible on every `k`-scheme. -/
lemma _root_.AlgebraicGeometry.Scheme.isUnit_natCast_of_isUnit_natCast {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {m : ℕ} (hm : IsUnit (m : k)) :
    IsUnit (m : Γ(X, ⊤)) := by
  simpa using hm.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom


set_option linter.unusedVariables false in
/-- Transport the standard-pair calculation across smooth codimension-one étale charts.

The proof uses the smooth-pair coordinate theorem and the stalk dimension equation to obtain
an étale jointly-surjective family of charts carrying the divisor to a zero section.  Exact
inverse image commutes with homology of the right-derived support functor, and the finite Tate
pullback comparison identifies the coefficients on each chart.  The standard-pair hypothesis
therefore gives zero homology on every chart; geometric stalk conservativity descends it to the
original sheaf.  The empty-divisor case is the zero support functor.  This is a transport step,
not another formulation of the standard-pair calculation.
(source: clause (b), local-comparison paragraph beginning
"Both classes are global classes supported on D";
blueprint: lem-pur-smooth-divisor-low-support)
-/
theorem isZero_homology_rightDerivedSectionsWithSupport_of_smooth_divisor_of_standard_pair
    {k : Type u} [Field k] (ell N : ℕ) (hell : Nat.Prime ell)
    (hell_unit : IsUnit (ell : k)) (hN : 1 ≤ N)
    {B T D : Scheme.{u}}
    (b : B ⟶ Spec (.of k)) [IsSeparated b] [LocallyOfFiniteType b]
    [QuasiCompact b]
    (v : T ⟶ B) (n : ℕ) [SmoothOfRelativeDimension n v]
    [IsSeparated (v ≫ b)] [LocallyOfFiniteType (v ≫ b)] [QuasiCompact (v ≫ b)]
    (i : D ⟶ T) [IsClosedImmersion i] [Smooth (i ≫ v)]
    [IsSeparated (i ≫ v ≫ b)] [LocallyOfFiniteType (i ≫ v ≫ b)]
    [QuasiCompact (i ≫ v ≫ b)]
    (hcodim : ∀ d : D, ringKrullDim (T.presheaf.stalk (i d)) =
      ringKrullDim (D.presheaf.stalk d) + (1 : WithBot ℕ∞))
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : ((ell ^ N : ℕ) : Λ) = 0)
    (hstandard : ∀ {Y G : Scheme.{u}}
      (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
      [QuasiCompact aY]
      (j : G ⟶ AffineSpace (ULift.{u} (Fin 1)) Y) [IsOpenImmersion j]
      (hj : Set.range j.base =
        (Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y).base)ᶜ),
      ∀ q : ℤ, q < 2 →
        IsZero (((DerivedCategory.homologyFunctor _ q).obj
          ((sectionsWithSupport (ModuleCat.{u + 1} Λ) j).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj
              (AlgebraicGeometry.Scheme.finiteEtaleTateSheaf Λ (ell ^ N)
                (AffineSpace (ULift.{u} (Fin 1)) Y) (by simpa using hΛ) 1))))) ) :
    ∀ q : ℤ, q < 2 →
      IsZero (((DerivedCategory.homologyFunctor _ q).obj
        ((sectionsWithSupport (ModuleCat.{u + 1} Λ) i.openComplement.ι).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (AlgebraicGeometry.Scheme.finiteEtaleTateSheaf Λ (ell ^ N) T hΛ 1))))) := by
  intro q hq
  classical
  obtain ⟨-, c, -, -⟩ := Scheme.etaleFiniteTwistPullback Λ (ell ^ N) (pow_pos hell.pos N) hΛ
  have hunit {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) : IsUnit ((ell ^ N : ℕ) : Γ(X, ⊤)) :=
    Scheme.isUnit_natCast_of_isUnit_natCast f (by rw [Nat.cast_pow]; exact hell_unit.pow N)
  -- the Tate coefficients and their pullbacks
  let S (X : Scheme.{u}) := (DerivedCategory.singleFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
      (Scheme.finiteEtaleTateSheaf Λ (ell ^ N) X hΛ 1)
  have τ {X X' : Scheme.{u}} (e : X' ⟶ X) (aX : X ⟶ Spec (.of k)) :
      (L((e)^*[ModuleCat.{u + 1} Λ])).obj (S X) ≅ S X' :=
    (leftDerivedUpperStarIsoMapDerivedCategory _ e).app _ ≪≫
      (((e)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (c e (hunit aX) (hunit (e ≫ aX)) 1)
  -- the étale charts
  choose U hdU Y aY hsep hlft hqc h het hrange using
    exists_etale_affineLine_zeroSection_of_smooth_divisor b v n i hcodim
  let V : Option D → Scheme.{u} := fun o ↦ Option.rec i.openComplement.toScheme
    (fun d ↦ (U d).toScheme) o
  let w : ∀ o, V o ⟶ T := fun o ↦ Option.rec (motive := fun o ↦ V o ⟶ T)
    i.openComplement.ι (fun d ↦ (U d).ι) o
  have hw : ∀ o, AlgebraicGeometry.Etale (w o) := fun o ↦
    Option.rec (motive := fun o ↦ AlgebraicGeometry.Etale (w o))
      (inferInstanceAs (AlgebraicGeometry.Etale i.openComplement.ι))
      (fun d ↦ inferInstanceAs (AlgebraicGeometry.Etale (U d).ι)) o
  have hu : ∀ x : T, ∃ (o : Option D) (y : V o), (w o).base y = x := by
    intro x
    by_cases hx : x ∈ Set.range i
    · obtain ⟨d, rfl⟩ := hx
      exact ⟨some d, ⟨i d, hdU d⟩, rfl⟩
    · refine ⟨none, ⟨x, ?_⟩, rfl⟩
      rwa [← SetLike.mem_coe, Scheme.Hom.coe_openComplement]
  have e₀ := (rightDerivedSectionsWithSupportIsoLowerShriekUpperShriek Λ i).app (S T)
  refine isZero_homology_of_jointlySurjective Λ w hu _ q fun o ↦ ?_
  cases o with
  | none =>
    refine Functor.map_isZero _
      ((isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint
        (ModuleCat.{u + 1} Λ) i i.openComplement.ι ?_ i.openComplement.ι subset_rfl _).of_iso
          ((L((i.openComplement.ι)^*[ModuleCat.{u + 1} Λ])).mapIso e₀))
    rw [i.range_eq_compl_range_openComplement_ι]
    exact disjoint_compl_left
  | some d =>
    have := hsep d
    have := hlft d
    have := hqc d
    have := het d
    let e := (U d).ι
    let s := AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Y d)
    let iV := pullback.snd i e
    let sV := pullback.snd s (h d)
    have hstd := hstandard (aY d) s.openComplement.ι
      (by rw [s.range_eq_compl_range_openComplement_ι, compl_compl]) q hq
    have := isIso_supportedRestriction_of_etale Λ e i iV (pullback.fst i e)
      (IsPullback.of_hasPullback i e) (S T) (S _) (τ e (v ≫ b))
    have := isIso_supportedRestriction_of_etale Λ (h d) s sV (pullback.fst s (h d))
      (IsPullback.of_hasPullback s (h d)) (S _) (S _)
      (τ (h d) (AffineSpace (ULift.{u} (Fin 1)) (Y d) ↘ Y d ≫ aY d))
    have e₁ := (L((e)^*[ModuleCat.{u + 1} Λ])).mapIso e₀ ≪≫
      asIso (supportedRestriction Λ e i iV (pullback.fst i e)
        (IsPullback.of_hasPullback i e) (S T) (S _) (τ e (v ≫ b)))
    have e₂ := asIso (supportedRestriction Λ (h d) s sV (pullback.fst s (h d))
      (IsPullback.of_hasPullback s (h d)) (S _) (S _)
      (τ (h d) (AffineSpace (ULift.{u} (Fin 1)) (Y d) ↘ Y d ≫ aY d)))
    have hr : Set.range iV = Set.range sV := by
      rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd]
      exact hrange d
    have e₃ := ((rightDerivedSectionsWithSupportIsoLowerShriekUpperShriek Λ iV).app (S _)).symm ≪≫
      rightDerivedSectionsWithSupportCongr Λ (iV.openComplement_eq_of_range_eq sV hr) _ ≪≫
      (rightDerivedSectionsWithSupportIsoLowerShriekUpperShriek Λ sV).app (S _)
    have hzero := hstd.of_iso ((DerivedCategory.homologyFunctor _ q).mapIso
      ((rightDerivedSectionsWithSupportIsoLowerShriekUpperShriek Λ s).app (S _)).symm)
    exact (isZero_homology_leftDerivedUpperStar_obj (ModuleCat.{u + 1} Λ) (h d) _ q hzero).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso (e₁ ≪≫ e₃ ≪≫ e₂.symm))

end AlgebraicGeometry.Etale

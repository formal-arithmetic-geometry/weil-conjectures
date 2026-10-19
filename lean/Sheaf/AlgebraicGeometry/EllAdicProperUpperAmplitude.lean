/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

import Sheaf.AlgebraicGeometry.EllAdicProperHeartUpperBound
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.Triangulated.PostnikovDerivedLimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Proper upper amplitude on the adic localizing hull

This isolates the class-relative upper-amplitude argument from the truncation-window
corollary. Source: blueprint `sk-lem-proper-unbounded-window` and
`det-prop-int-compactness-direct-sums` (1)-(2).
(blueprint: new-lem-sfb-adic-proper-upper-amplitude)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem bounded_upper
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {B : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    (T : DerivedCategory A ⥤ DerivedCategory B) [T.CommShift ℤ] [T.IsTriangulated]
    (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    (c : ℤ) (hc : ∀ M, P M → (T.obj ((DerivedCategory.singleFunctor A 0).obj M)).IsLE c)
    (K : DerivedCategory A) (hK : DerivedCategory.homologyProperty P K)
    (a b : ℤ) [K.IsGE a] [K.IsLE b] : (T.obj K).IsLE (b + c) := by
  have hs (M : A) (hM : P M) (n : ℤ) :
      (T.obj ((DerivedCategory.singleFunctor A n).obj M)).IsLE (n + c) := by
    have := hc M hM
    have : DerivedCategory.TStructure.t.IsLE
        ((T.obj ((DerivedCategory.singleFunctor A 0).obj M))⟦-n⟧) (n + c) :=
      DerivedCategory.TStructure.t.isLE_shift _ c (-n) (n + c) (by omega)
    let e : (T.obj ((DerivedCategory.singleFunctor A 0).obj M))⟦-n⟧ ≅
        T.obj ((DerivedCategory.singleFunctor A n).obj M) :=
      (T.commShiftIso (-n)).symm.app _ ≪≫ T.mapIso
        (((DerivedCategory.singleFunctors A).shiftIso (-n) n 0 (by omega)).app M)
    exact DerivedCategory.TStructure.t.isLE_of_iso e _
  suffices h : ∀ (k : ℕ) (M : DerivedCategory A) (n : ℤ),
      M.IsGE (n - k) → M.IsLE n → DerivedCategory.homologyProperty P M →
      (T.obj M).IsLE (n + c) by
    exact h (b - a).toNat K b
      (DerivedCategory.TStructure.t.isGE_of_ge K _ a (by omega)) inferInstance hK
  intro k
  induction k with
  | zero =>
    intro M n hlo hhi hM
    have : M.IsGE n := by simpa using hlo
    obtain ⟨N, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE M n
    have hN : P N := P.prop_of_iso
      ((DerivedCategory.homologyFunctor A n).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso A n).app N) (hM n)
    have := hs N hN n
    exact DerivedCategory.TStructure.t.isLE_of_iso (T.mapIso e.symm) _
  | succ k ih =>
    intro M n hlo hhi hM
    let t := DerivedCategory.TStructure.t (C := A)
    have hT := T.map_distinguished _ (t.triangleLTGE_distinguished n M)
    refine DerivedCategory.TStructure.t.isLE₂ _ hT (n + c) ?_ ?_
    · have : ((t.triangleLTGE n).obj M).obj₁.IsLE (n - 1) :=
        t.isLE_truncLT_obj M n (n - 1) (by omega)
      have : M.IsGE (n - 1 - k) := t.isGE_of_ge M _ (n - ↑(k + 1)) (by omega)
      have : ((t.triangleLTGE n).obj M).obj₁.IsGE (n - 1 - k) :=
        inferInstanceAs (t.IsGE ((t.truncLT n).obj M) (n - 1 - k))
      have hlow : DerivedCategory.homologyProperty P ((t.truncLT n).obj M) :=
        (DerivedCategory.homologyProperty P).prop_of_iso
          ((t.truncLEIsoTruncLT (n - 1) n (by omega)).app M)
          (DerivedCategory.homologyProperty_truncLE hM (n - 1))
      have hi : (T.obj ((t.truncLT n).obj M)).IsLE (n - 1 + c) :=
        ih ((t.truncLT n).obj M) (n - 1) inferInstance inferInstance hlow
      change (T.obj ((t.truncLT n).obj M)).IsLE (n + c)
      exact DerivedCategory.TStructure.t.isLE_of_le
        (T.obj ((t.truncLT n).obj M)) (n - 1 + c) (n + c) (by omega)
    · have : ((t.triangleLTGE n).obj M).obj₃.IsLE n :=
        inferInstanceAs (t.IsLE ((t.truncGE n).obj M) n)
      have : ((t.triangleLTGE n).obj M).obj₃.IsGE n := inferInstance
      obtain ⟨N, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
        ((t.triangleLTGE n).obj M).obj₃ n
      have hhigh := DerivedCategory.homologyProperty_truncGE hM n
      have hN : P N := P.prop_of_iso
        ((DerivedCategory.homologyFunctor A n).mapIso e ≪≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso A n).app N) (hhigh n)
      have := hs N hN n
      exact DerivedCategory.TStructure.t.isLE_of_iso (T.mapIso e.symm) _


open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y) [IsProper g.left]
  (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance)

omit [IsCommMonObj Λ] in
private theorem constructible_zero (X : Scheme.{u}) :
    IsConstructibleModuleObject (condensedRingObj Λ X)
      (0 : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  refine ⟨S, fun a ↦ ?_⟩
  refine ⟨.singleton (𝟙 (S.domain a)) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, 0, 𝟙 _, ⟨?_⟩⟩
  exact (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} _).mapMod _).map_isZero
    (((AlgebraicGeometry.ProEtale.upperStar Ab.{u + 1} _).mapMod _).map_isZero
      (isZero_zero _))).iso
      (isZero_cokernel_of_epi (𝟙 _))

private theorem internal_countableAB4Star (X : Scheme.{u}) :
    CountableAB4Star
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) := by
  let e := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj Λ X)
  have h := Scheme.ProEt.products_exact.{u, u + 1, 0} X
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X) (condensedRingObj Λ X))) ℕ
  have : HasExactLimitsOfShape (Discrete ℕ)
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
    HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) e.symm
  exact CountableAB4Star.of_hasExactLimitsOfShape_nat _

include ℓ k hΛ

/-- A uniform upper-amplitude bound for proper pushforward on ind-constructible cohomology.

Source: blueprint `sk-lem-proper-unbounded-window` (arbitrary-complex clause) and
`det-prop-int-compactness-direct-sums` (1)-(2).
Proof: take a uniform bound c on the ind-constructible heart. Shift compatibility
bounds the image of a heart object in degree n by n+c. Induct on the length of a
finite cohomology interval, using the standard truncation triangle: its lower part
has one fewer degree, and its upper part is the top cohomology object in that degree.
This gives the bound b+c on every lower truncation of a complex supported above by b.
Exact countable products reconstruct the complex by its canonical Postnikov triangle.
The right adjunction makes derived pushforward preserve its product, and exact target
products commute with homology. Thus both product terms in the image triangle are
supported above by b+c. Its homology sequence bounds the first term by b+c+1.
The existential constant can therefore be chosen to be c+1. This deliberately allows
one additional degree and requires no stabilization theorem for the output tower.
The source ind-heart contains zero, so its cohomology property is truncation stable.
The argument includes zero objects, empty fibres and negative values of b.
(blueprint: new-lem-sfb-adic-proper-upper-amplitude)
-/
theorem ellAdic_proper_pushforward_isLE_of_isLE :
    ∃ c : ℕ, ∀ (b : ℤ)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
          (condensedRingObj Λ Z.left))),
      DerivedCategory.homologyProperty (ObjectProperty.ind.{u + 1}
        (IsConstructibleModuleObject (condensedRingObj Λ Z.left))) K → K.IsLE b →
      ((R((g.left)_*⟦Λ⟧)).obj K).IsLE (b + (c : ℤ)) := by
  let A := Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
    (condensedRingObj Λ Z.left)
  let B := Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
    (condensedRingObj Λ Y.left)
  let T := R((g.left)_*⟦Λ⟧)
  have : CountableAB4Star A := internal_countableAB4Star Λ Z.left
  have : CountableAB4Star B := internal_countableAB4Star Λ Y.left
  have : T.IsTriangulated := inferInstance
  let P := ObjectProperty.ind.{u + 1}
    (IsConstructibleModuleObject (condensedRingObj Λ Z.left))
  have : P.ContainsZero :=
    ⟨0, isZero_zero _, ObjectProperty.le_ind _ _ (constructible_zero Λ Z.left)⟩
  obtain ⟨c, hc⟩ := ellAdic_proper_heart_upper_bound Λ ℓ g hΛ
  obtain ⟨hPA, _, _⟩ := derivedCategory_countableProducts_core.{0} A
  obtain ⟨hPB, _, hHB⟩ := derivedCategory_countableProducts_core.{0} B
  let := hPA
  let := hPB
  let (j : ℤ) : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor B j) :=
    hHB ℕ j
  refine ⟨c + 1, ?_⟩
  intro b K hK hbound
  let L : ℕ → DerivedCategory A := fun n ↦
    (DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K
  have hL (n : ℕ) : (T.obj (L n)).IsLE (b + (c : ℤ)) := by
    have := hbound
    apply bounded_upper T P (c : ℤ) (fun M hM ↦
      (DerivedCategory.isLE_iff _ _).2 (hc M hM)) (L n)
      (DerivedCategory.homologyProperty_truncGE hK (-(n : ℤ))) (-(n : ℤ)) b
  obtain ⟨δ, hδ⟩ := DerivedCategory.lowerTruncation_isDerivedLimitTriangle A K
  have hT := T.map_distinguished _ hδ
  have hprod : (T.obj (∏ᶜ L)).IsLE (b + (c : ℤ)) := by
    rw [DerivedCategory.isLE_iff]
    intro j hj
    let H := DerivedCategory.homologyFunctor B j
    have hz (n : ℕ) : IsZero ((T ⋙ H).obj (L n)) :=
      (DerivedCategory.isLE_iff _ _).1 (hL n) j hj
    have hzprod : IsZero (∏ᶜ fun n : ℕ ↦ (T ⋙ H).obj (L n)) := by
      apply (IsZero.iff_id_eq_zero _).2
      apply Pi.hom_ext
      intro n
      exact (hz n).eq_of_tgt _ _
    exact hzprod.of_iso (PreservesProduct.iso (T ⋙ H) L)
  let f : ∀ n, L (n + 1) ⟶ L n := fun n ↦
    (DerivedCategory.TStructure.t.natTransTruncGEOfLE
      (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app K
  let p : K ⟶ ∏ᶜ L := Pi.lift (fun n : ℕ ↦
    (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)
  let D := T.mapTriangle.obj (CategoryTheory.Pretriangulated.Triangle.mk p
    (towerTransitionEndomorphism f) δ)
  have hD : D ∈ distTriang _ := hT
  rw [DerivedCategory.isLE_iff]
  intro j hj
  have h₁ : IsZero ((DerivedCategory.homologyFunctor B (j - 1)).obj D.obj₃) := by
    exact (DerivedCategory.isLE_iff _ _).1 hprod (j - 1) (by omega)
  have : Mono ((DerivedCategory.homologyFunctor B j).map D.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      D hD (j - 1) j (by omega)).2 (h₁.eq_of_src _ _)
  exact IsZero.of_mono ((DerivedCategory.homologyFunctor B j).map D.mor₁)
    ((DerivedCategory.isLE_iff _ _).1 hprod j (by omega))

end AlgebraicGeometry.ProEtale.CondensedRing

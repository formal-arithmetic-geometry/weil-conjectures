/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Functor.OfSequence

import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts

/-!
# Surjective towers of module complexes

Source: Stacks Project, Tags 091D (3), (5) and 0CQD
(blueprint: lem-weil-pbc-surjective-module-complex-tower-limit).
Natural index `n` denotes the source's positive index `n + 1`.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- Restrict a varying-ring complex tower to the vertex of its ring cone, using the
canonical composition comparison for restriction of scalars. Source: Stacks Project,
Tag 091D, preceding setup (blueprint: lem-weil-pbc-surjective-module-complex-tower-limit).
The comparison has identity underlying additive maps, so these are the original transitions.
-/
noncomputable def restrictedComplexTower
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A)
    (P : ∀ n : ℕ, CochainComplex (ModuleCat.{v} (A.obj (Opposite.op n))) ℤ)
    (t : ∀ n : ℕ, P (n + 1) ⟶
      ((restrictScalars (A.map (homOfLE (Nat.le_succ n)).op).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (P n)) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} c.pt) ℤ :=
  Functor.ofOpSequence (fun n ↦
    ((restrictScalars (c.π.app (Opposite.op (n + 1))).hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (t n) ≫
    (Functor.mapHomologicalComplexCompIso
      (restrictScalarsComp'
        (c.π.app (Opposite.op (n + 1))).hom
        (A.map (homOfLE (Nat.le_succ n)).op).hom
        (c.π.app (Opposite.op n)).hom
        (congrArg CommRingCat.Hom.hom (c.w (homOfLE (Nat.le_succ n)).op).symm)).symm
      (ComplexShape.up ℤ)).hom.app (P n))

private theorem module_countableAB4Star (R : Type u) [Ring R] :
    CountableAB4Star (ModuleCat.{v} R) := by
  let U := forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}
  have : PreservesFiniteColimits U := ⟨fun J _ _ ↦
    ModuleCat.forget₂PreservesColimitsOfShape.{v, u, 0, 0} R J⟩
  have : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} R) :=
    HasExactLimitsOfShape.domain_of_functor (Discrete ℕ)
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})
  have : HasFiniteBiproducts (ModuleCat.{v} R) := Abelian.hasFiniteBiproducts
  exact CountableAB4Star.of_hasExactLimitsOfShape_nat _

private theorem epi_one_sub
    {R : Type u} [Ring R] {F : ℕᵒᵖ ⥤ ModuleCat.{v} R}
    {B : Fan (fun n : ℕ ↦ F.obj (Opposite.op n))} (hB : IsLimit B)
    (s : B.pt ⟶ B.pt)
    (hs : ∀ n : ℕ, s ≫ B.proj n =
      B.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE n.le_succ).op)) :
    Epi (𝟙 B.pt - s) := by
  classical
  let M := fun n : ℕ ↦ F.obj (Opposite.op n)
  let e : B.pt ≅ ModuleCat.of R (∀ n, M n) :=
    hB.conePointUniqueUpToIso (ModuleCat.productConeIsLimit M)
  have he (n : ℕ) (x : B.pt) : e.hom x n = B.proj n x := by
    exact ConcreteCategory.congr_hom
      (hB.conePointUniqueUpToIso_hom_comp (ModuleCat.productConeIsLimit M) ⟨n⟩) x
  rw [ModuleCat.epi_iff_surjective]
  intro y
  have hsurj (n : ℕ) := (ModuleCat.epi_iff_surjective _).mp (hF n)
  let x : ∀ n : ℕ, M n := fun n ↦ Nat.rec (motive := fun n ↦ M n) 0
    (fun n xn ↦ (hsurj n (xn - B.proj n y)).choose) n
  have hx (n : ℕ) : F.map (homOfLE n.le_succ).op (x (n + 1)) =
      x n - B.proj n y := (hsurj n _).choose_spec
  let z : B.pt := e.inv x
  have hz (n : ℕ) : B.proj n z = x n := by
    rw [← he]
    exact congrFun (e.toLinearEquiv.apply_symm_apply x) n
  refine ⟨z, e.toLinearEquiv.injective (funext fun n ↦ ?_)⟩
  change e.hom ((𝟙 B.pt - s) z) n = e.hom y n
  rw [he, he]
  have hn := ConcreteCategory.congr_hom (hs n) z
  simp only [ModuleCat.comp_apply] at hn
  change B.proj n (z - s z) = B.proj n y
  simp only [map_sub, hn, hz, hx, sub_sub_cancel]

/-- A degreewise surjective tower is represented by its termwise limit, with the original
projections. Source: Stacks Project, Tags 091D (3), (5) and 0CQD
(blueprint: lem-weil-pbc-surjective-module-complex-tower-limit).

Proof: (1) Restrict scalars along the limiting ring cone. Cone compatibility and the
linearity of t make every transition linear over the limit ring. Form B degreewise as
product of the restricted complexes; its differentials act componentwise. (2) The kernel
of u = 1-s on B is the termwise limit P, with its projection inclusion j. Surjectivity of
u in each degree follows by choosing x_0 = 0 and recursively lifting x_n-y_n under t_n.
Thus 0 → P → B → B → 0 is degreewise short exact; no linear choice is needed.
(3) By lem-pc-cone-short-exact-quasi-iso, the map q : Cone(j) → B induced by u is a
quasi-isomorphism. Transport the distinguished cone triangle along Q(q), with connecting
map -Q(p)Q(q)⁻¹, keeping its first two arrows unchanged.
(4) Products of modules are exact, by componentwise kernels and choice of preimages.
Apply lem-weil-derived-limit-products-core to identify Q(B) with the derived product,
including its projections. (5) Checking on projections identifies Q(u) with the tower
transition endomorphism 1-s, and Q(j) followed by the nth projection is Q of the original
limit projection. The resulting triangle is precisely IsDerivedLimitTriangle.
-/
theorem surjective_moduleComplexTower_limit
    (A : ℕᵒᵖ ⥤ CommRingCat.{u}) (c : Cone A) (hc : IsLimit c)
    (P : ∀ n : ℕ, CochainComplex (ModuleCat.{v} (A.obj (Opposite.op n))) ℤ)
    (t : ∀ n : ℕ, P (n + 1) ⟶
      ((restrictScalars (A.map (homOfLE (Nat.le_succ n)).op).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (P n))
    (ht : ∀ (n : ℕ) (i : ℤ), Function.Surjective ((t n).f i))
    [HasDerivedCategory.{w} (ModuleCat.{v} c.pt)] :
    HasProduct (fun n : ℕ ↦
      DerivedCategory.Q.obj ((restrictedComplexTower A c P t).obj (Opposite.op n))) ∧
    ∀ [HasProduct (fun n : ℕ ↦
      DerivedCategory.Q.obj ((restrictedComplexTower A c P t).obj (Opposite.op n)))],
      ∃ δ : (∏ᶜ fun n : ℕ ↦
        DerivedCategory.Q.obj ((restrictedComplexTower A c P t).obj (Opposite.op n))) ⟶
        (DerivedCategory.Q.obj
          (HomologicalComplex.coneOfHasLimitEval (restrictedComplexTower A c P t)).pt)
          ⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle
          (fun n : ℕ ↦ DerivedCategory.Q.map
            ((restrictedComplexTower A c P t).map (homOfLE (Nat.le_succ n)).op))
          (DerivedCategory.Q.obj
            (HomologicalComplex.coneOfHasLimitEval (restrictedComplexTower A c P t)).pt)
          (Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map
            ((HomologicalComplex.coneOfHasLimitEval (restrictedComplexTower A c P t)).π.app
              (Opposite.op n)))) δ := by
  classical
  have _hc := hc
  let T := restrictedComplexTower A c P t
  let L := HomologicalComplex.coneOfHasLimitEval T
  let K := fun n : ℕ ↦ T.obj (Opposite.op n)
  let B : Fan K := Fan.mk (∏ᶜ K) (Pi.π K)
  let hB : IsLimit B := productIsProduct K
  let s : B.pt ⟶ B.pt := towerProductShift
    (fun n ↦ T.map (homOfLE n.le_succ).op)
  have hs (n : ℕ) : s ≫ B.proj n =
      B.proj (n + 1) ≫ T.map (homOfLE n.le_succ).op := Pi.lift_π _ _
  have hT (n : ℕ) (i : ℤ) : Epi ((T.map (homOfLE n.le_succ).op).f i) := by
    rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective
      (((restrictedComplexTower A c P t).map (homOfLE n.le_succ).op).f i)
    simp only [restrictedComplexTower, Functor.ofOpSequence_map_homOfLE_succ]
    intro y
    obtain ⟨x, hx⟩ := ht n i y
    exact ⟨x, hx⟩
  let S := ShortComplex.mk _ _ (Fan.IsLimit.lift_π_comp_one_sub_eq_zero hB s hs L)
  have hk := Fan.IsLimit.isLimitKernelForkOneSub hB s hs
    (HomologicalComplex.isLimitConeOfHasLimitEval T)
  have hS : S.ShortExact := by
    have : Mono S.f := mono_of_isLimit_fork hk
    have : Epi S.g := HomologicalComplex.epi_of_epi_f _ fun i ↦ by
      rw [HomologicalComplex.sub_f_apply, HomologicalComplex.id_f]
      exact epi_one_sub (F := T ⋙ HomologicalComplex.eval _ _ i)
        (isLimitFanMkObjOfIsLimit (HomologicalComplex.eval _ _ i) K _ hB) (s.f i)
        (fun n ↦ (HomologicalComplex.comp_f _ _ i).symm.trans
          ((congrArg (fun φ ↦ φ.f i) (hs n)).trans (HomologicalComplex.comp_f _ _ i)))
        (fun n ↦ hT n i)
    exact { exact := ShortComplex.exact_of_f_is_kernel _ hk }
  have : CountableAB4Star (ModuleCat.{v} c.pt) := module_countableAB4Star c.pt
  obtain ⟨hD, hQ, _⟩ := derivedCategory_countableProducts_core (ModuleCat.{v} c.pt)
  have hQB : IsLimit (DerivedCategory.Q.mapCone B) := (hQ ℕ K).some
  let hQFan := (Fan.isLimitMapConeEquiv DerivedCategory.Q K B) hQB
  refine ⟨inferInstance, ?_⟩
  intro hprod
  let K₀ := fun n : ℕ ↦ DerivedCategory.Q.obj (K n)
  let f₀ := fun n : ℕ ↦ DerivedCategory.Q.map (T.map (homOfLE n.le_succ).op)
  let p : DerivedCategory.Q.obj L.pt ⟶ ∏ᶜ K₀ :=
    Pi.lift (fun n : ℕ ↦ DerivedCategory.Q.map (L.π.app (Opposite.op n)))
  let E : DerivedCategory.Q.obj B.pt ≅ ∏ᶜ K₀ :=
    hQFan.conePointUniqueUpToIso (productIsProduct K₀)
  have hE (n : ℕ) : E.hom ≫ Pi.π K₀ n = DerivedCategory.Q.map (B.proj n) :=
    hQFan.conePointUniqueUpToIso_hom_comp (productIsProduct K₀) ⟨n⟩
  have hπ (n : ℕ) : p ≫ Pi.π K₀ n =
      DerivedCategory.Q.map (L.π.app (Opposite.op n)) := Pi.lift_π _ _
  have hi : DerivedCategory.Q.map S.f ≫ E.hom = p := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hE, ← Functor.map_comp, hπ]
    exact congrArg DerivedCategory.Q.map (hB.fac _ ⟨n⟩)
  have hu (n : ℕ) : S.g ≫ B.proj n = B.proj n -
      B.proj (n + 1) ≫ T.map (homOfLE n.le_succ).op := by
    change (𝟙 B.pt - s) ≫ B.proj n = _
    rw [Preadditive.sub_comp, Category.id_comp, hs]
  have htrans : DerivedCategory.Q.map S.g ≫ E.hom =
      E.hom ≫ towerTransitionEndomorphism f₀ := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, hE, ← Functor.map_comp, hu, Functor.map_sub]
    simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
      Category.id_comp, Preadditive.comp_sub, Pi.lift_π, hE, f₀]
    rw [Functor.map_comp, ← Category.assoc, hE]
  let δ := DerivedCategory.triangleOfSESδ hS
  refine ⟨E.inv ≫ δ, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk (DerivedCategory.Q.map S.f) (DerivedCategory.Q.map S.g) δ)
      (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism f₀) (E.inv ≫ δ))
      (Iso.refl _) E E (by simpa using hi) htrans (by simp))).mp
    (DerivedCategory.triangleOfSES_distinguished hS)

end ModuleCat

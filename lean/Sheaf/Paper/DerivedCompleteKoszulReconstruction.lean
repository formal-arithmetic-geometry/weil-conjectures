/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.Triangulated.DerivedLimitLevelwiseIsomorphism
import Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import Mathlib.Algebra.Homology.HomologicalComplexLimits

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Koszul reconstruction of a derived-complete reduction tower

Source: Stacks Project, algebraization.tex Tag 0A0E and sites-cohomology.tex Tag 0941
(blueprint: lem-pur-derived-complete-koszul-reconstruction).

The strict towers and quotient maps are the canonical constructions of
`def-pur-principal-koszul-quotient-towers`. Total right derived inverse limit is
provided by the recorded strict-tower homotopy-limit dependency.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem roosComparison_reconstruction
    {D : Type uC} [Category.{vC} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
    {M N : ℕ → D} [HasProduct M] [HasProduct N]
    (v : ∀ n, M (n + 1) ⟶ M n) (u : ∀ n, N (n + 1) ⟶ N n)
    (a : ∀ n, M n ⟶ N n) (ha : ∀ n, v n ≫ a n = a (n + 1) ≫ u n)
    [∀ n, IsIso (a n)] (L K : D) (pV : L ⟶ ∏ᶜ M) (pU : K ⟶ ∏ᶜ N)
    (δV : ∏ᶜ M ⟶ L⟦(1 : ℤ)⟧) (δU : ∏ᶜ N ⟶ K⟦(1 : ℤ)⟧)
    (hv : IsDerivedLimitTriangle v L pV δV) (hu : IsDerivedLimitTriangle u K pU δU) :
    ∃ φ : K ≅ L, φ.hom ≫ pV ≫ Limits.Pi.map a = pU ∧
      Limits.Pi.map a ≫ δU = δV ≫ φ.inv⟦(1 : ℤ)⟧' := by
  let ai := fun n ↦ inv (a n)
  have hai (n : ℕ) : u n ≫ ai n = ai (n + 1) ≫ v n := by
    dsimp only [ai]
    apply (IsIso.comp_inv_eq (a n)).2
    rw [Category.assoc]
    apply (IsIso.eq_inv_comp (a (n + 1))).2
    exact (ha n).symm
  have hi : IsIso (Limits.Pi.map a) := by
    refine ⟨⟨Limits.Pi.map ai, ?_, ?_⟩⟩ <;> simp [ai, Limits.Pi.map_comp_map]
  let A := asIso (Limits.Pi.map a)
  have hAi : Limits.Pi.map ai = A.inv := by
    apply (cancel_mono A.hom).1
    simp [A, ai, Limits.Pi.map_comp_map]
  have hn := towerTransitionEndomorphism_natural_backward u v ai
    (fun n ↦ (hai n).symm)
  obtain ⟨ψ, hψp, hψδ⟩ :=
    Pretriangulated.complete_distinguished_triangle_morphism₁ _ _ hu hv
      (Limits.Pi.map ai) (Limits.Pi.map ai) hn.symm
  have hp : ψ ≫ pV = pU ≫ Limits.Pi.map ai := hψp.symm
  have hd : δU ≫ ψ⟦(1 : ℤ)⟧' = Limits.Pi.map ai ≫ δV := hψδ
  have : IsIso ψ := isIso_derivedLimit_of_levelwise u v K L pU pV δU δV hu hv
    ai hai ψ hp hd
  refine ⟨asIso ψ, ?_, ?_⟩
  · change ψ ≫ pV ≫ A.hom = pU
    rw [← Category.assoc, hp, hAi, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · change A.hom ≫ δU = δV ≫ inv ψ⟦(1 : ℤ)⟧'
    apply (cancel_epi A.inv).1
    rw [Iso.inv_hom_id_assoc, ← hAi, ← Category.assoc, ← hd, Category.assoc,
      ← Functor.map_comp, IsIso.hom_inv_id, Functor.map_id, Category.comp_id]

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
variable {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

set_option hygiene false in
local notation "𝓞" => (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
set_option hygiene false in
local notation "𝒜" => ringedSiteModules.{r} 𝓞

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private theorem principalAugmentation_quasiIso
    (t : (SheafOfModules.unit 𝓞).sections)
    (hreg : Mono (globalSectionMultiplication R t)) (m : ℕ) :
    QuasiIso (principalAugmentation R t m) := by
  have hp (n : ℕ) : Mono (endoPow (globalSectionMultiplication R t) n) := by
    induction n with
    | zero => change Mono (𝟙 _); infer_instance
    | succ n hn => change Mono (endoPow _ n ≫ _); infer_instance
  let f := endoPow (globalSectionMultiplication R t) (m + 1)
  have : Mono f := hp (m + 1)
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  have : PreservesFiniteLimits (CochainComplex.singleFunctor 𝒜 0) :=
    inferInstanceAs (PreservesFiniteLimits (HomologicalComplex.single 𝒜 (.up ℤ) 0))
  have : PreservesFiniteColimits (CochainComplex.singleFunctor 𝒜 0) :=
    inferInstanceAs (PreservesFiniteColimits (HomologicalComplex.single 𝒜 (.up ℤ) 0))
  have hSC := hS.map_of_exact (CochainComplex.singleFunctor 𝒜 0)
  exact CochainComplex.mappingCone.quasiIso_descShortComplex hSC

variable [HasDerivedCategory.{w} 𝒜]
variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ 𝒜)]

/-- Total right derived inverse limit supplied by the strict-tower dependency. The defining
universal property determines this functor up to unique natural isomorphism.
Source: Stacks Tag 0941 (blueprint: lem-pur-derived-complete-koszul-reconstruction). -/
noncomputable def koszulRlim : DerivedCategory.{w} (ℕᵒᵖ ⥤ 𝒜) ⥤ DerivedCategory.{w} 𝒜 :=
  Classical.choose (ringedStrictTowerHomotopyLimitIndependentCoefficients J 𝓞
    (fun U a b ↦ @mul_comm (R.obj.obj U) _ a b))

/-- The derived strict Koszul completion, using the total right derived inverse limit.
Source: Stacks Tags 0A0E and 0941
(blueprint: lem-pur-derived-complete-koszul-reconstruction). -/
noncomputable def koszulCompletion (P : CochainComplex 𝒜 ℤ)
    (t : (SheafOfModules.unit 𝓞).sections) : DerivedCategory.{w} 𝒜 :=
  (koszulRlim R).obj (DerivedCategory.Q.obj
    (koszulTowerComplex R (koszulTensorTower R P t)))

set_option maxHeartbeats 1000000 in
-- Destructing the strict-limit universal property elaborates its full dependent interface.
/-- Koszul reconstruction of the derived-complete quotient tower.

Source: Stacks Tag 0A0E, lemma-derived-completion-koszul; Tag 0941,
lemma-derived-limit-is-ok (blueprint: lem-pur-derived-complete-koszul-reconstruction).

Proof: (1) Since `t` is monic, every positive power is monic. The principal cone has
zero cohomology in degree `-1` and quotient cohomology in degree zero, hence its quotient
augmentation is a quasi-isomorphism. The `t/id` and quotient transitions commute strictly.
(2) K-flatness of `P` tensors the acyclic cone of this augmentation to an acyclic complex.
Our tensor order is `Q_m ⊗ P`, exactly the recorded K-flat convention; symmetry identifies
it with the source's `P ⊗ Q_m`. Thus the strict tensor map is levelwise a quasi-isomorphism.
(3) Exact level evaluations identify this with a quasi-isomorphism in the tower category.
The total right derived limit functor of the strict-tower dependency inverts it and
preserves the equality of the strict augmentation composites.
(4) The dependency supplies a Roos triangle on that actual derived limit. In any given
quotient Roos triangle whose first map has the canonical quotient components through `e`,
the product of the level comparisons is invertible. TR3 on rotated triangles with its
inverse on both products gives `φ`; two-out-of-three makes `φ` invertible. The first
triangle equation gives all projection equations, and the third gives the displayed
shifted connecting equation for this very same `φ`.
-/
theorem derivedComplete_koszul_reconstruction
    (t : (SheafOfModules.unit 𝓞).sections)
    (hreg : Mono (globalSectionMultiplication R t))
    (P : CochainComplex 𝒜 ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients P) :
    let V := koszulTensorTower R P t
    let U := reductionTensorTower R P t
    let a := koszulTensorTowerComparison R P t
    let aC := koszulTowerComplexMap R a
    let VD := fun m : ℕ ↦ DerivedCategory.Q.{w}.obj (V.obj (op m))
    let UD := fun m : ℕ ↦ DerivedCategory.Q.{w}.obj (U.obj (op m))
    let aD := fun m : ℕ ↦ DerivedCategory.Q.{w}.map (a.app (op m))
    let v := fun m : ℕ ↦ DerivedCategory.Q.{w}.map
      (V.map (homOfLE (Nat.le_succ m)).op)
    let u := fun m : ℕ ↦ DerivedCategory.Q.{w}.map
      (U.map (homOfLE (Nat.le_succ m)).op)
    (∀ m : ℕ, QuasiIso (a.app (op m))) ∧ QuasiIso aC ∧
      IsIso (DerivedCategory.Q.{w}.map aC) ∧
      IsIso ((koszulRlim R).map (DerivedCategory.Q.{w}.map aC)) ∧
      ((koszulRlim R).map (DerivedCategory.Q.{w}.map
          (koszulTowerComplexMap R (koszulStrictAugmentation R P t))) ≫
        (koszulRlim R).map (DerivedCategory.Q.{w}.map aC) =
        (koszulRlim R).map (DerivedCategory.Q.{w}.map
          (koszulTowerComplexMap R (koszulStrictAugmentation R P t ≫ a)))) ∧
      ∃ (_hV : HasProduct VD) (_hU : HasProduct UD)
        (pV : koszulCompletion R P t ⟶ ∏ᶜ VD)
        (δV : ∏ᶜ VD ⟶ (koszulCompletion R P t)⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle v (koszulCompletion R P t) pV δV ∧
        IsIso (Limits.Pi.map aD) ∧
        ∀ (K : DerivedCategory.{w} 𝒜) (e : DerivedCategory.Q.{w}.obj P ≅ K)
          (pU : K ⟶ ∏ᶜ UD) (δU : ∏ᶜ UD ⟶ K⟦(1 : ℤ)⟧),
          IsDerivedLimitTriangle u K pU δU →
          (∀ m : ℕ, pU ≫ Limits.Pi.π UD m =
            e.inv ≫ DerivedCategory.Q.{w}.map (koszulRepresentativeQuotient R P t m)) →
          ∃ φ : K ≅ koszulCompletion R P t,
            (∀ m : ℕ, φ.hom ≫ pV ≫ Limits.Pi.π VD m ≫ aD m =
              e.inv ≫ DerivedCategory.Q.{w}.map (koszulRepresentativeQuotient R P t m)) ∧
            φ.hom ≫ pV ≫ Limits.Pi.map aD = pU ∧
            Limits.Pi.map aD ≫ δU = δV ≫ φ.inv⟦(1 : ℤ)⟧' := by
  dsimp only
  let V := koszulTensorTower R P t
  let U := reductionTensorTower R P t
  let a := koszulTensorTowerComparison R P t
  let X := koszulTowerComplex R V
  let aC := koszulTowerComplexMap R a
  have hl (m : ℕ) : QuasiIso (a.app (op m)) := by
    exact kFlatTensorPreservesQuasiIsoIndependentCoefficients R P hP (principalAugmentation R t m)
      (principalAugmentation_quasiIso R t hreg m)
  have hC : QuasiIso aC := by
    apply (HomologicalComplex.quasiIso_iff_evaluation aC).2
    intro n
    exact hl n.unop
  have hQ : IsIso (DerivedCategory.Q.{w}.map aC) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ aC).2 hC
  have hlim : IsIso ((koszulRlim R).map (DerivedCategory.Q.{w}.map aC)) := inferInstance
  refine ⟨hl, hC, hQ, hlim, ?_, ?_⟩
  · have hc : koszulTowerComplexMap R (koszulStrictAugmentation R P t ≫ a) =
        koszulTowerComplexMap R (koszulStrictAugmentation R P t) ≫ aC := by
      ext i n
      rfl
    rw [hc, Functor.map_comp, Functor.map_comp]
  · obtain ⟨η, hη, hI, hres, hshift, hproducts, E, ε, p, δ,
      htri, hroos, hp, hδ, hz, hcone⟩ :=
      Classical.choose_spec (ringedStrictTowerHomotopyLimitIndependentCoefficients J 𝓞
        (fun U a b ↦ @mul_comm (R.obj.obj U) _ a b))
    let VD := fun m : ℕ ↦ DerivedCategory.Q.{w}.obj (V.obj (op m))
    let UD := fun m : ℕ ↦ DerivedCategory.Q.{w}.obj (U.obj (op m))
    let aD := fun m : ℕ ↦ DerivedCategory.Q.{w}.map (a.app (op m))
    let v := fun m : ℕ ↦ DerivedCategory.Q.{w}.map
      (V.map (homOfLE (Nat.le_succ m)).op)
    let u := fun m : ℕ ↦ DerivedCategory.Q.{w}.map
      (U.map (homOfLE (Nat.le_succ m)).op)
    have ha (m : ℕ) : IsIso (aD m) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (hl m)
    have han (m : ℕ) : v m ≫ aD m = aD (m + 1) ≫ u m := by
      dsimp only [v, u, aD]
      rw [← Functor.map_comp, ← Functor.map_comp, a.naturality]
    let Z := DerivedCategory.Q.{w}.obj X
    let W := fun m : ℕ ↦ (E.obj Z).obj (op m)
    let ew : E.obj Z ≅ V ⋙ DerivedCategory.Q.{w} := ε.app X
    let b := fun m : ℕ ↦ ew.hom.app (op m)
    have hb (m : ℕ) : IsIso (b m) := inferInstance
    have hprodB : IsIso (Limits.Pi.map b) := by
      refine ⟨⟨Limits.Pi.map (fun m ↦ inv (b m)), ?_, ?_⟩⟩ <;>
        simp [Limits.Pi.map_comp_map]
    let B := asIso (Limits.Pi.map b)
    let pV : koszulCompletion R P t ⟶ ∏ᶜ VD := p Z ≫ B.hom
    let δV : ∏ᶜ VD ⟶ (koszulCompletion R P t)⟦(1 : ℤ)⟧ := B.inv ≫ δ Z
    have hv : IsDerivedLimitTriangle v (koszulCompletion R P t) pV δV := by
      have hn := towerTransitionEndomorphism_natural_backward
        (fun m : ℕ ↦ (E.obj Z).map (homOfLE (Nat.le_succ m)).op) v b
        (fun m ↦ (ew.hom.naturality (homOfLE (Nat.le_succ m)).op).symm)
      exact Pretriangulated.isomorphic_distinguished _ (hroos Z) _
        (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) B.symm B.symm
          (by simp [pV])
          (by
            change towerTransitionEndomorphism v ≫ B.inv =
              B.inv ≫ towerTransitionEndomorphism _
            apply (Iso.comp_inv_eq B).2
            rw [Category.assoc]
            exact (Iso.eq_inv_comp B).2 hn)
          (by simp [δV]))
    have hprodA : IsIso (Limits.Pi.map aD) := by
      refine ⟨⟨Limits.Pi.map (fun m ↦ inv (aD m)), ?_, ?_⟩⟩ <;>
        simp [Limits.Pi.map_comp_map]
    refine ⟨inferInstance, inferInstance, pV, δV, hv, hprodA, ?_⟩
    intro K e pU δU hu he
    obtain ⟨φ, hprojection, hconnecting⟩ := roosComparison_reconstruction v u aD han
      (koszulCompletion R P t) K pV pU δV δU hv hu
    refine ⟨φ, ?_, hprojection, hconnecting⟩
    intro m
    have hh := congrArg (fun f ↦ f ≫ Limits.Pi.π UD m) hprojection
    rw [Category.assoc, Category.assoc, Limits.Pi.map_π] at hh
    exact hh.trans (he m)

end CategoryTheory

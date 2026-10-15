/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Sheaf.CategoryTheory.TruncationCouple
public import Sheaf.CategoryTheory.ExactCoupleConvergence
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Sheaf.CategoryTheory.AbutmentImageFiltration
import Sheaf.CategoryTheory.ExactCoupleMorphism
import all Sheaf.CategoryTheory.ExactFunctorCouple

/-!
# Hypercohomology filtrations for an étale base-change square

Source: blueprint sec-proper-base-change/sk-thm-properbasechange, order 1315;
Stacks Project, Tags 0DDE and 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations).

The three functors are Rf_*, g^{-1}Rf_*, and Rf'_*g'^{-1}. The generic construction
below applies cohomology to their images of the canonical truncation triangles.
The index of `pageCouple` is the actual page minus two.
-/

@[expose] public section

set_option synthInstance.maxSize 2048

universe u v₁ u₁ v₂ u₂ w₁ w₂ uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Transport an exact pair along three object isomorphisms. -/
private theorem exact_transport
    {C : Type uC} [Category.{vC, uC} C] [Abelian C]
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₃)
    (w : a ≫ b = 0) (h : (ShortComplex.mk a b w).Exact)
    {a' : Y₁ ⟶ Y₂} {b' : Y₂ ⟶ Y₃}
    (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂) (e₃ : X₃ ≅ Y₃)
    (h₁ : e₁.hom ≫ a' = a ≫ e₂.hom)
    (h₂ : e₂.hom ≫ b' = b ≫ e₃.hom) :
    ∃ w' : a' ≫ b' = 0, (ShortComplex.mk _ _ w').Exact := by
  have w' : a' ≫ b' = 0 := by
    rw [← cancel_epi e₁.hom, ← Category.assoc, h₁, Category.assoc, h₂,
      ← Category.assoc, w, zero_comp, comp_zero]
  refine ⟨w', ShortComplex.exact_of_iso ?_ h⟩
  exact ShortComplex.isoMk e₁ e₂ e₃ h₁ h₂

/-- Naturality of an indexed morphism with respect to equality transports. -/
private theorem cast_naturality
    {C : Type uC} [Category.{vC, uC} C] {I : Type*} (X Y : I → C)
    (f : ∀ i, X i ⟶ Y i) {i j : I} (h : i = j) :
    eqToHom (congrArg X h) ≫ f j = f i ≫ eqToHom (congrArg Y h) := by
  subst j
  simp

/-- Naturality with a common target, including its final equality transports. -/
private theorem cast_naturality_last
    {C : Type uC} [Category.{vC, uC} C] {I : Type*} (X Y : I → C)
    (f : ∀ i, X i ⟶ Y i) {i j : I} (h : i = j) {Z : C}
    (hi : Y i = Z) (hj : Y j = Z) :
    eqToHom (congrArg X h) ≫ f j ≫ eqToHom hj = f i ≫ eqToHom hi := by
  subst j
  simp

/-- Reindex a family of morphisms along equalities of the two indices. -/
private theorem reindex_hom
    {C : Type uC} [Category.{vC, uC} C] (X Y : ℤ → ℤ → C)
    (f : ∀ p q, X p q ⟶ Y p q) {p q p' q' : ℤ}
    (hp : p = p') (hq : q = q') :
    eqToHom (congrArg₂ X hp hq) ≫ f p' q' =
      f p q ≫ eqToHom (congrArg₂ Y hp hq) := by
  subst p'
  subst q'
  simp

/-- Adding the zero bidegree does not change an exact pair. -/
private theorem exact_zero_right
    {C : Type uC} [Category.{vC, uC} C] [Abelian C] (D E : ℤ → ℤ → C)
    (g : ∀ p q, D p q ⟶ E p q)
    (f : ∀ p q, E p q ⟶ D (p + 2) (q - 1)) (p q : ℤ)
    (h : ∃ w : g p q ≫ f p q = 0, (ShortComplex.mk _ _ w).Exact) :
    ∃ w : (g p q ≫ eqToHom (by simp : E p q = E (p + (0 : ℕ)) (q - (0 : ℕ)))) ≫
        f (p + (0 : ℕ)) (q - (0 : ℕ)) = 0,
      (ShortComplex.mk _ _ w).Exact := by
  obtain ⟨w, h⟩ := h
  refine exact_transport _ _ w h (Iso.refl _) (eqToIso ?_) (eqToIso ?_) ?_ ?_
  · simp
  · simp
  · simp
  · exact reindex_hom E (fun p q ↦ D (p + 2) (q - 1)) f
      (by simp) (by simp)

/-- Postcomposing the last map with an equality isomorphism preserves exactness. -/
private theorem exact_cast_last
    {C : Type uC} [Category.{vC, uC} C] [Abelian C] {X Y Z Z' : C}
    (a : X ⟶ Y) (b : Y ⟶ Z)
    (h : ∃ w : a ≫ b = 0, (ShortComplex.mk _ _ w).Exact) (hz : Z = Z') :
    ∃ w : a ≫ (b ≫ eqToHom hz) = 0, (ShortComplex.mk _ _ w).Exact := by
  obtain ⟨w, h⟩ := h
  exact exact_transport a b w h (Iso.refl _) (Iso.refl _) (eqToIso hz)
    (by simp) (by simp)

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]
  (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] [F.IsTriangulated]
  (K : CochainComplex.Plus A)
/-- The D-terms after applying the chosen triangulated functor to truncations.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyD (p q : ℤ) : B :=
  (DerivedCategory.homologyFunctor B (p + q)).obj
    (F.obj (DerivedCategory.Q.obj (TruncationCouple.truncation K q).obj))

/-- The E₂-terms after applying the functor to the shifted cohomology complexes.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyE (p q : ℤ) : B :=
  (DerivedCategory.homologyFunctor B (p + q)).obj
    (F.obj (DerivedCategory.Q.obj (TruncationCouple.cohomologyComplex K q).obj))

/-- The truncation inclusion, of bidegree (-1,+1).
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyAlpha (p q : ℤ) :
    hypercohomologyD F K p q ⟶ hypercohomologyD F K (p - 1) (q + 1) :=
  (DerivedCategory.homologyFunctor B (p + q)).map
    (F.map (DerivedCategory.Q.map
      (eqToHom (congrArg (fun n : ℤ ↦ K.obj.truncLE n)
        (by omega : q = (q + 1) - 1)) ≫ TruncationCouple.transition K (q + 1)))) ≫
    eqToHom (by unfold hypercohomologyD; congr 2; omega)

/-- The projection from a truncation to its top cohomology, of bidegree (0,0).
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyG (p q : ℤ) :
    hypercohomologyD F K p q ⟶ hypercohomologyE F K (p + (0 : ℕ)) (q - (0 : ℕ)) :=
  (DerivedCategory.homologyFunctor B (p + q)).map
    (F.map (DerivedCategory.Q.map (TruncationCouple.projection K q))) ≫
    eqToHom (by simp only [hypercohomologyE, Nat.cast_zero, add_zero, sub_zero])

/-- The cohomological boundary of the image triangle, of bidegree (+2,-1).
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyBoundary (p q : ℤ) :
    hypercohomologyE F K p q ⟶ hypercohomologyD F K (p + 2) (q - 1) :=
  DerivedCategory.HomologySequence.δ
    (F.mapTriangle.obj (TruncationCouple.triangle K q)) (p + q) (p + q + 1) ≫
    eqToHom (by unfold hypercohomologyD; congr 2; omega)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The three cohomology maps form an exact couple.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations).

Proof: The canonical truncation triangle is distinguished (def-sp-truncation-couple). The
triangulated functor carries it to a distinguished triangle. Its cohomology long exact sequence
gives the three zero composites and image-kernel equalities at every bidegree; reindex by the
displayed shifts (def-sp-exact-couple). -/
theorem hypercohomology_maps_exact :
    (∀ p q : ℤ, hypercohomologyBoundary F K p q ≫
      hypercohomologyAlpha F K (p + 2) (q - 1) = 0) ∧
    (∀ p q : ℤ, hypercohomologyG F K p q ≫ 
      hypercohomologyBoundary F K (p + (0 : ℕ)) (q - (0 : ℕ)) = 0) ∧
    (∀ p q : ℤ, hypercohomologyAlpha F K p q ≫
      hypercohomologyG F K (p - 1) (q + 1) = 0) ∧
    (∀ p q : ℤ, imageSubobject (hypercohomologyBoundary F K p q) =
      kernelSubobject (hypercohomologyAlpha F K (p + 2) (q - 1))) ∧
    (∀ p q : ℤ, imageSubobject (hypercohomologyG F K p q) =
      kernelSubobject (hypercohomologyBoundary F K (p + (0 : ℕ)) (q - (0 : ℕ)))) ∧
    (∀ p q : ℤ, imageSubobject (hypercohomologyAlpha F K p q) =
      kernelSubobject (hypercohomologyG F K (p - 1) (q + 1))) := by
  have hT (q : ℤ) : F.mapTriangle.obj (TruncationCouple.triangle K q) ∈
      Pretriangulated.distinguishedTriangles := by
    apply F.map_distinguished
    exact (Classical.choose_spec (TruncationCouple.existsUnique_boundary K q)).1
  have h₁ (p q : ℤ) : ∃ w : hypercohomologyBoundary F K p q ≫
      hypercohomologyAlpha F K (p + 2) (q - 1) = 0,
      (ShortComplex.mk _ _ w).Exact := by
    have h := DerivedCategory.HomologySequence.exact₁
      (F.mapTriangle.obj (TruncationCouple.triangle K q)) (hT q) (p + q) (p + q + 1)
    refine exact_transport _ _ _ h (Iso.refl _) (eqToIso ?_) (eqToIso ?_) ?_ ?_
    · unfold hypercohomologyD
      congr 2
      omega
    · unfold hypercohomologyD
      rw [sub_add_cancel]
      congr 2
      omega
    · simp [hypercohomologyBoundary]
    · simp only [hypercohomologyAlpha, Functor.map_comp, eqToHom_map, Category.assoc,
        eqToIso.hom, eqToHom_trans_assoc]
      simpa only [TruncationCouple.triangle, Functor.mapTriangle,
        Pretriangulated.Triangle.mk_mor₁] using
        cast_naturality_last
          (fun rn : ℤ × ℤ ↦ (DerivedCategory.homologyFunctor B rn.2).obj
            (F.obj (DerivedCategory.Q.obj (TruncationCouple.truncation K (rn.1 - 1)).obj)))
          (fun rn : ℤ × ℤ ↦ (DerivedCategory.homologyFunctor B rn.2).obj
            (F.obj (DerivedCategory.Q.obj (TruncationCouple.truncation K rn.1).obj)))
          (fun rn ↦ (DerivedCategory.homologyFunctor B rn.2).map
            (F.map (DerivedCategory.Q.map (TruncationCouple.transition K rn.1))))
          (by ext <;> omega : (q, p + q + 1) = (q - 1 + 1, p + 2 + (q - 1)))
          (Z := hypercohomologyD F K (p + 2 - 1) (q - 1 + 1))
          (by unfold hypercohomologyD; rw [sub_add_cancel]; congr 2; omega)
          (by unfold hypercohomologyD; congr 2; omega)
  have h₂ (p q : ℤ) : ∃ w : hypercohomologyG F K p q ≫
      hypercohomologyBoundary F K (p + (0 : ℕ)) (q - (0 : ℕ)) = 0,
      (ShortComplex.mk _ _ w).Exact := by
    have h := DerivedCategory.HomologySequence.exact₃
      (F.mapTriangle.obj (TruncationCouple.triangle K q)) (hT q) (p + q) (p + q + 1)
    apply exact_zero_right (hypercohomologyD F K) (hypercohomologyE F K)
      (fun p q ↦ (DerivedCategory.homologyFunctor B (p + q)).map
        (F.map (DerivedCategory.Q.map (TruncationCouple.projection K q))))
      (hypercohomologyBoundary F K)
    refine exact_transport _ _ _ h (Iso.refl _) (Iso.refl _) (eqToIso ?_) ?_ ?_
    · unfold hypercohomologyD
      congr 2
      omega
    · simp [TruncationCouple.triangle, Functor.mapTriangle]
    · simp [hypercohomologyBoundary]
  have h₃ (p q : ℤ) : ∃ w : hypercohomologyAlpha F K p q ≫
      hypercohomologyG F K (p - 1) (q + 1) = 0,
      (ShortComplex.mk _ _ w).Exact := by
    apply exact_cast_last
    have h := DerivedCategory.HomologySequence.exact₂
      (F.mapTriangle.obj (TruncationCouple.triangle K (q + 1))) (hT (q + 1)) (p + q)
    refine exact_transport _ _ _ h (eqToIso ?_) (eqToIso ?_) (eqToIso ?_) ?_ ?_
    · exact congrArg (fun r ↦ (DerivedCategory.homologyFunctor B (p + q)).obj
        (F.obj (DerivedCategory.Q.obj (TruncationCouple.truncation K r).obj)))
          (by omega : (q + 1) - 1 = q)
    · unfold hypercohomologyD
      congr 2
      omega
    · dsimp only [TruncationCouple.triangle, Functor.mapTriangle]
      congr 2
      omega
    · simp [hypercohomologyAlpha, TruncationCouple.triangle, Functor.mapTriangle,
        Functor.map_comp, eqToHom_map]
    · exact cast_naturality
        (fun n ↦ (DerivedCategory.homologyFunctor B n).obj
          (F.mapTriangle.obj (TruncationCouple.triangle K (q + 1))).obj₂)
        (fun n ↦ (DerivedCategory.homologyFunctor B n).obj
          (F.mapTriangle.obj (TruncationCouple.triangle K (q + 1))).obj₃)
        (fun n ↦ (DerivedCategory.homologyFunctor B n).map
          (F.mapTriangle.obj (TruncationCouple.triangle K (q + 1))).mor₂) (by omega)
  exact ⟨fun p q ↦ (h₁ p q).choose, fun p q ↦ (h₂ p q).choose,
    fun p q ↦ (h₃ p q).choose,
    fun p q ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp (h₁ p q).choose_spec,
    fun p q ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp (h₂ p q).choose_spec,
    fun p q ↦ (ShortComplex.exact_iff_image_eq_kernel _).mp (h₃ p q).choose_spec⟩

/-- The exact truncation couple, with explicit data and separately named exactness proofs.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyCouple : BigradedExactCouple B 0 :=
  BigradedExactCouple.ofShifted (hypercohomologyD F K) (hypercohomologyE F K)
    (hypercohomologyAlpha F K) (hypercohomologyBoundary F K) (hypercohomologyG F K)
    (hypercohomology_maps_exact F K).1
    (hypercohomology_maps_exact F K).2.1
    (hypercohomology_maps_exact F K).2.2.1
    (hypercohomology_maps_exact F K).2.2.2.1
    (hypercohomology_maps_exact F K).2.2.2.2.1
    (hypercohomology_maps_exact F K).2.2.2.2.2

/-- The canonical map from a truncation to the abutment in total degree n.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyAbutmentMap (n q : ℤ) :
    (DerivedCategory.homologyFunctor B n).obj
        (F.obj (DerivedCategory.Q.obj (TruncationCouple.truncation K q).obj)) ⟶
      (DerivedCategory.homologyFunctor B n).obj (F.obj (DerivedCategory.Q.obj K.obj)) :=
  (DerivedCategory.homologyFunctor B n).map
    (F.map (DerivedCategory.Q.map (K.obj.ιTruncLE q)))

set_option linter.unusedSectionVars false in
/-- The images of the truncation maps decrease with p.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations).

Proof: For i ≤ j, n-j ≤ n-i. The canonical inclusion of the lower truncation into the higher
truncation commutes with their inclusions into K. Apply F and H^n to this factorization. The image
of a composite is contained in the image of its second factor, which gives the required
antitonicity (def-sp-image-filtration). -/
theorem hypercohomology_images_antitone (n : ℤ) :
    Antitone (fun p : ℤ ↦ imageSubobject (hypercohomologyAbutmentMap F K n (n - p))) := by
  intro i j hij
  have : (K.obj.truncLE (n - j)).IsStrictlyLE (n - i) :=
    CochainComplex.isStrictlyLE_of_le _ (n - j) (n - i) (by omega)
  let t : K.obj.truncLE (n - j) ⟶ K.obj.truncLE (n - i) :=
    inv ((K.obj.truncLE (n - j)).ιTruncLE (n - i)) ≫
      CochainComplex.truncLEMap (K.obj.ιTruncLE (n - j)) (n - i)
  have ht : t ≫ K.obj.ιTruncLE (n - i) = K.obj.ιTruncLE (n - j) := by
    simp [t, Category.assoc]
  let t' := (DerivedCategory.homologyFunctor B n).map (F.map (DerivedCategory.Q.map t))
  have ht' : t' ≫ hypercohomologyAbutmentMap F K n (n - i) =
      hypercohomologyAbutmentMap F K n (n - j) := by
    simp only [t', hypercohomologyAbutmentMap, ← Functor.map_comp, ht]
  dsimp only
  rw [← ht']
  exact imageSubobject_comp_le _ _

/-- The image filtration FᵖHⁿ = im(Hⁿ(Fτ≤(n-p)K) → Hⁿ(FK)).
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyFiltration (n : ℤ) :
    DecreasingFiltration
      ((DerivedCategory.homologyFunctor B n).obj (F.obj (DerivedCategory.Q.obj K.obj))) where
  F p := imageSubobject (hypercohomologyAbutmentMap F K n (n - p))
  F_succ_le p := hypercohomology_images_antitone F K n (by omega)

omit [HasDerivedCategory A] in
set_option backward.isDefEq.respectTransparency false in
private theorem cycles_iso {S₁ S₂ : ShortComplex A} (φ : S₁ ⟶ S₂)
    [Epi φ.τ₁] [Mono φ.τ₂] [IsIso (ShortComplex.homologyMap φ)] :
    IsIso (ShortComplex.cyclesMap φ) := by
  let B₁ := ShortComplex.mk S₁.toCycles S₁.homologyπ S₁.toCycles_comp_homologyπ
  let B₂ := ShortComplex.mk S₂.toCycles S₂.homologyπ S₂.toCycles_comp_homologyπ
  let ψ : B₁ ⟶ B₂ :=
    { τ₁ := φ.τ₁
      τ₂ := ShortComplex.cyclesMap φ
      τ₃ := ShortComplex.homologyMap φ
      comm₁₂ := (ShortComplex.toCycles_naturality φ).symm
      comm₂₃ := (ShortComplex.homologyπ_naturality φ).symm }
  have : Epi ψ.τ₁ := inferInstanceAs (Epi φ.τ₁)
  have : Epi ψ.τ₃ := inferInstanceAs (Epi (ShortComplex.homologyMap φ))
  have : Epi B₁.g := inferInstanceAs (Epi S₁.homologyπ)
  have : Epi B₂.g := inferInstanceAs (Epi S₂.homologyπ)
  have : Epi (ShortComplex.cyclesMap φ) :=
    ShortComplex.epi_τ₂_of_exact_of_epi ψ
      (B₂.exact_of_g_is_cokernel S₂.homologyIsCokernel)
  have : Mono (ShortComplex.cyclesMap φ) :=
    mono_of_mono_fac (ShortComplex.cyclesMap_i φ)
  exact isIso_of_mono_of_epi _

omit [HasDerivedCategory A] in
set_option backward.isDefEq.respectTransparency false in
private theorem truncation_below_iso (I : CochainComplex A ℤ) (n j : ℤ) (hj : j < n) :
    IsIso ((I.ιTruncLE n).f j) := by
  change IsIso (((I.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f j).unop)
  have h : IsIso ((I.op.πTruncGE (ComplexShape.embeddingUpIntLE n).op).f j) := by
    dsimp only [HomologicalComplex.πTruncGE]
    apply ((ComplexShape.embeddingUpIntLE n).op.isIso_liftExtend_f_iff _ _
      (i := (n - j).natAbs) (by
        change n - (n - j).natAbs = j
        rw [Int.natAbs_of_nonneg (by omega)]
        omega)).mpr
    apply I.op.isIso_restrictionToTruncGE'
    simp only [ComplexShape.Embedding.op_boundaryGE_iff,
      ComplexShape.boundaryLE_embeddingUpIntLE_iff, Int.natAbs_eq_zero]
    omega
  infer_instance

omit [HasDerivedCategory A] [HasDerivedCategory B] in
set_option backward.isDefEq.respectTransparency false in
private theorem exact_truncation_comparison (G : A ⥤ B) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (I : CochainComplex A ℤ) (n : ℤ) :
    ∃ c : (G.mapHomologicalComplex (.up ℤ)).obj (I.truncLE n) ≅
        CochainComplex.truncLE ((G.mapHomologicalComplex (.up ℤ)).obj I) n,
      c.hom ≫ CochainComplex.ιTruncLE ((G.mapHomologicalComplex (.up ℤ)).obj I) n =
        (G.mapHomologicalComplex (.up ℤ)).map (I.ιTruncLE n) := by
  let J : CochainComplex B ℤ := (G.mapHomologicalComplex (.up ℤ)).obj I
  let L : CochainComplex B ℤ := (G.mapHomologicalComplex (.up ℤ)).obj (I.truncLE n)
  let i : L ⟶ J := (G.mapHomologicalComplex (.up ℤ)).map (I.ιTruncLE n)
  have : L.IsStrictlyLE n := inferInstance
  let t : L ⟶ J.truncLE n :=
    inv (L.ιTruncLE n) ≫ CochainComplex.truncLEMap i n
  have ht : t ≫ J.ιTruncLE n = i := by simp [t, Category.assoc]
  have htf (j : ℤ) : t.f j ≫ (J.ιTruncLE n).f j = i.f j :=
    congrArg (fun f => f.f j) ht
  have hl (j : ℤ) (hj : j < n) : IsIso (t.f j) := by
    have := truncation_below_iso I n j hj
    have hi : IsIso (i.f j) := inferInstanceAs (IsIso (G.map ((I.ιTruncLE n).f j)))
    have := truncation_below_iso J n j hj
    have : IsIso (t.f j ≫ (J.ιTruncLE n).f j) := by rw [htf]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((J.ιTruncLE n).f j)
  have htop : IsIso (t.f n) := by
    let φ := (HomologicalComplex.shortComplexFunctor B (.up ℤ) n).map t
    have : Epi φ.τ₁ := by
      change Epi (t.f ((ComplexShape.up ℤ).prev n))
      rw [CochainComplex.prev]
      have := hl (n - 1) (by omega)
      infer_instance
    have : Mono φ.τ₂ := by
      change Mono (t.f n)
      have hmono : Mono ((I.ιTruncLE n).f n) := by
        change Mono ((HomologicalComplex.ιTruncLE I
          (ComplexShape.embeddingUpIntLE n)).f n)
        infer_instance
      have : Mono (i.f n) := inferInstanceAs (Mono (G.map ((I.ιTruncLE n).f n)))
      exact mono_of_mono_fac (htf n)
    have : QuasiIsoAt (t ≫ J.ιTruncLE n) n := by
      rw [ht]
      infer_instance
    have : QuasiIsoAt t n := quasiIsoAt_of_comp_right t (J.ιTruncLE n) n
    have : IsIso (ShortComplex.homologyMap φ) :=
      (quasiIsoAt_iff_isIso_homologyMap t n).1 inferInstance
    have hcycle : IsIso (HomologicalComplex.cyclesMap t n) := cycles_iso φ
    have hL : L.d n (n + 1) = 0 := by
      exact (L.isZero_of_isStrictlyLE n (n + 1) (by omega)).eq_of_tgt _ _
    have hJ : (J.truncLE n).d n (n + 1) = 0 := by
      exact ((J.truncLE n).isZero_of_isStrictlyLE n (n + 1) (by omega)).eq_of_tgt _ _
    have := L.isIso_iCycles n (n + 1) (by simp) hL
    have := (J.truncLE n).isIso_iCycles n (n + 1) (by simp) hJ
    have h : IsIso (L.iCycles n ≫ t.f n) := by
      rw [← HomologicalComplex.cyclesMap_i]
      infer_instance
    exact IsIso.of_isIso_comp_left (L.iCycles n) _
  have (j : ℤ) : IsIso (t.f j) := by
    rcases lt_trichotomy j n with hj | rfl | hj
    · exact hl j hj
    · exact htop
    · exact (L.isZero_of_isStrictlyLE n j hj).isIso
        ((J.truncLE n).isZero_of_isStrictlyLE n j hj) _
  have := HomologicalComplex.Hom.isIso_of_components t
  exact ⟨asIso t, ht⟩

omit [Abelian A] [HasDerivedCategory A] in
private theorem inverse_square {V W V' W' : A} (a : V ⟶ W) (b : V' ⟶ W')
    (e : V ≅ V') (f : W ≅ W') (h : a ≫ f.hom = e.hom ≫ b) :
    b ≫ f.inv = e.inv ≫ a := by
  rw [← cancel_epi e.hom]
  simp only [Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← h]
  simp

omit [HasDerivedCategory A] in
set_option backward.isDefEq.respectTransparency false in
private theorem couple_iso_pages (X Y : BigradedExactCouple A 0)
    (eD : ∀ p q : ℤ, X.D p q ≅ Y.D p q)
    (eE : ∀ p q : ℤ, X.E p q ≅ Y.E p q)
    (ha : ∀ p q, X.alpha p q ≫ (eD (p - 1) (q + 1)).hom =
      (eD p q).hom ≫ Y.alpha p q)
    (hf : ∀ p q, X.f p q ≫ (eD (p + 2) (q - 1)).hom =
      (eE p q).hom ≫ Y.f p q)
    (hg : ∀ p q, X.initialG p q ≫ (eE p q).hom =
      (eD p q).hom ≫ Y.initialG p q) :
    ∃ e : ∀ r p q, (X.pageCouple r).E p q ≅ (Y.pageCouple r).E p q,
      (∀ p q, e 0 p q = eE p q) ∧
      (∀ r p q, (X.pageCouple r).d p q ≫ (e r (p + 2 + r) (q - 1 - r)).hom =
        (e r p q).hom ≫ (Y.pageCouple r).d p q) := by
  obtain ⟨t, ht₀, htd, htπ, _⟩ := BigradedExactCouple.coupleMorphism X Y
    (fun p q => (eD p q).hom) (fun p q => (eE p q).hom) ha hf hg
  obtain ⟨s, hs₀, hsd, hsπ, _⟩ := BigradedExactCouple.coupleMorphism Y X
    (fun p q => (eD p q).inv) (fun p q => (eE p q).inv)
    (fun p q => inverse_square _ _ _ _ (ha p q))
    (fun p q => inverse_square _ _ _ _ (hf p q))
    (fun p q => inverse_square _ _ _ _ (hg p q))
  have hind (r : ℕ) :
      (∀ p q, t r p q ≫ s r p q = 𝟙 _) ∧
      (∀ p q, s r p q ≫ t r p q = 𝟙 _) := by
    induction r with
    | zero =>
      constructor <;> intro p q <;> rw [ht₀, hs₀] <;> simp
    | succ r ih =>
      have hcomp {U V : BigradedExactCouple A 0}
          (a : ∀ p q, (U.pageCouple r).E p q ⟶ (V.pageCouple r).E p q)
          (b : ∀ p q, (V.pageCouple r).E p q ⟶ (U.pageCouple r).E p q)
          (a' : ∀ p q, (U.pageCouple (r + 1)).E p q ⟶ (V.pageCouple (r + 1)).E p q)
          (b' : ∀ p q, (V.pageCouple (r + 1)).E p q ⟶ (U.pageCouple (r + 1)).E p q)
          (hab : ∀ p q, a p q ≫ b p q = 𝟙 _)
          (haπ : ∀ p q, ∃ k : kernel ((U.pageCouple r).d p q) ⟶
              kernel ((V.pageCouple r).d p q),
            k ≫ kernel.ι ((V.pageCouple r).d p q) =
              kernel.ι ((U.pageCouple r).d p q) ≫ a p q ∧
            (U.pageCouple r).derivedEProjection p q ≫ a' p q =
              k ≫ (V.pageCouple r).derivedEProjection p q)
          (hbπ : ∀ p q, ∃ k : kernel ((V.pageCouple r).d p q) ⟶
              kernel ((U.pageCouple r).d p q),
            k ≫ kernel.ι ((U.pageCouple r).d p q) =
              kernel.ι ((V.pageCouple r).d p q) ≫ b p q ∧
            (V.pageCouple r).derivedEProjection p q ≫ b' p q =
              k ≫ (U.pageCouple r).derivedEProjection p q) :
          ∀ p q, a' p q ≫ b' p q = 𝟙 _ := by
        intro p q
        obtain ⟨ka, hka, hpa⟩ := haπ p q
        obtain ⟨kb, hkb, hpb⟩ := hbπ p q
        have hk : ka ≫ kb = 𝟙 _ := by
          apply (cancel_mono (kernel.ι ((U.pageCouple r).d p q))).mp
          rw [Category.assoc, hkb, ← Category.assoc, hka, Category.assoc, hab]
          simp
        have : Epi ((U.pageCouple r).derivedEProjection p q) := by
          dsimp only [BigradedExactCouple.derivedEProjection]
          infer_instance
        apply (cancel_epi ((U.pageCouple r).derivedEProjection p q)).mp
        rw [← Category.assoc, hpa, Category.assoc, hpb, ← Category.assoc, hk]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
      exact ⟨hcomp (t r) (s r) (t (r + 1)) (s (r + 1)) ih.1 (htπ r) (hsπ r),
        hcomp (s r) (t r) (s (r + 1)) (t (r + 1)) ih.2 (hsπ r) (htπ r)⟩
  let e (r : ℕ) (p q : ℤ) : (X.pageCouple r).E p q ≅ (Y.pageCouple r).E p q :=
    { hom := t r p q
      inv := s r p q
      hom_inv_id := (hind r).1 p q
      inv_hom_id := (hind r).2 p q }
  refine ⟨e, ?_, htd⟩
  intro p q
  exact Iso.ext (ht₀ p q)

omit [Abelian A] [HasDerivedCategory A] in
private theorem change_source_square {V W V' W' V'' W'' : A}
    (a : V ⟶ W) (b : V' ⟶ W') (c : V'' ⟶ W'')
    (e : V ≅ V') (f : W ≅ W') (u : V ≅ V'') (v : W ≅ W'')
    (h : a ≫ f.hom = e.hom ≫ b) (k : a ≫ v.hom = u.hom ≫ c) :
    b ≫ (f.symm ≪≫ v).hom = (e.symm ≪≫ u).hom ≫ c := by
  rw [← cancel_epi e.hom]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← h]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using k

omit [HasDerivedCategory A] [HasDerivedCategory B] in
set_option backward.isDefEq.respectTransparency false in
private theorem exact_couple_pages (Φ : A ⥤ B) [Φ.Additive]
    [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    (X : BigradedExactCouple A 0) (Y : BigradedExactCouple B 0)
    (eD : ∀ p q : ℤ, Φ.obj (X.D p q) ≅ Y.D p q)
    (eE : ∀ p q : ℤ, Φ.obj (X.E p q) ≅ Y.E p q)
    (ha : ∀ p q, Φ.map (X.alpha p q) ≫ (eD (p - 1) (q + 1)).hom =
      (eD p q).hom ≫ Y.alpha p q)
    (hf : ∀ p q, Φ.map (X.f p q) ≫ (eD (p + 2) (q - 1)).hom =
      (eE p q).hom ≫ Y.f p q)
    (hg : ∀ p q, Φ.map (X.initialG p q) ≫ (eE p q).hom =
      (eD p q).hom ≫ Y.initialG p q) :
    ∃ e : ∀ r p q, Φ.obj ((X.pageCouple r).E p q) ≅ (Y.pageCouple r).E p q,
      (∀ p q, e 0 p q = eE p q) ∧
      (∀ r p q, Φ.map ((X.pageCouple r).d p q) ≫
        (e r (p + 2 + r) (q - 1 - r)).hom =
          (e r p q).hom ≫ (Y.pageCouple r).d p q) := by
  obtain ⟨Z, hD, hE, ha₀, hf₀, hg₀, δ, φ, iX, iZ, h₀, hi₀, hiS, hi,
      hα, hf', hg', hd, _⟩ := BigradedExactCouple.exactFunctor_couple Φ X
  have hg₀' (p q : ℤ) : Φ.map (X.initialG p q) ≫ eqToHom (hE p q) =
      eqToHom (hD p q) ≫ Z.initialG p q := by
    have h : Φ.map (eqToHom (by congr 1 <;> omega :
        X.E (p + 0) (q - 0) = X.E p q)) ≫ eqToHom (hE p q) =
        eqToHom (hE (p + 0) (q - 0)) ≫
          eqToHom (by congr 1 <;> omega : Z.E (p + 0) (q - 0) = Z.E p q) := by
      simp only [eqToHom_map, eqToHom_trans]
    unfold BigradedExactCouple.initialG
    rw [Functor.map_comp, Category.assoc, h, ← Category.assoc, hg₀ p q, Category.assoc]
  obtain ⟨ψ, hψ₀, hψd⟩ := couple_iso_pages Z Y
    (fun p q => (eqToIso (hD p q)).symm ≪≫ eD p q)
    (fun p q => (eqToIso (hE p q)).symm ≪≫ eE p q)
    (fun p q => change_source_square _ _ _ _ _ _ _ (ha₀ p q) (ha p q))
    (fun p q => change_source_square _ _ _ _ _ _ _ (hf₀ p q) (hf p q))
    (fun p q => change_source_square _ _ _ _ _ _ _ (hg₀' p q) (hg p q))
  refine ⟨fun r p q => φ r p q ≪≫ ψ r p q, ?_, ?_⟩
  · intro p q
    change φ 0 p q ≪≫ ψ 0 p q = eE p q
    rw [(h₀ p q).2, hψ₀]
    simp
  · intro r p q
    simp only [Iso.trans_hom, ← Category.assoc]
    rw [hd]
    rw [Category.assoc, hψd]
    simp only [Category.assoc]


set_option backward.isDefEq.respectTransparency false in
private theorem exact_boundary_naturality (G : A ⥤ B) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (T : Pretriangulated.Triangle (DerivedCategory A)) (n m : ℤ) (h : n + 1 = m) :
    G.map (DerivedCategory.HomologySequence.δ T n m h) ≫
        (G.mapDerivedCategoryHomologyFunctorIso m).hom.app T.obj₁ =
      (G.mapDerivedCategoryHomologyFunctorIso n).hom.app T.obj₃ ≫
        DerivedCategory.HomologySequence.δ (G.mapDerivedCategory.mapTriangle.obj T) n m h := by
  dsimp only [DerivedCategory.HomologySequence.δ, Functor.shiftMap,
    Functor.mapTriangle, Functor.mapTriangle_obj]
  rw [G.map_comp, Category.assoc,
    G.mapDerivedCategoryHomologyFunctorIso_hom_app_shiftIso 1 n m (by omega)]
  have he := (G.mapDerivedCategoryHomologyFunctorIso n).hom.naturality T.mor₃
  dsimp only [Functor.comp_map] at he
  erw [← Category.assoc, he]
  simp only [Pretriangulated.Triangle.mk_mor₃, Functor.map_comp, Category.assoc]
  rfl


set_option backward.isDefEq.respectTransparency false in
private theorem exact_homology_naturality_cast (G : A ⥤ B) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {M N : DerivedCategory A} (t : M ⟶ N) (n m : ℤ) (h : n = m) :
    G.map ((DerivedCategory.homologyFunctor A n).map t ≫
      eqToHom (congrArg (fun i => (DerivedCategory.homologyFunctor A i).obj N) h)) ≫
        (G.mapDerivedCategoryHomologyFunctorIso m).hom.app N =
      (G.mapDerivedCategoryHomologyFunctorIso n).hom.app M ≫
        (DerivedCategory.homologyFunctor B n).map (G.mapDerivedCategory.map t) ≫
          eqToHom (congrArg (fun i => (DerivedCategory.homologyFunctor B i).obj
            (G.mapDerivedCategory.obj N)) h) := by
  subst m
  simpa only [eqToHom_refl, Category.comp_id, Functor.comp_map, Functor.comp_obj] using
    (G.mapDerivedCategoryHomologyFunctorIso n).hom.naturality t

set_option backward.isDefEq.respectTransparency false in
private theorem exact_boundary_naturality_cast (G : A ⥤ B) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (T : Pretriangulated.Triangle (DerivedCategory A)) (n m k : ℤ)
    (h : n + 1 = m) (hk : m = k) :
    G.map (DerivedCategory.HomologySequence.δ T n m h ≫
      eqToHom (congrArg (fun i => (DerivedCategory.homologyFunctor A i).obj T.obj₁) hk)) ≫
        (G.mapDerivedCategoryHomologyFunctorIso k).hom.app T.obj₁ =
      (G.mapDerivedCategoryHomologyFunctorIso n).hom.app T.obj₃ ≫
        DerivedCategory.HomologySequence.δ (G.mapDerivedCategory.mapTriangle.obj T) n m h ≫
          eqToHom (congrArg (fun i => (DerivedCategory.homologyFunctor B i).obj
            (G.mapDerivedCategory.obj T.obj₁)) hk) := by
  subst k
  simpa only [eqToHom_refl, Category.comp_id] using exact_boundary_naturality G T n m h

private noncomputable def single_cohomology_iso (V : A) (p q : ℤ) :
    (DerivedCategory.homologyFunctor B (p + q)).obj
      (F.obj ((DerivedCategory.singleFunctor A q).obj V)) ≅
    (DerivedCategory.homologyFunctor B p).obj
      (F.obj ((DerivedCategory.singleFunctor A 0).obj V)) :=
  (DerivedCategory.homologyFunctor B (p + q)).mapIso
      (F.mapIso (((DerivedCategory.singleFunctors A).shiftIso (-q) q 0
        (by omega)).app V).symm) ≪≫
    (DerivedCategory.homologyFunctor B (p + q)).mapIso
      ((F.commShiftIso (-q)).app ((DerivedCategory.singleFunctor A 0).obj V)) ≪≫
    ((DerivedCategory.homologyFunctor B 0).shiftIso (-q) (p + q) p (by omega)).app
      (F.obj ((DerivedCategory.singleFunctor A 0).obj V))

private theorem rightDerived_preserves_isGE (G : A ⥤ B) [G.Additive]
    [EnoughInjectives A] [Abelian.HasKInjectiveResolutions A]
    (M : DerivedCategory A) (n : ℤ) [M.IsGE n] :
    (G.rightDerivedFunctor.obj M).IsGE n := by
  let M' : DerivedCategory.Plus A := ⟨M, ⟨n, inferInstance⟩⟩
  have : M'.IsGE n := (M'.isGE_ι_obj_iff n).1 ‹_›
  refine (DerivedCategory.isGE_iff _ n).2 fun q hq ↦ ?_
  exact (G.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE M' n hq).of_iso
    ((DerivedCategory.homologyFunctor B q).mapIso
      (G.rightDerivedFunctorPlusCompatibility.app M')).symm

private theorem hypercohomology_bounds_of_isGE (a : ℤ)
    (ha : ∀ i : ℤ, i < a → IsZero (K.obj.homology i))
    (hF : ∀ (M : DerivedCategory A) (n : ℤ), M.IsGE n → (F.obj M).IsGE n) :
    (∀ p q : ℤ, q < a → IsZero (hypercohomologyD F K p q)) ∧
    (∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (hypercohomologyE F K p q)) ∧
    (∀ n : ℤ, IsIso (hypercohomologyAbutmentMap F K n n)) := by
  have hz (q : ℤ) (hq : q < a) :
      IsZero (DerivedCategory.Q.obj (TruncationCouple.truncation K q).obj) := by
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro i
    apply IsZero.of_iso _ ((DerivedCategory.homologyFunctorFactors A i).app _)
    change IsZero ((K.obj.truncLE q).homology i)
    by_cases hi : i ≤ q
    · have := K.obj.quasiIsoAt_ιTruncLE q i hi
      exact (ha i (by omega)).of_iso
        (asIso (HomologicalComplex.homologyMap (K.obj.ιTruncLE q) i))
    · exact ((K.obj.truncLE q).exactAt_of_isLE q i (by omega)).isZero_homology
  refine ⟨?_, ?_, ?_⟩
  · intro p q hq
    exact (DerivedCategory.homologyFunctor B (p + q)).map_isZero (F.map_isZero (hz q hq))
  · intro p q hpq
    rcases hpq with hp | hq
    · have hGE : (DerivedCategory.Q.obj (TruncationCouple.cohomologyComplex K q).obj).IsGE q := by
        change (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor A q).obj (K.obj.homology q))).IsGE q
        infer_instance
      have := hF _ q hGE
      exact DerivedCategory.isZero_of_isGE _ q (p + q) (by omega)
    · exact (DerivedCategory.homologyFunctor B (p + q)).map_isZero
        (F.map_isZero (DerivedCategory.Q.map_isZero
          ((CochainComplex.singleFunctor A q).map_isZero (ha q hq))))
  · intro n
    let i := DerivedCategory.Q.map (K.obj.ιTruncLE n)
    have hlow (m : ℤ) (hm : m ≤ n) :
        IsIso ((DerivedCategory.homologyFunctor A m).map i) := by
      have := K.obj.quasiIsoAt_ιTruncLE n m hm
      change IsIso ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor A m).map
        (K.obj.ιTruncLE n))
      exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors A m)
        (K.obj.ιTruncLE n)).2
          ((quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance)
    have hmono (m : ℤ) (hm : m ≤ n + 1) :
        Mono ((DerivedCategory.homologyFunctor A m).map i) := by
      by_cases h : m ≤ n
      · have := hlow m h
        infer_instance
      · have hz : IsZero ((DerivedCategory.homologyFunctor A m).obj
            (DerivedCategory.Q.obj (K.obj.truncLE n))) :=
          DerivedCategory.isZero_of_isLE _ n m (by omega)
        exact hz.mono _
    obtain ⟨C, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle i
    let T := Pretriangulated.Triangle.mk i g h
    have hC : C.IsGE (n + 1) := by
      rw [DerivedCategory.isGE_iff]
      intro m hm
      have h₁ : IsIso ((DerivedCategory.homologyFunctor A m).map T.mor₁) :=
        hlow m (by omega)
      have h₂ : Mono ((DerivedCategory.homologyFunctor A (m + 1)).map T.mor₁) :=
        hmono (m + 1) (by omega)
      exact (DerivedCategory.HomologySequence.exact₃ T hT m (m + 1)).isZero_X₂
        ((DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT m).1
          inferInstance)
        ((DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT m (m + 1)).1
          inferInstance)
    have hFC : (F.mapTriangle.obj T).obj₃.IsGE (n + 1) := hF C (n + 1) hC
    exact DerivedCategory.isIso_homologyMap_mor₁ (F.mapTriangle.obj T)
      (F.map_distinguished T hT) (n - 1) n (by omega)
      (DerivedCategory.isZero_of_isGE _ (n + 1) (n - 1) (by omega))
      (DerivedCategory.isZero_of_isGE _ (n + 1) n (by omega))

set_option backward.isDefEq.respectTransparency false in
private theorem hypercohomology_initialG (p q : ℤ) :
    (hypercohomologyCouple F K).initialG p q =
      (DerivedCategory.homologyFunctor B (p + q)).map
        (F.map (DerivedCategory.Q.map (TruncationCouple.projection K q))) := by
  simp only [hypercohomologyCouple, BigradedExactCouple.initialG,
    BigradedExactCouple.ofShifted_g, hypercohomologyG, Category.assoc]
  change (DerivedCategory.homologyFunctor B (p + q)).map
      (F.map (DerivedCategory.Q.map (TruncationCouple.projection K q))) ≫
        eqToHom (by simp : hypercohomologyE F K p q =
          hypercohomologyE F K (p + (0 : ℕ)) (q - (0 : ℕ))) ≫
        eqToHom (by simp : hypercohomologyE F K (p + (0 : ℕ)) (q - (0 : ℕ)) =
          hypercohomologyE F K p q) = _
  erw [eqToHom_trans, eqToHom_refl]
  exact Category.comp_id _


attribute [local irreducible] TruncationCouple.bridgeIso

set_option backward.isDefEq.respectTransparency false in
private theorem hypercohomology_bridge [IsGrothendieckAbelian.{v₁} A]
    [IsGrothendieckAbelian.{v₂} B] (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] :
    (∀ p q : ℤ, hypercohomologyAlpha G.rightDerivedFunctor K p q ≫
        (TruncationCouple.bridgeIso G
          (TruncationCouple.truncation K (q + 1)) (p - 1 + (q + 1))).hom =
      (TruncationCouple.bridgeIso G
          (TruncationCouple.truncation K q) (p + q)).hom ≫
        TruncationCouple.alpha G K p q) ∧
    (∀ p q : ℤ, hypercohomologyBoundary G.rightDerivedFunctor K p q ≫
        (TruncationCouple.bridgeIso G
          (TruncationCouple.truncation K (q - 1)) (p + 2 + (q - 1))).hom =
      (TruncationCouple.bridgeIso G
          (TruncationCouple.cohomologyComplex K q) (p + q)).hom ≫
        TruncationCouple.f G K p q) ∧
    (∀ p q : ℤ, (hypercohomologyCouple G.rightDerivedFunctor K).initialG p q ≫
        (TruncationCouple.bridgeIso G
          (TruncationCouple.cohomologyComplex K q) (p + q)).hom =
      (TruncationCouple.bridgeIso G
          (TruncationCouple.truncation K q) (p + q)).hom ≫
        TruncationCouple.g G K p q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p q
    simp only [hypercohomologyAlpha, TruncationCouple.alpha, Category.assoc,
      Iso.hom_inv_id_assoc]
    congr 1
    exact (eqToHom_iso_hom_naturality
      (fun n : ℤ ↦ TruncationCouple.bridgeIso (G)
        (TruncationCouple.truncation K (q + 1)) n)
      (by omega : p + q = p - 1 + (q + 1))).symm
  · intro p q
    simp only [hypercohomologyBoundary, TruncationCouple.f, Category.assoc,
      Iso.hom_inv_id_assoc]
    congr 1
    exact (eqToHom_iso_hom_naturality
      (fun n : ℤ ↦ TruncationCouple.bridgeIso (G)
        (TruncationCouple.truncation K (q - 1)) n)
      (by omega : p + q + 1 = p + 2 + (q - 1))).symm
  · intro p q
    rw [hypercohomology_initialG]
    simp only [TruncationCouple.g, TruncationCouple.derivedTriangle,
      Functor.mapTriangle, TruncationCouple.triangle,
      Pretriangulated.Triangle.mk_mor₂, Iso.hom_inv_id_assoc]

private theorem hypercohomology_convergence_of_bounds (a : ℤ)
    (hD : ∀ p q : ℤ, q < a → IsZero (hypercohomologyD F K p q))
    (hE : ∀ p q : ℤ, (p < 0 ∨ q < a) → IsZero (hypercohomologyE F K p q))
    (hiso : ∀ n : ℤ, IsIso (hypercohomologyAbutmentMap F K n n)) :
    (∀ n : ℤ, (hypercohomologyFiltration F K n).IsFinite ∧
      (∀ p : ℤ, p ≤ 0 → (hypercohomologyFiltration F K n).step p = ⊤) ∧
      (∀ p : ℤ, n - a + 1 ≤ p → ((hypercohomologyFiltration F K n).step p).arrow = 0)) ∧
    (∀ (r : ℕ) (p q : ℤ), 2 ≤ r →
      (q < a ∨ p < 0) → IsZero ((hypercohomologyCouple F K).page r p q)) ∧
    (∃ T : ∀ n : ℤ, (hypercohomologyCouple F K).AlphaColimit n,
      ∃ Z : (hypercohomologyCouple F K).LimitSubobjects,
      ∃ hT : ∀ n : ℤ, (T n).obj =
          (DerivedCategory.homologyFunctor B n).obj (F.obj (DerivedCategory.Q.obj K.obj)),
        (hypercohomologyCouple F K).ConvergesTo Z T ∧
        (∀ n p : ℤ, (T n).ι p ≫ eqToHom (hT n) =
          eqToHom (congrArg (fun m : ℤ ↦ (DerivedCategory.homologyFunctor B m).obj
            (F.obj (DerivedCategory.Q.obj (TruncationCouple.truncation K (n - p)).obj)))
              (by omega : p + (n - p) = n)) ≫
            hypercohomologyAbutmentMap F K n (n - p)) ∧
        (∀ n p : ℤ, (Subobject.«exists» (eqToHom (hT n))).obj
          (((hypercohomologyCouple F K).imageFiltration n (T n)).step p) =
            (hypercohomologyFiltration F K n).step p)) := by
  let X := hypercohomologyCouple F K
  let H (n : ℤ) := (DerivedCategory.homologyFunctor B n).obj
    (F.obj (DerivedCategory.Q.obj K.obj))
  let j (n q : ℤ) : X.D (n - q) q ⟶ H n :=
    eqToHom (by dsimp [X, hypercohomologyCouple, hypercohomologyD]; congr 2; omega) ≫
      hypercohomologyAbutmentMap F K n q
  let c (n : ℤ) : X.D 0 n ⟶ H n :=
    eqToHom (by congr 1; omega) ≫ j n n
  have hco (n p : ℤ) : X.alphaDiagonal n p ≫
      eqToHom (by congr 1; omega) ≫ j n (n - p) =
        eqToHom (by congr 1; omega) ≫ j n (n - (p + 1)) := by
    have ha (p q n t : ℤ) (hn : p + q = n) (ht : q + 1 = t) :
        hypercohomologyAlpha F K p q =
          eqToHom (by unfold hypercohomologyD; rw [hn]; rfl) ≫
          (DerivedCategory.homologyFunctor B n).map
            (F.map (DerivedCategory.Q.map
              (eqToHom (congrArg (fun r : ℤ ↦ K.obj.truncLE r)
                (by omega : q = t - 1)) ≫ TruncationCouple.transition K t))) ≫
          eqToHom (by unfold hypercohomologyD; rw [← ht, ← hn]; congr 2; omega) := by
      subst n
      subst t
      simp only [eqToHom_refl, Category.id_comp]
      rfl
    dsimp only [BigradedExactCouple.alphaDiagonal]
    simp only [X, hypercohomologyCouple, BigradedExactCouple.ofShifted_alpha,
      Category.assoc]
    rw [ha (p + 1) (n - (p + 1)) n (n - p) (by omega) (by omega)]
    simp only [j, hypercohomologyAbutmentMap, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    have hq : n - (p + 1) = n - p - 1 := by omega
    simp only [Category.assoc, TruncationCouple.transition_comp_ιTruncLE]
    have hι := eqToHom_naturality (fun r : ℤ ↦ K.obj.ιTruncLE r) hq
    simp only [eqToHom_refl, Category.comp_id] at hι
    rw [hι]
  have hn : ∀ (n p : ℤ) (_ : 0 ≤ p), eqToHom (by congr 1 <;> omega) ≫ j n (n - p) =
      X.incomingAlphaIter p.toNat 0 n ≫ c n := by
    let k (n p : ℤ) : X.D p (n - p) ⟶ H n :=
      eqToHom (by congr 1; omega) ≫ j n (n - p)
    have hk (n p : ℤ) : X.alphaDiagonal n p ≫ k n p = k n (p + 1) := hco n p
    have hi (n : ℤ) (r : ℕ) (p q : ℤ) (hn : p + q = n) :
        X.alphaIter r p q ≫ eqToHom (by congr 1; omega) ≫ k n (p - r) =
          eqToHom (by congr 1; omega) ≫ k n p := by
      induction r generalizing p q with
      | zero =>
        simp only [BigradedExactCouple.alphaIter, eqToHom_trans_assoc]
        have he := eqToHom_naturality (k n) (by omega : p - (↑(0 : ℕ) : ℤ) = p)
        simp only [eqToHom_refl, Category.comp_id] at he
        rw [he, eqToHom_trans_assoc]
      | succ r ih =>
        simp only [BigradedExactCouple.alphaIter, Category.assoc, eqToHom_trans_assoc]
        have he := ih (p - 1) (q + 1) (by omega)
        have hidx : p - ↑(r + 1 : ℕ) = p - 1 - ↑r := by omega
        have hcast := eqToHom_naturality (k n) hidx
        simp only [eqToHom_refl, Category.comp_id] at hcast
        rw [hcast, eqToHom_trans_assoc, he]
        have hq : q = n - p := by omega
        subst q
        have he' := hk n (p - 1)
        simp only [BigradedExactCouple.alphaDiagonal, Category.assoc] at he'
        dsimp only [k] at he' ⊢
        simp only [eqToHom_trans_assoc] at he' ⊢
        convert! he' using 1 <;> congr! 4 <;> omega
    intro n p hp
    lift p to ℕ using hp
    have he := hi n p (p : ℤ) (n - p) (by omega)
    have hend := eqToHom_naturality (k n) (by omega : (p : ℤ) - p = 0)
    simp only [eqToHom_refl, Category.comp_id] at hend
    rw [hend, eqToHom_trans_assoc] at he
    simp only [k, eqToHom_trans_assoc] at he
    simp only [Int.toNat_natCast, BigradedExactCouple.incomingAlphaIter, c,
      Category.assoc, eqToHom_trans_assoc]
    convert! he.symm using 1 <;> congr! 4 <;> omega
  have hc (n : ℤ) : IsIso (c n) := by
    dsimp [c, j]
    infer_instance
  obtain ⟨Z, T₀, hT₀, hT₀ι, hsupport, _⟩ :=
    BigradedExactCouple.halfPlaneConvergence X a hD hE
  obtain ⟨FA, FH, hFA, hFA0, hFH, hj, htop, hbot, hfinite, hneg, T, hT, hι, hconv⟩ :=
    abutment_image_filtration X a hD hE Z H j c (fun _ ↦ rfl) hc hco hn
  have ext {V : B} (F G : DecreasingFiltration V) (h : F.F = G.F) : F = G := by
    cases F
    cases G
    cases h
    rfl
  have hFH' (n : ℤ) : FH n = hypercohomologyFiltration F K n := by
    apply ext
    funext p
    simpa only [DecreasingFiltration.step, hypercohomologyFiltration, j,
      imageSubobject_comp_eq_of_epi] using hj n p
  refine ⟨?_, ?_, ⟨T, Z, hT, hconv, ?_, ?_⟩⟩
  · intro n
    refine ⟨hFH' n ▸ (hfinite n).1, ?_, ?_⟩
    · intro p hp
      rw [← hFH' n]
      exact htop n p hp
    · intro p hp
      apply Subobject.mk_eq_bot_iff_zero.mp
      simpa only [Subobject.mk_arrow, hFH' n] using hbot n p hp
  · intro r p q hr hpq
    by_contra hnz
    have hs := hsupport (r - 2) (p + q) p q rfl hnz
    rcases hpq with hq | hp
    · omega
    · omega
  · intro n p
    simpa only [j, Category.assoc, eqToHom_trans_assoc] using hι n p
  · intro n p
    rw [Subobject.exists_obj_eq_imageSubobject]
    change imageSubobject ((imageSubobject ((T n).ι p)).arrow ≫ eqToHom (hT n)) = _
    rw [← imageSubobject_comp_eq_of_epi (factorThruImageSubobject ((T n).ι p)),
      ← Category.assoc, imageSubobject_arrow_comp, hι]
    simp only [j, eqToHom_trans_assoc, imageSubobject_comp_eq_of_epi]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem hypercohomology_exactFunctor
    {C : Type uC} [Category.{vC, uC} C] [Abelian C] [HasDerivedCategory C]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (∃ δ : ∀ p q : ℤ, G.obj ((hypercohomologyCouple
      F K).D p q) ≅ (hypercohomologyCouple
      (F ⋙ G.mapDerivedCategory) K).D p q,
      ∃ φ : ∀ (r : ℕ) (p q : ℤ),
        G.obj (((hypercohomologyCouple
          F K).pageCouple r).E p q) ≅
          ((hypercohomologyCouple (F ⋙ G.mapDerivedCategory) K).pageCouple r).E p q,
        (∀ p q : ℤ, δ p q =
          (G.mapDerivedCategoryHomologyFunctorIso (p + q)).app
            (F.obj (DerivedCategory.Q.obj
              (TruncationCouple.truncation K q).obj))) ∧
        (∀ p q : ℤ, φ 0 p q =
          (G.mapDerivedCategoryHomologyFunctorIso (p + q)).app
            (F.obj (DerivedCategory.Q.obj
              (TruncationCouple.cohomologyComplex K q).obj))) ∧
        (∀ p q : ℤ, G.map ((hypercohomologyCouple
          F K).alpha p q) ≫
          (δ (p - 1) (q + 1)).hom = (δ p q).hom ≫ (hypercohomologyCouple
            (F ⋙ G.mapDerivedCategory) K).alpha p q) ∧
        (∀ p q : ℤ, G.map ((hypercohomologyCouple
          F K).f p q) ≫
          (δ (p + 2) (q - 1)).hom = (φ 0 p q).hom ≫ (hypercohomologyCouple
            (F ⋙ G.mapDerivedCategory) K).f p q) ∧
        (∀ p q : ℤ, G.map ((hypercohomologyCouple
          F K).initialG p q) ≫
          (φ 0 p q).hom = (δ p q).hom ≫
            (hypercohomologyCouple (F ⋙ G.mapDerivedCategory) K).initialG p q) ∧
        (∀ (r : ℕ) (p q : ℤ),
          G.map (((hypercohomologyCouple
            F K).pageCouple r).d p q) ≫
            (φ r (p + 2 + r) (q - 1 - r)).hom =
          (φ r p q).hom ≫ ((hypercohomologyCouple (F ⋙ G.mapDerivedCategory)
            K).pageCouple r).d p q)) := by
  let δ (p q : ℤ) := (G.mapDerivedCategoryHomologyFunctorIso (p + q)).app
    (F.obj (DerivedCategory.Q.obj (TruncationCouple.truncation K q).obj))
  let ε (p q : ℤ) := (G.mapDerivedCategoryHomologyFunctorIso (p + q)).app
    (F.obj (DerivedCategory.Q.obj (TruncationCouple.cohomologyComplex K q).obj))
  have hα (p q : ℤ) : G.map ((hypercohomologyCouple F K).alpha p q) ≫
      (δ (p - 1) (q + 1)).hom =
        (δ p q).hom ≫ (hypercohomologyCouple (F ⋙ G.mapDerivedCategory) K).alpha p q := by
    simp only [hypercohomologyCouple, BigradedExactCouple.ofShifted_alpha,
      hypercohomologyAlpha, Functor.comp_map]
    exact exact_homology_naturality_cast G
      (F.map (DerivedCategory.Q.map
        (eqToHom (congrArg (fun n : ℤ ↦ K.obj.truncLE n)
          (by omega : q = (q + 1) - 1)) ≫ TruncationCouple.transition K (q + 1))))
      (p + q) (p - 1 + (q + 1)) (by omega)
  have hf (p q : ℤ) : G.map ((hypercohomologyCouple F K).f p q) ≫
      (δ (p + 2) (q - 1)).hom =
        (ε p q).hom ≫ (hypercohomologyCouple (F ⋙ G.mapDerivedCategory) K).f p q := by
    simp only [hypercohomologyCouple, BigradedExactCouple.ofShifted_f,
      hypercohomologyBoundary]
    have h := exact_boundary_naturality_cast G
      (F.mapTriangle.obj (TruncationCouple.triangle K q))
      (p + q) (p + q + 1) (p + 2 + (q - 1)) (by omega) (by omega)
    have hδ : DerivedCategory.HomologySequence.δ
        (G.mapDerivedCategory.mapTriangle.obj
          (F.mapTriangle.obj (TruncationCouple.triangle K q))) (p + q) (p + q + 1) =
        DerivedCategory.HomologySequence.δ
          ((F ⋙ G.mapDerivedCategory).mapTriangle.obj (TruncationCouple.triangle K q))
            (p + q) (p + q + 1) := by
      dsimp only [DerivedCategory.HomologySequence.δ, Functor.shiftMap,
        Functor.mapTriangle, Functor.mapTriangle_obj, Pretriangulated.Triangle.mk,
        Functor.comp_obj, Functor.comp_map]
      simp only [Functor.commShiftIso_comp_hom_app, Functor.map_comp, Category.assoc]
    rw [hδ] at h
    exact h
  have hg (p q : ℤ) : G.map ((hypercohomologyCouple F K).initialG p q) ≫
      (ε p q).hom =
        (δ p q).hom ≫ (hypercohomologyCouple (F ⋙ G.mapDerivedCategory) K).initialG p q := by
    rw [hypercohomology_initialG, hypercohomology_initialG]
    exact (G.mapDerivedCategoryHomologyFunctorIso (p + q)).hom.naturality
      (F.map (DerivedCategory.Q.map (TruncationCouple.projection K q)))
  obtain ⟨φ, hφ, hd⟩ := exact_couple_pages G (hypercohomologyCouple F K)
    (hypercohomologyCouple (F ⋙ G.mapDerivedCategory) K) δ ε hα hf hg
  refine ⟨δ, φ, fun _ _ => rfl, hφ, hα, ?_, ?_, hd⟩
  · intro p q
    rw [hφ]
    exact hf p q
  · intro p q
    rw [hφ]
    exact hg p q

end CategoryTheory

namespace AlgebraicGeometry.Etale

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (g : Y' ⟶ Y) (g' : X' ⟶ X)
  (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))

/-- The functor Rf_*.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable abbrev hypercohomologyFirstFunctor :
    DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor

/-- The functor g⁻¹Rf_*.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable abbrev hypercohomologyBaseChangeFunctor :
    DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor ⋙
    (upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategory

/-- The functor Rf'_*(g')⁻¹.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable abbrev hypercohomologySecondFunctor :
    DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  (upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategory ⋙
    (lowerStar AddCommGrpCat.{u + 1} f').rightDerivedFunctor

/-- The three hypercohomology filtrations, on Y and twice on Y', in total degree n.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations). -/
noncomputable def hypercohomologyFiltrations (n : ℤ) :
    DecreasingFiltration
      ((DerivedCategory.homologyFunctor _ n).obj
        ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj))) ×
    DecreasingFiltration
      ((DerivedCategory.homologyFunctor _ n).obj
        ((hypercohomologyBaseChangeFunctor f g).obj (DerivedCategory.Q.obj K.obj))) ×
    DecreasingFiltration
      ((DerivedCategory.homologyFunctor _ n).obj
        ((hypercohomologySecondFunctor f' g').obj (DerivedCategory.Q.obj K.obj))) :=
  ⟨hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n,
    hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n,
    hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n⟩

attribute [local irreducible] TruncationCouple.bridgeIso

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- The three spectral sequences have the stated E₂ terms, finite filtrations, and unconditional
  convergence, the first couple is the truncation couple of def-sp-truncation-couple for f_*
  through `TruncationCouple.bridgeIso`, and the middle one is the exact inverse image of the
  first.
Source: blueprint order 1315; Stacks Tags 0DDE, 015J
(blueprint: def-weil-pbc-hypercohomology-filtrations).

Proof: Transfer the lower cohomological bound along the supplied representative isomorphism.
  Each of the three functors preserves lower bounds: use the bounded-below compatibility of
  right derived functors and exact inverse image. The truncation cone then shows that the
  degree-n abutment map from tau≤n is invertible. Apply half-plane convergence and
  lem-sp-abutment-image-filtration, using the actual truncation inclusions as the cocone, to
  obtain the finite canonical image filtrations and all three abutments. The bridge equations
  follow from the definitions and equality-transport naturality. Shift the single complex to
  degree zero to identify each E₂ term with the classical right derived functor. For termwise
  inverse image, factor the mapped truncation inclusion through the target truncation; its
  components are invertible below the cutoff, its top cycle map is invertible by exactness,
  and both sides vanish above it. The cohomology comparison is natural and commutes with shifts,
  hence with all three couple maps, including the boundary. Apply lem-sp-exact-functor-couple
  and couple functoriality in both directions; cancellation at the kernel inclusions and
  quotient projections proves that the page maps are inverses. Finally, exactness preserves
  the epi-image factorization of each abutment map, giving the stated filtration comparison. -/
theorem hypercohomologyFiltrations_spec
    (sq : IsPullback g' f' f g)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (e : DerivedCategory.Q.obj K.obj ≅ L.obj)
    (hT : ∀ q : ℤ, CategoryTheory.Sheaf.IsTorsion
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (a : ℤ)
    (ha : ∀ q : ℤ, q < a → IsZero
      ((DerivedCategory.homologyFunctor _ q).obj L.obj))
    (hterms : ∀ i : ℤ, i < a → IsZero (K.obj.X i)) :
    (∀ n : ℤ, (hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).IsFinite ∧
      (∀ p : ℤ, p ≤ 0 → (hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).step p =
        ⊤) ∧
      (∀ p : ℤ, n - a + 1 ≤ p →
        ((hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).step p).arrow = 0)) ∧
    (∀ (r : ℕ) (p q : ℤ), 2 ≤ r →
      (q < a ∨ p < 0) → IsZero ((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).page r p
        q)) ∧
    (∃ T : ∀ n : ℤ, (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).AlphaColimit n,
      ∃ Z : (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).LimitSubobjects,
      ∃ hT : ∀ n : ℤ, (T n).obj =
          (DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) n).obj
            ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj)),
        (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).ConvergesTo Z T ∧
        (∀ n p : ℤ, (T n).ι p ≫ eqToHom (hT n) =
          eqToHom (congrArg (fun m : ℤ ↦
            (DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
              m).obj
              ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj
                (TruncationCouple.truncation K (n - p)).obj)))
              (by omega : p + (n - p) = n)) ≫
            hypercohomologyAbutmentMap (hypercohomologyFirstFunctor f) K n (n - p)) ∧
        (∀ n p : ℤ,
          (Subobject.«exists» (eqToHom (hT n))).obj
              (((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).imageFiltration n (T
                n)).step p) =
            (hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).step p)) ∧
    (∀ n : ℤ, (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).IsFinite ∧
      (∀ p : ℤ, p ≤ 0 → (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K
        n).step p = ⊤) ∧
      (∀ p : ℤ, n - a + 1 ≤ p →
        ((hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).step p).arrow =
          0)) ∧
    (∀ (r : ℕ) (p q : ℤ), 2 ≤ r →
      (q < a ∨ p < 0) → IsZero ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g)
        K).page r p q)) ∧
    (∃ T : ∀ n : ℤ, (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).AlphaColimit n,
      ∃ Z : (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).LimitSubobjects,
      ∃ hT : ∀ n : ℤ, (T n).obj =
          (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
            n).obj
            ((hypercohomologyBaseChangeFunctor f g).obj (DerivedCategory.Q.obj K.obj)),
        (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).ConvergesTo Z T ∧
        (∀ n p : ℤ, (T n).ι p ≫ eqToHom (hT n) =
          eqToHom (congrArg (fun m : ℤ ↦
            (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
              m).obj
              ((hypercohomologyBaseChangeFunctor f g).obj (DerivedCategory.Q.obj
                (TruncationCouple.truncation K (n - p)).obj)))
              (by omega : p + (n - p) = n)) ≫
            hypercohomologyAbutmentMap (hypercohomologyBaseChangeFunctor f g) K n (n - p)) ∧
        (∀ n p : ℤ,
          (Subobject.«exists» (eqToHom (hT n))).obj
              (((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).imageFiltration n
                (T n)).step p) =
            (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).step p)) ∧
    (∀ n : ℤ, (hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).IsFinite ∧
      (∀ p : ℤ, p ≤ 0 → (hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).step
        p = ⊤) ∧
      (∀ p : ℤ, n - a + 1 ≤ p →
        ((hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).step p).arrow = 0)) ∧
    (∀ (r : ℕ) (p q : ℤ), 2 ≤ r →
      (q < a ∨ p < 0) → IsZero ((hypercohomologyCouple (hypercohomologySecondFunctor f' g')
        K).page r p q)) ∧
    (∃ T : ∀ n : ℤ, (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).AlphaColimit n,
      ∃ Z : (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).LimitSubobjects,
      ∃ hT : ∀ n : ℤ, (T n).obj =
          (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
            n).obj
            ((hypercohomologySecondFunctor f' g').obj (DerivedCategory.Q.obj K.obj)),
        (hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).ConvergesTo Z T ∧
        (∀ n p : ℤ, (T n).ι p ≫ eqToHom (hT n) =
          eqToHom (congrArg (fun m : ℤ ↦
            (DerivedCategory.homologyFunctor (Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1})
              m).obj
              ((hypercohomologySecondFunctor f' g').obj (DerivedCategory.Q.obj
                (TruncationCouple.truncation K (n - p)).obj)))
              (by omega : p + (n - p) = n)) ≫
            hypercohomologyAbutmentMap (hypercohomologySecondFunctor f' g') K n (n - p)) ∧
        (∀ n p : ℤ,
          (Subobject.«exists» (eqToHom (hT n))).obj
              (((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).imageFiltration n
                (T n)).step p) =
            (hypercohomologyFiltration (hypercohomologySecondFunctor f' g') K n).step p)) ∧
    (∀ p q : ℤ, hypercohomologyAlpha (hypercohomologyFirstFunctor f) K p q ≫
        (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.truncation K (q + 1)) (p - 1 + (q + 1))).hom =
      (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.truncation K q) (p + q)).hom ≫
        TruncationCouple.alpha (lowerStar AddCommGrpCat.{u + 1} f) K p q) ∧
    (∀ p q : ℤ, hypercohomologyBoundary (hypercohomologyFirstFunctor f) K p q ≫
        (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.truncation K (q - 1)) (p + 2 + (q - 1))).hom =
      (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.cohomologyComplex K q) (p + q)).hom ≫
        TruncationCouple.f (lowerStar AddCommGrpCat.{u + 1} f) K p q) ∧
    (∀ p q : ℤ, (hypercohomologyCouple (hypercohomologyFirstFunctor f) K).initialG p q ≫
        (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.cohomologyComplex K q) (p + q)).hom =
      (TruncationCouple.bridgeIso (lowerStar AddCommGrpCat.{u + 1} f)
          (TruncationCouple.truncation K q) (p + q)).hom ≫
        TruncationCouple.g (lowerStar AddCommGrpCat.{u + 1} f) K p q) ∧
    (∀ (p : ℕ) (q : ℤ), Nonempty
      ((hypercohomologyCouple (hypercohomologyFirstFunctor f) K).E p q ≅
        ((lowerStar AddCommGrpCat.{u + 1} f).rightDerived p).obj (K.obj.homology q))) ∧
    (∀ (p : ℕ) (q : ℤ), Nonempty
      ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).E p q ≅
        (upperStar AddCommGrpCat.{u + 1} g).obj
          (((lowerStar AddCommGrpCat.{u + 1} f).rightDerived p).obj (K.obj.homology q)))) ∧
    (∀ (p : ℕ) (q : ℤ), Nonempty
      ((hypercohomologyCouple (hypercohomologySecondFunctor f' g') K).E p q ≅
        ((lowerStar AddCommGrpCat.{u + 1} f').rightDerived p).obj
          ((upperStar AddCommGrpCat.{u + 1} g').obj (K.obj.homology q)))) ∧
    (∀ i : ℤ, i < a → IsZero
      ((((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K.obj).X i)) ∧
    (∀ q : ℤ, ∃ c :
        ((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (K.obj.truncLE q) ≅
        CochainComplex.truncLE
          (((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
            K.obj) q,
      c.hom ≫
        CochainComplex.ιTruncLE
          (((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
            K.obj) q =
        ((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).map
          (K.obj.ιTruncLE q)) ∧
    (∀ q : ℤ, Nonempty
      ((((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj
        K.obj).homology q ≅ (upperStar AddCommGrpCat.{u + 1} g').obj (K.obj.homology q))) ∧
    (∃ δ : ∀ p q : ℤ, (upperStar AddCommGrpCat.{u + 1} g).obj ((hypercohomologyCouple
      (hypercohomologyFirstFunctor f) K).D p q) ≅ (hypercohomologyCouple
      (hypercohomologyBaseChangeFunctor f g) K).D p q,
      ∃ φ : ∀ (r : ℕ) (p q : ℤ),
        (upperStar AddCommGrpCat.{u + 1} g).obj (((hypercohomologyCouple
          (hypercohomologyFirstFunctor f) K).pageCouple r).E p q) ≅
          ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g) K).pageCouple r).E p q,
        (∀ p q : ℤ, δ p q =
          ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryHomologyFunctorIso (p + q)).app
            ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj
              (TruncationCouple.truncation K q).obj))) ∧
        (∀ p q : ℤ, φ 0 p q =
          ((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryHomologyFunctorIso (p + q)).app
            ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj
              (TruncationCouple.cohomologyComplex K q).obj))) ∧
        (∀ p q : ℤ, (upperStar AddCommGrpCat.{u + 1} g).map ((hypercohomologyCouple
          (hypercohomologyFirstFunctor f) K).alpha p q) ≫
          (δ (p - 1) (q + 1)).hom = (δ p q).hom ≫ (hypercohomologyCouple
            (hypercohomologyBaseChangeFunctor f g) K).alpha p q) ∧
        (∀ p q : ℤ, (upperStar AddCommGrpCat.{u + 1} g).map ((hypercohomologyCouple
          (hypercohomologyFirstFunctor f) K).f p q) ≫
          (δ (p + 2) (q - 1)).hom = (φ 0 p q).hom ≫ (hypercohomologyCouple
            (hypercohomologyBaseChangeFunctor f g) K).f p q) ∧
        (∀ p q : ℤ, (upperStar AddCommGrpCat.{u + 1} g).map ((hypercohomologyCouple
          (hypercohomologyFirstFunctor f) K).initialG p q) ≫
          (φ 0 p q).hom = (δ p q).hom ≫ (hypercohomologyCouple (hypercohomologyBaseChangeFunctor f
            g) K).initialG p q) ∧
        (∀ (r : ℕ) (p q : ℤ),
          (upperStar AddCommGrpCat.{u + 1} g).map (((hypercohomologyCouple
            (hypercohomologyFirstFunctor f) K).pageCouple r).d p q) ≫
            (φ r (p + 2 + r) (q - 1 - r)).hom =
          (φ r p q).hom ≫ ((hypercohomologyCouple (hypercohomologyBaseChangeFunctor f g)
            K).pageCouple r).d p q)) ∧
    (∀ n : ℤ, ∃ c : (upperStar AddCommGrpCat.{u + 1} g).obj
        ((DerivedCategory.homologyFunctor _ n).obj
          ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj))) ≅
        (DerivedCategory.homologyFunctor _ n).obj
          ((hypercohomologyBaseChangeFunctor f g).obj (DerivedCategory.Q.obj K.obj)),
      c = (((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryHomologyFunctorIso n).app
        ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj))) ∧
      ∀ p : ℤ, imageSubobject ((upperStar AddCommGrpCat.{u + 1} g).map
          ((hypercohomologyFiltration (hypercohomologyFirstFunctor f) K n).step p).arrow ≫ c.hom) =
        (hypercohomologyFiltration (hypercohomologyBaseChangeFunctor f g) K n).step p) := by
  have haK (q : ℤ) (hq : q < a) : IsZero (K.obj.homology q) :=
    (ha q hq).of_iso
      (((DerivedCategory.homologyFunctorFactors _ q).app K.obj).symm ≪≫
        (DerivedCategory.homologyFunctor _ q).mapIso e)
  have hF₁ (M : DerivedCategory _) (n : ℤ) (hM : M.IsGE n) :
      ((hypercohomologyFirstFunctor f).obj M).IsGE n :=
    rightDerived_preserves_isGE _ M n
  have hF₂ (M : DerivedCategory _) (n : ℤ) (hM : M.IsGE n) :
      ((hypercohomologyBaseChangeFunctor f g).obj M).IsGE n := by
    have := hF₁ M n hM
    exact Functor.isGE_mapDerivedCategory_obj _ _ n
  have hF₃ (M : DerivedCategory _) (n : ℤ) (hM : M.IsGE n) :
      ((hypercohomologySecondFunctor f' g').obj M).IsGE n := by
    have := Functor.isGE_mapDerivedCategory_obj
      (upperStar AddCommGrpCat.{u + 1} g') M n
    exact rightDerived_preserves_isGE _ _ n
  obtain ⟨hD₁, hE₁, hi₁⟩ :=
    hypercohomology_bounds_of_isGE (hypercohomologyFirstFunctor f) K a haK hF₁
  obtain ⟨hD₂, hE₂, hi₂⟩ :=
    hypercohomology_bounds_of_isGE (hypercohomologyBaseChangeFunctor f g) K a haK hF₂
  obtain ⟨hD₃, hE₃, hi₃⟩ :=
    hypercohomology_bounds_of_isGE (hypercohomologySecondFunctor f' g') K a haK hF₃
  obtain ⟨hb₁, hp₁, hc₁⟩ :=
    hypercohomology_convergence_of_bounds (hypercohomologyFirstFunctor f) K a hD₁ hE₁ hi₁
  obtain ⟨hb₂, hp₂, hc₂⟩ :=
    hypercohomology_convergence_of_bounds (hypercohomologyBaseChangeFunctor f g) K a hD₂ hE₂ hi₂
  obtain ⟨hb₃, hp₃, hc₃⟩ :=
    hypercohomology_convergence_of_bounds (hypercohomologySecondFunctor f' g') K a hD₃ hE₃ hi₃
  obtain ⟨hα, hf, hg⟩ := hypercohomology_bridge K (lowerStar AddCommGrpCat.{u + 1} f)
  refine ⟨hb₁, hp₁, hc₁, hb₂, hp₂, hc₂, hb₃, hp₃, hc₃, hα, hf, hg, ?_⟩
  have e₁ (p : ℕ) (q : ℤ) :
      hypercohomologyE (hypercohomologyFirstFunctor f) K p q ≅
        ((lowerStar AddCommGrpCat.{u + 1} f).rightDerived p).obj (K.obj.homology q) :=
    (DerivedCategory.homologyFunctor _ ((p : ℤ) + q)).mapIso
        ((hypercohomologyFirstFunctor f).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ q).app (K.obj.homology q)).symm) ≪≫
      single_cohomology_iso (hypercohomologyFirstFunctor f) (K.obj.homology q) p q ≪≫
      (lowerStar AddCommGrpCat.{u + 1} f).homologyRightDerivedFunctorObjSingleFunctorIso
        (K.obj.homology q) p
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q
    exact ⟨e₁ p q⟩
  · intro p q
    exact ⟨((upperStar AddCommGrpCat.{u + 1} g).mapDerivedCategoryHomologyFunctorIso
        ((p : ℤ) + q)).symm.app _ ≪≫
      (upperStar AddCommGrpCat.{u + 1} g).mapIso (e₁ p q)⟩
  · intro p q
    exact ⟨(DerivedCategory.homologyFunctor _ ((p : ℤ) + q)).mapIso
        ((hypercohomologySecondFunctor f' g').mapIso
          ((DerivedCategory.singleFunctorIsoCompQ _ q).app (K.obj.homology q)).symm) ≪≫
      (DerivedCategory.homologyFunctor _ ((p : ℤ) + q)).mapIso
        ((hypercohomologyFirstFunctor f').mapIso
          (((upperStar AddCommGrpCat.{u + 1} g').mapDerivedCategorySingleFunctor q).app
            (K.obj.homology q))) ≪≫
      single_cohomology_iso (hypercohomologyFirstFunctor f')
        ((upperStar AddCommGrpCat.{u + 1} g').obj (K.obj.homology q)) p q ≪≫
      (lowerStar AddCommGrpCat.{u + 1} f').homologyRightDerivedFunctorObjSingleFunctorIso
        ((upperStar AddCommGrpCat.{u + 1} g').obj (K.obj.homology q)) p⟩
  · intro i hi
    exact (upperStar AddCommGrpCat.{u + 1} g').map_isZero (hterms i hi)
  · intro q
    exact exact_truncation_comparison (upperStar AddCommGrpCat.{u + 1} g') K.obj q
  · intro q
    exact ⟨((upperStar AddCommGrpCat.{u + 1} g').mapHomologicalComplexHomologyIso
      (.up ℤ) q).app K.obj⟩
  · exact hypercohomology_exactFunctor (hypercohomologyFirstFunctor f) K
      (upperStar AddCommGrpCat.{u + 1} g)
  · intro n
    let G := upperStar AddCommGrpCat.{u + 1} g
    let c := (G.mapDerivedCategoryHomologyFunctorIso n).app
      ((hypercohomologyFirstFunctor f).obj (DerivedCategory.Q.obj K.obj))
    refine ⟨c, rfl, ?_⟩
    intro p
    let i := hypercohomologyAbutmentMap (hypercohomologyFirstFunctor f) K n (n - p)
    change imageSubobject (G.map (imageSubobject i).arrow ≫ c.hom) = _
    rw [← imageSubobject_comp_eq_of_epi (G.map (factorThruImageSubobject i))
      (G.map (imageSubobject i).arrow ≫ c.hom)]
    rw [← Functor.map_comp_assoc, imageSubobject_arrow_comp]
    have hc := (G.mapDerivedCategoryHomologyFunctorIso n).hom.naturality
      ((hypercohomologyFirstFunctor f).map (DerivedCategory.Q.map
        (K.obj.ιTruncLE (n - p))))
    dsimp only [Functor.comp_map] at hc
    change G.map i ≫ c.hom = _ at hc
    rw [hc, imageSubobject_comp_eq_of_epi]
    rfl

end AlgebraicGeometry.Etale

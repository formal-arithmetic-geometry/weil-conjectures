/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Double
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.Dualizable
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableCriterion
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-!
# Dualizable objects of `D(C)` when the unit is a finite projective generator of sections

Let `C` be a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions, so that `D(C)` carries the derived tensor product. Suppose that the unit `𝟙` of
`C` is projective and that "global sections" `Hom(𝟙, -)` are finite in the following sense:

* a morphism from `𝟙` to a coproduct factors through a finite subcoproduct
  (`CategoryTheory.UnitFactorsThroughFiniteCoproducts`);
* a morphism from `𝟙` to a tensor product `F ⊗ G` is a finite sum of tensor products of
  morphisms `𝟙 ⟶ F` and `𝟙 ⟶ G` (`CategoryTheory.UnitTensorFinite`).

This is the situation of sheaves of modules on the pro-étale site of an affine weakly contractible
scheme. Then every dualizable object of `D(C)` is isomorphic to a bounded complex of finite
projective objects, that is, of retracts of finite direct sums `𝟙ʳ`
(`DerivedCategory.exists_iso_Q_obj_of_isDualizable`, the forward direction of Stacks 0FPV
in this setting).

## Strategy

1. (`DerivedCategory.exists_retract_of_exactPairing_of_projective_unit`) As over a ring, the
   coevaluation `𝟙 ⟶ K ⊗ N` is a cocycle of degree `0` of `M ⊗ F` for complexes `M`, `F`
   representing `K` and its dual `N` (`F` K-flat with flat terms), since `𝟙` is K-projective.
   By finiteness it is a finite sum of `sᵢ ⊗ tᵢ`, so it comes from the image `L` of a finite sum
   of disk complexes on `𝟙` mapping to `M`; hence `K` is a retract of `Q(L)`, a bounded complex
   whose terms are quotients of `𝟙ʳ`.
2. Consequently `K` is bounded, it has finite Tor amplitude, and if `M` vanishes above `b` the
   top cohomology `Hᵇ(K)` is a quotient of some `𝟙ʳ`.
3. Dualizable objects are closed under cones; one kills the top cohomology by a map
   `𝟙ʳ[-b] ⟶ K` and argues by induction on the length of the Tor amplitude. When the Tor
   amplitude is a single degree, `K = H[-b]` where `H` is a quotient of `𝟙ʳ` with
   `Hom(H, -)` exact, hence a retract of `𝟙ʳ`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [Preadditive C]

/-- Morphisms from the unit to a coproduct indexed by a type of `Type` factor through finite
subcoproducts: they are finite sums of morphisms to the summands. -/
def UnitFactorsThroughFiniteCoproducts : Prop :=
  ∀ ⦃J : Type⦄ (X : J → C) [HasCoproduct X] (x : 𝟙_ C ⟶ ∐ X),
    ∃ (S : Finset J) (y : ∀ j, 𝟙_ C ⟶ X j), x = ∑ j ∈ S, y j ≫ Sigma.ι X j

/-- Morphisms from the unit to a tensor product `F ⊗ G` are finite sums of composites
`𝟙 ⟶ 𝟙 ⊗ 𝟙 ⟶ F ⊗ G` of a morphism `uᵢ : 𝟙 ⟶ 𝟙 ⊗ 𝟙` with a tensor product of morphisms
`sᵢ : 𝟙 ⟶ F` and `tᵢ : 𝟙 ⟶ G`. -/
def UnitTensorFinite : Prop :=
  ∀ (F G : C) (x : 𝟙_ C ⟶ F ⊗ G), ∃ (n : ℕ) (u : Fin n → (𝟙_ C ⟶ 𝟙_ C ⊗ 𝟙_ C))
    (s : Fin n → (𝟙_ C ⟶ F)) (t : Fin n → (𝟙_ C ⟶ G)), x = ∑ i, u i ≫ (s i ⊗ₘ t i)

/-- **An elementwise five lemma.** In a preadditive category, consider a commutative ladder
`A₁ ⟶ A₂ ⟶ A₃ ⟶ A₄ ⟶ A₅` over `B₁ ⟶ B₂ ⟶ B₃ ⟶ B₄ ⟶ B₅` whose rows are exact at the
indicated places, in the sense of morphisms from arbitrary objects. If the outer four vertical
maps are isomorphisms, so is the middle one. -/
lemma isIso_of_five_exact {D : Type*} [Category D] [Preadditive D]
    {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : D}
    {a : A₁ ⟶ A₂} {b : A₂ ⟶ A₃} {c : A₃ ⟶ A₄} {d : A₄ ⟶ A₅}
    {a' : B₁ ⟶ B₂} {b' : B₂ ⟶ B₃} {c' : B₃ ⟶ B₄} {d' : B₄ ⟶ B₅}
    (γ₁ : A₁ ⟶ B₁) (γ₂ : A₂ ⟶ B₂) (γ₃ : A₃ ⟶ B₃) (γ₄ : A₄ ⟶ B₄) (γ₅ : A₅ ⟶ B₅)
    (h₁ : a ≫ γ₂ = γ₁ ≫ a') (h₂ : b ≫ γ₃ = γ₂ ≫ b') (h₃ : c ≫ γ₄ = γ₃ ≫ c')
    (h₄ : d ≫ γ₅ = γ₄ ≫ d') (hab : a ≫ b = 0) (hcd' : c' ≫ d' = 0)
    (ex₃ : ∀ ⦃W : D⦄ (u : W ⟶ A₃), u ≫ c = 0 → ∃ v, u = v ≫ b)
    (ex₄ : ∀ ⦃W : D⦄ (u : W ⟶ A₄), u ≫ d = 0 → ∃ v, u = v ≫ c)
    (ex₂' : ∀ ⦃W : D⦄ (u : W ⟶ B₂), u ≫ b' = 0 → ∃ v, u = v ≫ a')
    (ex₃' : ∀ ⦃W : D⦄ (u : W ⟶ B₃), u ≫ c' = 0 → ∃ v, u = v ≫ b')
    [IsIso γ₁] [IsIso γ₂] [IsIso γ₄] [IsIso γ₅] : IsIso γ₃ := by
  rw [isIso_iff_yoneda_map_bijective]
  intro W
  refine ⟨fun u₁ u₂ (h : u₁ ≫ γ₃ = u₂ ≫ γ₃) ↦ ?_, fun u' ↦ ?_⟩
  · rw [← sub_eq_zero]
    have hu : (u₁ - u₂) ≫ γ₃ = 0 := by rw [Preadditive.sub_comp, h, sub_self]
    have h1 : (u₁ - u₂) ≫ c = 0 := by
      rw [← cancel_mono γ₄, Category.assoc, h₃, reassoc_of% hu, zero_comp, zero_comp]
    obtain ⟨v, hv⟩ := ex₃ _ h1
    have h2 : (v ≫ γ₂) ≫ b' = 0 := by
      rw [Category.assoc, ← h₂, ← Category.assoc, ← hv, hu]
    obtain ⟨w', hw'⟩ := ex₂' _ h2
    have : v = (w' ≫ inv γ₁) ≫ a := by
      rw [← cancel_mono γ₂, hw', Category.assoc, Category.assoc, h₁, IsIso.inv_hom_id_assoc]
    rw [hv, this, Category.assoc, hab, comp_zero]
  · have hy : (u' ≫ c' ≫ inv γ₄) ≫ d = 0 := by
      rw [← cancel_mono γ₅]
      simp only [Category.assoc, h₄, IsIso.inv_hom_id_assoc, hcd', comp_zero, zero_comp]
    obtain ⟨u, hu⟩ := ex₄ _ hy
    have h3 : (u' - u ≫ γ₃) ≫ c' = 0 := by
      rw [Preadditive.sub_comp, Category.assoc, ← h₃, ← Category.assoc, ← hu]
      simp
    obtain ⟨v', hv'⟩ := ex₃' _ h3
    refine ⟨u + (v' ≫ inv γ₂) ≫ b, ?_⟩
    change (u + (v' ≫ inv γ₂) ≫ b) ≫ γ₃ = u'
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, h₂, IsIso.inv_hom_id_assoc, ← hv']
    abel

namespace MonoidalClosed

variable {D : Type*} [Category D] [MonoidalCategory D] [MonoidalClosed D]

/-- The comparison `[X, 𝟙] ⊗ Z ⟶ [X, Z]` is natural in `X`. -/
lemma ihomUnitTensorToIhom_pre {X X' : D} (f : X ⟶ X') (Z : D) :
    ihomUnitTensorToIhom X' Z ≫ (pre f).app Z =
      (pre f).app (𝟙_ D) ▷ Z ≫ ihomUnitTensorToIhom X Z := by
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, id_tensor_pre_app_comp_ev,
    whiskerLeft_ihomUnitTensorToIhom_ev, whisker_exchange_assoc,
    whiskerLeft_ihomUnitTensorToIhom_ev, associator_inv_naturality_middle_assoc,
    ← comp_whiskerRight_assoc, id_tensor_pre_app_comp_ev, comp_whiskerRight_assoc,
    associator_inv_naturality_left_assoc]

end MonoidalClosed

end CategoryTheory

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- If morphisms from the unit are finite on coproducts and on tensor products, a morphism from
the unit to the degree `0` term of a tensor product of complexes `M ⊗ F` is a finite sum of
tensor products `sᵢ ⊗ tᵢ` of morphisms to terms `M^{pᵢ}` and `F^{qᵢ}`, `pᵢ + qᵢ = 0`. -/
lemma exists_eq_sum_ιTensorObj (hC : UnitFactorsThroughFiniteCoproducts C)
    (hT : UnitTensorFinite C) (M F : CochainComplex C ℤ) (x : 𝟙_ C ⟶ (M ⊗ F).X 0) :
    ∃ (ι : Type) (_ : Fintype ι) (p q : ι → ℤ) (h : ∀ i, p i + q i = 0)
      (u : ι → (𝟙_ C ⟶ 𝟙_ C ⊗ 𝟙_ C))
      (s : ∀ i, 𝟙_ C ⟶ M.X (p i)) (t : ∀ i, 𝟙_ C ⟶ F.X (q i)),
      x = ∑ i, u i ≫ (s i ⊗ₘ t i) ≫
        HomologicalComplex.ιTensorObj M F (p i) (q i) 0 (h i) := by
  obtain ⟨S, y, hy⟩ := hC _ (show 𝟙_ C ⟶ ∐ _ from x)
  choose n u s t hst using fun j ↦ hT _ _ (y j)
  refine ⟨Σ j : S, Fin (n j), inferInstance, fun j ↦ j.1.1.1.1, fun j ↦ j.1.1.1.2,
    fun j ↦ j.1.1.2, fun j ↦ u j.1 j.2, fun j ↦ s j.1 j.2, fun j ↦ t j.1 j.2, ?_⟩
  refine hy.trans ?_
  rw [Fintype.sum_sigma, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hst j.1, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Category.assoc]
  rfl

omit [IsGrothendieckAbelian.{v} C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C] in
/-- A finite direct sum of morphisms which are epimorphisms is an epimorphism. -/
lemma epi_biproduct_map {ι : Type} [Finite ι] {X Y : ι → C} (f : ∀ i, X i ⟶ Y i)
    [∀ i, Epi (f i)] : Epi (biproduct.map f) := by
  have := Fintype.ofFinite ι
  refine ⟨fun g h hgh ↦ biproduct.hom_ext' _ _ fun i ↦ ?_⟩
  rw [← cancel_epi (f i)]
  simpa using congrArg (fun k ↦ biproduct.ι X i ≫ k) hgh

/-- If the terms of `F` are flat, tensoring a termwise monomorphism `f : L ⟶ M` of complexes with
`F` gives a termwise monomorphism `L ⊗ F ⟶ M ⊗ F`: in each degree it is a coproduct of the
monomorphisms `Lᵖ ⊗ F^q ⟶ Mᵖ ⊗ F^q`. -/
lemma mono_whiskerRight_f {L M : CochainComplex C ℤ} (f : L ⟶ M) [Mono f]
    (F : CochainComplex C ℤ) (hF : ∀ q, ObjectProperty.flat (F.X q)) (j : ℤ) :
    Mono ((f ▷ F).f j) := by
  have (i : ℤ × ℤ) : Mono (f.f i.1 ▷ F.X i.2) := by
    have : PreservesFiniteLimits (tensorRight (F.X i.2)) := (hF i.2).tensorRight.1
    have : PreservesLimitsOfShape WalkingCospan (tensorRight (F.X i.2)) := inferInstance
    exact (tensorRight (F.X i.2)).map_mono (f.f i.1)
  exact MorphismProperty.IsStableUnderColimitsOfShape.condition
    (W := MorphismProperty.monomorphisms C) _ _ (colimit.cocone _)
    (colimit.cocone _) (colimit.isColimit _) (colimit.isColimit _)
    (Discrete.natTrans fun i ↦ f.f i.as.1.1 ▷ F.X i.as.1.2)
    (fun i ↦ by exact this i.as.1) _ (fun ⟨⟨⟨p, q⟩, h⟩⟩ ↦ by
      refine (HomologicalComplex.ι_mapBifunctorMap f (𝟙 F) _ _ p q j h).trans ?_
      simp only [curriedTensor_obj_obj, curriedTensor_map_app, HomologicalComplex.id_f,
        curriedTensor_obj_map, whiskerLeft_id, Category.id_comp,
        Functor.mapBifunctorHomologicalComplex_obj_obj_toGradedObject,
        Discrete.functor_obj_eq_as, Functor.const_obj_obj]
      rfl)

/-- **A dualizable object is a retract of a finite complex.** Suppose that the unit of `C` is
projective, with finite morphisms to coproducts and tensor products. Let `K` be an object of
`D(C)` with a right dual `N`, represented by a complex `M`. Then the isomorphism `K ≅ Q(M)`
factors through `Q(L)` for a subcomplex `L` of `M` which is bounded and whose terms are
quotients of finite direct sums `𝟙ʳ`.

The coevaluation `𝟙 ⟶ K ⊗ N ≅ Q(M ⊗ F)`, where `F` is a K-flat complex of flat objects
representing `N`, is a cocycle `x` of degree `0` of `M ⊗ F`, as `𝟙[0]` is K-projective. It is a
finite sum of `sᵢ ⊗ tᵢ` with `sᵢ : 𝟙 ⟶ M^{pᵢ}`, so it comes from `L ⊗ F` where `L` is the image of
the sum of the disk complexes `𝟙 ⟶ 𝟙` in degrees `pᵢ, pᵢ + 1` mapping to `M` by `sᵢ`; it is a
cocycle there since `L ⊗ F ⟶ M ⊗ F` is a monomorphism. So the coevaluation factors through
`Q(L) ⊗ N`, and the zigzag identity factors `K ≅ Q(M)` through `Q(L)`. -/
theorem exists_retract_of_exactPairing_of_projective_unit [Projective (𝟙_ C)]
    (hC : UnitFactorsThroughFiniteCoproducts C) (hT : UnitTensorFinite C)
    (K N : DerivedCategory C) [ExactPairing K N] (M : CochainComplex C ℤ) (e : K ≅ Q.obj M) :
    ∃ (L : CochainComplex C ℤ) (ι : L ⟶ M) (_ : Mono ι) (a b : ℤ) (_ : L.IsStrictlyGE a)
      (_ : L.IsStrictlyLE b)
      (_ : ∀ n, ∃ (r : ℕ) (π : (⨁ fun _ : Fin r ↦ 𝟙_ C) ⟶ L.X n), Epi π)
      (w : K ⟶ Q.obj L), w ≫ Q.map ι = e.hom := by
  obtain ⟨F, π, _, hFflat, hF⟩ := CochainComplex.exists_quasiIso_flat_kFlat (Q.objPreimage N)
  have : IsIso (Q.map π) := by rwa [isIso_Q_map_iff_quasiIso]
  let eD : Q.obj F ≅ N := asIso (Q.map π) ≪≫ Q.objObjPreimageIso N
  let T (L' : CochainComplex C ℤ) : Q.obj L' ⊗ N ≅ Q.obj (L' ⊗ F) :=
    whiskerLeftIso (Q.obj L') eD.symm ≪≫ QObjTensorQObjIsoOfKFlatRight L' F hF
  have hTn {L₁ L₂ : CochainComplex C ℤ} (f : L₁ ⟶ L₂) :
      Q.map f ▷ N ≫ (T L₂).hom = (T L₁).hom ≫ Q.map (f ▷ F) := by
    simp only [T, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc, ← whisker_exchange_assoc,
      qObjTensorQObjIsoOfKFlatRight_hom_naturality]
  let U := (HomologicalComplex.single C (.up ℤ) 0).obj (𝟙_ C)
  let eU : 𝟙_ (DerivedCategory C) ≅ Q.obj U :=
    (singleFunctorObjUnitIso C).symm ≪≫ (singleFunctorIsoCompQ C 0).app _
  obtain ⟨φ, hφ⟩ := CochainComplex.IsKProjective.exists_Q_map_eq U (M ⊗ F)
    (eU.inv ≫ η_ K N ≫ e.hom ▷ N ≫ (T M).hom)
  let x : 𝟙_ C ⟶ (M ⊗ F).X 0 :=
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ C)).inv ≫ φ.f 0
  obtain ⟨ι, _, p, q, hpq, u, s, t, hx⟩ := exists_eq_sum_ιTensorObj hC hT M F x
  have hp (i : ι) : (ComplexShape.up ℤ).Rel (p i) (p i + 1) := rfl
  have hp' (i : ι) : p i ≠ p i + 1 := by omega
  let D (i : ι) : CochainComplex C ℤ := HomologicalComplex.double (𝟙 (𝟙_ C)) (hp i)
  let dm (i : ι) : D i ⟶ M := HomologicalComplex.mkHomFromDouble (hp i) (hp' i) (s i)
    (s i ≫ M.d (p i) (p i + 1)) (by simp) (fun k _ ↦ by simp)
  let g : (⨁ D) ⟶ M := biproduct.desc dm
  let L := image g
  let j : L ⟶ M := image.ι g
  let s' (i : ι) : 𝟙_ C ⟶ L.X (p i) :=
    (HomologicalComplex.doubleXIso₀ _ (hp i)).inv ≫ (biproduct.ι D i ≫ factorThruImage g).f (p i)
  have hs' (i : ι) : s' i ≫ j.f (p i) = s i := by
    have : (biproduct.ι D i ≫ factorThruImage g ≫ j) = dm i := by
      simp [j, g]
    simp only [s', Category.assoc, ← HomologicalComplex.comp_f, this, dm,
      HomologicalComplex.mkHomFromDouble_f₀, Iso.inv_hom_id_assoc]
  let x' : 𝟙_ C ⟶ (L ⊗ F).X 0 := ∑ i, u i ≫ (s' i ⊗ₘ t i) ≫
    HomologicalComplex.ιTensorObj L F (p i) (q i) 0 (hpq i)
  have hx' : x' ≫ (j ▷ F).f 0 = x := by
    rw [hx, Preadditive.sum_comp]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [Category.assoc]
    congr 1
    refine ((s' i ⊗ₘ t i) ≫= HomologicalComplex.ι_mapBifunctorMap j (𝟙 F) _ _
      (p i) (q i) 0 (hpq i)).trans ?_
    simp [← hs' i, tensorHom_def]
    rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]
  have hj : ∀ k, Mono ((j ▷ F).f k) := mono_whiskerRight_f j F hFflat
  have hd : x' ≫ (L ⊗ F).d 0 1 = 0 := by
    rw [← cancel_mono ((j ▷ F).f 1), Category.assoc, ← HomologicalComplex.Hom.comm,
      reassoc_of% hx', zero_comp]
    simp [x, (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 (𝟙_ C) 1 (by omega)).eq_of_tgt
      (U.d 0 1) 0]
  let φ' : U ⟶ L ⊗ F := HomologicalComplex.mkHomFromSingle x' (by
    rintro k (rfl : 0 + 1 = k)
    exact hd)
  have hφ' : φ' ≫ j ▷ F = φ := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.mkHomFromSingle_f, Category.assoc, hx']
    simp [x]
  have hu : (eU.hom ≫ Q.map φ' ≫ (T _).inv) ≫ Q.map j ▷ N = η_ K N ≫ e.hom ▷ N := by
    rw [← cancel_mono (T M).hom, Category.assoc, Category.assoc, Category.assoc, hTn j,
      Iso.inv_hom_id_assoc, ← Q.map_comp, hφ', hφ, Iso.hom_inv_id_assoc,
      Category.assoc]
  have key : (tensorRightHomEquiv _ K N _).symm (eU.hom ≫ Q.map φ' ≫ (T _).inv) ≫ Q.map j =
      (λ_ K).hom ≫ e.hom := by
    rw [← tensorRightHomEquiv_symm_coevaluation_comp_whiskerRight (Y' := N), ← hu,
      Equiv.eq_symm_apply, tensorRightHomEquiv_naturality, Equiv.apply_symm_apply]
  -- the terms of `L` are quotients of `𝟙ʳ`, and `L` is bounded
  have hD (i : ι) (k : ℤ) : ∃ c : 𝟙_ C ⟶ (D i).X k, Epi c := by
    by_cases h₀ : k = p i
    · subst h₀
      exact ⟨(HomologicalComplex.doubleXIso₀ _ (hp i)).inv, inferInstance⟩
    by_cases h₁ : k = p i + 1
    · subst h₁
      exact ⟨(HomologicalComplex.doubleXIso₁ _ (hp i) (hp' i)).inv, inferInstance⟩
    exact ⟨0, (HomologicalComplex.isZero_double_X _ (hp i) k h₀ h₁).epi _⟩
  choose c hc using hD
  let eX (k : ℤ) : (⨁ D).X k ≅ ⨁ fun i ↦ (D i).X k :=
    (HomologicalComplex.eval C (.up ℤ) k).mapBiproduct D
  have hL (k : ℤ) : Epi ((factorThruImage g).f k) := inferInstance
  let ε := Fintype.equivFin ι
  have hzero (k : ℤ) (hk : ∀ i, k ≠ p i ∧ k ≠ p i + 1) : IsZero (L.X k) := by
    refine IsZero.of_epi ((eX k).inv ≫ (factorThruImage g).f k) ?_
    refine (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext' _ _ fun i ↦ ?_)
    exact (HomologicalComplex.isZero_double_X _ (hp i) k (hk i).1 (hk i).2).eq_of_src _ _
  refine ⟨L, j, inferInstance, -∑ i, |p i|, ∑ i, |p i| + 1,
    (CochainComplex.isStrictlyGE_iff L _).2 fun k hk ↦ hzero k fun i ↦ ?_,
    (CochainComplex.isStrictlyLE_iff L _).2 fun k hk ↦ hzero k fun i ↦ ?_,
    fun k ↦ ⟨Fintype.card ι, (biproduct.whiskerEquiv (f := fun _ : Fin (Fintype.card ι) ↦ 𝟙_ C)
      (g := fun _ : ι ↦ 𝟙_ C) ε.symm (fun _ ↦ Iso.refl _)).hom ≫
      biproduct.map (fun i ↦ c i k) ≫ (eX k).inv ≫ (factorThruImage g).f k, ?_⟩,
    _, by rw [Category.assoc, key, Iso.inv_hom_id_assoc]⟩
  · have := Finset.single_le_sum (f := fun i ↦ |p i|) (fun i _ ↦ abs_nonneg _)
      (Finset.mem_univ i)
    constructor <;> linarith [neg_abs_le (p i)]
  · have := Finset.single_le_sum (f := fun i ↦ |p i|) (fun i _ ↦ abs_nonneg _)
      (Finset.mem_univ i)
    constructor <;> linarith [le_abs_self (p i)]
  · have := epi_biproduct_map (fun i ↦ c i k)
    infer_instance

end DerivedCategory

namespace DerivedCategory

open Pretriangulated MonoidalClosed

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]

/-- A shift of a dualizable object of `D(C)` is dualizable: `X⟦n⟧ ≅ X ⊗ 𝟙⟦n⟧`, and `𝟙⟦n⟧` has
tensor inverse `𝟙⟦-n⟧`. -/
lemma isDualizable_shift {X : DerivedCategory C} (hX : IsDualizable X) (n : ℤ) :
    IsDualizable (X⟦n⟧) := by
  let U := 𝟙_ (DerivedCategory C)
  have hU : IsDualizable (U⟦n⟧) := isDualizable_of_tensorIso (Y := U⟦-n⟧)
    (shiftTensorShiftIso (X := U) (Y := U) (a := n) (b := -n) ≪≫ (shiftFunctor _ _).mapIso (λ_ U) ≪≫
      eqToIso (by rw [add_neg_cancel]) ≪≫ (shiftFunctorZero _ ℤ).app U)
    (shiftTensorShiftIso (X := U) (Y := U) (a := -n) (b := n) ≪≫ (shiftFunctor _ _).mapIso (λ_ U) ≪≫
      eqToIso (by rw [neg_add_cancel]) ≪≫ (shiftFunctorZero _ ℤ).app U)
  have hX0 : IsDualizable (X⟦(0 : ℤ)⟧) := IsDualizable.of_iso ((shiftFunctorZero _ ℤ).app X).symm hX
  exact IsDualizable.of_iso (shiftTensorShiftIso (X := X) (Y := U) (a := 0) (b := n) ≪≫ (shiftFunctor _ _).mapIso (ρ_ X) ≪≫
    eqToIso (by rw [zero_add])) (hX0.tensorObj hU)

/-- **Dualizable objects are closed under cones.** If two vertices `T.obj₁` and `T.obj₂` of a
distinguished triangle of `D(C)` are dualizable, so is the third. For any `Z`, both
`X ↦ [X, 𝟙] ⊗ Z` and `X ↦ [X, Z]` carry distinguished triangles to distinguished triangles, and
the comparison `[X, 𝟙] ⊗ Z ⟶ [X, Z]`, natural in `X`, is an isomorphism for dualizable `X`; the
five lemma applies to the rotations of `T`. -/
theorem isDualizable_obj₃_of_distTriang (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (h₁ : IsDualizable T.obj₁) (h₂ : IsDualizable T.obj₂) :
    IsDualizable T.obj₃ := by
  obtain ⟨_⟩ := nonempty_braidedCategory C
  rw [isDualizable_iff_isIso_ihomUnitTensorToIhom]
  have hiso {X : DerivedCategory C} (hX : IsDualizable X) (Z : DerivedCategory C) :
      IsIso (ihomUnitTensorToIhom X Z) := by
    obtain ⟨_⟩ := hX
    let := BraidedCategory.exactPairing_swap X Xᘁ
    exact isIso_ihomUnitTensorToIhom Xᘁ X Z
  set Z := T.obj₃
  have hT₁ := rot_of_distTriang _ hT
  have hT₂ := rot_of_distTriang _ hT₁
  obtain ⟨k₀, hk₀⟩ := exists_distinguished_ihom_pre T hT (𝟙_ _)
  obtain ⟨k₁, hk₁⟩ := exists_distinguished_ihom_pre _ hT₁ (𝟙_ _)
  obtain ⟨k₂, hk₂⟩ := exists_distinguished_ihom_pre _ hT₂ (𝟙_ _)
  have hF₀ := (tensorRight Z).map_distinguished _ hk₀
  have hF₁ := (tensorRight Z).map_distinguished _ hk₁
  have hF₂ := (tensorRight Z).map_distinguished _ hk₂
  obtain ⟨l₀, hl₀⟩ := exists_distinguished_ihom_pre T hT Z
  obtain ⟨l₁, hl₁⟩ := exists_distinguished_ihom_pre _ hT₁ Z
  obtain ⟨l₂, hl₂⟩ := exists_distinguished_ihom_pre _ hT₂ Z
  have : IsIso (ihomUnitTensorToIhom T.rotate.rotate.obj₂ Z) := hiso (isDualizable_shift h₁ 1) Z
  have : IsIso (ihomUnitTensorToIhom T.rotate.rotate.obj₃ Z) := hiso (isDualizable_shift h₂ 1) Z
  have := hiso h₁ Z
  have := hiso h₂ Z
  exact isIso_of_five_exact (ihomUnitTensorToIhom _ Z) (ihomUnitTensorToIhom _ Z)
    (ihomUnitTensorToIhom _ Z) (ihomUnitTensorToIhom _ Z) (ihomUnitTensorToIhom _ Z)
    (ihomUnitTensorToIhom_pre _ _).symm (ihomUnitTensorToIhom_pre _ _).symm
    (ihomUnitTensorToIhom_pre _ _).symm (ihomUnitTensorToIhom_pre _ _).symm
    (comp_distTriang_mor_zero₁₂ _ hF₂) (comp_distTriang_mor_zero₁₂ _ hl₀)
    (fun _ u hu ↦ Triangle.coyoneda_exact₂ _ hF₁ u hu) (fun _ u hu ↦ Triangle.coyoneda_exact₂ _ hF₀ u hu)
    (fun _ u hu ↦ Triangle.coyoneda_exact₂ _ hl₂ u hu) (fun _ u hu ↦ Triangle.coyoneda_exact₂ _ hl₁ u hu)

end DerivedCategory

namespace CategoryTheory

open Limits

section FinProj

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C]

/-- The biproduct of copies of an object `X` indexed by a sum of finite types is the binary
biproduct of the two partial biproducts. -/
noncomputable def biprodBiproductConstIso (X : C) (ι κ : Type) [Finite ι] [Finite κ] :
    (⨁ fun _ : ι ↦ X) ⊞ (⨁ fun _ : κ ↦ X) ≅ ⨁ fun _ : ι ⊕ κ ↦ X where
  hom := biprod.desc (biproduct.desc fun i ↦ biproduct.ι (fun _ : ι ⊕ κ ↦ X) (Sum.inl i))
    (biproduct.desc fun k ↦ biproduct.ι (fun _ : ι ⊕ κ ↦ X) (Sum.inr k))
  inv := biproduct.desc fun s ↦ Sum.elim (fun i ↦ biproduct.ι (fun _ : ι ↦ X) i ≫ biprod.inl)
    (fun k ↦ biproduct.ι (fun _ : κ ↦ X) k ≫ biprod.inr) s
  hom_inv_id := by
    apply biprod.hom_ext' <;> apply biproduct.hom_ext' <;> intro j <;> simp
  inv_hom_id := by
    apply biproduct.hom_ext'
    rintro (i | k) <;> simp

/-- The biproduct of `r + s` copies of `X` is the binary biproduct of `r` and `s` copies. -/
noncomputable def biprodBiproductFinIso (X : C) (r s : ℕ) :
    (⨁ fun _ : Fin r ↦ X) ⊞ (⨁ fun _ : Fin s ↦ X) ≅ ⨁ fun _ : Fin (r + s) ↦ X :=
  biprodBiproductConstIso X (Fin r) (Fin s) ≪≫
    biproduct.whiskerEquiv (f := fun _ : Fin r ⊕ Fin s ↦ X) (g := fun _ : Fin (r + s) ↦ X)
      finSumFinEquiv (fun _ ↦ Iso.refl _)

variable [MonoidalCategory C]

variable (C) in
/-- The objects of `C` which are retracts of a finite direct sum `𝟙ʳ` of copies of the unit, the
*finite projective* objects of the blueprint. -/
def finProj : ObjectProperty C :=
  fun P ↦ ∃ r : ℕ, Nonempty (Retract P (⨁ fun _ : Fin r ↦ 𝟙_ C))

lemma finProj_of_iso {P P' : C} (e : P ≅ P') (hP : finProj C P) : finProj C P' := by
  obtain ⟨r, ⟨h⟩⟩ := hP
  exact ⟨r, ⟨(Retract.ofIso e.symm).trans h⟩⟩

lemma finProj_of_isZero {P : C} (hP : IsZero P) : finProj C P :=
  ⟨0, ⟨{ i := 0, r := 0, retract := hP.eq_of_src _ _ }⟩⟩

lemma finProj_biprod {P P' : C} (hP : finProj C P) (hP' : finProj C P') :
    finProj C (P ⊞ P') := by
  obtain ⟨r, ⟨h⟩⟩ := hP
  obtain ⟨s, ⟨h'⟩⟩ := hP'
  refine ⟨r + s, ⟨Retract.trans ?_ (Retract.ofIso (biprodBiproductFinIso _ r s))⟩⟩
  exact { i := biprod.map h.i h'.i, r := biprod.map h.r h'.r, retract := by apply biprod.hom_ext' <;> simp [h.retract_assoc, h'.retract_assoc] }

omit [MonoidalCategory C] in
lemma projective_biproduct_const (X : C) [Projective X] (ι : Type) [Finite ι] :
    Projective (⨁ fun _ : ι ↦ X) where
  factors f e _ := ⟨biproduct.desc fun b ↦ Projective.factorThru (biproduct.ι (fun _ : ι ↦ X) b ≫ f) e,
    biproduct.hom_ext' _ _ fun b ↦ by simp⟩

lemma finProj.projective [Projective (𝟙_ C)] {P : C} (hP : finProj C P) : Projective P := by
  obtain ⟨r, ⟨h⟩⟩ := hP
  have := projective_biproduct_const (𝟙_ C) (Fin r)
  exact h.projective

lemma isDualizable_biproduct_unit [MonoidalPreadditive C] (r : ℕ) : IsDualizable (⨁ fun _ : Fin r ↦ 𝟙_ C) := by
  induction r with
  | zero =>
    refine CategoryTheory.IsZero.isDualizable ((IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext' _ _ ?_))
    exact fun i ↦ i.elim0
  | succ r ih =>
    exact IsDualizable.of_iso (biprodBiproductFinIso _ r 1)
      (IsDualizable.biprod ih (IsDualizable.of_iso (biproductUniqueIso _).symm isDualizable_unit))

lemma finProj.isDualizable [MonoidalPreadditive C] [IsIdempotentComplete C] {P : C} (hP : finProj C P) :
    IsDualizable P := by
  obtain ⟨r, ⟨h⟩⟩ := hP
  exact IsDualizable.of_retract h (isDualizable_biproduct_unit r)

end FinProj

end CategoryTheory

namespace DerivedCategory

open Pretriangulated MonoidalClosed

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]

attribute [local instance] Abelian.hasFiniteBiproducts

/-- In a distinguished triangle `T` with `T.obj₁` and `T.obj₂` vanishing above `b`, if `Hᵇ` of the
first map is an epimorphism then `T.obj₃` vanishes above `b - 1`. -/
lemma isLE_obj₃_of_distTriang (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    (b : ℤ) (h₁ : T.obj₁.IsLE b) (h₂ : T.obj₂.IsLE b) (h : Epi ((homologyFunctor C b).map T.mor₁)) :
    T.obj₃.IsLE (b - 1) := by
  rw [isLE_iff]
  intro k hk
  have h0 : (homologyFunctor C k).map T.mor₂ = 0 := by
    by_cases hkb : k = b
    · subst hkb
      exact (HomologySequence.epi_homologyMap_mor₁_iff T hT k).1 h
    · exact (isZero_of_isLE T.obj₂ b k (by omega)).eq_of_src _ _
  have he : Epi ((homologyFunctor C k).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT k (k + 1)).2
      ((isZero_of_isLE T.obj₁ b (k + 1) (by omega)).eq_of_tgt _ _)
  rw [h0] at he
  exact (IsZero.iff_id_eq_zero _).2 ((cancel_epi (0 : (homologyFunctor C k).obj T.obj₂ ⟶ _)).1
    (by simp))

variable [Projective (𝟙_ C)]

/-- If the unit of `C` is projective, there are no nonzero morphisms from the unit of `D(C)` to an
object vanishing above `-1`. -/
lemma hom_unit_eq_zero {X : DerivedCategory C} [X.IsLE (-1)]
    (f : 𝟙_ (DerivedCategory C) ⟶ X) : f = 0 := by
  have : Subsingleton ((singleFunctor C 0).obj (𝟙_ C) ⟶ X) :=
    (homSingleEquivOfProjective (𝟙_ C) 0 X).subsingleton_congr.2
      ⟨fun a b ↦ (isZero_of_isLE X (-1) 0 (by omega)).eq_of_tgt a b⟩
  rw [← cancel_epi (singleFunctorObjUnitIso C).hom]
  exact Subsingleton.elim _ _

section Finite

variable (hC : UnitFactorsThroughFiniteCoproducts C) (hT : UnitTensorFinite C)
include hC hT

/-- A dualizable object `K` vanishing above `b` has a top cohomology `Hᵇ(K)` which is a quotient of
a finite direct sum `𝟙ʳ`: `K` is a retract of `Q(L)` for a complex `L` vanishing above `b` whose
terms are quotients of some `𝟙ʳ`, and `Hᵇ(L)` is a quotient of `Lᵇ`. -/
theorem exists_epi_homology_of_isDualizable {K : DerivedCategory C} (hK : IsDualizable K)
    (b : ℤ) [K.IsLE b] :
    ∃ (r : ℕ) (π : (⨁ fun _ : Fin r ↦ 𝟙_ C) ⟶ (homologyFunctor C b).obj K), Epi π := by
  obtain ⟨_⟩ := hK
  obtain ⟨M, _, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  obtain ⟨L, ι, _, -, -, -, -, hπ, w, hw⟩ :=
    exists_retract_of_exactPairing_of_projective_unit hC hT K Kᘁ M e
  have : L.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff L b).2 fun n hn ↦
    IsZero.of_mono (ι.f n) (M.isZero_of_isStrictlyLE b n hn)
  obtain ⟨r, π, _⟩ := hπ b
  have : IsIso (L.iCycles b) := L.isIso_iCycles b (b + 1) (by simp)
    ((L.isZero_of_isStrictlyLE b (b + 1) (by omega)).eq_of_tgt _ _)
  let H := homologyFunctor C b
  let ρ : Q.obj L ⟶ K := Q.map ι ≫ e.inv
  have hwρ : w ≫ ρ = 𝟙 K := by simp [ρ, reassoc_of% hw]
  have : Epi (H.map ρ) :=
    (IsSplitEpi.mk' ⟨H.map w, by rw [← H.map_comp, hwρ, H.map_id]⟩).epi
  exact ⟨r, π ≫ inv (L.iCycles b) ≫ L.homologyπ b ≫ ((homologyFunctorFactors C b).app L).inv ≫
    H.map ρ, inferInstance⟩

/-- A dualizable object is bounded: it is a retract of `Q(L)` for a bounded complex `L`. -/
theorem bounded_of_isDualizable {K : DerivedCategory C} (hK : IsDualizable K) :
    ∃ a b : ℤ, K.IsGE a ∧ K.IsLE b := by
  obtain ⟨_⟩ := hK
  obtain ⟨L, ι, _, a, b, _, _, -, w, hw⟩ :=
    exists_retract_of_exactPairing_of_projective_unit hC hT K Kᘁ (Q.objPreimage K)
      (Q.objObjPreimageIso K).symm
  let H (i : ℤ) := homologyFunctor C i
  have hret (i : ℤ) : (H i).map w ≫ (H i).map (Q.map ι ≫ (Q.objObjPreimageIso K).hom) = 𝟙 _ := by
    rw [← Functor.map_comp, reassoc_of% hw]
    simp
  have (i : ℤ) : Mono ((H i).map w) := (IsSplitMono.mk' ⟨_, hret i⟩).mono
  refine ⟨a, b, ?_, ?_⟩
  · rw [isGE_iff]
    intro i hi
    exact IsZero.of_mono ((H i).map w)
      ((L.exactAt_of_isGE a i hi).isZero_homology.of_iso ((homologyFunctorFactors C i).app L))
  · rw [isLE_iff]
    intro i hi
    exact IsZero.of_mono ((H i).map w)
      ((L.exactAt_of_isLE b i hi).isZero_homology.of_iso ((homologyFunctorFactors C i).app L))

/-- A dualizable object has finite Tor amplitude: it and its dual are bounded above. -/
theorem exists_torAmplitudeIn_of_isDualizable {K : DerivedCategory C} (hK : IsDualizable K) :
    ∃ a b : ℤ, torAmplitudeIn C a b K := by
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := nonempty_braidedCategory C
  let := BraidedCategory.exactPairing_swap K Kᘁ
  obtain ⟨-, b, -, _⟩ := bounded_of_isDualizable hC hT (K := K) ⟨inferInstance⟩
  obtain ⟨-, b', -, _⟩ := bounded_of_isDualizable hC hT (K := Kᘁ) ⟨⟨K⟩⟩
  exact ⟨-b', b, torAmplitudeIn_of_exactPairing_of_isLE (L := Kᘁ) b b'⟩

/-- **Base case.** A dualizable object of Tor amplitude in `[b, b]` is `P[-b]` for a retract `P`
of some `𝟙ʳ`. It is `Y[-b]` for `Y = Hᵇ(K)`, a quotient `π : 𝟙ʳ ⟶ Y`. Its dual `N` vanishes above
`-b`, so maps `Y ⟶ X` are maps `𝟙 ⟶ X[-b] ⊗ N`; as the cone of `π[-b] ⊗ N` vanishes above `-1`,
maps from `𝟙` lift along it, and the identity of `Y` lifts to a section of `π`. -/
theorem exists_iso_single_of_torAmplitudeIn_single {K : DerivedCategory C} (hK : IsDualizable K)
    (b : ℤ) (hKt : torAmplitudeIn C b b K) :
    ∃ P : C, finProj C P ∧ Nonempty (K ≅ (singleFunctor C b).obj P) := by
  obtain ⟨_, _⟩ := homologyConcentratedIn_of_torAmplitudeIn hKt
  obtain ⟨Y, ⟨eY⟩⟩ := K.exists_iso_singleFunctor_obj_of_isGE_of_isLE b
  obtain ⟨r, π, _⟩ := exists_epi_homology_of_isDualizable hC hT hK b
  let B := ⨁ fun _ : Fin r ↦ 𝟙_ C
  let S := singleFunctor C b
  let π' : B ⟶ Y := π ≫ (homologyFunctor C b).map eY.hom ≫
    ((singleFunctorCompHomologyFunctorIso C b).app Y).hom
  obtain ⟨_⟩ := hK
  obtain ⟨_⟩ := nonempty_braidedCategory C
  let := BraidedCategory.exactPairing_swap K Kᘁ
  have hN := homologyConcentratedIn_of_torAmplitudeIn
    (torAmplitudeIn_of_exactPairing (K := K) (L := Kᘁ) hKt)
  have : (Kᘁ).IsLE (-b) := hN.2
  obtain ⟨Co, g, h, hTr⟩ := distinguished_cocone_triangle (S.map π')
  have hepi : Epi ((homologyFunctor C b).map (S.map π')) := by
    have e := (singleFunctorCompHomologyFunctorIso C b).hom.naturality π'
    have : Epi ((S ⋙ homologyFunctor C b).map π' ≫
        (singleFunctorCompHomologyFunctorIso C b).hom.app Y) := by
      rw [e]
      infer_instance
    exact (epi_comp_iff_of_isIso _ _).1 this
  have : (S.obj B).IsLE b := inferInstanceAs (((singleFunctor C b).obj B).IsLE b)
  have : (S.obj Y).IsLE b := inferInstanceAs (((singleFunctor C b).obj Y).IsLE b)
  have : Co.IsLE (b - 1) := isLE_obj₃_of_distTriang _ hTr b
    (inferInstanceAs (((singleFunctor C b).obj B).IsLE b))
    (inferInstanceAs (((singleFunctor C b).obj Y).IsLE b)) hepi
  have : (Co ⊗ Kᘁ).IsLE (-1) := by
    have := isLE_tensor Co Kᘁ (b - 1) (-b)
    exact TStructure.t.isLE_of_le _ (b - 1 + -b) (-1) (by omega)
  have hTr' := (tensorRight Kᘁ).map_distinguished _ hTr
  let t := tensorRightHomEquiv (𝟙_ _) K Kᘁ (S.obj Y) ((λ_ K).hom ≫ eY.hom)
  obtain ⟨s', hs'⟩ := Triangle.coyoneda_exact₂ _ hTr' t (hom_unit_eq_zero (X := Co ⊗ Kᘁ) _)
  let g' := (tensorRightHomEquiv (𝟙_ _) K Kᘁ (S.obj B)).symm s'
  have hg' : g' ≫ S.map π' = (λ_ K).hom ≫ eY.hom := by
    apply (tensorRightHomEquiv (𝟙_ _) K Kᘁ (S.obj Y)).injective
    rw [tensorRightHomEquiv_naturality, Equiv.apply_symm_apply]
    exact hs'.symm
  let σ := eY.inv ≫ (λ_ K).inv ≫ g'
  have hσ : σ ≫ S.map π' = 𝟙 _ := by simp [σ, hg']
  exact ⟨Y, ⟨r, ⟨{ i := S.preimage σ, r := π', retract := S.map_injective (by rw [S.map_comp, S.map_preimage, hσ, S.map_id]) }⟩⟩,
    ⟨eY⟩⟩

/-- **Induction on the length of the Tor amplitude.** A dualizable object of Tor amplitude in
`[a, b]` is isomorphic to `Q(P)` for a bounded complex `P` of retracts of finite direct sums `𝟙ʳ`.
Kill the top cohomology by a map `f : 𝟙ʳ[-b] ⟶ K` inducing an epimorphism on `Hᵇ`; its cone `C'` is
dualizable with Tor amplitude in `[a, b - 1]`, hence `Q(P')` by induction, and `K` is the cone of
a map `C'[-1] ⟶ 𝟙ʳ[-b]`, which lifts to complexes since `P'[-1]` is K-projective. -/
theorem exists_iso_Q_obj_of_isDualizable_aux (n : ℕ) :
    ∀ {K : DerivedCategory C} (a b : ℤ), b - a = n → IsDualizable K → torAmplitudeIn C a b K →
      ∃ (P : CochainComplex C ℤ) (a' b' : ℤ), P.IsStrictlyGE a' ∧ P.IsStrictlyLE b' ∧
        (∀ k, finProj C (P.X k)) ∧ Nonempty (K ≅ Q.obj P) := by
  induction n with
  | zero =>
    intro K a b hab hK hKt
    obtain rfl : b = a := by omega
    obtain ⟨Y, hY, ⟨e⟩⟩ := exists_iso_single_of_torAmplitudeIn_single hC hT hK b hKt
    refine ⟨(HomologicalComplex.single C (.up ℤ) b).obj Y, b, b, inferInstance, inferInstance,
      fun k ↦ ?_, ⟨e ≪≫ (singleFunctorIsoCompQ C b).app Y⟩⟩
    by_cases hk : k = b
    · subst hk
      exact finProj_of_iso (HomologicalComplex.singleObjXSelf _ _ _).symm hY
    · exact finProj_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hk)
  | succ n ih =>
    intro K a b hab hK hKt
    obtain ⟨_, hKle⟩ := homologyConcentratedIn_of_torAmplitudeIn hKt
    obtain ⟨r, π, _⟩ := exists_epi_homology_of_isDualizable hC hT hK b
    let B := ⨁ fun _ : Fin r ↦ 𝟙_ C
    have hB : finProj C B := ⟨r, ⟨Retract.refl _⟩⟩
    have : Projective B := hB.projective
    let Ssing := (HomologicalComplex.single C (.up ℤ) b).obj B
    have hSsing (k : ℤ) : finProj C (Ssing.X k) := by
      by_cases hk : k = b
      · subst hk
        exact finProj_of_iso (HomologicalComplex.singleObjXSelf _ _ _).symm hB
      · exact finProj_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hk)
    let S := (singleFunctor C b).obj B
    let eS : S ≅ Q.obj Ssing := (singleFunctorIsoCompQ C b).app B
    let f : S ⟶ K := (homSingleEquivOfProjective B b K).symm π
    have hf : Epi ((homologyFunctor C b).map f) := by
      have h := (homSingleEquivOfProjective B b K).apply_symm_apply π
      rw [homSingleEquivOfProjective_apply, homSingleToHomology] at h
      have : (homologyFunctor C b).map f =
          ((singleFunctorCompHomologyFunctorIso C b).app B).hom ≫ π := by
        rw [← h, Iso.hom_inv_id_assoc]
      rw [this]
      infer_instance
    obtain ⟨Co, g, h, hTr⟩ := distinguished_cocone_triangle f
    have hSd : IsDualizable S := IsDualizable.of_iso eS.symm
      (isDualizable_Q_obj Ssing b b fun k ↦ (hSsing k).isDualizable)
    have hCo : IsDualizable Co := isDualizable_obj₃_of_distTriang _ hTr hSd hK
    have : Co.IsLE (b - 1) := isLE_obj₃_of_distTriang _ hTr b
      (inferInstanceAs (((singleFunctor C b).obj B).IsLE b)) hKle hf
    have hSt : torAmplitudeIn C b b S := (torAmplitudeIn C b b).prop_of_iso eS.symm
      (torAmplitudeIn_Q_obj_of_flat Ssing b b fun k ↦ (hSsing k).isDualizable.flat)
    have hCot : torAmplitudeIn C a (b - 1) Co := by
      intro F
      have hTF := rot_of_distTriang _
        ((tensorRight ((singleFunctor C 0).obj F)).map_distinguished _ hTr)
      refine ⟨TStructure.t.isGE₂ _ hTF a (hKt F).1 ?_, ?_⟩
      · have h1 := (hSt F).1
        have h2 := TStructure.t.isGE_shift (S ⊗ (singleFunctor C 0).obj F) b 1 (b - 1)
        exact TStructure.t.isGE_of_ge ((S ⊗ (singleFunctor C 0).obj F)⟦(1 : ℤ)⟧) a (b - 1)
          (by omega)
      · have := isLE_tensor Co ((singleFunctor C 0).obj F) (b - 1) 0
        exact TStructure.t.isLE_of_le _ (b - 1 + 0) (b - 1) (by omega)
    obtain ⟨P, a', b', _, _, hP, ⟨eP⟩⟩ := ih a (b - 1) (by omega) hCo hCot
    have hT₂ := inv_rot_of_distTriang _ hTr
    let eC : Co⟦(-1 : ℤ)⟧ ≅ Q.obj (P⟦(-1 : ℤ)⟧) :=
      (shiftFunctor _ (-1 : ℤ)).mapIso eP ≪≫ ((Q.commShiftIso (-1 : ℤ)).app P).symm
    have := P.isStrictlyGE_shift a' (-1) (a' + 1) (by omega)
    have := P.isStrictlyLE_shift b' (-1) (b' + 1) (by omega)
    have : ∀ k, Projective ((P⟦(-1 : ℤ)⟧).X k) := fun k ↦ (hP (k + -1)).projective
    have : (P⟦(-1 : ℤ)⟧).IsKProjective := CochainComplex.isKProjective_of_projective _ (b' + 1)
    obtain ⟨ψ, hψ⟩ := CochainComplex.IsKProjective.exists_Q_map_eq (P⟦(-1 : ℤ)⟧) Ssing
      (eC.inv ≫ (Triangle.mk f g h).invRotate.mor₁ ≫ eS.hom)
    obtain ⟨e', -, -⟩ := exists_iso_of_arrow_iso _ _ hT₂ (mappingCone_triangle_distinguished ψ)
      (Arrow.isoMk eC eS (by
        change eC.hom ≫ Q.map ψ = _
        rw [hψ, Iso.hom_inv_id_assoc]
        rfl))
    have : (CochainComplex.mappingCone ψ).IsStrictlyGE (min a' b) := by
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      rw [CochainComplex.mappingCone.isZero_X_iff]
      exact ⟨(P⟦(-1 : ℤ)⟧).isZero_of_isStrictlyGE (a' + 1) _ (by omega),
        CochainComplex.isZero_of_isStrictlyGE Ssing b _ (by omega)⟩
    have : (CochainComplex.mappingCone ψ).IsStrictlyLE (max b' b) := by
      rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      rw [CochainComplex.mappingCone.isZero_X_iff]
      exact ⟨(P⟦(-1 : ℤ)⟧).isZero_of_isStrictlyLE (b' + 1) _ (by omega),
        CochainComplex.isZero_of_isStrictlyLE Ssing b _ (by omega)⟩
    exact ⟨CochainComplex.mappingCone ψ, min a' b, max b' b, inferInstance, inferInstance,
      fun k ↦ finProj_of_iso (HomologicalComplex.homotopyCofiber.XIsoBiprod ψ k (k + 1) rfl).symm
        (finProj_biprod (hP (k + 1 + -1)) (hSsing k)), ⟨Triangle.π₃.mapIso e'⟩⟩

/-- **Dualizable objects are perfect.** If the unit of `C` is projective, with finite morphisms
to coproducts and tensor products, every dualizable object of `D(C)` is isomorphic to `Q(P)` for
a bounded complex `P` of retracts of finite direct sums `𝟙ʳ`. -/
theorem exists_iso_Q_obj_of_isDualizable {K : DerivedCategory C} (hK : IsDualizable K) :
    ∃ (P : CochainComplex C ℤ) (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ k, finProj C (P.X k)) ∧ Nonempty (K ≅ Q.obj P) := by
  obtain ⟨a, b, h⟩ := exists_torAmplitudeIn_of_isDualizable hC hT hK
  exact exists_iso_Q_obj_of_isDualizable_aux hC hT (max a b - a).toNat a (max a b) (by omega) hK
    (torAmplitudeIn.mono le_rfl (le_max_left b a |>.trans_eq (max_comm b a)) h)

end Finite

end DerivedCategory

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Etale.StandardEtale
public import WeilConjectures.AlgebraicGeometry.FunctionFieldLimit
public import WeilConjectures.AlgebraicGeometry.Sites.FieldPoints
public import WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!
# The counit at the generic point of an integral scheme

Let `X` be a quasi-separated integral scheme with function field `K` and generic point
`η : Spec K ⟶ X`. We show that the counit `η^* η_* Y ⟶ Y` of the adjunction `η^* ⊣ η_*` on
abelian étale sheaves is an isomorphism, i.e. that `η_*` is fully faithful.

Over the base change `W_K` of a quasi-compact quasi-separated étale `X`-scheme `W`, every section
of `η^* η_* Y` comes from a section of `η_* Y` over `W` under the unit, by continuity of sections
at the limit `Spec K = lim_U Spec Γ(X, U)`
(`AlgebraicGeometry.Etale.unitComparison_app_surjective_of_isLimit`) and since `η_* Y` is pushed
forward from every affine open `U`; by the triangle identity the counit is bijective over `W_K`. Every finite separable extension `E` of `K` spreads out to a
standard étale algebra over some `Γ(X, U)`, so the `W_K` cover the small étale site of `Spec K`.

## Main statements

- `AlgebraicGeometry.Scheme.exists_hom_etaleSpec_pullback`: spreading out a finite separable
  extension of the function field.
- `AlgebraicGeometry.Scheme.isIso_counit_fromSpecFunctionField`: the counit `η^* η_* Y ⟶ Y` is an
  isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Polynomial

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The map `Γ(X, U) ⟶ K` from the sections over a nonempty affine open to the function field. -/
noncomputable abbrev affineOpenToFunctionField (U : X.NonemptyAffineOpens) :
    Γ(X, U.1) ⟶ X.functionField :=
  X.affineOpensRingCocone.ι.app (op U)

/-- Finitely many elements of the function field come from the sections over a common nonempty
affine open. -/
lemma exists_affineOpen_forall_mem_range (s : Finset X.functionField) :
    ∃ U : X.NonemptyAffineOpens, ∀ x ∈ s, x ∈ Set.range (X.affineOpenToFunctionField U) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary _, by simp⟩
  | insert x s _ ih =>
    obtain ⟨U₁, hU₁⟩ := ih
    obtain ⟨⟨U₂⟩, a, ha⟩ := Concrete.isColimit_exists_rep _ X.isColimitAffineOpensRingCocone x
    obtain ⟨V, hV₁, hV₂⟩ := directed_of (· ≥ ·) U₁ U₂
    have hres {U U' : X.NonemptyAffineOpens} (h : U' ≤ U) (b : Γ(X, U.1)) :
        X.affineOpenToFunctionField U' (X.presheaf.map (homOfLE h).op b) =
          X.affineOpenToFunctionField U b := by
      have := X.affineOpensRingCocone.w (homOfLE h).op
      exact congr($(this) b)
    refine ⟨V, fun y hy ↦ ?_⟩
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact ⟨_, (hres hV₂ a).trans ha⟩
    · obtain ⟨b, rfl⟩ := hU₁ y hy
      exact ⟨_, hres hV₁ b⟩

/-- A monic polynomial over the function field comes from a monic polynomial over the sections
over some nonempty affine open. -/
lemma exists_monic_map_eq {f : X.functionField[X]} (hf : f.Monic) :
    ∃ (U : X.NonemptyAffineOpens) (g : Γ(X, U.1)[X]), g.Monic ∧
      g.map (X.affineOpenToFunctionField U).hom = f := by
  classical
  obtain ⟨U, hU⟩ := X.exists_affineOpen_forall_mem_range ((Finset.range f.natDegree).image f.coeff)
  choose a ha using fun i : Fin f.natDegree ↦
    hU (f.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 i.2, rfl⟩)
  refine ⟨U, Polynomial.X ^ f.natDegree + ∑ i : Fin f.natDegree, C (a i) * Polynomial.X ^ (i : ℕ),
    ?_, ?_⟩
  · refine monic_X_pow_add (degree_sum_fin_lt _)
  · conv_rhs => rw [hf.as_sum, ← Fin.sum_univ_eq_sum_range]
    simp only [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_sum,
      Polynomial.map_mul, map_C]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← ha i]

open scoped TensorProduct in
/-- **Spreading out a finite separable extension of the function field.** Let `E` be a finite
separable extension of the function field `K` of `X`. There is an affine étale `X`-scheme `W`
whose base change `W_K` along the generic point is nonempty and admits a morphism to `Spec E`
over `Spec K`: if `E = K[x]/(f)`, take `W = Spec Γ(X, U)[x, 1/g']/(g)` for a monic `g` over some
nonempty affine open `U` with `g = f` over `K`. -/
theorem exists_hom_etaleSpec_pullback (E : Type u) [Field E] [Algebra X.functionField E]
    [Algebra.Etale X.functionField E] :
    ∃ W : X.Etale, IsAffine W.left ∧
      Nonempty (X.fromSpecFunctionField.Etale.obj W).left ∧
      Nonempty (X.fromSpecFunctionField.Etale.obj W ⟶
        etaleSpec X.functionField E) := by
  set K := X.functionField
  have : FiniteDimensional K E := Algebra.FormallyUnramified.finite_of_free K E
  have : Algebra.IsSeparable K E := Algebra.FormallyUnramified.isSeparable K E
  let pb := Field.powerBasisOfFiniteOfSeparable K E
  have hsep : (minpoly K pb.gen).Separable := Algebra.IsSeparable.isSeparable K pb.gen
  obtain ⟨U, g, hg, hgf⟩ := X.exists_monic_map_eq
    (minpoly.monic (Algebra.IsSeparable.isIntegral K pb.gen))
  let A := Γ(X, U.1)
  let φ := X.affineOpenToFunctionField U
  let : Algebra A K := φ.hom.toAlgebra
  obtain ⟨P, hPf, hPg⟩ : ∃ P : StandardEtalePair A, P.f = g ∧ P.g = derivative g :=
    ⟨⟨g, hg, derivative g, ⟨1, 0, 1, by simp⟩⟩, rfl, rfl⟩
  let : Algebra A E := ((algebraMap K E).comp φ.hom).toAlgebra
  have : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hgf' : g.map (algebraMap A K) = minpoly K pb.gen := hgf
  -- the morphism `E → K ⊗_A P.Ring`
  have hroot : aeval ((1 : K) ⊗ₜ[A] P.X) (minpoly K pb.gen) = 0 := by
    rw [← hgf', aeval_map_algebraMap,
      show ((1 : K) ⊗ₜ[A] P.X) = Algebra.TensorProduct.includeRight P.X from rfl,
      aeval_algHom_apply, ← hPf, P.hasMap_X.1, map_zero]
  let ρ : E →ₐ[K] K ⊗[A] P.Ring := pb.lift _ hroot
  -- the morphism `K ⊗_A P.Ring → E`, so that `K ⊗_A P.Ring` is nontrivial
  have hmap : P.HasMap pb.gen := by
    refine ⟨?_, ?_⟩
    · rw [hPf, ← aeval_map_algebraMap K, hgf', minpoly.aeval]
    · rw [hPg, ← aeval_map_algebraMap K, ← derivative_map, hgf']
      exact (hsep.aeval_derivative_ne_zero (minpoly.aeval K pb.gen)).isUnit
  let σ : K ⊗[A] P.Ring →ₐ[A] E :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A K E) (P.lift pb.gen hmap)
      fun _ _ ↦ Commute.all _ _
  have : Nontrivial (K ⊗[A] P.Ring) := σ.toRingHom.domain_nontrivial
  -- the étale `X`-scheme `W`
  have hW : @Etale _ _ (Spec.map (CommRingCat.ofHom (algebraMap A P.Ring)) ≫ U.2.1.fromSpec) := by
    have hPe : Algebra.Etale A P.Ring := inferInstance
    have : @Etale _ _ (Spec.map (CommRingCat.ofHom (algebraMap A P.Ring))) :=
      HasRingHomProperty.Spec_iff.mpr ((RingHom.etale_algebraMap (R := A) (S := P.Ring)).mpr hPe)
    infer_instance
  let W : X.Etale := MorphismProperty.Over.mk ⊤ _ hW
  have hη : X.fromSpecFunctionField = Spec.map φ ≫ U.2.1.fromSpec :=
    X.fromSpecFunctionField_eq_functionFieldCone_comp U
  let ι := Spec.map (CommRingCat.ofHom (algebraMap A P.Ring))
  have h₁ : pullback.fst W.hom X.fromSpecFunctionField ≫ ι ≫ U.2.1.fromSpec =
      pullback.snd W.hom X.fromSpecFunctionField ≫ Spec.map φ ≫ U.2.1.fromSpec := by
    rw [← hη]
    exact pullback.condition
  have hcond : pullback.snd W.hom X.fromSpecFunctionField ≫
      Spec.map (CommRingCat.ofHom (algebraMap A K)) =
      pullback.fst W.hom X.fromSpecFunctionField ≫ ι := by
    rw [← cancel_mono U.2.1.fromSpec]
    simp only [Category.assoc]
    exact h₁.symm
  let q : pullback W.hom X.fromSpecFunctionField ⟶ Spec (.of (K ⊗[A] P.Ring)) :=
    pullback.lift _ _ hcond ≫ (pullbackSpecIso A K P.Ring).hom
  refine ⟨W, inferInstanceAs (IsAffine (Spec _)), ?_, ⟨MorphismProperty.Over.homMk
    (q ≫ Spec.map (CommRingCat.ofHom ρ.toRingHom)) ?_⟩⟩
  · obtain ⟨p⟩ : Nonempty
        ↥(pullback (C := Scheme.{u}) (Spec.map (CommRingCat.ofHom (algebraMap A K))) ι) := by
      obtain ⟨z⟩ : Nonempty (Spec (.of (K ⊗[A] P.Ring))) := inferInstance
      exact ⟨(pullbackSpecIso A K P.Ring).inv z⟩
    let a : pullback (Spec.map (CommRingCat.ofHom (algebraMap A K))) ι ⟶ Spec K :=
      pullback.fst _ _
    let b : pullback (Spec.map (CommRingCat.ofHom (algebraMap A K))) ι ⟶ W.left :=
      pullback.snd _ _
    have key : b ≫ W.hom = a ≫ X.fromSpecFunctionField := by
      rw [hη]
      have hpc : a ≫ Spec.map (CommRingCat.ofHom (algebraMap A K)) = b ≫ ι :=
        pullback.condition
      change b ≫ ι ≫ U.2.1.fromSpec = _
      rw [← Category.assoc b ι, ← hpc, Category.assoc]
      rfl
    obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := W.hom)
      (g := X.fromSpecFunctionField) (b p) (a p) (congrArg (fun φ ↦ φ p) key)
    exact ⟨w⟩
  · change (q ≫ Spec.map _) ≫ Spec.map _ = pullback.snd W.hom X.fromSpecFunctionField
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : ρ.toRingHom.comp (algebraMap K E) =
        (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[A] P.Ring) := by
      ext x
      exact ρ.commutes x
    rw [this]
    change (pullback.lift _ _ hcond ≫ (pullbackSpecIso A K P.Ring).hom) ≫ _ = _
    refine (Category.assoc _ _ _).trans ?_
    exact (congrArg (pullback.lift _ _ hcond ≫ ·) (pullbackSpecIso_hom_fst A K P.Ring)).trans
      (pullback.lift_fst _ _ _)

end AlgebraicGeometry.Scheme

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C}

lemma hom_app_inv_hom_app_apply {A B D : Sheaf J AddCommGrpCat.{u}} (f : A ⟶ B) [IsIso f]
    (g : B ⟶ D) (V : Cᵒᵖ) (s : B.obj.obj V) :
    (f ≫ g).hom.app V ((inv f).hom.app V s) = g.hom.app V s := by
  rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
    ← ObjectProperty.FullSubcategory.comp_hom, IsIso.inv_hom_id_assoc]

end CategoryTheory.Sheaf

namespace AlgebraicGeometry

open Etale

/-- For an open immersion `j`, the unit of `j^* ⊣ j_*` is an isomorphism at every pushforward
`j_* B`: the counit is an isomorphism since `j^*` is restriction. -/
lemma Etale.isIso_unit_app_lowerStar_of_isOpenImmersion {U Y : Scheme.{u}} (j : U ⟶ Y)
    [IsOpenImmersion j] (B : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).unit.app
      ((j)_*[AddCommGrpCat.{u + 1}].obj B)) := by
  set adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j
  have : IsIso (adj.counit.app B) := by
    rw [← Adjunction.leftAdjointUniq_hom_app_counit adj
      (openImmersionRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} j)]
    infer_instance
  have : IsIso (adj.unit.app ((j)_*[AddCommGrpCat.{u + 1}].obj B) ≫
      (j)_*[AddCommGrpCat.{u + 1}].map (adj.counit.app B)) := by
    rw [adj.right_triangle_components B]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ ((j)_*[AddCommGrpCat.{u + 1}].map (adj.counit.app B))

/-- If `η = π ≫ ι` for an open immersion `ι`, the unit of `ι^* ⊣ ι_*` is an isomorphism at every
pushforward `η_* Y`. -/
lemma Etale.isIso_unit_app_lowerStar_comp {T S R : Scheme.{u}} (π : T ⟶ S) (ι : S ⟶ R)
    [IsOpenImmersion ι] (η : T ⟶ R) (h : η = π ≫ ι)
    (Y : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} ι).unit.app
      ((η)_*[AddCommGrpCat.{u + 1}].obj Y)) := by
  set adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} ι
  let e := ((lowerStarComp AddCommGrpCat.{u + 1} π ι η h).app Y).symm
  have := isIso_unit_app_lowerStar_of_isOpenImmersion ι ((π)_*[AddCommGrpCat.{u + 1}].obj Y)
  have h' : adj.unit.app ((η)_*[AddCommGrpCat.{u + 1}].obj Y) =
      e.hom ≫ adj.unit.app _ ≫ (upperStar AddCommGrpCat.{u + 1} ι ⋙
        (ι)_*[AddCommGrpCat.{u + 1}]).map e.inv := by
    have := adj.unit.naturality e.hom
    simp only [Functor.id_map] at this
    rw [reassoc_of% this, Functor.comp_map, ← Functor.map_comp,
      ← Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  rw [h']
  infer_instance

namespace Scheme

variable {X : Scheme.{u}} [IsIntegral X]

/-- The base changes `W_K` of the affine étale `X`-schemes `W` along the generic point cover the
small étale site of `Spec K`. -/
lemma mem_smallEtaleTopology_of_forall_fromSpecFunctionField
    {V : (Spec X.functionField).Etale} (R : Sieve V)
    (hR : ∀ (W : X.Etale) [IsAffine W.left] (k : X.fromSpecFunctionField.Etale.obj W ⟶ V), R k) :
    R ∈ (Spec X.functionField).smallEtaleTopology V := by
  refine (mem_smallEtaleTopology_iff R).2 fun x ↦ ?_
  obtain ⟨E, _, _, _, ψ, e, rfl⟩ := exists_etaleSpec_field_mem V x
  obtain ⟨W, hW, ⟨w⟩, ⟨k⟩⟩ := X.exists_hom_etaleSpec_pullback E
  refine ⟨_, k ≫ ψ, hR W (k ≫ ψ), w, ?_⟩
  change ψ.left (k.left w) = ψ.left e
  congr 1
  exact Subsingleton.elim (α := Spec (.of E)) _ _

variable [QuasiSeparatedSpace X]

/-- Over a quasi-compact quasi-separated étale `X`-scheme `W`, every section of `η_* η^* η_* Y`
comes from a section of `η_* Y` under the unit. -/
lemma exists_unit_app_eq (Y : Sheaf (Spec X.functionField).smallEtaleTopology
      AddCommGrpCat.{u + 1}) (W : X.Etale) [CompactSpace W.left] [QuasiSeparatedSpace W.left]
    (x : ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj
      ((X.fromSpecFunctionField)^*[AddCommGrpCat.{u + 1}].obj
        ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj Y))).obj.obj (op W)) :
    ∃ y : ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj Y).obj.obj (op W),
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} X.fromSpecFunctionField).unit.app
        ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj Y)).hom.app (op W) y = x := by
  obtain ⟨U, s, hs⟩ := unitComparison_app_surjective_of_isLimit X.affineOpensDiagram
    X.affineOpensDiagramι X.functionFieldCone X.fromSpecFunctionField
    X.fromSpecFunctionField_eq_functionFieldCone_comp X.isLimitFunctionFieldCone _ W x
  have : IsIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (X.affineOpensDiagramι.app U)).unit.app
        ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj Y)) :=
    isIso_unit_app_lowerStar_comp (X.functionFieldCone.π.app U)
      (X.affineOpensDiagramι.app U) _ (X.fromSpecFunctionField_eq_functionFieldCone_comp U) Y
  refine ⟨(inv ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    (X.affineOpensDiagramι.app U)).unit.app
      ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj Y))).hom.app (op W) s, ?_⟩
  have key := unit_app_comp_unitComparison (X.functionFieldCone.π.app U)
    (X.affineOpensDiagramι.app U) X.fromSpecFunctionField
    (X.fromSpecFunctionField_eq_functionFieldCone_comp U)
    ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj Y)
  rw [← hs]
  erw [← key]
  exact Sheaf.hom_app_inv_hom_app_apply _ _ _ _

/-- The counit `η^* η_* Y ⟶ Y` is bijective over the base change `W_K` of a quasi-compact
quasi-separated étale `X`-scheme `W`. -/
lemma bijective_counit_app_fromSpecFunctionField
    (Y : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}) (W : X.Etale)
    [CompactSpace W.left] [QuasiSeparatedSpace W.left] :
    Function.Bijective (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      X.fromSpecFunctionField).counit.app Y).hom.app
        (op (X.fromSpecFunctionField.Etale.obj W))) := by
  set adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} X.fromSpecFunctionField
  have htri (y : ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj Y).obj.obj (op W)) :
      (adj.counit.app Y).hom.app (op (X.fromSpecFunctionField.Etale.obj W))
        ((adj.unit.app ((X.fromSpecFunctionField)_*[AddCommGrpCat.{u + 1}].obj Y)).hom.app
          (op W) y) = y :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (congr_arg (fun φ ↦ φ.hom) (adj.right_triangle_components Y)) (op W)) y
  refine ⟨fun a b hab ↦ ?_, fun z ↦ ⟨_, htri z⟩⟩
  obtain ⟨a', rfl⟩ := exists_unit_app_eq Y W a
  obtain ⟨b', rfl⟩ := exists_unit_app_eq Y W b
  rw [htri, htri] at hab
  rw [hab]

/-- **The counit at the generic point is an isomorphism.** Let `X` be a quasi-separated integral
scheme with generic point `η : Spec K ⟶ X`. For every abelian étale sheaf `Y` on `Spec K` the
counit `η^* η_* Y ⟶ Y` is an isomorphism: it is bijective over the base changes `W_K` of the
affine étale `X`-schemes `W`, which cover the small étale site of `Spec K`. -/
theorem isIso_counit_fromSpecFunctionField
    (Y : Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      X.fromSpecFunctionField).counit.app Y) := by
  set ε := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
    X.fromSpecFunctionField).counit.app Y
  have : PreservesLimitsOfSize.{u, u + 1} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesLimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  have : (Spec X.functionField).smallEtaleTopology.HasSheafCompose
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    inferInstance
  refine (Sheaf.isLocallyBijective_iff_isIso ε).1 ⟨?_, ?_⟩
  · refine ⟨fun {V} x y h ↦ ?_⟩
    refine mem_smallEtaleTopology_of_forall_fromSpecFunctionField _ fun W _ k ↦ ?_
    apply (bijective_counit_app_fromSpecFunctionField Y W).1
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h]
  · refine ⟨fun {V} s ↦ ?_⟩
    refine mem_smallEtaleTopology_of_forall_fromSpecFunctionField _ fun W _ k ↦ ?_
    exact (bijective_counit_app_fromSpecFunctionField Y W).2 _

end Scheme

end AlgebraicGeometry

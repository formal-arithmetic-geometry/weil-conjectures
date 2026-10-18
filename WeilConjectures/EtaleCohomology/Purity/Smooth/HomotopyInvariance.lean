/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpaceTrace
public import WeilConjectures.SixFunctors.Etale.Derived.TensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local

/-!
# Homotopy invariance of étale cohomology for affine space

For the projection `p : 𝔸^d_Y ⟶ Y` of relative affine space over a separated scheme of finite
type over a field, on which the exponent of `Λ` is invertible, the unit `Λ_Y ⟶ Rp_* Λ_{𝔸^d_Y}` is
an isomorphism (`AlgebraicGeometry.Etale.isIso_constantComplexUnit_affineSpace`).

The proof is by duality. The tensor–Hom exchange
`Rp_* RHom(M, Rp^! Λ_Y) ≅ RHom(Rp_! M, Λ_Y)`, at `M = Λ(d)[2d]`, together with affine-space
purity `Rp^! Λ_Y ≅ Λ(d)[2d]` and the affine-space trace `Rp_! Λ(d)[2d] ≅ Λ_Y`, gives some
isomorphism `Rp_* Λ ≅ Λ_Y` (`RHom(M, M) ≅ Λ` as `M` is invertible). The unit has a left
inverse, restriction along the zero section, and the endomorphisms of `Λ_Y` commute (they are
endomorphisms of the monoidal unit), so the unit is itself an isomorphism.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace CategoryTheory

/-- The endomorphisms of the monoidal unit commute (Eckmann–Hilton). -/
lemma MonoidalCategory.endUnit_comm {C : Type*} [Category C] [MonoidalCategory C]
    (f g : 𝟙_ C ⟶ 𝟙_ C) : f ≫ g = g ≫ f := by
  have h₁ : 𝟙_ C ◁ g = (λ_ (𝟙_ C)).hom ≫ g ≫ (λ_ (𝟙_ C)).inv := by
    rw [← leftUnitor_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  have h₂ : f ▷ 𝟙_ C = (λ_ (𝟙_ C)).hom ≫ f ≫ (λ_ (𝟙_ C)).inv := by
    rw [unitors_equal, unitors_inv_equal, ← rightUnitor_naturality_assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h := whisker_exchange f g
  rw [h₁, h₂] at h
  simp only [Category.assoc, Iso.inv_hom_id_assoc, cancel_epi] at h
  simpa using h.symm

/-- A morphism `u : A ⟶ B` with a left inverse is an isomorphism if `B ≅ A` and the
endomorphisms of `A` commute. -/
lemma isIso_of_comp_eq_id_of_iso {C : Type*} [Category C] {A B : C} (u : A ⟶ B) (r : B ⟶ A)
    (hur : u ≫ r = 𝟙 A) (ψ : B ≅ A) (hcomm : ∀ f g : A ⟶ A, f ≫ g = g ≫ f) : IsIso u := by
  have h₁ : (u ≫ ψ.hom) ≫ (ψ.inv ≫ r) = 𝟙 A := by simp [hur]
  have h₂ : (ψ.inv ≫ r) ≫ (u ≫ ψ.hom) = 𝟙 A := by rw [← hcomm, h₁]
  have : IsIso (u ≫ ψ.hom) := ⟨⟨_, h₁, h₂⟩⟩
  have : u = (u ≫ ψ.hom) ≫ ψ.inv := by simp
  rw [this]
  infer_instance

end CategoryTheory

namespace AlgebraicGeometry.Etale

section Generic

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

attribute [local instance] derivedBraidedCategory

/-- `RHom(Λ, K) ≅ K`. -/
lemma nonempty_iso_derivedHom_unit (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Nonempty ((RHom(X)[A].obj (op (𝟙_ _))).obj K ≅ K) :=
  ⟨MonoidalClosed.ihomObjIsoTensor (𝟙_ _) (𝟙_ _) K ≪≫ λ_ K⟩

/-- `RHom(T, T) ≅ Λ` for an invertible `T`. -/
lemma nonempty_iso_derivedHom_self_of_isInvertible
    {T : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hT : IsInvertible T) :
    Nonempty ((RHom(X)[A].obj (op T)).obj T ≅ 𝟙_ _) := by
  have := MonoidalClosed.isIso_ihomUnitToIhomTensor (𝟙_ _) hT
  obtain ⟨e⟩ := nonempty_iso_derivedHom_unit (A := A) (X := X) (𝟙_ _)
  exact ⟨(MonoidalClosed.internalHom.flip.obj T).mapIso (λ_ T).op ≪≫
    (asIso (MonoidalClosed.ihomUnitToIhomTensor (𝟙_ _) T)).symm ≪≫ e⟩

/-- The endomorphisms of `Λ_X` commute. -/
lemma endUnit_comm_derivedCategory
    (f g : 𝟙_ (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) ⟶ 𝟙_ _) :
    f ≫ g = g ≫ f :=
  MonoidalCategory.endUnit_comm f g

/-- `RHom(Q, Z ⊗ Q) ≅ Z` for an invertible `Q`: `Q ⊗ -` is an equivalence, so the unit of
`Q ⊗ - ⊣ RHom(Q, -)` is an isomorphism. -/
lemma nonempty_iso_derivedHom_tensor_of_isInvertible
    {Q : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (hQ : IsInvertible Q)
    (Z : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Nonempty ((RHom(X)[A].obj (op Q)).obj (((derivedTensor A X).obj Z).obj Q) ≅ Z) := by
  have := hQ.isEquivalence_tensorLeft
  have : IsIso (ihom.adjunction Q).unit := inferInstance
  exact ⟨(ihom Q).mapIso (β_ Z Q) ≪≫ (asIso ((ihom.adjunction Q).unit.app Z)).symm⟩

/-- The endomorphisms of an invertible object commute: they are those of the unit, transported
by the equivalence `K ⊗ -`. -/
lemma comm_of_isInvertible {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hK : IsInvertible K) (f g : K ⟶ K) : f ≫ g = g ≫ f := by
  have := hK.isEquivalence_tensorLeft
  obtain ⟨a, ha⟩ := (tensorLeft K).map_surjective ((ρ_ K).hom ≫ f ≫ (ρ_ K).inv)
  obtain ⟨b, hb⟩ := (tensorLeft K).map_surjective ((ρ_ K).hom ≫ g ≫ (ρ_ K).inv)
  have hf : f = (ρ_ K).inv ≫ (tensorLeft K).map a ≫ (ρ_ K).hom := by rw [ha]; simp
  have hg : g = (ρ_ K).inv ≫ (tensorLeft K).map b ≫ (ρ_ K).hom := by rw [hb]; simp
  rw [hf, hg]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, MonoidalCategory.endUnit_comm a b]

end Generic

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ]

/-- `RHom(Λ(m)[2m], Λ(m)[2m]) ≅ Λ`: the twisting objects are invertible. -/
lemma nonempty_iso_derivedHom_tateObjectShift (X : Scheme.{u}) [HasInvertibleExponent Λ X]
    (d : ℕ) :
    Nonempty ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op ((tateObject Λ X d)⟦(2 * d : ℤ)⟧))).obj
      ((tateObject Λ X d)⟦(2 * d : ℤ)⟧) ≅ constantComplex Λ X) :=
  nonempty_iso_derivedHom_self_of_isInvertible (isInvertible_tateObject_shift Λ X d)

variable [Finite Λ] [HasTateTwist.IsNormalized Λ]

/-- For relative affine space `p : 𝔸^d_Y ⟶ Y` over a separated scheme of finite type over a
field, `Rp_* Λ ≅ Λ_Y`: by the tensor–Hom exchange,
`Rp_* RHom(Λ(d)[2d], Rp^! Λ) ≅ RHom(Rp_! Λ(d)[2d], Λ)`, where `Rp^! Λ ≅ Λ(d)[2d]` (purity) and
`Rp_! Λ(d)[2d] ≅ Λ` (the affine-space trace). -/
theorem nonempty_iso_rightDerivedLowerStar_constantComplex_affineSpace
    {k : Type u} [Field k] (d : ℕ)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ Y] :
    Nonempty ((R((𝔸(ULift.{u} (Fin d); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
      (constantComplex Λ 𝔸(ULift.{u} (Fin d); Y)) ≅ constantComplex Λ Y) := by
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin d); Y) := .of_hom (𝔸(ULift.{u} (Fin d); Y) ↘ Y)
  obtain ⟨th⟩ := nonempty_iso_derivedHom_rightDerivedLowerShriek Λ (𝔸(ULift.{u} (Fin d); Y) ↘ Y)
    ((twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj (constantComplex Λ 𝔸(ULift.{u} (Fin d); Y)))
    (constantComplex Λ Y)
  obtain ⟨ω⟩ := nonempty_iso_dualizingComplex_affineSpace Λ d Y aY
  obtain ⟨tr⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace_fin Λ d Y
  obtain ⟨hP⟩ := nonempty_iso_derivedHom_tateObjectShift Λ 𝔸(ULift.{u} (Fin d); Y) d
  obtain ⟨hΛ⟩ := nonempty_iso_derivedHom_unit (A := ModuleCat.{u + 1} Λ)
    (𝟙_ _ : _root_.DerivedCategory
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
  let eM : (twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj (constantComplex Λ 𝔸(ULift.{u} (Fin d); Y))
      ≅ (tateObject Λ 𝔸(ULift.{u} (Fin d); Y) d)⟦(2 * d : ℤ)⟧ :=
    (shiftFunctor _ (2 * (d : ℤ))).mapIso (derivedTensorLeftUnitor _ _ _)
  let e₁ := (RHom(_)[ModuleCat.{u + 1} Λ].obj (op ((twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj
      (constantComplex Λ 𝔸(ULift.{u} (Fin d); Y))))).mapIso (ω ≪≫ eM) ≪≫
    (RHom(_)[ModuleCat.{u + 1} Λ].mapIso eM.symm.op).app _ ≪≫ hP
  exact ⟨(R((𝔸(ULift.{u} (Fin d); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).mapIso e₁.symm ≪≫ th ≪≫
    (RHom(Y)[ModuleCat.{u + 1} Λ].mapIso tr.symm.op).app _ ≪≫ hΛ⟩

/-- **Homotopy invariance** for relative affine space: over a separated scheme `Y` of finite
type over a field, the unit `Λ_Y ⟶ Rp_* Λ_{𝔸^d_Y}` is an isomorphism. It has a left inverse,
restriction along the zero section, and `Rp_* Λ ≅ Λ_Y`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_constantComplex_affineSpace`);
the endomorphisms of `Λ_Y` commute, so a morphism `Λ_Y ⟶ Rp_* Λ` with a left inverse is an
isomorphism. -/
theorem isIso_constantComplexUnit_affineSpace
    {k : Type u} [Field k] (d : ℕ)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ Y] :
    IsIso (constantComplexUnit Λ (𝔸(ULift.{u} (Fin d); Y) ↘ Y)) := by
  obtain ⟨ψ⟩ := nonempty_iso_rightDerivedLowerStar_constantComplex_affineSpace Λ d Y aY
  let z : Y ⟶ 𝔸(ULift.{u} (Fin d); Y) := AffineSpace.homOfVector (𝟙 Y) 0
  have hz : z ≫ 𝔸(ULift.{u} (Fin d); Y) ↘ Y = 𝟙 Y := AffineSpace.homOfVector_over _ _
  have := isIso_constantComplexUnit_comp_map_unit Λ _ z hz
  let w := (R((𝔸(ULift.{u} (Fin d); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).map
    ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) z).unit.app
      (constantComplex Λ _))
  refine isIso_of_comp_eq_id_of_iso _ (w ≫ inv (constantComplexUnit Λ _ ≫ w)) ?_ ψ
    endUnit_comm_derivedCategory
  rw [← Category.assoc, IsIso.hom_inv_id]

omit [Finite Λ] [HasTateTwist.IsNormalized Λ] in
/-- The shifted Tate twist `Λ_X(m)[2m]` is invertible, for any `m : ℤ`. -/
theorem isInvertible_tateObject_shift' (X : Scheme.{u}) [HasInvertibleExponent Λ X] (m : ℤ) :
    IsInvertible ((tateObject Λ X m)⟦2 * m⟧) :=
  DerivedCategory.isInvertible_shift
    ((isInvertible_iff_exists_derivedTensor _).2 (isInvertible_tateObject Λ X m)) _

omit [Finite Λ] [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ] in
/-- For a section `i` of `q`, the unit `K ⟶ Rq_* Lq^* K` followed by `Rq_*` of the unit
`Lq^* K ⟶ Ri_* i^* Lq^* K` is an isomorphism: it is the unit of the composite adjunction, whose
left adjoint `L(i ≫ q)^* = L(𝟙)^*` is an equivalence. -/
theorem isIso_unit_comp_map_unit_of_section {X S : Scheme.{u}} (q : X ⟶ S) (i : S ⟶ X)
    (hi : i ≫ q = 𝟙 S) (K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app K ≫
      (R((q)_*[ModuleCat.{u + 1} Λ])).map
        ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i).unit.app
          ((L((q)^*[ModuleCat.{u + 1} Λ])).obj K))) := by
  let adj := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).comp
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) i)
  obtain ⟨eid⟩ := nonempty_leftDerivedUpperStar_id_iso Λ S (i ≫ q) hi
  let e : L((q)^*[ModuleCat.{u + 1} Λ]) ⋙ D((i)^*[ModuleCat.{u + 1} Λ]) ≅ 𝟭 _ :=
    Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ i).symm ≪≫
      (leftDerivedUpperStarComp _ i q).symm ≪≫ eid
  have : (L((q)^*[ModuleCat.{u + 1} Λ]) ⋙ D((i)^*[ModuleCat.{u + 1} Λ])).Full :=
    Functor.Full.of_iso e.symm
  have : (L((q)^*[ModuleCat.{u + 1} Λ]) ⋙ D((i)^*[ModuleCat.{u + 1} Λ])).Faithful :=
    Functor.Faithful.of_iso e.symm
  have hu : IsIso (adj.unit.app K) := inferInstance
  simpa only [adj, Adjunction.comp_unit_app] using hu

/-- For relative affine space `p : 𝔸^d_Y ⟶ Y` over a separated scheme of finite type over a field
and `K ∈ D^b_{ctf}(Y)`, `Rp_* Lp^* K ≅ K`: by the tensor–Hom exchange at `M = Λ(d)[2d]`, with
`Rp^! K ≅ Lp^* K ⊗ Λ(d)[2d]` (purity) and `Rp_! Λ(d)[2d] ≅ Λ` (the trace). -/
theorem nonempty_iso_rightDerivedLowerStar_leftDerivedUpperStar_affineSpace
    {k : Type u} [Field k] (d : ℕ)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ Y]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ Y K) :
    Nonempty ((R((𝔸(ULift.{u} (Fin d); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).obj
      ((L(((𝔸(ULift.{u} (Fin d); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj K) ≅ K) := by
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin d); Y) := .of_hom (𝔸(ULift.{u} (Fin d); Y) ↘ Y)
  obtain ⟨th⟩ := nonempty_iso_derivedHom_rightDerivedLowerShriek Λ (𝔸(ULift.{u} (Fin d); Y) ↘ Y)
    ((twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj (constantComplex Λ 𝔸(ULift.{u} (Fin d); Y))) K
  obtain ⟨pur⟩ := nonempty_iso_rightDerivedUpperShriek_affineSpace Λ d Y aY K hK
  obtain ⟨tr⟩ := nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace_fin Λ d Y
  obtain ⟨hQ⟩ := nonempty_iso_derivedHom_tensor_of_isInvertible
    (isInvertible_tateObject_shift Λ 𝔸(ULift.{u} (Fin d); Y) d)
    ((L(((𝔸(ULift.{u} (Fin d); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj K)
  obtain ⟨hΛ⟩ := nonempty_iso_derivedHom_unit (A := ModuleCat.{u + 1} Λ) K
  let eM : (twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj (constantComplex Λ 𝔸(ULift.{u} (Fin d); Y))
      ≅ (tateObject Λ 𝔸(ULift.{u} (Fin d); Y) d)⟦(2 * d : ℤ)⟧ :=
    (shiftFunctor _ (2 * (d : ℤ))).mapIso (derivedTensorLeftUnitor _ _ _)
  let eT : (twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj
      ((L(((𝔸(ULift.{u} (Fin d); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      ((derivedTensor (ModuleCat.{u + 1} Λ) _).obj
        ((L(((𝔸(ULift.{u} (Fin d); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj K)).obj
        ((tateObject Λ 𝔸(ULift.{u} (Fin d); Y) d)⟦(2 * d : ℤ)⟧) :=
    ((((derivedTensor (ModuleCat.{u + 1} Λ) _).obj
      ((L(((𝔸(ULift.{u} (Fin d); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj K)).commShiftIso
        (2 * (d : ℤ))).app _).symm
  let e₁ := (RHom(_)[ModuleCat.{u + 1} Λ].obj (op ((twistShift Λ 𝔸(ULift.{u} (Fin d); Y) d).obj
      (constantComplex Λ 𝔸(ULift.{u} (Fin d); Y))))).mapIso (pur ≪≫ eT) ≪≫
    (RHom(_)[ModuleCat.{u + 1} Λ].mapIso eM.symm.op).app _ ≪≫ hQ
  exact ⟨(R((𝔸(ULift.{u} (Fin d); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).mapIso e₁.symm ≪≫ th ≪≫
    (RHom(Y)[ModuleCat.{u + 1} Λ].mapIso tr.symm.op).app _ ≪≫ hΛ⟩

/-- **Homotopy invariance with twisted coefficients** for relative affine space: the unit
`Λ_Y(m)[2m] ⟶ Rp_* Lp^* Λ_Y(m)[2m]` is an isomorphism. As for `m = 0`
(`AlgebraicGeometry.Etale.isIso_constantComplexUnit_affineSpace`), it has a left inverse given by
the zero section, its target is isomorphic to its source, and the endomorphisms of the
invertible object `Λ_Y(m)[2m]` commute. -/
theorem isIso_unit_tateObjectShift_affineSpace
    {k : Type u} [Field k] (d : ℕ)
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    [HasInvertibleExponent Λ Y] (m : ℤ) :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin d); Y) ↘ Y)).unit.app ((tateObject Λ Y m)⟦2 * m⟧)) := by
  obtain ⟨ψ⟩ := nonempty_iso_rightDerivedLowerStar_leftDerivedUpperStar_affineSpace Λ d Y aY
    ((tateObject Λ Y m)⟦2 * m⟧) ((boundedConstructibleFiniteTor_tateObject Λ Y m).shift _)
  let z : Y ⟶ 𝔸(ULift.{u} (Fin d); Y) := AffineSpace.homOfVector (𝟙 Y) 0
  have hz : z ≫ 𝔸(ULift.{u} (Fin d); Y) ↘ Y = 𝟙 Y := AffineSpace.homOfVector_over _ _
  have := isIso_unit_comp_map_unit_of_section Λ _ z hz ((tateObject Λ Y m)⟦2 * m⟧)
  let w := (R((𝔸(ULift.{u} (Fin d); Y) ↘ Y)_*[ModuleCat.{u + 1} Λ])).map
    ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) z).unit.app
      ((L(((𝔸(ULift.{u} (Fin d); Y) ↘ Y))^*[ModuleCat.{u + 1} Λ])).obj
        ((tateObject Λ Y m)⟦2 * m⟧)))
  refine isIso_of_comp_eq_id_of_iso _ (w ≫ inv ((derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} Λ) (𝔸(ULift.{u} (Fin d); Y) ↘ Y)).unit.app ((tateObject Λ Y m)⟦2 * m⟧) ≫
      w)) ?_ ψ
    (comm_of_isInvertible (isInvertible_tateObject_shift' Λ Y m))
  rw [← Category.assoc, IsIso.hom_inv_id]

section OpenBaseChange

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}
  [IsOpenImmersion j] [IsOpenImmersion j']

omit [Finite Λ] [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ] in
/-- **The unit of `Lg^* ⊣ Rg_*` restricts to open subsets**: for a cartesian square
`g' ≫ j = j' ≫ g''` with `j`, `j'` open immersions, if the unit of `Lg'^* ⊣ Rg'_*` at `j^* K`
is an isomorphism, then so is `j^*` of the unit of `Lg''^* ⊣ Rg''_*` at `K`. The two units are
related through the conjugate `j^* Rg''_* ≅ Rg'_* j'^*` of the base change isomorphism
`Lg'^* j'_! ≅ j_! Lg''^*` of the extension by zero (`CategoryTheory.unit_conjugateEquiv`). -/
theorem isIso_upperStar_map_unit_of_isPullback (hsq : IsPullback g' j' j g'')
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g').unit.app
      ((D((j)^*[ModuleCat.{u + 1} Λ])).obj K))) :
    IsIso ((D((j)^*[ModuleCat.{u + 1} Λ])).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g'').unit.app K)) := by
  let aj := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j
  let aj' := derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j'
  let ag := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g''
  let ag' := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g'
  let adj₁ := aj.comp ag
  let adj₂ := ag'.comp aj'
  let α := (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) hsq).hom
  let c := conjugateEquiv adj₁ adj₂ α
  have hc : IsIso c := inferInstance
  let X := (D((j)^*[ModuleCat.{u + 1} Λ])).obj K
  let ε := aj.counit.app K
  -- `j^* ε` is invertible
  have hε : IsIso ((D((j)^*[ModuleCat.{u + 1} Λ])).map ε) := by
    have : IsIso (aj.unit.app X ≫ (D((j)^*[ModuleCat.{u + 1} Λ])).map ε) := by
      rw [aj.right_triangle_components K]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_left (aj.unit.app X) _
  -- the key identity
  have key : (D((j)^*[ModuleCat.{u + 1} Λ])).map (ag.unit.app K) ≫
      c.app ((L((g'')^*[ModuleCat.{u + 1} Λ])).obj K) =
      ag'.unit.app X ≫ (R((g')_*[ModuleCat.{u + 1} Λ])).map ((aj'.unit.app _) ≫
        (D((j')^*[ModuleCat.{u + 1} Λ])).map (α.app X) ≫
        (D((j')^*[ModuleCat.{u + 1} Λ])).map ((L((g'')^*[ModuleCat.{u + 1} Λ])).map ε)) := by
    have hu : adj₁.unit.app X ≫ c.app _ = adj₂.unit.app X ≫ _ := unit_conjugateEquiv adj₁ adj₂ α X
    have hn := c.naturality ((L((g'')^*[ModuleCat.{u + 1} Λ])).map ε)
    have hn' : ag.unit.app ((D((j)_!open[ModuleCat.{u + 1} Λ])).obj X) ≫
        (R((g'')_*[ModuleCat.{u + 1} Λ])).map ((L((g'')^*[ModuleCat.{u + 1} Λ])).map ε) =
          ε ≫ ag.unit.app K :=
      (ag.unit.naturality ε).symm
    have hη : (D((j)^*[ModuleCat.{u + 1} Λ])).map (ag.unit.app K) =
        adj₁.unit.app X ≫ (D((j)^*[ModuleCat.{u + 1} Λ])).map ((R((g'')_*[ModuleCat.{u + 1} Λ])).map
          ((L((g'')^*[ModuleCat.{u + 1} Λ])).map ε)) := by
      simp only [adj₁, Adjunction.comp_unit_app, Category.assoc]
      rw [← Functor.map_comp, hn', Functor.map_comp, ← Category.assoc,
        aj.right_triangle_components K]
      exact (Category.id_comp _).symm
    rw [hη, Category.assoc]
    erw [hn]
    rw [← Category.assoc]
    erw [hu]
    simp only [adj₂, Adjunction.comp_unit_app, Category.assoc, Functor.comp_map,
      Functor.map_comp]
  -- `j'^* Lg''^* ε` is invertible
  have hε' : IsIso ((D((j')^*[ModuleCat.{u + 1} Λ])).map
      ((L((g'')^*[ModuleCat.{u + 1} Λ])).map ε)) := by
    let e : L((g'')^*[ModuleCat.{u + 1} Λ]) ⋙ D((j')^*[ModuleCat.{u + 1} Λ]) ≅
        D((j)^*[ModuleCat.{u + 1} Λ]) ⋙ L((g')^*[ModuleCat.{u + 1} Λ]) :=
      Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j').symm ≪≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) j' g'' _ rfl).symm ≪≫
        leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) g' j (j' ≫ g'') hsq.w.symm ≪≫
        Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) j) _
    have : IsIso ((D((j)^*[ModuleCat.{u + 1} Λ]) ⋙ L((g')^*[ModuleCat.{u + 1} Λ])).map ε) :=
      inferInstanceAs (IsIso ((L((g')^*[ModuleCat.{u + 1} Λ])).map
        ((D((j)^*[ModuleCat.{u + 1} Λ])).map ε)))
    exact (NatIso.isIso_map_iff e ε).2 this
  have : IsIso ((D((j)^*[ModuleCat.{u + 1} Λ])).map (ag.unit.app K) ≫
      c.app ((L((g'')^*[ModuleCat.{u + 1} Λ])).obj K)) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (c.app _)

end OpenBaseChange

end AlgebraicGeometry.Etale

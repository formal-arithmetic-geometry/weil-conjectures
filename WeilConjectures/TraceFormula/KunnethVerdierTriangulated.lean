module

public import WeilConjectures.TraceFormula.KunnethVerdier
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraidingShift
public import WeilConjectures.CategoryTheory.Monoidal.SubcategoryShiftNatTrans
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.LeftUnitorShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
public import WeilConjectures.CategoryTheory.Monoidal.DerivedSymmetric

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

instance (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    TopologicalSpace.NoetherianSpace X.left := by
  have : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := {}
  infer_instance


noncomputable instance (f : X ⟶ Y) : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).IsTriangulated := by
  delta boundedConstructibleUpperStar
  infer_instance


variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  [IsFinitenessCoefficient ℓ Λ]

instance (f : X ⟶ Y) : (boundedConstructibleLowerStar Λ ℓ f).IsTriangulated := by
  delta boundedConstructibleLowerStar
  infer_instance

instance {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [IsSeparated U.hom] (j : U ⟶ X) [IsOpenImmersion j.left] :
    (boundedConstructibleOpenImmersionLowerShriek Λ ℓ j).IsTriangulated := by
  delta boundedConstructibleOpenImmersionLowerShriek
  infer_instance

instance {f : X ⟶ Y} (c : Compactification f.left) :
    (boundedConstructibleLowerShriekOfCompactification Λ ℓ c).IsTriangulated := by
  delta boundedConstructibleLowerShriekOfCompactification
  infer_instance

instance (f : X ⟶ Y) : (boundedConstructibleLowerShriek Λ ℓ f).IsTriangulated := by
  delta boundedConstructibleLowerShriek
  infer_instance

instance (f : X ⟶ Y)
    [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField f).overG).IsLeftAdjoint] :
    (boundedConstructibleUpperShriek Λ ℓ f).IsTriangulated :=
  (boundedConstructibleUpperShriekAdjunction Λ ℓ f).isTriangulated_rightAdjoint


section Tensor

variable [IsEllAdicFinitenessCoefficient ℓ Λ]

instance (K : Dᵇc(X.left)⟦Λ⟧) : ((curriedTensor (Dᵇc(X.left)⟦Λ⟧)).flip.obj K).IsTriangulated := by
  have := Functor.CommShift.ofIso_compatibility (ObjectProperty.tensorRightIsoLift _ K) ℤ
  exact Functor.isTriangulated_of_iso (ObjectProperty.tensorRightIsoLift _ K)

instance (K : Dᵇc(X.left)⟦Λ⟧) : ((curriedTensor (Dᵇc(X.left)⟦Λ⟧)).obj K).IsTriangulated := by
  have := Functor.CommShift.ofIso_compatibility (ObjectProperty.tensorLeftIsoLift _ K) ℤ
  exact Functor.isTriangulated_of_iso (ObjectProperty.tensorLeftIsoLift _ K)

noncomputable instance (K : Dᵇc(X.left)⟦Λ⟧) : (tensorLeft K).CommShift ℤ :=
  inferInstanceAs (((curriedTensor (Dᵇc(X.left)⟦Λ⟧)).obj K).CommShift ℤ)

instance (K : Dᵇc(X.left)⟦Λ⟧) : (tensorLeft K).IsTriangulated :=
  inferInstanceAs (((curriedTensor (Dᵇc(X.left)⟦Λ⟧)).obj K).IsTriangulated)

noncomputable instance (K : Dᵇc(X.left)⟦Λ⟧) : (ihom K).CommShift ℤ :=
  (ihom.adjunction K).rightAdjointCommShift ℤ

instance (K : Dᵇc(X.left)⟦Λ⟧) : (ihom.adjunction K).CommShift ℤ :=
  (ihom.adjunction K).commShift_of_leftAdjoint ℤ

instance (K : Dᵇc(X.left)⟦Λ⟧) : (ihom K).IsTriangulated :=
  (ihom.adjunction K).isTriangulated_rightAdjoint

end Tensor



section NatTrans

variable [IsEllAdicFinitenessCoefficient ℓ Λ]

/-- The commutations of the derived tensor products `K ⊗ᴸ -` with the shifts, as a family
(instance search for the family itself times out). -/
private noncomputable abbrev commShiftTensorLeftFamily (X : Scheme.{u}) :
    ∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)), ((curriedTensor (DerivedCategory (Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))).obj K).CommShift ℤ :=
  fun K ↦ DerivedCategory.commShiftTensorLeft _ K

/-- The commutations of the derived tensor products `- ⊗ᴸ K` with the shifts, as a family. -/
private noncomputable abbrev commShiftTensorRightFamily (X : Scheme.{u}) :
    ∀ K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)), ((curriedTensor (DerivedCategory (Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))).flip.obj
          K).CommShift ℤ :=
  fun K ↦ DerivedCategory.commShiftTensorRight _ K

instance commShift_boundedConstructible_curriedTensor_map {K K' : Dᵇc(X.left)⟦Λ⟧}
    (g : K ⟶ K') : NatTrans.CommShift ((curriedTensor (Dᵇc(X.left)⟦Λ⟧)).map g) ℤ := by
  letI := commShiftTensorLeftFamily Λ X.left
  letI := commShiftTensorRightFamily Λ X.left
  have := commShift_curriedTensor_map Λ g.hom
  exact ObjectProperty.commShift_curriedTensor_map _ g

instance commShift_boundedConstructible_curriedTensor_flip_map {K K' : Dᵇc(X.left)⟦Λ⟧}
    (g : K ⟶ K') : NatTrans.CommShift ((curriedTensor (Dᵇc(X.left)⟦Λ⟧)).flip.map g) ℤ := by
  letI := commShiftTensorLeftFamily Λ X.left
  letI := commShiftTensorRightFamily Λ X.left
  have := Functor.CommShift₂.commShift_flip_map
    (G := curriedTensor (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))) (h := .int) g.hom
  exact ObjectProperty.commShift_curriedTensor_flip_map _ g

instance commShift_boundedConstructible_associatorNatTrans₁ (K L : Dᵇc(X.left)⟦Λ⟧) :
    NatTrans.CommShift (associatorNatTrans₁ (Dᵇc(X.left)⟦Λ⟧) K L) ℤ := by
  letI := commShiftTensorLeftFamily Λ X.left
  letI := commShiftTensorRightFamily Λ X.left
  have : NatTrans.CommShift (associatorNatTrans₁ (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left))) K.obj L.obj)
      ℤ := inferInstance
  exact ObjectProperty.commShift_associatorNatTrans₁ _ K L

instance commShift_boundedConstructible_associatorNatTrans₂ (K L : Dᵇc(X.left)⟦Λ⟧) :
    NatTrans.CommShift (associatorNatTrans₂ (Dᵇc(X.left)⟦Λ⟧) K L) ℤ := by
  letI := commShiftTensorLeftFamily Λ X.left
  letI := commShiftTensorRightFamily Λ X.left
  have : NatTrans.CommShift (associatorNatTrans₂ (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left))) K.obj L.obj)
      ℤ := inferInstance
  exact ObjectProperty.commShift_associatorNatTrans₂ _ K L

instance commShift_boundedConstructible_leftUnitorNatTrans :
    NatTrans.CommShift (leftUnitorNatTrans (Dᵇc(X.left)⟦Λ⟧)) ℤ := by
  letI := commShiftTensorLeftFamily Λ X.left
  have : NatTrans.CommShift (leftUnitorNatTrans (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left)))) ℤ :=
    ⟨fun n ↦ by
      ext K
      simpa using DerivedCategory.leftUnitor_commShift_app _ K n⟩
  exact ObjectProperty.commShift_leftUnitorNatTrans _

section Braiding

attribute [local instance] boundedConstructibleBraiding

/-- The Koszul braiding of `Dᵇc(X)⟦Λ⟧` is symmetric. -/
lemma boundedConstructible_braiding_hom_braiding_hom (K M : Dᵇc(X.left)⟦Λ⟧) :
    (β_ K M).hom ≫ (β_ M K).hom = 𝟙 _ := by
  refine ObjectProperty.hom_ext _ ?_
  exact DerivedCategory.braiding_hom_braiding_hom _
    (fun A B ↦ SymmetricCategory.symmetry A B) K.obj M.obj

/-- The braiding `K ⊗ M ⟶ M ⊗ K`, natural in its second variable `M`. -/
@[simps]
noncomputable def boundedConstructibleBraidingNatTrans₂ (K : Dᵇc(X.left)⟦Λ⟧) :
    (curriedTensor (Dᵇc(X.left)⟦Λ⟧)).obj K ⟶ (curriedTensor (Dᵇc(X.left)⟦Λ⟧)).flip.obj K where
  app M := (β_ K M).hom
  naturality _ _ f := BraidedCategory.braiding_naturality_right K f

/-- The braiding `M ⊗ K ⟶ K ⊗ M`, natural in its first variable `M`. -/
@[simps]
noncomputable def boundedConstructibleBraidingNatTrans₁ (K : Dᵇc(X.left)⟦Λ⟧) :
    (curriedTensor (Dᵇc(X.left)⟦Λ⟧)).flip.obj K ⟶ (curriedTensor (Dᵇc(X.left)⟦Λ⟧)).obj K where
  app M := (β_ M K).hom
  naturality _ _ f := BraidedCategory.braiding_naturality_left f K

instance commShift_boundedConstructibleBraidingNatTrans₂ (K : Dᵇc(X.left)⟦Λ⟧) :
    NatTrans.CommShift (boundedConstructibleBraidingNatTrans₂ ℓ Λ K) ℤ :=
  ⟨fun a ↦ by
    refine NatTrans.ext (funext fun M ↦ ?_)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      boundedConstructibleBraidingNatTrans₂_app]
    exact (boundedConstructible_braiding_hom_commShiftIso_hom_app Λ a K M).symm⟩

instance commShift_boundedConstructibleBraidingNatTrans₁ (K : Dᵇc(X.left)⟦Λ⟧) :
    NatTrans.CommShift (boundedConstructibleBraidingNatTrans₁ ℓ Λ K) ℤ := by
  have : IsIso (boundedConstructibleBraidingNatTrans₂ ℓ Λ K) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    rw [boundedConstructibleBraidingNatTrans₂_app]
    infer_instance
  have h : boundedConstructibleBraidingNatTrans₁ ℓ Λ K =
      inv (boundedConstructibleBraidingNatTrans₂ ℓ Λ K) := by
    rw [← cancel_epi (boundedConstructibleBraidingNatTrans₂ ℓ Λ K), IsIso.hom_inv_id]
    refine NatTrans.ext (funext fun M ↦ ?_)
    exact boundedConstructible_braiding_hom_braiding_hom ℓ Λ K M
  rw [h]
  exact NatTrans.CommShift.of_isIso _ ℤ

end Braiding

end NatTrans

end AlgebraicGeometry.ProEtale.CondensedRing

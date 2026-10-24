module

public import WeilConjectures.TraceFormula.KunnethVerdier
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekShift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraidingShift

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

end AlgebraicGeometry.ProEtale.CondensedRing

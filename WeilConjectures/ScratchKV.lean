module

public import WeilConjectures.TraceFormula.KunnethVerdierTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
variable {X : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  [IsEllAdicFinitenessCoefficient ℓ Λ]

noncomputable example (K : Dᵇc(X.left)⟦Λ⟧) : ((curriedTensor (Dᵇc(X.left)⟦Λ⟧)).obj K).CommShift ℤ := inferInstance

noncomputable example (K : (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left)))) : ((curriedTensor (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left)))).obj K).CommShift ℤ := inferInstance

set_option maxHeartbeats 400000 in
example {K K' : Dᵇc(X.left)⟦Λ⟧} (g : K ⟶ K') : Prop :=
    NatTrans.CommShift ((curriedTensor (Dᵇc(X.left)⟦Λ⟧)).map g) ℤ

noncomputable def hL : ∀ K : (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left))), ((curriedTensor (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left)))).obj K).CommShift ℤ := fun K ↦ inferInstance

example {K K' : Dᵇc(X.left)⟦Λ⟧} (g : K ⟶ K') :
    NatTrans.CommShift ((curriedTensor (Dᵇc(X.left)⟦Λ⟧)).map g) ℤ := by
  letI : ∀ K : (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left))), ((curriedTensor (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left)))).obj K).CommShift ℤ := fun K ↦ DerivedCategory.commShiftTensorLeft _ K
  letI : ∀ K : (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left))), ((curriedTensor (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left)))).flip.obj K).CommShift ℤ := fun K ↦ DerivedCategory.commShiftTensorRight _ K
  have : NatTrans.CommShift ((curriedTensor (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1}) (condensedRingObj Λ X.left)))).map g.hom) ℤ := commShift_curriedTensor_map Λ g.hom
  exact ObjectProperty.commShift_curriedTensor_map _ g

end AlgebraicGeometry.ProEtale.CondensedRing

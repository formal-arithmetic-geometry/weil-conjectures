module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactSupportTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.Coproducts
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

@[expose] public section

universe u' u

open scoped CategoryTheory.Obj
open CategoryTheory Abelian Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

example : HasCoproducts.{u + 1} (DerivedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u+1})) :=
  fun _ => inferInstance
example (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :
  HasCoproducts.{u + 1} (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X))) :=
  fun _ => inferInstance
example (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :
  (rightDerivedLowerShriekOfCompactification Λ c).IsTriangulated :=
  inferInstance
example (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ] :
  (rightDerivedLowerShriekOfCompactification Λ c).CommShift ℤ :=
  inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing

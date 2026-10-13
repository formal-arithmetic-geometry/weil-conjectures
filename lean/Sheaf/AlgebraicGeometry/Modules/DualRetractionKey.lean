module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
import Sheaf.AlgebraicGeometry.InternalHomRestrictScheme

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- Categorical cancellation for the local transpose retraction.
Source: Stacks Project, Tag 0EKP, transpose compatibility.
(blueprint: new-sbc-dual-retraction-key)

The proof expands naturality of the internal-Hom restriction isomorphisms and
uses contravariant functoriality of `homObjMap`; the final reassociation and
cancellation are isolated here for a subsequent worker. -/
theorem dual_retraction_key
    {X : Scheme.{u}} {P Q : X.Modules} (f : P ⟶ Q) (U : X.Opens)
    (s : (restrictFunctor U.ι).obj Q ⟶ (restrictFunctor U.ι).obj P)
    (e : ∀ A B : X.Modules,
      (restrictFunctor U.ι).obj (SheafOfModules.homObj
        (R := X.toRingedSpace.sheaf) A B) ≅
        SheafOfModules.homObj (R := U.toScheme.toRingedSpace.sheaf)
          ((restrictFunctor U.ι).obj A) ((restrictFunctor U.ι).obj B))
    (hs : s ≫ (restrictFunctor U.ι).map f = 𝟙 _) :
    (restrictFunctor U.ι).map (dualMap f) ≫
        (e P (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        SheafOfModules.homObjMap (R := U.toScheme.toRingedSpace.sheaf)
          s (𝟙 _) ≫ (e Q (SheafOfModules.unit X.ringCatSheaf)).inv = 𝟙 _ := by
  sorry

end AlgebraicGeometry.Scheme.Modules

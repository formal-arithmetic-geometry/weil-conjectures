module
public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.InternalHom
open CategoryTheory
namespace AlgebraicGeometry
open Scheme
universe u
variable {V U : Scheme.{u}} (f : V ⟶ U) (h : WeaklyEtale f)
#check (MorphismProperty.Over.map ⊤ h : V.ProEt ⥤ U.ProEt)
#check (MorphismProperty.Over.map ⊤ h : V.ProEt ⥤ U.ProEt).op.lanUnit
#print Scheme.ProEt

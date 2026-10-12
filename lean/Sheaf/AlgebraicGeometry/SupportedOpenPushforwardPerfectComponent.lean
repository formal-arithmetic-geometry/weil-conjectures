module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- The perfectness obligation for a supported open pushforward.
Source: Stacks Project, Tag 08DP, using Tag 08FE and Definition 08CM.
(blueprint: lem-pc-supported-open-pushforward-perfect-component).

Proof: Put V = X minus T, which is open since T is closed. The opens U and V
cover X because T is contained in U. On U the derived direct image restricts
to F, by open restriction of derived direct image and the identity map on U.
On V it is the derived direct image of F restricted to U intersect V (Tag 08FE).
All cohomology stalks there vanish by the support hypothesis, so this restriction
is zero; direct image is additive and its derived functor sends zero to zero.
The restriction on U is perfect by hypothesis, and that on V is represented by
the zero strictly perfect complex. Combining their local strictly perfect models
using the definition of perfectness gives perfectness on X. When T or U is empty,
the same argument gives the zero object; when U is total it recovers F. -/
theorem supported_open_pushforward_perfect (X : Scheme.{u}) (U : X.Opens)
    (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))] :
    (∀ F : schemeDerivedCategory U.toScheme, IsPerfect U.toScheme F →
      (∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj F).val.presheaf
            x))) →
      IsPerfect X ((schemeDerivedDirectImage U.ι).obj F)) := by
  sorry

end AlgebraicGeometry.Scheme

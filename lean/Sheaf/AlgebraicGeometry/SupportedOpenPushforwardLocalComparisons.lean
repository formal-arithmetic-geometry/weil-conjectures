module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
/-- The two supported comparison maps are invertible after restriction to U
and to V = X minus T; this states local comparisons, not global invertibility.
Source: Stacks Project, Tag 08DF, its restriction computations using Tags 08FE
and 08BS (exact extension by zero).
(blueprint: lem-pc-supported-open-pushforward-local-comparisons).

Proof: For any G supported on T in U, G restricted to U intersect V is zero:
its cohomology sheaves have zero stalks there, so vanish, and cohomology detects
zero derived objects. Tag 08FE identifies Rj_*G on V with the direct image of
this zero restriction, hence with zero; on U it identifies Rj_*G with G.
For E supported on T, E on V is also zero. The adjunction unit restricts on U
to an isomorphism by the fully faithful open direct image adjunction, and on V
to a morphism between zero objects. These statements hold for any adjunction
since two adjunction structures differ by natural automorphisms.
For S left adjoint to restriction, uniqueness of left adjoints identifies S
with the derived exact extension-by-zero functor (Tag 08BS). Its unit is an
isomorphism, its restriction on U is F, and on V it is extension by zero of
F on U intersect V, hence zero. The given adjunct equation says that the
restriction of phi to U, composed with the unit, is the identity, after the
counit identification for Rj_*. Thus this restriction is invertible. On V
both endpoints are zero, so the restriction is invertible there too.
Empty opens and T empty use the zero-object statements with no stalks to test. -/
theorem supported_open_pushforward_local_comparisons (X : Scheme.{u}) (U : X.Opens)
    (T : Set X) (hT : IsClosed T) (hTU : T ⊆ (U : Set X))
    (V : X.Opens) (hV : (V : Set X) = Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))] :
    (∀ (adj : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
        (E : schemeDerivedCategory X),
      (∀ (n : ℤ) (x : X), x ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj E).val.presheaf x))) →
      ∀ W : X.Opens, W = U ∨ W = V →
        IsIso ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) W).mapDerivedCategory.map (adj.unit.app E))) ∧
    (∀ (adj : ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
        (S : schemeDerivedCategory U.toScheme ⥤ schemeDerivedCategory X)
        (adjS : S ⊣ ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory)
        (F : schemeDerivedCategory U.toScheme), IsPerfect U.toScheme F →
      (∀ (n : ℤ) (x : U.toScheme), x.val ∉ T →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj F).val.presheaf
            x))) →
      ∀ φ : S.obj F ⟶ (schemeDerivedDirectImage U.ι).obj F,
        adjS.unit.app F ≫ (adj.homEquiv (S.obj F) F).symm φ = 𝟙 F →
        ∀ W : X.Opens, W = U ∨ W = V →
          IsIso ((SheafOfModules.overFunctor.{u}
            (moduleRings X.toRingedSpace) W).mapDerivedCategory.map φ)) := by
  sorry

end AlgebraicGeometry.Scheme

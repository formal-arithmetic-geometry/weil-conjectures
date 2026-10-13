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
/-- The supported adjunction unit is invertible after restriction to U and X minus T.
Source: Stacks Project, Tag 08DF (1), using Tag 08FE.
(blueprint: lem-pc-supported-open-pushforward-local-comparisons-first).

Proof: Write L for restriction to U and R for its derived direct image. The
open direct image is fully faithful, so the counit of any L ⊣ R is invertible.
The triangle identity then makes L applied to the unit at E invertible; the
scheme/over-site equivalence reflects invertibility. On V = X minus T,
restriction of E is zero: restriction commutes with cohomology, its cohomology
stalks vanish there, stalks detect zero sheaves, and cohomology detects zero
objects in the derived category. The restriction of L(E) to U intersect V is
likewise zero. Tag 08FE identifies restriction of R(L(E)) to V with the derived
direct image of that zero object, hence zero. Thus the restricted unit on V
is a map between zero objects and is invertible. This proves both allowed
values of W. The argument also covers empty opens and empty T. -/
theorem supported_open_pushforward_local_comparisons_first (X : Scheme.{u}) (U : X.Opens)
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
          (moduleRings X.toRingedSpace) W).mapDerivedCategory.map (adj.unit.app E))) := by
  sorry

/-- The supported left/right direct-image comparison is locally invertible.
Source: Stacks Project, Tag 08DF (2), using Tags 08FE and 08BS.
(blueprint: lem-pc-supported-open-pushforward-local-comparisons-second).

Proof: Exact extension by zero gives a left adjoint to derived restriction L.
Its unit is invertible, since restriction of extension by zero is the identity.
Uniqueness of left adjoints transports these facts to the given S and adjS.
The open direct image R is fully faithful, so the counit of the given L ⊣ R
is invertible. The equation in the statement makes the right adjunct of phi
the inverse of adjS.unit at F. This adjunct is L(phi) followed by the counit
at F, so L(phi) is invertible. The scheme/over-site equivalence reflects this,
proving the assertion on U. Support of F makes its restriction to U intersect V
zero, by stalkwise vanishing of cohomology. Tag 08FE makes restriction of R(F)
to V zero. Restriction of extension by zero to V is extension by zero from
U intersect V, hence also zero; transport along the left-adjoint isomorphism
makes restriction of S(F) zero. Thus phi on V is invertible between zero
objects. No perfectness is needed for this local calculation, but its existing
hypothesis is retained. Empty opens and empty T obey the same zero argument. -/
theorem supported_open_pushforward_local_comparisons_second (X : Scheme.{u}) (U : X.Opens)
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
  exact ⟨supported_open_pushforward_local_comparisons_first X U T hT hTU V hV,
    supported_open_pushforward_local_comparisons_second X U T hT hTU V hV⟩

end AlgebraicGeometry.Scheme

module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits

/-! # Global regular functions on algebraic spaces

Source: Stacks Project, Properties of Spaces, Tag 03G7; Spaces Limits, Tag 07SI
(blueprint: def-sfb-space-global-functions).

Compatible functions on all scheme tests give the canonical extension of the small
etale structure sheaf. Pullback is composition on tests, including non-etale maps.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Ring colimits indexed in the scheme universe also exist in the larger function universe.
Source: Mathlib, `hasColimitsOfSizeShrink`, applied to commutative rings
(blueprint: def-sfb-space-global-functions). -/
instance globalFunctionRings_hasSmallColimits :
    HasColimitsOfSize.{u, u} CommRingCat.{u + 1} :=
  hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _

/-- The regular-function diagram on all scheme tests, with ordinary scheme pullbacks.
Source: Stacks, Properties of Spaces, Tag 03G7; Spaces Limits, Tag 07SI
(blueprint: def-sfb-space-global-functions). -/
def functionDiagram {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (CostructuredArrow yoneda X.obj.obj)ᵒᵖ ⥤ CommRingCat.{u} :=
  (CostructuredArrow.proj yoneda X.obj.obj ⋙ Over.forget S).op ⋙ Scheme.Γ

/-- Compatible regular functions on every scheme test. This is the ring of global
functions, using the canonical extension of the small etale structure sheaf.
Source: Stacks, Properties of Spaces, Tag 03G7
(blueprint: def-sfb-space-global-functions). -/
def globalFunctionRing {S : Scheme.{u}} (X : AlgebraicSpace S) : CommRingCat.{u + 1} :=
  @CommRingCat.of _ (@Subring.toCommRing (∀ T, X.functionDiagram.obj T) inferInstance
    (RingCat.sectionsSubring (X.functionDiagram ⋙ forget₂ CommRingCat RingCat)))

/-- Pullback is restriction of a compatible family to tests composed with the given map.
Source: Stacks, Properties of Spaces, Tag 03G7; Spaces Limits, Tag 07SI
(blueprint: def-sfb-space-global-functions). -/
def globalFunctionMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Y.globalFunctionRing ⟶ X.globalFunctionRing :=
  CommRingCat.ofHom
    { toFun := fun s ↦ ⟨fun T ↦ s.val ((CostructuredArrow.map f.hom.hom).op.obj T), by
        intro T U a
        exact s.property ((CostructuredArrow.map f.hom.hom).op.map a)⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }

/-- The contravariant global-functions functor with the actual pullback ring maps.
Source: Stacks, Properties of Spaces, Tag 03G7; Spaces Limits, Tag 07SI
(blueprint: def-sfb-space-global-functions). -/
def globalFunctions {S : Scheme.{u}} : (AlgebraicSpace S)ᵒᵖ ⥤ CommRingCat.{u + 1} where
  obj X := X.unop.globalFunctionRing
  map f := globalFunctionMap f.unop
  map_id X := by
    ext s
    apply Subtype.ext
    funext T
    exact congrArg
      (fun a : yoneda.obj T.unop.left ⟶ X.unop.obj.obj ↦
        @id (Scheme.Γ.obj (op T.unop.left.left))
          (s.val (op (CostructuredArrow.mk a)))) (Category.comp_id T.unop.hom)
  map_comp f g := by
    ext s
    apply Subtype.ext
    funext T
    exact congrArg
      (fun a : yoneda.obj T.unop.left ⟶ _ ↦ @id (Scheme.Γ.obj (op T.unop.left.left))
          (s.val (op (CostructuredArrow.mk a))))
      (Category.assoc T.unop.hom g.unop.hom.hom f.unop.hom.hom).symm

/-- Restriction of the all-test compatible family to the small etale site.
Source: Stacks, Properties of Spaces, Tag 03G7
(blueprint: def-sfb-space-global-functions). -/
def globalFunctionEtaleRestriction {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.globalFunctionRing →
      (X.etaleForget.op ⋙ Scheme.Γ ⋙ forget CommRingCat).sections :=
  fun s ↦ ⟨fun T ↦ s.val (op T.unop.obj), fun a ↦ s.property a.unop.hom.op⟩

/-- All-test compatible functions are exactly global sections of the specified small
etale structure sheaf. No schematicity or separatedness is assumed.
Source: Stacks, Properties of Spaces, Tag 03G7
(blueprint: def-sfb-space-global-functions).
Proof: restrict a compatible family to etale tests. Conversely, given compatible etale
sections and a scheme T mapping to X, pull an etale scheme atlas of X back to T. Pull
the sections on the atlas to this cover by ordinary scheme pullback. On overlaps, their
agreement follows by pullback from the atlas overlap and compatibility on etale tests.
Etale descent of scheme regular functions glues a unique section on T. Refining the cover
proves independence, and uniqueness
proves compatibility with every scheme morphism. On etale tests the recovered section is
the original one; uniqueness on the same covers also proves injectivity. All operations
are componentwise, so the bijection respects the ring operations. -/
theorem globalFunctionEtaleRestriction_bijective {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Function.Bijective (globalFunctionEtaleRestriction X) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

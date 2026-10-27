module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Yoneda

/-!
# Relative morphisms and their graphs

Source: Stacks Project, quot.tex, Tag 0D1A, lemma-Mor-into-Hilb
(blueprint: def-sfb-relative-morphisms-presheaf).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

/-- The relative morphism presheaf. Its points are maps `T ×[S] Z ⟶ X` over `S`,
equivalently maps `Z_T ⟶ X_T` over `T`. The action is precomposition by base change.
Source: Stacks Project, quot.tex, Tag 0D1A
(blueprint: def-sfb-relative-morphisms-presheaf). -/
noncomputable def relativeMorphismsPresheaf {Z X S : Scheme.{u}} (z : Z ⟶ S) (x : X ⟶ S) :
    (Over S)ᵒᵖ ⥤ Type u :=
  (Over.pullback z ⋙ Over.map z).op ⋙ yoneda.obj (Over.mk x)

/-- The graph in `(Z ×[S] X)_T` of a relative morphism over `T`.
Source: Stacks Project, quot.tex, Tag 0D1A
(blueprint: def-sfb-relative-morphisms-presheaf). -/
noncomputable def relativeMorphismGraph {Z X S : Scheme.{u}} (z : Z ⟶ S) (x : X ⟶ S)
    (T : Over S) (f : (relativeMorphismsPresheaf z x).obj (op T)) :
    pullback T.hom z ⟶ pullback (pullback.fst z x ≫ z) T.hom :=
  pullback.lift
    (pullback.lift (pullback.snd T.hom z) f.left (by simpa using f.w.symm))
    (pullback.fst T.hom z) (by
      simpa only [Category.assoc, pullback.lift_fst_assoc] using
        (pullback.condition (f := T.hom) (g := z)).symm)

/-- First projection from `(Z ×[S] X)_T` to `Z_T`, using `T ×[S] Z` for `Z_T`.
Source: Stacks Project, quot.tex, Tag 0D1B
(blueprint: def-sfb-relative-morphisms-presheaf). -/
noncomputable def graphFirstProjection {Z X S : Scheme.{u}} (z : Z ⟶ S) (x : X ⟶ S)
    (T : Over S) : pullback (pullback.fst z x ≫ z) T.hom ⟶ pullback T.hom z :=
  pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ pullback.fst z x)
    (by simpa only [Category.assoc] using
      (pullback.condition (f := pullback.fst z x ≫ z) (g := T.hom)).symm)

/-- Second projection to `X`; paired with the structure map to `T` this is the projection
onto `X_T`. Source: Stacks Project, quot.tex, Tags 0D1A and 0D1B
(blueprint: def-sfb-relative-morphisms-presheaf). -/
noncomputable def graphSecondProjection {Z X S : Scheme.{u}} (z : Z ⟶ S) (x : X ⟶ S)
    (T : Over S) : pullback (pullback.fst z x ≫ z) T.hom ⟶ X :=
  pullback.fst _ _ ≫ pullback.snd z x

end AlgebraicGeometry

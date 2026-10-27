module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeMorphisms
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties

/-! # Hilbert-family values for algebraic spaces

Source: Stacks Project, quot.tex, definition of Hilb and Tags 0D1A--0D1B
(blueprint: def-sfb-space-hilbert-family-values).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Closed subspaces of A_T proper, flat and finitely presented over T.
Finite presentation means locally finitely presented, quasi-compact and quasi-separated.
The use of ClosedSubspace identifies isomorphic closed immersions over the ambient space.
Source: Stacks, quot.tex, definition of Hilb and Tags 0D1A--0D1B
(blueprint: def-sfb-space-hilbert-family-values). -/
abbrev SpaceHilbertFamily {S : Scheme.{u}} {A B : AlgebraicSpace S}
    (a : A ⟶ B) (T : SchemeTests B.obj.obj) :=
  {D : ClosedSubspace (relativeSpace a T) //
    MapIsProper (D.val.arrow ≫ relativeSpaceProjection a T) ∧
    MapIsFlat (D.val.arrow ≫ relativeSpaceProjection a T) ∧
    MapIsLocallyOfFinitePresentation (D.val.arrow ≫ relativeSpaceProjection a T) ∧
    MapIsQuasiCompact (D.val.arrow ≫ relativeSpaceProjection a T).hom.hom ∧
    MapIsQuasiCompact (pullback.diagonal
      (D.val.arrow ≫ relativeSpaceProjection a T).hom.hom)}

/-- The underlying algebraic space of a Hilbert family.
Source: Stacks, Tag 0D1B (blueprint: def-sfb-space-hilbert-family-values). -/
abbrev SpaceHilbertFamily.space {S : Scheme.{u}} {A B : AlgebraicSpace S}
    {a : A ⟶ B} {T : SchemeTests B.obj.obj} (D : SpaceHilbertFamily a T) : AlgebraicSpace S :=
  (D.val.val : AlgebraicSpace S)

/-- The actual closed immersion of a Hilbert family into the ambient base change.
Source: Stacks, Tag 0D1B (blueprint: def-sfb-space-hilbert-family-values). -/
abbrev SpaceHilbertFamily.inclusion {S : Scheme.{u}} {A B : AlgebraicSpace S}
    {a : A ⟶ B} {T : SchemeTests B.obj.obj} (D : SpaceHilbertFamily a T) :
    D.space ⟶ relativeSpace a T :=
  D.val.val.arrow

/-- The first projection of a family in (Z ×_B W)_T.
Source: Stacks, Tag 0D1B (blueprint: def-sfb-space-hilbert-family-values). -/
def SpaceHilbertFamily.first {S : Scheme.{u}} {Z W B : AlgebraicSpace S}
    {z : Z ⟶ B} {w : W ⟶ B} {T : SchemeTests B.obj.obj}
    (D : SpaceHilbertFamily (relativeProductMap z w) T) : D.space ⟶ relativeSpace z T :=
  D.inclusion ≫ relativeFirstProjection z w T

/-- The second projection of a family, composed with W_T → W.
Source: Stacks, Tags 0D1A--0D1B (blueprint: def-sfb-space-hilbert-family-values). -/
def SpaceHilbertFamily.second {S : Scheme.{u}} {Z W B : AlgebraicSpace S}
    {z : Z ⟶ B} {w : W ⟶ B} {T : SchemeTests B.obj.obj}
    (D : SpaceHilbertFamily (relativeProductMap z w) T) : D.space ⟶ W :=
  D.inclusion ≫ relativeSecondProjection z w T

end AlgebraicGeometry.AlgebraicSpace

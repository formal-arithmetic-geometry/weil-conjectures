module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Relative isomorphisms and graph-classifying bijections

Source: Stacks Project, schemes.tex, Tags 01JP, 01JJ and 01KT
(blueprint: def-sfb-relative-isom-graph-classification).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Isomorphisms of the two pulled-back schemes over the test scheme.
Source: Stacks, Tags 01JP and 01JJ
(blueprint: def-sfb-relative-isom-graph-classification). -/
abbrev relativeIsomorphisms {S X Y : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S)
    (T : Over S) :=
  Over.mk (pullback.fst T.hom x) ≅ Over.mk (pullback.fst T.hom y)

/-- The canonical pullback relation, expressed by its forward and inverse squares.
These squares uniquely specify pullback, without a choice of a transition map.
Source: Stacks, Tag 01JP
(blueprint: def-sfb-relative-isom-graph-classification). -/
def RelativeIsomorphisms.Restricts {S X Y : Scheme.{u}} {x : X ⟶ S} {y : Y ⟶ S}
    {T' T : Over S} (h : T' ⟶ T)
    (e' : relativeIsomorphisms x y T') (e : relativeIsomorphisms x y T) : Prop :=
  ((Over.pullback x).map h).left ≫ e.hom.left =
      e'.hom.left ≫ ((Over.pullback y).map h).left ∧
    ((Over.pullback y).map h).left ≫ e.inv.left =
      e'.inv.left ≫ ((Over.pullback x).map h).left

/-- The actual graph `(1,e)` in `X_T ×_T Y_T`.
Source: Stacks, Tag 01KT
(blueprint: def-sfb-relative-isom-graph-classification). -/
noncomputable def relativeIsomGraph {S X Y : Scheme.{u}} {x : X ⟶ S} {y : Y ⟶ S}
    {T : Over S} (e : relativeIsomorphisms x y T) :
    pullback T.hom x ⟶ pullback (pullback.fst T.hom x) (pullback.fst T.hom y) :=
  pullback.lift (𝟙 _) e.hom.left (by simpa using e.hom.w.symm)

/-- A bijection classifies precisely the closed graphs with invertible projections.
Closed subschemes are compared by their ideal sheaves; isomorphic presentations
of a closed immersion therefore give the same graph. Recovery is `p_X⁻¹ ≫ p_Y`.
Source: Stacks, Tags 01KT and 01JJ
(blueprint: def-sfb-relative-isom-graph-classification). -/
def IsRelativeIsomGraphClassification {S X Y : Scheme.{u}} {x : X ⟶ S} {y : Y ⟶ S}
    {T : Over S} {A : Type u} (E : A ≃ relativeIsomorphisms x y T) : Prop :=
  (∀ a : A, IsClosedImmersion (relativeIsomGraph (E a))) ∧
    ∀ (D : Scheme.{u})
      (j : D ⟶ pullback (pullback.fst T.hom x) (pullback.fst T.hom y)),
      IsClosedImmersion j →
      ∀ (p : D ≅ pullback T.hom x) (q : D ≅ pullback T.hom y),
        j ≫ pullback.fst _ _ = p.hom → j ≫ pullback.snd _ _ = q.hom →
        ∃! a : A, (E a).hom.left = p.inv ≫ q.hom ∧
          j.ker = (relativeIsomGraph (E a)).ker

/-- A natural graph-classifying representation of the relative Isom functor.
Source: Stacks, Tag 01JJ
(blueprint: def-sfb-relative-isom-graph-classification). -/
structure RelativeIsomGraphRepresentation {S X Y : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S)
    (J : Over S) where
  /-- The representing bijections on all test schemes. -/
  equiv : ∀ T : Over S, (T ⟶ J) ≃ relativeIsomorphisms x y T
  /-- Naturality for the canonical pullbacks, including inverses. -/
  natural : ∀ (T' T : Over S) (h : T' ⟶ T) (a : T ⟶ J),
    RelativeIsomorphisms.Restricts h (equiv T' (h ≫ a)) (equiv T a)
  /-- Both directions of classification by the actual closed graphs. -/
  graphs : ∀ T : Over S, IsRelativeIsomGraphClassification (equiv T)

/-- Canonical reassociation of a twice-pulled-back family, preserving its test coordinate.
Source: Stacks, Tag 01JP
(blueprint: def-sfb-relative-isom-graph-classification). -/
noncomputable def relativeIsomBaseChangeIso {S X B : Scheme.{u}} (x : X ⟶ S)
    (b : B ⟶ S) (T : Over B) :
    pullback T.hom (pullback.snd x b) ≅ pullback (T.hom ≫ b) x :=
  pullbackSymmetry _ _ ≪≫ pullbackLeftPullbackSndIso x b T.hom ≪≫ pullbackSymmetry _ _

/-- The canonical comparison on the products containing the graphs after base change.
Source: Stacks, Tag 01JP
(blueprint: def-sfb-relative-isom-graph-classification). -/
noncomputable def relativeIsomGraphBaseChangeMap {S X Y B : Scheme.{u}}
    (x : X ⟶ S) (y : Y ⟶ S) (b : B ⟶ S) (T : Over B) :
    pullback (pullback.fst T.hom (pullback.snd x b))
        (pullback.fst T.hom (pullback.snd y b)) ⟶
      pullback (pullback.fst (T.hom ≫ b) x) (pullback.fst (T.hom ≫ b) y) :=
  pullback.map _ _ _ _ (relativeIsomBaseChangeIso x b T).hom
    (relativeIsomBaseChangeIso y b T).hom (𝟙 T.left)
    (by simp [relativeIsomBaseChangeIso]) (by simp [relativeIsomBaseChangeIso])

/-- Zariski descent of relative isomorphisms, including their inverses. Compatibility
is tested after maps into any two covering charts, hence is the usual overlap condition.
Source: Stacks, Tags 01JB and 01JJ
(blueprint: def-sfb-relative-isom-graph-classification). -/
def IsRelativeIsomZariskiSheaf {S X Y : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) : Prop :=
  ∀ (T : Over S) (I : Type v) (V : I → Over S) (j : ∀ i : I, V i ⟶ T),
    (∀ i : I, IsOpenImmersion (j i).left) →
    (∀ t : T.left, ∃ (i : I) (s : (V i).left), (j i).left s = t) →
    ∀ e : ∀ i : I, relativeIsomorphisms x y (V i),
      (∀ (i k : I) (R : Over S) (a : R ⟶ V i) (b : R ⟶ V k),
        a ≫ j i = b ≫ j k →
        ((Over.pullback x).map a).left ≫ (e i).hom.left ≫
            ((Over.pullback y).map (j i)).left =
          ((Over.pullback x).map b).left ≫ (e k).hom.left ≫
            ((Over.pullback y).map (j k)).left) →
      ∃! f : relativeIsomorphisms x y T,
        ∀ i : I, RelativeIsomorphisms.Restricts (j i) (e i) f

end AlgebraicGeometry

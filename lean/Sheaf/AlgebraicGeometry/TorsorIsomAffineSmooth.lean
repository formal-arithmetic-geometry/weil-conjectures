module

public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.AffineFpqcDescent
import WeilConjectures.AlgebraicGeometry.FpqcMorphismsDescend
import Sheaf.AlgebraicGeometry.FpqcAffineDescent

/-! # Affine smooth isomorphism schemes of represented right torsors

Source: Stacks Project, groupoids.tex, Tag 049C; descent.tex, Tags 0245, 02W0,
02L5 and 02VL (blueprint: lem-sfb-torsor-isom-affine-smooth).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits CartesianMonoidalCategory

namespace AlgebraicGeometry.RepresentedRightTorsor

/-- The set of equivariant T-isomorphisms between the two pulled-back torsors.
The isomorphism is between the actual fibre products in schemes over B. The first
law makes it a T-isomorphism. In the second law, p' is the translate of p by g:
its P-coordinate is p*g and its T-coordinate is unchanged. Thus the equation
requires its Q-coordinate to be the translate of the image of p. Testing all
B-schemes includes exactly all sections of H_T over all schemes over T.
Source: Stacks Project, Tag 049C, simultaneous right-torsor trivializations
(blueprint: lem-sfb-torsor-isom-affine-smooth). -/
structure EquivariantIsom {B : Scheme.{u}} {H : Grp (Over B)} {Y : Over B}
    (P Q : RepresentedRightTorsor H Y) {T : Over B} (f : T ⟶ Y) where
  iso : pullback P.projection f ≅ pullback Q.projection f
  over_base : iso.hom ≫ pullback.snd Q.projection f = pullback.snd P.projection f
  equivariant : ∀ (U : Over B) (p p' : U ⟶ pullback P.projection f) (g : U ⟶ H.X),
    p' ≫ pullback.fst P.projection f =
      lift (p ≫ pullback.fst P.projection f) g ≫ P.action →
    p' ≫ pullback.snd P.projection f = p ≫ pullback.snd P.projection f →
    p' ≫ iso.hom ≫ pullback.fst Q.projection f =
      lift (p ≫ iso.hom ≫ pullback.fst Q.projection f) g ≫ Q.action

/-- The canonical map from P_T' to P_T for a map T' -> T over Y. It preserves
P-coordinates and applies the given map to the test-scheme coordinate.
Source: Stacks Project, Tag 049C, pullback of equivariant isomorphisms
(blueprint: lem-sfb-torsor-isom-affine-smooth). -/
def testChangeMap {B : Scheme.{u}} {H : Grp (Over B)} {Y : Over B}
    (P : RepresentedRightTorsor H Y) {T T' : Over Y} (h : T' ⟶ T) :
    pullback P.projection T'.hom ⟶ pullback P.projection T.hom :=
  pullback.map P.projection T'.hom P.projection T.hom (𝟙 P.space) h.left (𝟙 Y)
    (by simp) (by simp)

/-- The equivariant isomorphism functor of any two represented right torsors under
an affine smooth group scheme over an arbitrary base is represented by an affine
smooth Y-scheme. The family E gives the representing bijections; its displayed
compatibility says precisely that restriction is pullback of isomorphisms.
If Y is affine the representing scheme is affine. No field, connectedness,
reductivity, or global section of either torsor is assumed.

Source: Stacks Project, groupoids.tex Tag 049C and descent.tex Tags 0245, 02W0,
02L5 and 02VL (blueprint: lem-sfb-torsor-isom-affine-smooth).

Proof:
1. Set W = P times_Y Q. The torsor projections are flat, surjective and finitely
presented. Their fppf singleton covers are fpqc by
lem-trf-fppf-covering-is-fpqc. Base change and composition of fpqc coverings
(lem-weil-pbc-fpqc-covering-axioms) make W -> Y and every T_W -> T fpqc.
2. The tautological sections p,q over W trivialize both torsors using their
cartesian torsor squares. Every equivariant isomorphism is uniquely
p*h -> q*c*h for a section c of H_W, with inverse q*h -> p*c^{-1}*h.
All these expressions are morphisms and commute with arbitrary base change.
3. On W times_Y W write p_2=p_1*a and q_2=q_1*b. The transition is
c_2=b^{-1}*c_1*a, with inverse c -> b*c*a^{-1}. On the triple product,
a_13=a_12*a_23 and b_13=b_12*b_23 give the cocycle equation. The scheme H_W
is affine over W by lem-weil-pbc-affine-morphism-permanence, so
lem-galois-fpqc-affine-descent-effective descends it to I over Y.
4. By lem-galois-fpqc-morphisms-descend, sections of I_T are exactly the local
coefficients satisfying this transition relation. The associated local maps,
their inverses and their equivariance descend uniquely. This gives E at every
T. The same formulas and descent uniqueness give the displayed naturality.
5. The base change I_W is H_W, hence affine. By
lem-weil-pbc-fpqc-descend-affine, I -> Y is affine. If Y is affine its source
is affine by lem-weil-pbc-affine-morphism-permanence.
6. Smooth base change (lem-pc-proper-base-change, clause 2) makes H_W smooth
over W. Apply lem-trf-smooth-fpqc-base-descent first along W -> P and then
P -> Y. Each cover is flat, surjective and quasi-compact: this holds for the
torsor projections by definition and for their base changes by
lem-pc-quasi-compact-base-change. Thus I -> Y is smooth. -/
theorem isom_affine_smooth {B : Scheme.{u}} (H : Grp (Over B))
    [IsAffineHom H.X.hom] [Smooth H.X.hom] (Y : Over B)
    (P Q : RepresentedRightTorsor H Y) :
    ∃ I : Over Y, IsAffineHom I.hom.left ∧ Smooth I.hom.left ∧
      (IsAffine Y.left → IsAffine I.left.left) ∧
      ∃ E : ∀ T : Over Y, (T ⟶ I) ≃ EquivariantIsom P Q T.hom,
        ∀ (T T' : Over Y) (h : T' ⟶ T) (s : T ⟶ I),
          (E T' (h ≫ s)).iso.hom ≫ testChangeMap Q h =
            testChangeMap P h ≫ (E T s).iso.hom := by
  sorry

end AlgebraicGeometry.RepresentedRightTorsor

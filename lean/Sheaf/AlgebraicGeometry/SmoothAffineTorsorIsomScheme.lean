module

public import Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.AffineFpqcDescent
import Sheaf.AlgebraicGeometry.FpqcAffineDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Limits

/-! # The smooth affine scheme of equivariant torsor isomorphisms

Source: Stacks Project, examples.tex, Tag 04AG (section-not-algebraic-stack),
the Isom-scheme paragraph; the fpqc descent argument works over any base.
Smoothness: Alper--Halpern-Leistner--Heinloth, Cartan--Iwahori--Matsumoto
Decompositions, Section 2, Claim 3, printed page 3.
(blueprint: lem-sfb-smooth-affine-torsor-isom-scheme)

The helper structures encode the isomorphism functor and its representation.
They use the actual represented torsors, without assuming local trivializations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Limits CartesianMonoidalCategory

namespace AlgebraicGeometry.RepresentedRightTorsor

variable {S : Scheme.{u}} {H : Grp (Over S)} {Y : Over S}

/-- An equivariant isomorphism over T, encoded on all test-scheme points. A point
of P_T over t is precisely a p with p ≫ P.projection = t ≫ T.hom. The equivalences
and their naturality are exactly a scheme isomorphism P_T ≅ Q_T by Yoneda;
the final field says it commutes with the right H_T-action. Both p and its translate
are quantified with their fibre conditions, so no choice of a lift is made.
Source: Stacks Tag 04AG, Isom-scheme paragraph.
(blueprint: lem-sfb-smooth-affine-torsor-isom-scheme) -/
structure EquivariantIsoAt (P Q : RepresentedRightTorsor H Y) (T : Over Y) where
  app : ∀ (V : Over S) (t : V ⟶ T.left),
    {p : V ⟶ P.space // p ≫ P.projection = t ≫ T.hom} ≃
      {q : V ⟶ Q.space // q ≫ Q.projection = t ≫ T.hom}
  naturality : ∀ (V W : Over S) (f : V ⟶ W) (t : W ⟶ T.left)
    (p : W ⟶ P.space) (p' : V ⟶ P.space)
    (hp : p ≫ P.projection = t ≫ T.hom)
    (hp' : p' ≫ P.projection = (f ≫ t) ≫ T.hom),
    p' = f ≫ p → (app V (f ≫ t) ⟨p', hp'⟩).val = f ≫ (app W t ⟨p, hp⟩).val
  equivariance : ∀ (V : Over S) (t : V ⟶ T.left)
    (p p' : V ⟶ P.space) (h : V ⟶ H.X)
    (hp : p ≫ P.projection = t ≫ T.hom)
    (hp' : p' ≫ P.projection = t ≫ T.hom),
    p' = lift p h ≫ P.action →
      (app V t ⟨p', hp'⟩).val = lift (app V t ⟨p, hp⟩).val h ≫ Q.action

/-- The graph of an equivariant isomorphism on a test scheme. The existential
quantifies only a proof of the fibre condition, not any new geometric data.
Source: Stacks Tag 04AG, functor of torsor isomorphisms.
(blueprint: lem-sfb-smooth-affine-torsor-isom-scheme) -/
def EquivariantIsoAt.graph {P Q : RepresentedRightTorsor H Y} {T : Over Y}
    (e : EquivariantIsoAt P Q T) (V : Over S) (t : V ⟶ T.left)
    (p : V ⟶ P.space) (q : V ⟶ Q.space) : Prop :=
  ∃ hp : p ≫ P.projection = t ≫ T.hom, (e.app V t ⟨p, hp⟩).val = q

/-- Restriction of an isomorphism along a test-scheme morphism, characterized by
its graph. This characterizes the actual pullback, including identity and composite
base changes, without choosing fibre-product associativity isomorphisms.
Source: Stacks Tag 04AG, functoriality of Isom.
(blueprint: lem-sfb-smooth-affine-torsor-isom-scheme) -/
def EquivariantIsoAt.IsRestriction {P Q : RepresentedRightTorsor H Y}
    {T T' : Over Y} (f : T' ⟶ T)
    (e : EquivariantIsoAt P Q T) (e' : EquivariantIsoAt P Q T') : Prop :=
  ∀ (V : Over S) (t : V ⟶ T'.left) (p : V ⟶ P.space) (q : V ⟶ Q.space),
    e'.graph V t p q ↔ e.graph V (t ≫ f.left) p q

/-- A representing scheme and its natural representing bijections. F is either
the identity on Y-schemes or Over.map g for a base change g : Z ⟶ Y. In the latter
case the functor is exactly Isom of the base-changed torsors: on a Z-scheme T their
fibres are P_T and Q_T, with the same H_T-actions.
Source: Stacks Tag 04AG, representability and base change of Isom.
(blueprint: lem-sfb-smooth-affine-torsor-isom-scheme) -/
structure IsomRepresentation (P Q : RepresentedRightTorsor H Y)
    {Z : Over S} (F : Over Z ⥤ Over Y) where
  space : Over Z
  equiv : ∀ T : Over Z, (T ⟶ space) ≃ EquivariantIsoAt P Q (F.obj T)
  naturality : ∀ (T T' : Over Z) (f : T' ⟶ T) (a : T ⟶ space),
    EquivariantIsoAt.IsRestriction (F.map f) (equiv T a) (equiv T' (f ≫ a))

/-- The functor of equivariant isomorphisms of two represented right torsors under
a smooth affine group scheme is represented by a smooth affine morphism. The source
is affine when Y is affine. For each base change g the theorem supplies a representing
scheme for the base-changed isomorphism functor, and an isomorphism from the actual
pullback. Its equation on all test schemes specifies the canonical comparison via
the pullback adjunction, rather than an arbitrary isomorphism. At T = Over.mk (𝟙 Y),
the representing bijection identifies sections with equivariant isomorphisms P ≅ Q.

Source: Stacks examples.tex Tag 04AG; Alper--Halpern-Leistner--Heinloth,
Section 2, Claim 3, printed page 3.
(blueprint: lem-sfb-smooth-affine-torsor-isom-scheme)

Proof plan:
1. The flat, surjective, finitely presented torsor maps are fpqc singleton covers.
   By fpqc base change and composition U = P ×_Y Q is such a cover; quasi-compactness
   uses lem-weil-pbc-qcqs-morphism-permanence and the covering axioms node.
2. The two tautological sections trivialize P_U and Q_U. Every equivariant map is
   uniquely f_c(ph) = qch, with inverse qk ↦ p c⁻¹k. Thus H_U represents Isom over U.
3. On U ×_Y U write p₁ = p₀a₀₁ and q₁ = q₀b₀₁. The transition on parameters is
   c₁ = b₀₁⁻¹c₀a₀₁. The identities a₀₂ = a₀₁a₁₂ and b₀₂ = b₀₁b₁₂ prove its cocycle,
   without assuming H commutative.
4. Affine base change and lem-galois-fpqc-affine-descent-effective descend H_U
   with this specific cocycle to I over Y, compatibly with the local representing maps.
5. Affineness descends by lem-weil-pbc-fpqc-descend-affine. Smoothness follows by
   smooth base change (the independent smooth clause of lem-pc-proper-base-change)
   and lem-trf-smooth-fpqc-base-descent. Affine target implies affine source by
   lem-weil-pbc-affine-morphism-permanence.
6. Representable fpqc descent glues morphisms, their inverses, and the equivariance
   equalities. This gives the displayed representing bijections, natural in T
   (lem-weil-pbc-fpqc-representable-descent).
7. The fibre-product universal property identifies the restricted functor with
   Isom of the base-changed torsors. Yoneda full faithfulness gives the canonical
   comparison isomorphism with its displayed adjunction normalization. Evaluation
   at the terminal Y-scheme gives the assertion about sections.
-/
theorem exists_smooth_affine_isomRepresentation
    (P Q : RepresentedRightTorsor H Y) [Smooth H.X.hom] [IsAffineHom H.X.hom] :
    ∃ R : IsomRepresentation P Q (𝟭 (Over Y)),
      IsAffineHom R.space.hom.left ∧ Smooth R.space.hom.left ∧
      (IsAffine Y.left → IsAffine R.space.left.left) ∧
      ∀ (Z : Over S) (g : Z ⟶ Y),
        ∃ R' : IsomRepresentation P Q (Over.map g),
          ∃ k : (Over.pullback g).obj R.space ⟶ R'.space,
            IsIso k ∧ ∀ (T : Over Z) (a : T ⟶ (Over.pullback g).obj R.space),
              R'.equiv T (a ≫ k) = R.equiv ((Over.map g).obj T)
                (((Over.mapPullbackAdj g).homEquiv T R.space).symm a) := by
  sorry

end AlgebraicGeometry.RepresentedRightTorsor

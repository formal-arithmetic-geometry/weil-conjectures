/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import WeilConjectures.AlgebraicGeometry.Thickening
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition

/-! # Versality is stable under generalization

Source: Stacks Project, Artin's Axioms, Tag 0G2K, lemma-generalization-versality;
definition-RS-star, definition-limit-preserving and definition-versal
(blueprint: lem-sfb-artin-versality-generalization).

The general-base helpers unpack the notions written inline in this node. Unlike the
integer-base Artin criterion, they apply to arbitrary schemes over Spec Lambda.
Arrows in the existing total category encode the specified pullback isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ArtinVersality

/-- Objects in the existing fibre, with all their automorphisms.
Source: Stacks, Categories, Tag 003T
(blueprint: lem-sfb-artin-versality-generalization). -/
abbrev Object {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) (T : Over S) :=
  Functor.Fiber F.p T

/-- An arrow over the specified base map; in a fibred groupoid it is cartesian and
therefore retains the actual pullback identification.
Source: Stacks, Categories, Tag 003T
(blueprint: lem-sfb-artin-versality-generalization). -/
abbrev Lift {S : Scheme.{u}} {F : BasedCategory.{v, w} (Over S)} {T U : Over S}
    (a : T ⟶ U) (x : Object F T) (y : Object F U) :=
  {b : x.val ⟶ y.val // F.p.IsHomLift a b}

/-- Every object over a directed affine limit descends to one stage.
Source: Stacks, Artin's Axioms, definition-limit-preserving
(blueprint: lem-sfb-artin-versality-generalization). -/
def ObjectsDescend {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D),
    (∀ i : I, IsAffine (D.obj (op i)).left) → IsAffine c.pt.left →
    Nonempty (IsLimit c) → ∀ x : Object F c.pt,
      ∃ (i : I) (xi : Object F (D.obj (op i))), Nonempty (Lift (c.π.app (op i)) x xi)

/-- Arrows descend to a common later stage, with their given limit identifications.
Source: Stacks, Artin's Axioms, definition-limit-preserving
(blueprint: lem-sfb-artin-versality-generalization). -/
def ArrowsDescend {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D),
    (∀ i : I, IsAffine (D.obj (op i)).left) → IsAffine c.pt.left →
    Nonempty (IsLimit c) → ∀ (i : I) (xi yi : Object F (D.obj (op i)))
      (x y : Object F c.pt) (px : Lift (c.π.app (op i)) x xi)
      (py : Lift (c.π.app (op i)) y yi) (a : x ⟶ y),
      ∃ (j : I) (hij : i ≤ j) (xj yj : Object F (D.obj (op j)))
        (qx : Lift (D.map (homOfLE hij).op) xj xi)
        (qy : Lift (D.map (homOfLE hij).op) yj yi)
        (rx : Lift (c.π.app (op j)) x xj) (ry : Lift (c.π.app (op j)) y yj)
        (b : xj ⟶ yj),
        rx.val ≫ qx.val = px.val ∧ ry.val ≫ qy.val = py.val ∧
          a.val ≫ ry.val = rx.val ≫ b.val

/-- Equality of arrows detected at the limit holds at a later stage.
Source: Stacks, Artin's Axioms, definition-limit-preserving
(blueprint: lem-sfb-artin-versality-generalization). -/
def ArrowEqualitiesDescend {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ∀ (I : Type u) [Preorder I] [IsDirectedOrder I] [Nonempty I]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D),
    (∀ i : I, IsAffine (D.obj (op i)).left) → IsAffine c.pt.left →
    Nonempty (IsLimit c) → ∀ (i : I) (xi yi : Object F (D.obj (op i)))
      (a b : xi ⟶ yi) (x : Object F c.pt) (px : Lift (c.π.app (op i)) x xi),
      px.val ≫ a.val = px.val ≫ b.val →
      ∃ (j : I) (hij : i ≤ j) (xj : Object F (D.obj (op j)))
        (qx : Lift (D.map (homOfLE hij).op) xj xi), qx.val ≫ a.val = qx.val ≫ b.val

/-- Limit preservation includes objects, isomorphisms, and equality of isomorphisms.
Source: Stacks, Artin's Axioms, definition-limit-preserving
(blueprint: lem-sfb-artin-versality-generalization). -/
def IsLimitPreserving {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ObjectsDescend F ∧ ArrowsDescend F ∧ ArrowEqualitiesDescend F

/-- Strong Rim--Schlessinger in total-category form. An affine pushout along a first
order thickening is Spec of the ring fibre product. The common object `x` and the two
cartesian arrows retain the specified isomorphism over the common ring. A pushout of
these arrows expresses both existence of a glued object and unique gluing of arrows,
so gives equivalence of groupoids, not just surjectivity on isomorphism classes.
Source: Stacks, Artin's Axioms, definition-RS-star
(blueprint: lem-sfb-artin-versality-generalization). -/
def IsRimSchlessingerStar {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S)) : Prop :=
  ∀ (A B B' P : Over S), IsAffine A.left → IsAffine B.left → IsAffine B'.left →
    ∀ (a : B ⟶ A) (b : B ⟶ B') (i : A ⟶ P) (j : B' ⟶ P),
      IsFirstOrderThickening b.left → IsPushout a b i j →
      ∀ (x : Object F B) (y : Object F A) (z : Object F B')
        (f : Lift a x y) (g : Lift b x z),
        ∃ (q : Object F P) (h : Lift i y q) (k : Lift j z q),
          IsPushout f.val g.val h.val k.val

/-- The Artinian local lifting condition, retaining the specified reduction isomorphism.
The surjection `r` to the actual residue field marks A; its composite with `q` marks
A'. Since both rings are local, these surjections have the respective maximal ideals
as kernels. Thus no embedding of the residue field into either ring is imposed.
The point equation fixes the residue marking, and `b ≫ d = c` extends exactly the
specified pullback identification.
Source: Stacks, Artin's Axioms, definition-versal and equation-hat-x
(blueprint: lem-sfb-artin-versality-generalization). -/
def IsVersalAt {S : Scheme.{u}} (F : BasedCategory.{v, w} (Over S))
    (U : Over S) (x : Object F U) (u₀ : U.left) : Prop :=
  ∀ (A' A : CommRingCat.{u}) [IsArtinianRing A'] [IsLocalRing A']
    [IsArtinianRing A] [IsLocalRing A] (q : A' ⟶ A),
    Function.Surjective q.hom → IsNilpotent (RingHom.ker q.hom) →
    ∀ (r : A ⟶ U.left.residueField u₀), Function.Surjective r.hom →
    ∀ (s' : Spec A' ⟶ S) (a : Over.mk (Spec.map q ≫ s') ⟶ U),
      Spec.map r ≫ a.left = U.left.fromSpecResidueField u₀ →
    ∀ (y' : Object F (Over.mk s')) (y : Object F (Over.mk (Spec.map q ≫ s')))
      (b : Lift (Over.homMk (Spec.map q) rfl) y y') (c : Lift a y x),
      ∃ (a' : Over.mk s' ⟶ U) (d : Lift a' y' x),
        Spec.map q ≫ a'.left = a.left ∧ b.val ≫ d.val = c.val

/-- Versality at a finite-type specialization implies versality at the original point.
Source: Stacks, Artin's Axioms, Tag 0G2K, lemma-generalization-versality,
specialized to an affine Noetherian base
(blueprint: lem-sfb-artin-versality-generalization).

1. Choose an affine finite-type neighbourhood of u₀ in U. It contains u because
u specializes to u₀. Artinian local spectra have one point, so the lifting definition
of versality is unchanged by this restriction.
2. If x is not versal at u, lem-sfb-artin-single-point-obstruction supplies a square-zero
thickening U -> T and an extension y, with no retraction arrow near u. Its hypotheses
are the Noetherian base, finite type point, and strong Rim--Schlessinger condition.
3. Express the coordinate ring of T as the directed union of finite-type base
subalgebras. By lem-weil-pbc-limit-affine-transition and limit preservation, y descends
to x' over a finite-type affine U'. Enlarge the subalgebra to surject onto the coordinate
ring of U. Then U -> U' is a first order thickening.
4. The diagonal hypothesis represents the comparison by an algebraic space Z, with a
map i : U -> Z and projections p : Z -> U, q : Z -> U'. By
lem-sfb-artin-noetherian-versal-base-change, q is smooth on an open neighbourhood of
i(u₀), whose inverse image in U also contains u.
5. Shrink to corresponding principal affine opens in U, U', T. By
lem-sfb-smooth-space-affine-infinitesimal-lift, i lifts across U -> U'. Pulling back
and inverting the universal comparison gives an arrow x' -> x whose reduction is
the identity. Compose y -> x' -> x to contradict the obstruction in step 2.
-/
theorem isVersalAt_of_specializes
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (F : BasedCategory.{v, w} (Over (Spec (.of R))))
    (hFibred : IsFibredInGroupoids F) (hDiagonal : HasAlgebraicSpaceDiagonal F)
    (hRS : IsRimSchlessingerStar F) (hLimits : IsLimitPreserving F)
    (U : Over (Spec (.of R))) [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (x : Object F U) (u u₀ : U.left)
    (hu : LocallyOfFiniteType (U.left.fromSpecResidueField u) ∧
      QuasiCompact (U.left.fromSpecResidueField u))
    (hu₀ : LocallyOfFiniteType (U.left.fromSpecResidueField u₀) ∧
      QuasiCompact (U.left.fromSpecResidueField u₀))
    (hsp : u ⤳ u₀) (hx : IsVersalAt F U x u₀) :
    IsVersalAt F U x u := by
  sorry

end AlgebraicGeometry.ArtinVersality

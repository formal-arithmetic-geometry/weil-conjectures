/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.RegularGroupSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedSubspace
public import Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Constructible
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
import Sheaf.AlgebraicGeometry.LocallySeparatedGroupSpaceScheme
import Sheaf.AlgebraicGeometry.SchemeProductDimension
import WeilConjectures.AlgebraicGeometry.Dimension
import Sheaf.AlgebraicGeometry.FiniteTypeFibreImageDimensionBounds
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Bad tuples of translates in a smooth group algebraic space

Source: Deligne, Le lemme de Gabber, Lemma 4.6, printed p.144; Stacks Project,
Tags 03IQ, 0ECX, 0B2M and 0B2L
(blueprint: lem-sfb-translate-bad-tuple-dimension).

The tuple and incidence spaces are specified by their functors of points, and the
incidence closed subspace by reducedness and its support. No representing object is
chosen from a bare existence assertion. The group functor need not be commutative.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace.TranslateBadTuple

/-- The explicit finite power of a presheaf, with componentwise restriction.
Source: the tuple space in Deligne 4.6
(blueprint: lem-sfb-translate-bad-tuple-dimension). -/
def tuples {S : Scheme.{u}} (P : (Over S)ᵒᵖ ⥤ Type u) (n : ℕ) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj U := Fin n → P.obj U
  map f := ↾fun g j ↦ P.map f (g j)
  map_id U := by ext g j; simp
  map_comp f g := by ext a j; simp

/-- Forget the first entry `x` of `(x,g₁,...,gₙ)`.
Source: the incidence projection in Deligne 4.6
(blueprint: lem-sfb-translate-bad-tuple-dimension). -/
def tail {S : Scheme.{u}} (P : (Over S)ᵒᵖ ⥤ Type u) (n : ℕ) :
    tuples P (n + 1) ⟶ tuples P n where
  app _ := ↾fun g j ↦ g j.succ

/-- The actual incidence map `(x,g) ↦ gⱼ⁻¹x`, in the specified order.
Source: Deligne 4.6, incidence construction
(blueprint: lem-sfb-translate-bad-tuple-dimension). -/
def difference {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ GrpCat.{u}) (n : ℕ) (j : Fin n) :
    tuples (F ⋙ forget GrpCat) (n + 1) ⟶ F ⋙ forget GrpCat where
  app U := ↾fun g ↦ (g j.succ)⁻¹ * g 0
  naturality U W f := by
    ext g
    exact (((F.map f).hom.map_mul (g j.succ)⁻¹ (g 0)).trans
      (congrArg (fun z ↦ z * (F.map f) (g 0)) ((F.map f).hom.map_inv (g j.succ)))).symm

/-- The existing presheaf pullback defining a geometric fibre over `s`.
Source: Stacks, Tag 03H4, used in Deligne 4.6
(blueprint: lem-sfb-translate-bad-tuple-dimension). -/
abbrev fibre {S : Scheme.{u}} (X : AlgebraicSpace S) {K : Type u} [Field K]
    (s : Spec (.of K) ⟶ S) : (Over S)ᵒᵖ ⥤ Type u :=
  Limits.pullback (groupSpaceProjection X).hom.hom
    (yoneda.map (Over.homMk (U := Over.mk s) (V := Over.mk (𝟙 S)) s (by simp)))

/-- The canonical map from the fibre to the original space.
Source: Stacks, Tag 03H4, used in Deligne 4.6
(blueprint: lem-sfb-translate-bad-tuple-dimension). -/
def fibreProjection {S : Scheme.{u}} (X : AlgebraicSpace S) {K : Type u} [Field K]
    (s : Spec (.of K) ⟶ S) : fibre X s ⟶ X.obj.obj :=
  Limits.pullback.fst (groupSpaceProjection X).hom.hom
    (yoneda.map (Over.homMk (U := Over.mk s) (V := Over.mk (𝟙 S)) s (by simp)))

/-- A geometric tuple is bad if, after an algebraically closed field extension,
there is an `x` outside every left translate. Membership is in the actual open subfunctor.
Source: Deligne 4.6 and the geometric-tuple convention of the node
(blueprint: lem-sfb-translate-bad-tuple-dimension). -/
def geometricBad {S : Scheme.{u}} {H : AlgebraicSpace S}
    (F : (Over S)ᵒᵖ ⥤ GrpCat.{u}) (e : F ⋙ forget GrpCat ≅ H.obj.obj)
    (V : OpenSubspace H) (n : ℕ)
    (a : PointRepresentative (tuples (F ⋙ forget GrpCat) n)) : Prop :=
  ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (s : Spec (.of L) ⟶ S)
    (i : Over.mk s ⟶ Over.mk a.base) (x : F.obj (op (Over.mk s))),
    ∀ j : Fin n,
      e.hom.app _ (((F.map i.op) (a.value j))⁻¹ * x) ∉ V.val.obj (op (Over.mk s))

/-- Bad geometric tuple classes, with the residue-field extension explicitly retained.
Source: Deligne 4.6 (blueprint: lem-sfb-translate-bad-tuple-dimension). -/
def geometricBadPoints {S : Scheme.{u}} {H : AlgebraicSpace S}
    (F : (Over S)ᵒᵖ ⥤ GrpCat.{u}) (e : F ⋙ forget GrpCat ≅ H.obj.obj)
    (V : OpenSubspace H) (n : ℕ) : Set (Point (tuples (F ⋙ forget GrpCat) n)) :=
  {p | ∃ a : PointRepresentative (tuples (F ⋙ forget GrpCat) n),
    Quot.mk _ a = p ∧ geometricBad F e V n a}

/-- The closed incidence support: every `gⱼ⁻¹x` lies outside `V`. The image of a point
class under `gⱼ⁻¹x` is read on a field-valued representative; it does not depend on it.
Source: Deligne 4.6, incidence construction
(blueprint: lem-sfb-translate-bad-tuple-dimension). -/
def incidenceSupport {S : Scheme.{u}} {H : AlgebraicSpace S}
    (F : (Over S)ᵒᵖ ⥤ GrpCat.{u}) (e : F ⋙ forget GrpCat ≅ H.obj.obj)
    (V : OpenSubspace H) (n : ℕ) (M : AlgebraicSpace S)
    (eM : M.obj.obj ≅ tuples (F ⋙ forget GrpCat) (n + 1)) : Set (Point M.obj.obj) :=
  {p | ∃ a : PointRepresentative M.obj.obj, (Quot.mk _ a : Point M.obj.obj) = p ∧
    ∀ j : Fin n, (Quot.mk _ (a.map (eM.hom ≫ difference F n j ≫ e.hom)) :
      Point H.obj.obj) ∉ pointImage V.val.ι}

/-- The image `Zₙ` of the reduced incidence subspace under the actual tuple projection.
Source: Deligne 4.6 (blueprint: lem-sfb-translate-bad-tuple-dimension). -/
def locus {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ GrpCat.{u}) (n : ℕ)
    {X M : AlgebraicSpace S} (eX : X.obj.obj ≅ tuples (F ⋙ forget GrpCat) n)
    (eM : M.obj.obj ≅ tuples (F ⋙ forget GrpCat) (n + 1)) (E : ClosedSubspace M) :
    Set (Point X.obj.obj) :=
  pointImage (E.val.arrow.hom.hom ≫ eM.hom ≫ tail (F ⋙ forget GrpCat) n ≫ eX.inv)

/-- Constructibility, geometric identification and dimension of the bad tuple locus.
The existential presentations are the actual finite products, identified on every test
scheme by `eX` and `eM`; reducedness and support specify the reduced induced `Eₙ`.
Finite presentation of `X → S` is local finite presentation together with
quasi-compactness of the structure map and of its relative diagonal, written out as
compactness of point spaces over affine tests. Inverse images of point sets under the
fibre inclusion are read on field-valued representatives.

Source: Deligne, Le lemme de Gabber, Lemma 4.6, printed p.144
(blueprint: lem-sfb-translate-bad-tuple-dimension).

Proof (agent-written: the local Deligne PDF is WANTED):
1. The finite products exist by lem-trf-space-fibre-products-etale-covers; smoothness,
separatedness and finite presentation follow from
lem-sfb-fibred-groupoid-representable-smooth-calculus,
lem-sfb-space-flat-proper-fp-locality and lem-sfb-space-separated-fp-composition.
2. The inverse images of the complement of V under the difference maps intersect in a
closed support. Apply lem-sfb-space-reduced-closed-support. Its projection is finite type:
the ambient spaces are finite presentation over the Noetherian base, hence Noetherian,
by lem-sfb-space-fp-qcqs-source and pqf-lem-locnoeth-lft. Closed immersions are finite type.
Then lem-sfb-noetherian-space-chevalley-image gives constructibility of its image.
3. lem-a1-space-point-open-calculus identifies this image after any base change with
the image of the incidence fibre. Extending a tuple's residue field to an algebraic
closure identifies this with failure of the finite translates to cover the fibre.
4. Each geometric group fibre G is a scheme by
lem-sfb-locally-separated-group-space-scheme. Its open V is nonempty and its closed
complement C has dimension at most d-1, or is empty when d=0.
5. The automorphism (x,gⱼ) ↦ (x,gⱼ⁻¹x), inverse (x,cⱼ) ↦ (x,xcⱼ⁻¹), identifies
incidence supports with G times C^n; lem-sfb-space-reduced-closed-support justifies this
without assuming that reduction commutes with base change. Use
lem-weil-pbc-homeomorphism-krull-dimension, lem-sfb-scheme-product-dimension and
lem-pc-scheme-dimension-local-rings to obtain d+n(d-1); then
lem-zl-finite-type-fibre-image-dimension-bounds bounds the image closure. Adding n
gives the displayed inequality, including the empty case where the dimension is bottom.
6. lem-sbc-equidimensional-open-local-dimension gives constant local dimension d on G.
Induct using lem-sbc-smooth-relative-dimension-permanence to give relative dimension nd
on G^n. Apply lem-sbc-constant-local-dimension-components to obtain purity; the identity
supplies a point. The finite-type fibre is locally Noetherian by pqf-lem-locnoeth-lft.
7. For d=0 the complement C and hence every incidence fibre are empty. Geometric-point
lifting from lem-a1-space-point-open-calculus forces the total incidence space and image
empty, including over an empty base. -/
theorem translate_bad_tuple_dimension {S : Scheme.{u}} [IsNoetherian S]
    (H : AlgebraicSpace S) (F : (Over S)ᵒᵖ ⥤ GrpCat.{u})
    (e : F ⋙ forget GrpCat ≅ H.obj.obj) (hH : IsSmoothIntegralGroupSpace H)
    (V : OpenSubspace H) (hVqc : IsCompact (pointImage V.val.ι))
    (hV : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
      Nonempty (V.val.obj (op (Over.mk s))))
    (d : ℕ) (hd : ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
      topologicalKrullDim (Point (fibre H s)) = (d : WithBot ℕ∞))
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (X M : AlgebraicSpace S)
      (eX : X.obj.obj ≅ tuples (F ⋙ forget GrpCat) n)
      (eM : M.obj.obj ≅ tuples (F ⋙ forget GrpCat) (n + 1)) (E : ClosedSubspace M),
      IsReduced (E.val : AlgebraicSpace S) ∧
      pointImage E.val.arrow.hom.hom = incidenceSupport F e V n M eM ∧
      Topology.IsConstructible (locus F n eX eM E) ∧
      MapIsLocally (@Smooth) (groupSpaceProjection X) ∧
      MapIsSeparated (groupSpaceProjection X) ∧
      MapIsLocallyOfFinitePresentation (groupSpaceProjection X) ∧
      (∀ (T : Over S) (a : yoneda.obj T ⟶ (groupSpaceBase S).obj.obj), IsAffine T.left →
        CompactSpace (Point (Limits.pullback (groupSpaceProjection X).hom.hom a))) ∧
      (∀ (T : Over S) (a : yoneda.obj T ⟶ Limits.pullback (groupSpaceProjection X).hom.hom
          (groupSpaceProjection X).hom.hom), IsAffine T.left →
        CompactSpace (Point (Limits.pullback
          (pullback.diagonal (groupSpaceProjection X).hom.hom) a))) ∧
      (∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (.of K) ⟶ S),
        Nonempty (Point (fibre X s)) ∧
        (∀ C ∈ irreducibleComponents (Point (fibre X s)),
          topologicalKrullDim C = (n * d : WithBot ℕ∞)) ∧
        (∀ a : PointRepresentative (fibre X s),
          (Quot.mk _ (a.map (fibreProjection X s)) : Point X.obj.obj) ∈
              locus F n eX eM E ↔
            (Quot.mk _ (a.map (fibreProjection X s ≫ eX.hom)) :
              Point (tuples (F ⋙ forget GrpCat) n)) ∈ geometricBadPoints F e V n) ∧
        topologicalKrullDim
          (closure {q : Point (fibre X s) | ∃ a : PointRepresentative (fibre X s),
            (Quot.mk _ a : Point (fibre X s)) = q ∧
              (Quot.mk _ (a.map (fibreProjection X s)) : Point X.obj.obj) ∈
                locus F n eX eM E}) +
            (n : WithBot ℕ∞) ≤ (n * d + d : WithBot ℕ∞)) ∧
      (d = 0 → IsEmpty (Point (E.val : AlgebraicSpace S).obj.obj) ∧
        locus F n eX eM E = ∅) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace.TranslateBadTuple

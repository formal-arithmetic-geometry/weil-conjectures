/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q134
-/
module

public import Sheaf.AlgebraicGeometry.FiniteClosedCoverResolution
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Augmented rows of finite closed intersections

Source: Stacks Project, proetale.tex, Tags 09AA, 09BM and 09AH; the finite-intersection
and signed-insertion construction in lem-sfb-closed-intersection-vertex-contraction.
(blueprint: def-sfb-closed-intersection-augmented-row).

The existing finite closed intersection and restriction functors are reused. The empty
index denotes Z, rather than the empty product X. Finite products are the canonical finite
biproducts. All comparison and homotopy components are natural transformations of actual
module functors; no construction is selected from an uncharacterized existence theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtaleTensorComparison

namespace AlgebraicGeometry.ClosedIntersection

attribute [local irreducible] proEtaleModuleInverseImage
  proEtaleRingedDirectImage ringComp moduleComp

/-- The empty intersection is the augmentation scheme Z; other intersections are the
existing finite products over X. Source: Stacks, Tag 09AH, finite-intersection construction
(blueprint: def-sfb-closed-intersection-augmented-row). -/
def intersection {X Z : Scheme.{u}} (i : Z ⟶ X) {m : ℕ} (W : Fin m → Over X)
    (s : Finset (Fin m)) : Over X :=
  if s = ∅ then Over.mk i else finiteClosedIntersection W s

/-- The actual closed restriction, including the augmentation at the empty index.
Source: Stacks, Tag 09AH (blueprint: def-sfb-closed-intersection-augmented-row). -/
def term {X Z : Scheme.{u}} (i : Z ⟶ X) {m : ℕ} (W : Fin m → Over X)
    (A : Rings X) (s : Finset (Fin m)) : Modules A ⥤ Modules A :=
  finiteClosedRestriction (intersection i W s).hom A

/-- Its prescribed section-normalized adjunction unit.
Source: Stacks, Tag 09AH (blueprint: def-sfb-closed-intersection-augmented-row). -/
def unit {X Z : Scheme.{u}} (i : Z ⟶ X) {m : ℕ} (W : Fin m → Over X)
    (A : Rings X) (s : Finset (Fin m)) : 𝟭 (Modules A) ⟶ term i W A s :=
  finiteClosedUnit (intersection i W s).hom A

attribute [local irreducible] intersection

/-- Indices of augmented degree p: the empty index has degree -1.
Source: Stacks, Tag 09AH, signed finite row
(blueprint: def-sfb-closed-intersection-augmented-row). -/
abbrev Degree (m : ℕ) (p : ℤ) := {s : Finset (Fin m) // (s.card : ℤ) - 1 = p}

/-- The finite product of intersection terms in augmented degree p.
Source: Stacks, Tag 09AH, signed finite row
(blueprint: def-sfb-closed-intersection-augmented-row). -/
def graded {X Z : Scheme.{u}} (i : Z ⟶ X) {m : ℕ} (W : Fin m → Over X)
    (A : Rings X) (p : ℤ) : Modules A ⥤ Modules A :=
  ∏ᶜ fun s : Degree m p ↦ term i W A s.1

/-- The displayed alternating differential, including the empty-to-singleton unit.
The two finite sums are its matrix formula; the only nonzero entry deletes one vertex.
Source: Stacks, Tag 09AH, signed finite row
(blueprint: def-sfb-closed-intersection-augmented-row). -/
def differential {X Z : Scheme.{u}} (i : Z ⟶ X) {m : ℕ} (W : Fin m → Over X)
    (A : Rings X) (r : ∀ s t, term i W A s ⟶ term i W A t) (p q : ℤ) :
    graded i W A p ⟶ graded i W A q :=
  Pi.lift fun t ↦ ∑ s : Degree m p, ∑ a : Fin m,
    if p + 1 = q ∧ a ∈ t.1 ∧ t.1.erase a = s.1 then
      (-1 : ℤ) ^ (t.1.filter (· < a)).card •
        (Pi.π (fun z : Degree m p ↦ term i W A z.1) s ≫ r s.1 t.1)
    else 0

/-- An augmented row with its exact terms and faces. The unit equation fixes each
restriction to the pushed actual unit: closed restriction units are epimorphisms under
the hypotheses of the theorem. Non-inclusions have zero matrix entry. No exactness or
contractibility is included in these data.
Source: Stacks, Tags 09AA and 09AH, signed finite row
(blueprint: def-sfb-closed-intersection-augmented-row). -/
structure Row {X Z : Scheme.{u}} (i : Z ⟶ X) {m : ℕ} (W : Fin m → Over X)
    (A : Rings X) where
  restriction : ∀ s t, term i W A s ⟶ term i W A t
  restriction_unit : ∀ s t, s ⊆ t → unit i W A s ≫ restriction s t = unit i W A t
  restriction_zero : ∀ s t, ¬s ⊆ t → restriction s t = 0
  rows : Modules A ⥤ CochainComplex (Modules A) ℤ
  additive : rows.Additive
  terms : ∀ p, rows ⋙ HomologicalComplex.eval _ _ p ≅ graded i W A p
  differential : ∀ M p q,
    (terms p).inv.app M ≫ (rows.obj M).d p q ≫ (terms q).hom.app M =
      (ClosedIntersection.differential i W A restriction p q).app M

/-- Projection onto an indicated summand, in any equal presentation of its degree.
Source: Stacks, Tag 09AH (blueprint: def-sfb-closed-intersection-augmented-row). -/
def Row.projection {X Z : Scheme.{u}} {i : Z ⟶ X} {m : ℕ} {W : Fin m → Over X}
    {A : Rings X} (D : Row i W A) (p : ℤ) (s : Finset (Fin m))
    (hs : (s.card : ℤ) - 1 = p) :
    D.rows ⋙ HomologicalComplex.eval _ _ p ⟶ term i W A s :=
  (D.terms p).hom ≫ Pi.π (fun t : Degree m p ↦ term i W A t.1) ⟨s, hs⟩


/-- The coefficient comparison in the actual fibre-product square, built from the
unit-normalized ring compositors and the pullback equation.
Source: Stacks, Tags 03CB, 03CC and 09AA
(blueprint: def-sfb-closed-intersection-augmented-row). -/
def squareCoefficients {X Y T : Scheme.{u}} (g : Y ⟶ X) (f : T ⟶ X) (A : Rings X) :
    inverseRing (pullback.fst g f) (inverseRing g A) ≅
      inverseRing (pullback.snd g f) (inverseRing f A) :=
  (ringComp (pullback.fst g f) g A).symm ≪≫
    eqToIso (congrArg (fun h ↦ inverseRing h A) (pullback.condition (f := g) (g := f))) ≪≫
      ringComp (pullback.snd g f) f A

/-- Inverse image on the second side of the square, with scalars transported back by
the canonical coefficient comparison. Source: Stacks, Tags 03CB and 03CC
(blueprint: def-sfb-closed-intersection-augmented-row). -/
def squarePullback {X Y T : Scheme.{u}} (g : Y ⟶ X) (f : T ⟶ X) (A : Rings X) :
    Modules (inverseRing f A) ⥤
      Modules (inverseRing (pullback.fst g f) (inverseRing g A)) :=
  inverse (pullback.snd g f) (inverseRing f A) ⋙
    ProEtaleTensorComparison.restrict (squareCoefficients g f A).hom

/-- Forget only scalars from a module-sheaf map, retaining its actual abelian map.
Source: Stacks, Section 03EK
(blueprint: def-sfb-closed-intersection-augmented-row). -/
def underlyingMap {X : Scheme.{u}} {A : Rings X} {M N : Modules A} (f : M ⟶ N) :
    M.val.presheaf ⟶ N.val.presheaf :=
  ((SheafOfModules.toSheaf (proEtaleModuleCoefficients A)).map f).hom

attribute [local irreducible] squareCoefficients

/-- Pasting of test objects around the fibre-product square.
Source: Stacks, Tags 03CB and 03CC
(blueprint: def-sfb-closed-intersection-augmented-row). -/
def squareTestIso {X Y T : Scheme.{u}} (g : Y ⟶ X) (f : T ⟶ X) (V : X.ProEt) :
    (proEtaleBaseChange (pullback.fst g f)).obj ((proEtaleBaseChange g).obj V) ≅
      (proEtaleBaseChange (pullback.snd g f)).obj ((proEtaleBaseChange f).obj V) :=
  ((MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
      (pullback.fst g f) g).app V).symm ≪≫
    eqToIso (congrArg (fun k ↦ (proEtaleBaseChange k).obj V)
      (pullback.condition (f := g) (g := f))) ≪≫
    (MorphismProperty.Over.pullbackComp (P := @WeaklyEtale) (Q := ⊤)
      (pullback.snd g f) f).app V

/-- The base-change isomorphism together with its canonical mate characterization.
The first equation fixes delta by the existing section-normalized module compositors,
after forgetting scalars; hence delta and beta cannot be replaced by scalar twists.
Source: Stacks, Tags 09AA, 03CB and 03CC; closed base-change consequence
(blueprint: def-sfb-closed-intersection-augmented-row). -/
structure BaseChange {X Y T : Scheme.{u}} (g : Y ⟶ X) (f : T ⟶ X) (A : Rings X) where
  delta : inverse g A ⋙ inverse (pullback.fst g f) (inverseRing g A) ≅
    inverse f A ⋙ squarePullback g f A
  normalized : ∀ (M : Modules A) (V : X.ProEt) (s : M.val.obj (op V)),
    (delta.hom.app M).val.app
        (op ((proEtaleBaseChange (pullback.fst g f)).obj ((proEtaleBaseChange g).obj V)))
        (inverseSection (pullback.fst g f) ((inverse g A).obj M)
          ((proEtaleBaseChange g).obj V) (inverseSection g M V s)) =
      ((inverse (pullback.snd g f) (inverseRing f A)).obj ((inverse f A).obj M)).val.map
        (squareTestIso g f V).hom.op
        (inverseSection (pullback.snd g f) ((inverse f A).obj M)
          ((proEtaleBaseChange f).obj V) (inverseSection f M V s))
  beta : proEtaleRingedDirectImage f A ⋙ inverse g A ≅
    squarePullback g f A ⋙ proEtaleRingedDirectImage (pullback.fst g f) (inverseRing g A)
  mate : ∀ N,
    ((ProEtaleClosedProjection.adjunction (pullback.fst g f) (inverseRing g A)).homEquiv
      _ _).symm (beta.hom.app N) =
      delta.hom.app ((proEtaleRingedDirectImage f A).obj N) ≫
        (squarePullback g f A).map ((ProEtaleClosedProjection.adjunction f A).counit.app N)


/-- The intersection direct image on the base, with its actual inverse-image ring
transport. Source: Stacks, Tag 09AA
(blueprint: def-sfb-closed-intersection-augmented-row). -/
def baseChangedTerm {X Y T : Scheme.{u}} (g : Y ⟶ X) (f : T ⟶ X) (A : Rings X) :
    Modules A ⥤ Modules (inverseRing g A) :=
  inverse f A ⋙ squarePullback g f A ⋙
    proEtaleRingedDirectImage (pullback.fst g f) (inverseRing g A)

/-- The canonical closed base-change comparison applied to the restricted module.
Source: Stacks, Tag 09AA (blueprint: def-sfb-closed-intersection-augmented-row). -/
def BaseChange.termIso {X Y T : Scheme.{u}} {g : Y ⟶ X} {f : T ⟶ X} {A : Rings X}
    (B : BaseChange g f A) : finiteClosedRestriction f A ⋙ inverse g A ≅
      baseChangedTerm g f A :=
  Functor.isoWhiskerLeft (inverse f A) B.beta

/-- Open restriction compatibility, including units, every face, and every summand of
the augmented row. The base-change mates retain the actual coefficient identifications.
Source: Stacks, Tags 09AA and 09AH; restriction to the localized site
(blueprint: def-sfb-closed-intersection-augmented-row). -/
structure OpenCompatibility {X Z Y : Scheme.{u}} {i : Z ⟶ X} {m : ℕ}
    {W : Fin m → Over X} {A : Rings X} (D : Row i W A) (g : Y ⟶ X)
    (D' : Row (pullback.fst g i) (finiteClosedPullbackFamily W g) (inverseRing g A)) where
  baseChange : ∀ s, BaseChange g (intersection i W s).hom A
  comparison : ∀ s, term i W A s ⋙ inverse g A ≅
    inverse g A ⋙ term (pullback.fst g i) (finiteClosedPullbackFamily W g) (inverseRing g A) s
  units : ∀ s M,
    (inverse g A).map ((unit i W A s).app M) ≫ (comparison s).hom.app M =
      (unit (pullback.fst g i) (finiteClosedPullbackFamily W g) (inverseRing g A) s).app
        ((inverse g A).obj M)
  faces : ∀ s t M,
    (inverse g A).map ((D.restriction s t).app M) ≫ (comparison t).hom.app M =
      (comparison s).hom.app M ≫ (D'.restriction s t).app ((inverse g A).obj M)
  rowIso : D.rows ⋙ finiteClosedPullbackComplex g A ≅ inverse g A ⋙ D'.rows
  components : ∀ p s (hs : (s.card : ℤ) - 1 = p) M,
    (rowIso.hom.app M).f p ≫ (D'.projection p s hs).app ((inverse g A).obj M) =
      (inverse g A).map ((D.projection p s hs).app M) ≫ (comparison s).hom.app M


set_option maxHeartbeats 800000 in
-- The full signed matrix uses both functor and complex evaluations.
/-- Vertex insertion with its exact sign and both inverse identities. Its empty-output
component is the inverse of the pulled-back singleton augmentation. The homotopy equation
is imposed in every integer degree, including both endpoints. All maps are natural and
linear in the module. Source: Stacks, Tags 09AA and 09AH; signed-insertion deduction
(blueprint: def-sfb-closed-intersection-augmented-row). -/
structure VertexContraction {X Z : Scheme.{u}} {i : Z ⟶ X} {m : ℕ}
    {W : Fin m → Over X} {A : Rings X} (D : Row i W A) (a : Fin m) where
  baseChange : ∀ s, BaseChange (W a).hom (intersection i W s).hom A
  intersectionRestriction : ∀ s t,
    baseChangedTerm (W a).hom (intersection i W s).hom A ⟶
      baseChangedTerm (W a).hom (intersection i W t).hom A
  restriction_units : ∀ s t, s ⊆ t →
    Functor.whiskerRight (unit i W A s) (inverse (W a).hom A) ≫
        (baseChange s).termIso.hom ≫ intersectionRestriction s t =
      Functor.whiskerRight (unit i W A t) (inverse (W a).hom A) ≫
        (baseChange t).termIso.hom
  faces : ∀ s t, s ⊆ t →
    Functor.whiskerRight (D.restriction s t) (inverse (W a).hom A) ≫
        (baseChange t).termIso.hom =
      (baseChange s).termIso.hom ≫ intersectionRestriction s t
  unionIntersection : ∀ s,
    ∃ e : pullback (W a).hom (intersection i W s).hom ≅
        (intersection i W (insert a s)).left,
      e.hom ≫ (intersection i W (insert a s)).hom =
        pullback.fst (W a).hom (intersection i W s).hom ≫ (W a).hom
  augmentation : term i W A ∅ ⋙ inverse (W a).hom A ≅ inverse (W a).hom A
  augmentation_unit : ∀ M,
    (inverse (W a).hom A).map ((unit i W A ∅).app M) ≫ augmentation.hom.app M = 𝟙 _
  back : ∀ s, term i W A (insert a s) ⋙ inverse (W a).hom A ⟶
    term i W A s ⋙ inverse (W a).hom A
  left_inverse : ∀ s, a ∉ s →
    Functor.whiskerRight (D.restriction s (insert a s)) (inverse (W a).hom A) ≫ back s = 𝟙 _
  right_inverse : ∀ s, a ∉ s →
    back s ≫ Functor.whiskerRight (D.restriction s (insert a s)) (inverse (W a).hom A) = 𝟙 _
  h : ∀ p : ℤ,
    D.rows ⋙ HomologicalComplex.eval _ _ p ⋙ inverse (W a).hom A ⟶
      D.rows ⋙ HomologicalComplex.eval _ _ (p - 1) ⋙ inverse (W a).hom A
  component_zero : ∀ p s (hs : (s.card : ℤ) - 1 = p - 1), a ∈ s →
    h p ≫ Functor.whiskerRight (D.projection (p - 1) s hs) (inverse (W a).hom A) = 0
  component_insert : ∀ p s (hs : (s.card : ℤ) - 1 = p - 1)
    (ht : ((insert a s).card : ℤ) - 1 = p), a ∉ s →
    h p ≫ Functor.whiskerRight (D.projection (p - 1) s hs) (inverse (W a).hom A) =
      (-1 : ℤ) ^ (s.filter (· < a)).card •
        (Functor.whiskerRight (D.projection p (insert a s) ht) (inverse (W a).hom A) ≫ back s)
  contraction : ∀ (p : ℤ) (M : Modules A),
    @Add.add (End ((inverse (W a).hom A).obj ((D.rows.obj M).X p))) inferInstance
      ((h p).app M ≫ (inverse (W a).hom A).map ((D.rows.obj M).d (p - 1) p))
      ((inverse (W a).hom A).map ((D.rows.obj M).d p (p + 1)) ≫ (h (p + 1)).app M ≫
        (inverse (W a).hom A).map
          ((D.rows.obj M).XIsoOfEq (add_sub_cancel_right p 1)).hom) = 𝟙 _

end AlgebraicGeometry.ClosedIntersection

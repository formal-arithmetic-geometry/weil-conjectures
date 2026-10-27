/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q83
-/
module

public import Sheaf.AlgebraicGeometry.KnudsenPointedForgetfulUniversalCurve
public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Smooth labelled isomorphism fibres of a forgetful tower

Source: Knudsen, The projectivity of the moduli space of stable curves II (1983),
§2, especially Corollary 2.6 and the universal-curve interpretation, p.162
(blueprint: lem-sfb-smooth-marking-isomorphism-fibre-comparison).

The contraction data are the witnesses of the recorded Knudsen theorem, rather than
arbitrary functors. A square is tested by its actual comparison functor to the recorded
2-fibre product. Isomorphism pairs retain both the map of schemes and the entire labelled
isomorphism. Pullback naturality is expressed by the canonical cartesian-arrow equations.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace SmoothMarkingComparison

/-- The specified Knudsen contraction, with precisely the witnesses and normalization of
`exists_knudsen_pointed_forgetful_universal_curve`. This packages that recorded notion;
no functor or curve is selected from a mere existence assertion.
Source: Knudsen II §2, Corollary 2.6 and Theorem 2.7
(blueprint: lem-sfb-smooth-marking-isomorphism-fibre-comparison). -/
structure Contraction (S : Scheme.{u}) (g r : ℕ) where
  c : BasedFunctor (StablePointedModuli.based S g (r + 1))
    (StablePointedUniversalCurve.based S g r)
  s : BasedFunctor (StablePointedUniversalCurve.based S g r)
    (StablePointedModuli.based S g (r + 1))
  eta : ModuliTwoIso (BasedFunctor.id (StablePointedModuli.based S g (r + 1))) (c.comp s)
  epsilon : ModuliTwoIso (s.comp c)
    (BasedFunctor.id (StablePointedUniversalCurve.based S g r))
  contraction : ∀ Y : StablePointedModuli S g (r + 1), Y.curve ⟶ (c.obj Y).family.curve
  base_equation : ∀ Y : StablePointedModuli S g (r + 1),
    contraction Y ≫ (c.obj Y).family.projection =
      Y.projection ≫ eqToHom (congrArg Over.left (c.w_obj Y).symm)
  naturality : ∀ {Y Z : StablePointedModuli S g (r + 1)} (h : Y ⟶ Z),
    h.map ≫ contraction Z = contraction Y ≫ (c.map h).val.map
  old_markings : ∀ (Y : StablePointedModuli S g (r + 1)) (i : Fin r),
    Y.sections i.castSucc ≫ contraction Y =
      eqToHom (congrArg Over.left (c.w_obj Y).symm) ≫ (c.obj Y).family.sections i
  last_marking : ∀ Y : StablePointedModuli S g (r + 1),
    Y.sections (Fin.last r) ≫ contraction Y =
      eqToHom (congrArg Over.left (c.w_obj Y).symm) ≫ (c.obj Y).extra
  geometry : ∀ Y : StablePointedModuli S g (r + 1),
    StablePointedUniversalCurve.HasFiberGeometry Y (c.obj Y)
      (eqToHom (congrArg Over.left (c.w_obj Y).symm)) (contraction Y) (base_equation Y)
  represented : ∀ X : StablePointedModuli S g r,
    ∃ R : BasedFunctor
        (moduliTwoFiberProduct X.familyMap (StablePointedUniversalCurve.forgetful c))
        (discreteModuli (yoneda.obj X.totalScheme)),
      R.toFunctor.IsEquivalence ∧
      (∀ Z, (yoneda.preimage (R.obj Z).hom).left =
        eqToHom (congrArg Over.left (R.w_obj Z)) ≫
          StablePointedUniversalCurve.representedPoint c X Z) ∧
      (∀ Z, (yoneda.preimage (R.obj Z).hom).left ≫ X.projection =
        eqToHom (congrArg Over.left (R.w_obj Z)) ≫
          (yoneda.preimage Z.obj.left.hom).left) ∧
      IsProjectiveBundle X.projection ∧ Flat X.projection ∧
        LocallyOfFinitePresentation X.projection ∧ QuasiCompact X.projection ∧
        QuasiSeparated X.projection
  smooth_identity : ∀ X : StablePointedUniversalCurve S g r,
    Smooth X.family.projection →
    (∀ i : Fin r, Disjoint (Set.range X.extra) (Set.range (X.family.sections i))) →
    IsIso (contraction (s.obj X) ≫ (epsilon.val.hom.app X).val.map)
  stable_base_change : ∀ (X : StablePointedModuli S g r) (T : Over S) (a : T ⟶ X.base),
    IsStablePointedCurve (X.pullback T a).projection (X.pullback T a).sections
      (X.pullback T a).section_projection

/-- Postcomposition of actual test-scheme maps with a tower map.
Source: Knudsen II §2, the representable-groupoid convention
(blueprint: lem-sfb-smooth-marking-isomorphism-fibre-comparison). -/
abbrev schemeMap {S : Scheme.{u}} {T U : Over S} (q : U ⟶ T) :
    BasedFunctor (discreteModuli (yoneda.obj U)) (discreteModuli (yoneda.obj T)) :=
  discreteModuliMap (yoneda.map q)

/-- The specified comparison functor of a 2-commutative square. Its objects retain the
comparison isomorphism; equivalence of this functor is precisely 2-cartesianness.
Source: Knudsen II Corollary 2.6 and the recorded moduli 2-fibre product
(blueprint: lem-sfb-smooth-marking-isomorphism-fibre-comparison). -/
def squareComparison {S : Scheme.{u}} {g r : ℕ}
    (X : StablePointedModuli S g r) (Y : StablePointedModuli S g (r + 1))
    (q : Y.base ⟶ X.base) (K : Contraction S g r)
    (chi : ModuliTwoIso ((schemeMap q).comp X.familyMap)
      (Y.familyMap.comp (StablePointedUniversalCurve.forgetful K.c))) :
    BasedFunctor (discreteModuli (yoneda.obj Y.base))
      (moduliTwoFiberProduct X.familyMap (StablePointedUniversalCurve.forgetful K.c)) :=
  moduliTwoFiberLift (schemeMap q) Y.familyMap (BasedNatIso.mkNatIso chi.val chi.property)

/-- One forgetful contraction on the original total curves, using the comparison at the
identity test map and the canonical identity-pullback maps. This is actual scheme data.
Source: Knudsen II §2, contraction and stabilization
(blueprint: lem-sfb-smooth-marking-isomorphism-fibre-comparison). -/
def stepContraction {S : Scheme.{u}} {g r : ℕ}
    (X : StablePointedModuli S g r) (Y : StablePointedModuli S g (r + 1))
    (q : Y.base ⟶ X.base) (K : Contraction S g r)
    (chi : ModuliTwoIso ((schemeMap q).comp X.familyMap)
      (Y.familyMap.comp (StablePointedUniversalCurve.forgetful K.c))) :
    Y.curve ⟶ X.curve :=
  pullback.lift (𝟙 Y.curve) Y.projection (by simp) ≫
    K.contraction (Y.familyMap.obj (CostructuredArrow.mk (𝟙 (yoneda.obj Y.base)))) ≫
    (chi.val.inv.app (CostructuredArrow.mk (𝟙 (yoneda.obj Y.base)))).map ≫
    pullback.fst _ _

/-- A finite forgetful tower, with specified 2-cartesian squares over every test scheme.
Its families are the recorded stable ordered families, not coarse moduli points.
Source: Knudsen II §2, iterated Corollary 2.6
(blueprint: lem-sfb-smooth-marking-isomorphism-fibre-comparison). -/
structure Tower (S : Scheme.{u}) (g n : ℕ) where
  family : (r : Fin (n + 1)) → StablePointedModuli S g r.val
  transition : (r : Fin n) → (family r.succ).base ⟶ (family r.castSucc).base
  knudsen : (r : Fin n) → Contraction S g r.val
  comparison : (r : Fin n) →
    ModuliTwoIso ((schemeMap (transition r)).comp (family r.castSucc).familyMap)
      ((family r.succ).familyMap.comp
        (StablePointedUniversalCurve.forgetful (knudsen r).c))
  cartesian : ∀ r : Fin n,
    (squareComparison (family r.castSucc) (family r.succ) (transition r)
      (knudsen r) (comparison r)).toFunctor.IsEquivalence

/-- The composite base map, equal to the identity for an empty tower.
Source: Knudsen II §2, iterating forgetting
(blueprint: lem-sfb-smooth-marking-isomorphism-fibre-comparison). -/
def Tower.baseToZero {S : Scheme.{u}} {g n : ℕ} (D : Tower S g n)
    (r : Fin (n + 1)) : (D.family r).base ⟶ (D.family 0).base :=
  Fin.induction (𝟙 _) (fun i previous ↦ D.transition i ≫ previous) r

/-- The composite of the actual contractions on total curves, identity for zero steps.
Source: Knudsen II §2, iterating contraction
(blueprint: lem-sfb-smooth-marking-isomorphism-fibre-comparison). -/
def Tower.curveToZero {S : Scheme.{u}} {g n : ℕ} (D : Tower S g n)
    (r : Fin (n + 1)) : (D.family r).curve ⟶ (D.family 0).curve :=
  Fin.induction (𝟙 _) (fun i previous ↦
    stepContraction (D.family i.castSucc) (D.family i.succ) (D.transition i)
      (D.knudsen i) (D.comparison i) ≫ previous) r

/-- Actual map-and-labelled-isomorphism pairs, with no quotient. `B` is over `Spec F`,
and its composite structure map regards it as a scheme over `S`.
Source: Knudsen II §2, smooth disjoint-section case
(blueprint: lem-sfb-smooth-marking-isomorphism-fibre-comparison). -/
structure IsoPair {S : Scheme.{u}} {g r : ℕ} {F : Type u} [Field F]
    (j : Spec (.of F) ⟶ S) (X : StablePointedModuli S g r)
    (C : Scheme.{u}) (f : C ⟶ Spec (.of F))
    (p : Fin r → (Spec (.of F) ⟶ C)) (hp : ∀ i, p i ≫ f = 𝟙 _)
    (B : Over (Spec (.of F))) where
  map : (Over.map j).obj B ⟶ X.base
  iso : (X.pullback ((Over.map j).obj B) map).curve ≅ pullback f B.hom
  base_equation : iso.hom ≫ pullback.snd f B.hom =
    (X.pullback ((Over.map j).obj B) map).projection
  markings : ∀ i : Fin r,
    (X.pullback ((Over.map j).obj B) map).sections i ≫ iso.hom =
      f.baseChangeSection (p i) (hp i) B.hom

/-- Canonical base change between the two copies of the fixed curve.
Source: scheme fibre products; Knudsen II §2, arbitrary base change
(blueprint: lem-sfb-smooth-marking-isomorphism-fibre-comparison). -/
def fixedCurveMap {F : Type u} [Field F] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of F)) {B B' : Over (Spec (.of F))} (a : B' ⟶ B) :
    pullback f B'.hom ⟶ pullback f B.hom :=
  pullback.map f B'.hom f B.hom (𝟙 _) a.left (𝟙 _) (by simp) (by simp)

/-- The canonical pullback relation on actual pairs. The equation on isomorphisms is
exactly their cartesian pullback square, so it specifies ordinary pullback uniquely.
Source: Knudsen II §2, naturality under arbitrary base change
(blueprint: lem-sfb-smooth-marking-isomorphism-fibre-comparison). -/
def IsPullbackPair {S : Scheme.{u}} {g r : ℕ} {F : Type u} [Field F]
    {j : Spec (.of F) ⟶ S} {X : StablePointedModuli S g r}
    {C : Scheme.{u}} {f : C ⟶ Spec (.of F)}
    {p : Fin r → (Spec (.of F) ⟶ C)} {hp : ∀ i, p i ≫ f = 𝟙 _}
    {B B' : Over (Spec (.of F))} (a : B' ⟶ B)
    (x : IsoPair j X C f p hp B) (x' : IsoPair j X C f p hp B') : Prop :=
  ∃ h : (Over.map j).map a ≫ x.map = x'.map,
    x'.iso.hom ≫ fixedCurveMap f a =
      StablePointedModuli.pullbackCurveMap X ((Over.map j).map a) h ≫ x.iso.hom

end SmoothMarkingComparison

/-- Forgetting every ordered marking induces a natural bijection of actual isomorphism
fibres over a smooth projective geometrically connected genus-`g` curve. Its base coordinate
is the tower composite, its isomorphism is induced by the actual contractions, and its
inverse has the prescribed transported sections. The last equation expresses naturality
for both directions, through the canonical pullback relation.

Source: Knudsen II §2, Corollary 2.6 and the universal-curve interpretation, p.162
(blueprint: lem-sfb-smooth-marking-isomorphism-fibre-comparison).

Proof: (1) Unpack each specified 2-cartesian comparison using the recorded stable moduli
2-fibre product. Over a fixed test scheme, a triple with its comparison has a unique actual
map-and-isomorphism lift: essential surjectivity gives a lift and full faithfulness forces
any two lifts to agree, since a representable groupoid has discrete fibres. No comparison
or automorphism is discarded.
(2) Given a pointed pair, compose its map with the tower maps and its isomorphism with
forgetting and each specified comparison. By the smooth disjoint-section clause of
lem-sfb-knudsen-pointed-forgetful-universal-curve, every truncation of the fixed smooth
curve has unchanged underlying curve. The resulting unpointed isomorphism obeys the
contraction equation in the statement.
(3) Conversely transport the next section by the inverse of the current isomorphism.
It is smooth and disjoint from every previous marking. The same Knudsen theorem appends
this section without changing the underlying curve. Step (1), with the comparison fixed,
gives a unique lift to the next tower level. Iterate up to `n`.
(4) The defining compatibility equations recover each intermediate pair in either
composite, proving that these constructions are inverse. The section chosen at stage `i`
is exactly the inverse image of `p_i`, giving the displayed inverse-marking equation.
(5) Pull back the comparisons, contractions and these equations along any map of test
schemes. Knudsen stabilization commutes with arbitrary base change; uniqueness in (1)
identifies the pulled-back lift with the lift of the pulled-back pair. This proves the
pullback-relation equivalence, including empty and nonreduced bases. With no markings,
both recursions have no steps and are identities. -/
theorem smooth_marking_isomorphism_fibre_comparison
    (k F : Type u) [Field k] [Field F] [Algebra k F]
    (g n : ℕ) (hg : 2 ≤ g)
    (D : SmoothMarkingComparison.Tower (Spec (.of k)) g n)
    (C : Scheme.{u}) (f : C ⟶ Spec (.of F))
    [IsConnectedCurve f] [Smooth f] [IsHProjective f] [GeometricallyConnected f]
    (hgenus : @Scheme.arithmeticGenus F _ C ⟨f⟩ = g)
    (p : Fin n → (Spec (.of F) ⟶ C)) (hp : ∀ i, p i ≫ f = 𝟙 _)
    (hdistinct : Function.Injective p) :
    ∃ e : ∀ B : Over (Spec (.of F)),
      SmoothMarkingComparison.IsoPair (Spec.map (CommRingCat.ofHom (algebraMap k F)))
        (D.family (Fin.last n)) C f p hp B ≃
      SmoothMarkingComparison.IsoPair (Spec.map (CommRingCat.ofHom (algebraMap k F)))
        (D.family 0) C f Fin.elim0 (fun i ↦ Fin.elim0 i) B,
      (∀ (B : Over (Spec (.of F))) (x : SmoothMarkingComparison.IsoPair
          (Spec.map (CommRingCat.ofHom (algebraMap k F))) (D.family (Fin.last n)) C f p hp B),
        (e B x).map = x.map ≫ D.baseToZero (Fin.last n) ∧
        x.iso.inv ≫ pullback.fst (D.family (Fin.last n)).projection x.map.left ≫
            D.curveToZero (Fin.last n) =
          (e B x).iso.inv ≫ pullback.fst (D.family 0).projection (e B x).map.left) ∧
      (∀ (B : Over (Spec (.of F)))
          (y : SmoothMarkingComparison.IsoPair (Spec.map (CommRingCat.ofHom (algebraMap k F)))
            (D.family 0) C f Fin.elim0 (fun i ↦ Fin.elim0 i) B) (i : Fin n),
        f.baseChangeSection (p i) (hp i) B.hom ≫ y.iso.inv ≫
            pullback.fst (D.family 0).projection y.map.left =
          ((D.family (Fin.last n)).pullback ((Over.map
              (Spec.map (CommRingCat.ofHom (algebraMap k F)))).obj B)
              ((e B).symm y).map).sections i ≫
            pullback.fst (D.family (Fin.last n)).projection ((e B).symm y).map.left ≫
              D.curveToZero (Fin.last n)) ∧
      (∀ (B B' : Over (Spec (.of F))) (a : B' ⟶ B)
          (x : SmoothMarkingComparison.IsoPair (Spec.map (CommRingCat.ofHom (algebraMap k F)))
            (D.family (Fin.last n)) C f p hp B)
          (x' : SmoothMarkingComparison.IsoPair (Spec.map (CommRingCat.ofHom (algebraMap k F)))
            (D.family (Fin.last n)) C f p hp B'),
        SmoothMarkingComparison.IsPullbackPair a x x' ↔
          SmoothMarkingComparison.IsPullbackPair a (e B x) (e B' x')) := by
  sorry

end AlgebraicGeometry

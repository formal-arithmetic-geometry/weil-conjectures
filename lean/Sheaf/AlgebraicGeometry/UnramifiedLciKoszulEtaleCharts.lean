/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Sheaf.AlgebraicGeometry.SpaceUniversalConormal
public import Sheaf.AlgebraicGeometry.LciCotangentPresentation
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.UnramifiedEtaleFiniteNeighbourhoods
import WeilConjectures.FieldTheory.CommonExtensionFields
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.FiniteUnramifiedOnePointClosed

/-!
# Koszul-regular affine charts for an unramified lci map of algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tags 06C4 and 06C5;
Étale Morphisms, Tag 04HH; More on Morphisms, Tag 02HE; Divisors, Tags 063G and 067P
(blueprint: lem-sfb-unramified-lci-koszul-etale-charts).

Both unrestricted existence and refinement of an arbitrary prescribed scheme covering
are stated. All local complete intersection factorizations are written explicitly;
local Koszul regularity is the existing closed-chart predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A formally unramified lci map has affine étale closed-immersion charts with finite
Koszul-regular equations, refining any prescribed étale scheme covering of the target.
These closed immersions remain locally Koszul-regular under every étale scheme base change.
Source: Stacks, Tags 06C5, 04HH, 02HE, 063G and 067P
(blueprint: lem-sfb-unramified-lci-koszul-etale-charts).

Proof, following the seven steps of the node:
1. Pull back a prescribed target covering and take scheme atlases. Refine source and
   target by affine opens using lem-trf-space-chartwise-etale-permanence,
   lem-weil-pbc-affine-opens-basis and lem-weil-pbc-etale-composition-cancellation.
2. A local Koszul-regular/smooth factorization is locally of finite type: on affine
   pieces a quotient of a finitely presented algebra is finitely generated, even without
   finite generation of its ideal. Use def-sbc-locally-finite-presentation,
   def-weil-closed-immersion and lem-weil-pbc-lft-pointwise-criterion. The square-zero
   tests imply formal unramifiedness on the chart by
   lem-sfb-space-formally-unramified-etale-charts. Then
   lem-weil-pbc-lft-formally-unramified-unramified makes the chart unramified.
3. Apply lem-weil-pbc-unramified-etale-finite-neighbourhoods to one chosen source point.
   By lem-weil-common-extension-fields and lem-weil-pbc-fibre-product-points, some marked
   point lies above it. The exhaustion clause ensures the marked point is available.
4. Apply lem-weil-pbc-finite-unramified-one-point-closed and shrink the target. The open
   source of this finite map is now a closed immersion, still passing through the chosen
   point. Étale base change and composition preserve its maps to the original charts.
5. Compare its local lci factorizations with the identity smooth ambient by
   lem-sfb-koszul-immersion-smooth-ambient-independence. This proves local Koszul regularity
   of the new closed immersion, rather than assuming regularity of its new ideal.
6. Use lem-sfb-koszul-closed-immersion-affine-criterion to shrink the target to an affine
   neighbourhood with global finite Koszul-regular generators. The closed source is
   affine. Choosing these at all source points gives joint surjectivity; every target
   map still factors through the prescribed covering. For the empty source use no charts.
7. Étale maps are flat. Apply lem-sfb-koszul-immersion-flat-ascent-etale-descent, then the
   affine criterion, to obtain local generators after arbitrary étale scheme base change.
   The base-changed map is closed by the affine quotient description of closed immersions.
-/
theorem exists_unramified_lci_koszul_etale_charts
    {S : Scheme.{u}} {Z Y : AlgebraicSpace S} (uMap : Z ⟶ Y)
    (hunramified : SpaceFormallyUnramified uMap)
    (hlci : ∀ (U V : Over S) (p : yoneda.obj U ⟶ Z.obj.obj)
      (q : yoneda.obj V ⟶ Y.obj.obj) (g : U ⟶ V),
      IsEtale p → IsEtale q → p ≫ uMap.hom.hom = yoneda.map g ≫ q →
      ∀ x : U.left, ∃ O : U.left.Opens, x ∈ O ∧
        ∃ (P : Scheme.{u}) (j : O.toScheme ⟶ P) (s : P ⟶ V.left),
          IsClosedImmersion j ∧ CotangentPresentation.IsKoszulImmersion j ∧
            Smooth s ∧ j ≫ s = O.ι ≫ g.left) :
    (∃ (I : Type u) (W V : I → Over S)
        (p : ∀ a : I, yoneda.obj (W a) ⟶ Z.obj.obj)
        (q : ∀ a : I, yoneda.obj (V a) ⟶ Y.obj.obj) (i : ∀ a : I, W a ⟶ V a),
        (∀ a : I, IsAffine (W a).left ∧ IsAffine (V a).left) ∧
        (∀ a : I, IsEtale (p a) ∧ IsEtale (q a)) ∧ IsJointlySurjective p ∧
        (∀ a : I, IsClosedImmersion (i a).left ∧
          yoneda.map (i a) ≫ q a = p a ≫ uMap.hom.hom) ∧
        (∀ a : I, ∃ (r : ℕ) (f : Fin r → Γ((V a).left, ⊤)),
          RingTheory.Sequence.IsKoszulRegular f ∧
            Ideal.span (Set.range f) = RingHom.ker (i a).left.appTop.hom) ∧
        (∀ (a : I) (T : Scheme.{u}) (g : T ⟶ (V a).left), Etale g →
          IsClosedImmersion (Limits.pullback.snd (i a).left g) ∧
            CotangentPresentation.IsKoszulImmersion (Limits.pullback.snd (i a).left g))) ∧
    ∀ (B : Type w) (T : B → Over S)
      (b : ∀ β : B, yoneda.obj (T β) ⟶ Y.obj.obj),
      (∀ β : B, IsEtale (b β)) → IsJointlySurjective b →
      ∃ (I : Type u) (W V : I → Over S)
        (p : ∀ a : I, yoneda.obj (W a) ⟶ Z.obj.obj)
        (q : ∀ a : I, yoneda.obj (V a) ⟶ Y.obj.obj) (i : ∀ a : I, W a ⟶ V a),
        (∀ a : I, IsAffine (W a).left ∧ IsAffine (V a).left) ∧
        (∀ a : I, IsEtale (p a) ∧ IsEtale (q a)) ∧ IsJointlySurjective p ∧
        (∀ a : I, IsClosedImmersion (i a).left ∧
          yoneda.map (i a) ≫ q a = p a ≫ uMap.hom.hom) ∧
        (∀ a : I, ∃ (r : ℕ) (f : Fin r → Γ((V a).left, ⊤)),
          RingTheory.Sequence.IsKoszulRegular f ∧
            Ideal.span (Set.range f) = RingHom.ker (i a).left.appTop.hom) ∧
        (∀ (a : I) (T : Scheme.{u}) (g : T ⟶ (V a).left), Etale g →
          IsClosedImmersion (Limits.pullback.snd (i a).left g) ∧
            CotangentPresentation.IsKoszulImmersion (Limits.pullback.snd (i a).left g)) ∧
        (∀ a : I, ∃ (β : B) (r : V a ⟶ T β), yoneda.map r ≫ b β = q a) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

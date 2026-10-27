/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.PGLTwoTriangularPresentation
public import Sheaf.AlgebraicGeometry.RelativeTorus
public import Sheaf.AlgebraicGeometry.RelativeSplitTorus
public import Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.AlgebraicGeometry.GroupScheme.BorelMaximalTorusConjugacy
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Triangular maximal tori in PGL₂ are locally diagonal

Source: Conrad, Reductive group schemes, Proposition 4.2.7, final proof paragraph,
printed p.124 (blueprint: lem-sfb-triangular-maximal-torus-conjugacy).

The transporter is specified on all test schemes, and its inclusion supplies the natural
representing bijection. Its torsor comparison is the actual left multiplication map.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.PGLTwoTriangular

/-- Equality of the conjugated subgroup functor with the diagonal subgroup functor,
tested after every scheme extension of V. Source: Conrad, Proposition 4.2.7, p.124
(blueprint: lem-sfb-triangular-maximal-torus-conjugacy). -/
def Conjugates {S : Scheme.{u}} {B D T : Grp (Over S)}
    (iD : D ⟶ B) (iT : T ⟶ B) (V : Over S) (b : V ⟶ B.X) : Prop :=
  ∀ (W : Over S) (h : W ⟶ V) (z : W ⟶ B.X),
    (∃ d : W ⟶ D.X, d ≫ iD.hom.hom = z) ↔
      ∃ t : W ⟶ T.X, (h ≫ b) * (t ≫ iT.hom.hom) * (h ≫ b)⁻¹ = z

/-- The triangular conjugacy transporter is a smooth surjective D-torsor with etale
and Zariski local sections, and its conjugacy identity survives every base change.

Source: Conrad, Reductive group schemes, Proposition 4.2.7, final proof paragraph,
printed p.124 (blueprint: lem-sfb-triangular-maximal-torus-conjugacy).

Proof:
1. Use lem-sfb-projective-frames-pgl to write B∞ as Spec A[a,a⁻¹,x], with
   multiplication (a,x)(c,z)=(ac,az+x), and D as x=0, hence G_m. This chart is smooth
   by sbc-lem-affine-space-smooth and lem-weil-pbc-smooth-restrict-open-subschemes.
   Conjugating diag(t,1) by (a,x) has upper entry x(1-t). Its Laurent coefficient
   shows N_B(D)=D over every test algebra, including nonreduced ones.
2. Over each algebraically closed geometric field B∞ is smooth, connected and affine
   of finite type. D is maximal by the preceding centralizer computation; T is maximal
   because it is maximal in G. Apply lem-sfb-borel-maximal-torus-conjugacy to B∞ to
   obtain a geometric conjugator carrying T to D.
3. Lem-sfb-multiplicative-type-transporter-smooth represents the containment transporter
   as a closed smooth scheme. On an fppf cover splitting T, the map T to D is locally
   an integer character map by lem-sfb-relative-diagonalizable-character-duality.
   It is an isomorphism on geometric fibres by maximality; the character map therefore
   has rank one and is ±1 locally. It is an isomorphism before specialization. Equality
   of subgroup functors descends from this cover, giving precisely Conjugates.
4. The geometric conjugators make the representing scheme surjective over S.
   Lem-sfb-smooth-space-cover-etale-sections gives its etale local sections.
5. Left multiplication by D preserves the equality transporter. The map (d,y) to
   (dy,y) has inverse (y₁,y₂) to (y₁y₂⁻¹,y₂), since the quotient lies in N_B(D)=D.
   Both are scheme maps induced by group operations. This gives the torsor isomorphism.
6. Lem-sc-line-bundle-torsor identifies the etale G_m-torsor with the frames of an
   invertible module. Def-sc-invertible-module gives Zariski local frames and therefore
   Zariski local transporter sections; no global triviality of an affine line bundle
   is asserted.
7. For any further scheme extension the universal equality in Conjugates restricts
   along the composite map. This proves the last assertion for all base changes,
   including nonreduced and empty test schemes. -/
theorem triangular_maximal_torus_conjugacy
    (A : Type u) [CommRing A] [Nontrivial A] [IsNoetherianRing A]
    (G B D T : Grp (Over (Spec (.of A)))) (iB : B ⟶ G) (iD : D ⟶ B)
    (P : Presentation G B D iB iD) (iT : T ⟶ B)
    [IsClosedImmersion iT.hom.hom.left] (hT : IsRelativeTorus T.X)
    (hmax : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (f : A →+* Ω),
      ReductiveTorusCentralizer.IsMaximalTorus
        ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.map (iT ≫ iB))) :
    Nonempty (D ≅ relativeSplitTorus (Spec (.of A)) 1) ∧
    ∃ (Y : Over (Spec (.of A))) (j : Y ⟶ B.X)
      (act : D.X ⊗ Y ⟶ Y),
      Mono j ∧
      (∀ (V : Over (Spec (.of A))) (b : V ⟶ B.X),
        (∃ y : V ⟶ Y, y ≫ j = b) ↔ Conjugates iD iT V b) ∧
      Smooth Y.hom ∧ Surjective Y.hom ∧
      (∀ (V : Over (Spec (.of A))) (d : V ⟶ D.X) (y : V ⟶ Y),
        lift d y ≫ act ≫ j = (d ≫ iD.hom.hom) * (y ≫ j)) ∧
      IsIso (lift act (snd D.X Y)) ∧
      (∃ (I : Type u) (U : I → Over (Spec (.of A))),
        Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
          Scheme.etalePrecoverage (Spec (.of A)) ∧
        ∀ i : I, Nonempty (U i ⟶ Y)) ∧
      ∃ (I : Type u) (U : I → Over (Spec (.of A))) (b : ∀ i : I, U i ⟶ B.X),
        Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈
          Scheme.zariskiPrecoverage (Spec (.of A)) ∧
        (∀ i : I, Conjugates iD iT (U i) (b i)) ∧
        ∀ (i : I) (V : Over (Spec (.of A))) (h : V ⟶ U i),
          Conjugates iD iT V (h ≫ b i) := by
  sorry

end AlgebraicGeometry.PGLTwoTriangular

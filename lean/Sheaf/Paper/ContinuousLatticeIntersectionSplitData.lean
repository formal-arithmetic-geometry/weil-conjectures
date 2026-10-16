/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousLatticeIntersection
public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.Paper.FiniteEtaleEtaleLocalSplit
import Sheaf.Paper.RegularExtensionComparison
import Sheaf.Paper.ContinuousIntegralUnderivedPushComparison
import Sheaf.Paper.ProfinitePointPullback

/-! # Finite-sheet coordinates for the two canonical adjunction maps -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Local trivializations of the two canonical maps attached to a finite etale cover.
Source: Bhatt--Scholze, Lemma 6.8.13, first paragraph; agent finite-sheet variant.
(blueprint: lem-weil-pbc-continuous-lattice-intersection-split-data)

Proof. Split the finite etale surjection over an etale covering of X. On a
nonempty member the finite sheet set is nonempty. Pull back the given local bases
of P and of every sheet restriction of M, and refine them simultaneously using
finitely many fiber products of pro-etale covers. Refine by affine opens and
compose the covers, obtaining compact members.

For the base-change comparison, use the map obtained by inserting the unit
of the adjunction over the pulled-back finite cover, applying inverse-image
composition around the cartesian square, and contracting the original finite
cover's counit. Forgetting module structures and composing with
profinitePointModuleForgetPullbackIso identifies its unit and composition terms
with the abelian ones. The counit terms agree by the adjunction triangle equations.
Thus the underlying map is the abelian weakly-etale base-change map, which is
invertible. Faithful module forgetful functors reflect its inverse. For the
finite-product comparison the component maps are restrictions to the clopen
sheets. Their scalar compatibility follows from naturality of the action; the
sheaf condition on this disjoint covering is the product universal property.
The module forgetful functor creates these finite products, giving the same
comparison as a module isomorphism.

On one member, write D for the finite direct sum of the integral sheet modules.
Their chosen bases give D = O^n for the sum n of their ranks. Weakly-etale base
change and the sheaf condition for a finite disjoint union identify the normalized
restriction of p_*M with D, giving eB. Applying the same comparison to p_*p^*P
and the specified rationalization e, and using the coefficient/pushforward mate,
gives eD with target Res(Ext(D)). The rational basis of P gives eA with target
Res(Ext(O^r)). All these are linear isomorphisms with the normalized coefficient
ring, using condensedPullbackHom for the raw inverse-image coefficient ring.

Under these comparisons the rational adjunction unit has as components the
rationalization isomorphisms from P to the individual sheets. Denote this map by
i:Ext(O^r) to Ext(D). Choosing one sheet and inverting its component gives a
retraction, hence i is mono. Subtract its chosen-sheet component from each other
coordinate to identify coker(i) with a direct sum of copies of P. The basis of P
therefore gives an isomorphism with Ext(O^m), where m is r times the number of
remaining sheets. This does not require equality of the integral sheet ranks.

The first displayed map equation is the diagonal description of the rational
adjunction unit. For the second, the pushed integral embedding has on each sheet
the map m to e(1 tensor m). Naturality of the extension adjunction unit and the
coefficient/pushforward mate identifies these components with the localization
unit D to Res(Ext(D)); equality on every sheet gives the stated equation. All
comparisons are natural under further cover refinements. Discard empty members;
for a single sheet the complementary sum and m are zero. This statement concerns
only the three objects and two maps: it asserts no property of their intersection. -/
theorem continuousLatticeIntersection_splitData
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u})
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hP : ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod _).obj P))
    {U : Scheme.{u}} (p : U ⟶ X) [IsFinite p] [Etale p] [Surjective p]
    (M : Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) U))
    (hM : ∃ D : Scheme.Cover.{u} Scheme.proetalePrecoverage U, ∀ s : D.I₀,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (D.f s)).obj
        (condensedRingObj (integralCoeff ℓ E) U))
        (((ProEtale.upperStar Ab.{u + 1} (D.f s)).mapMod _).obj M))
    (e : (Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) U)).obj M ≅
      (upperStar (Profinite.continuousMapRingObj E) p).obj P) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      CompactSpace (C.X s) ∧
      let R := condensedRingObj (integralCoeff ℓ E) (C.X s)
      let T := (ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod
          (condensedRingObj (integralCoeff ℓ E) X) ⋙
        Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) (C.f s)))
      let F := Mod.extendScalars
        (coefficientMap (integralScalarMap ℓ E) (C.X s))
      let G := Mod.comap (D := Sheaf (Scheme.ProEt.topology (C.X s)) Ab.{u + 1})
        (coefficientMap (integralScalarMap ℓ E) (C.X s))
      let adj := Mod.extendRestrictAdjunction
        (coefficientMap (integralScalarMap ℓ E) (C.X s))
      ∃ (r n m : ℕ) (i : F.obj (Mod.finiteFree R r) ⟶ F.obj (Mod.finiteFree R n)),
        Mono i ∧ Nonempty (cokernel i ≅ F.obj (Mod.finiteFree R m)) ∧
        ∃ (eA : T.obj ((Mod.comap (coefficientMap (integralScalarMap ℓ E) X)).obj P) ≅
              G.obj (F.obj (Mod.finiteFree R r)))
          (eB : T.obj ((lowerStar (integralCoeff ℓ E) p).obj M) ≅ Mod.finiteFree R n)
          (eD : T.obj ((Mod.comap (coefficientMap (integralScalarMap ℓ E) X)).obj
              ((lowerStar (Profinite.continuousMapRingObj E) p).obj
                ((upperStar (Profinite.continuousMapRingObj E) p).obj P))) ≅
              G.obj (F.obj (Mod.finiteFree R n))),
          eA.hom ≫ G.map i =
            T.map (latticeIntersectionUnit (integralScalarMap ℓ E) X P p) ≫ eD.hom ∧
          eB.hom ≫ adj.unit.app (Mod.finiteFree R n) =
            T.map (latticePushedEmbedding (integralScalarMap ℓ E) X P p M e) ≫ eD.hom := by sorry


end AlgebraicGeometry.ProEtale.CondensedRing

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.InternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.HomShift
public import WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude

import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContinuity
import WeilConjectures.AlgebraicGeometry.IndEtaleConstructibleMappingContinuity
import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluationForget
import WeilConjectures.Algebra.Homology.RhomGlobalSectionsOfUniverses
import WeilConjectures.AlgebraicGeometry.CofilteredAffineEtaleModel
import WeilConjectures.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.Algebra.Homology.RingedSiteGlobalRHomCoefficientModel
import WeilConjectures.AlgebraicGeometry.DerivedCohomologyGermIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

/-!
# Internal-Hom comparison for affine ind-etale pullback

Source: Bhatt--Scholze, Lemma 6.3.16 and its proof, pp. 47--48,
small-etale analogue (blueprint: lem-weil-pbc-ind-etale-internal-hom-comparison).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The evaluation-transpose map for an affine ind-etale pullback.

Source: Bhatt--Scholze, Lemma 6.3.16 and its proof, pp. 47--48
(the small-etale analogue); the construction uses the evaluation counit and the
monoidal comparison for exact inverse image. (blueprint:
lem-weil-pbc-ind-etale-internal-hom-comparison). -/
noncomputable def indEtaleInternalHomComparison
    (A : Type (u + 1)) [CommRing A] {X U : Scheme.{u}} (f : U ⟶ X)
    (K M : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (L((f)^*[ModuleCat.{u + 1} A])).obj
        ((RHom(X)[ModuleCat.{u + 1} A].obj (op K)).obj M) ⟶
      (RHom(U)[ModuleCat.{u + 1} A].obj
        (op ((L((f)^*[ModuleCat.{u + 1} A])).obj K))).obj
        ((L((f)^*[ModuleCat.{u + 1} A])).obj M) :=
  derivedHomUpperStarComparison (ModuleCat.{u + 1} A) f K M

/-- Affine ind-etale pullback preserves the derived internal-Hom comparison and
its stated functorial, t-structure, and shift compatibilities.

Source: Bhatt--Scholze, Lemma 6.3.16 and its proof, pp. 47--48
(the small-etale analogue, using Lemma 6.3.14).

Proof plan: (1) form the evaluation transpose from the closed derived tensor-Hom
adjunction and the exact monoidal inverse image. (2) Base change the affine
ind-etale presentation to an affine neighbourhood and descend each affine
etale test object to a finite stage. (3) Apply the affine constructible
mapping-continuity comparison to the finite stages; the colimit of the pulled
back Hom maps is bijective. (4) Pass from neighbourhoods to geometric stalks;
strict-local stalks detect the isomorphism of the two bounded-below derived
sheaves. (5) Naturality in both variables, independence of the presentation,
composition, identities, and shifts follow from the evaluation transpose, the
monoidal pullback comparison, inverse-image composition, and the closed
shift calculus. (6) The small-etale lower-bound estimate gives degree
`N - b` on both internal Homs, and the identity morphism gives the bound for
the source internal Hom itself. The proof uses `det-sf-comparison-affine-
continuity`, `lem-pe-left-module-derived-evaluation-forget`,
`lem-per-ind-etale-constructible-mapping-continuity`,
`lem-pur-rhom-global-sections`, `lem-sc-cofiltered-affine-etale-model`,
`lem-sf-ringed-derived-closed-symmetric-monoidal`,
`lem-sfb-global-rhom-coefficient-model`,
`lem-weil-pbc-derived-cohomology-germ-isomorphism`,
`lem-weil-pbc-etale-internal-hom-lower-bound`,
`lem-weil-pbc-inverse-image-composition`,
`lem-weil-pbc-ringed-internal-hom-exact-restriction`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lemma-weil-pbc-geometric-stalk-conservative`, and
`prop-weil-pbc-inverse-image-modules-exact`.
(blueprint: lem-weil-pbc-ind-etale-internal-hom-comparison). -/
theorem isIso_indEtaleInternalHomComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U : Scheme.{u}} [IsNoetherian X] [IsNoetherian U]
    (f : U ⟶ X) [IsAffineHom f] (hf : MorphismProperty.pro.{u} (@Etale ⊓ @IsAffineHom) f)
    (K M : _root_.DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.isBoundedConstructible A X K)
    (hKtor : DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) X K)
    (hM : ∃ N : ℤ, M.IsGE N) :
    IsIso (indEtaleInternalHomComparison A f K M) ∧
      (∀ {K' : _root_.DerivedCategory
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
        (q : K' ⟶ K),
        (L((f)^*[ModuleCat.{u + 1} A])).map
            (((RHom(X)[ModuleCat.{u + 1} A]).map q.op).app M) ≫
            indEtaleInternalHomComparison A f K' M =
          indEtaleInternalHomComparison A f K M ≫
            (((RHom(U)[ModuleCat.{u + 1} A]).map
              ((L((f)^*[ModuleCat.{u + 1} A])).map q).op).app
                ((L((f)^*[ModuleCat.{u + 1} A])).obj M))) ∧
      (∀ {M M' : _root_.DerivedCategory
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
        (q : M ⟶ M'),
        (L((f)^*[ModuleCat.{u + 1} A])).map
            ((RHom(X)[ModuleCat.{u + 1} A].obj (op K)).map q) ≫
            indEtaleInternalHomComparison A f K M' =
          indEtaleInternalHomComparison A f K M ≫
            (RHom(U)[ModuleCat.{u + 1} A].obj
              (op ((L((f)^*[ModuleCat.{u + 1} A])).obj K))).map
              ((L((f)^*[ModuleCat.{u + 1} A])).map q)) ∧
      (∀ {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R)
        (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂)
        (P Q : _root_.DerivedCategory
          (Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} A))),
        indEtaleInternalHomComparison A g₁₂ P Q ≫
            (RHom(T)[ModuleCat.{u + 1} A].obj
              (op ((L((g₁₂)^*[ModuleCat.{u + 1} A])).obj P))).map
              ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₁ g₂ g₁₂ hg).hom.app Q) =
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) g₁ g₂ g₁₂ hg).hom.app
              ((RHom(R)[ModuleCat.{u + 1} A].obj (op P)).obj Q) ≫
            (L((g₁)^*[ModuleCat.{u + 1} A])).map
              (indEtaleInternalHomComparison A g₂ P Q) ≫
            indEtaleInternalHomComparison A g₁
              ((L((g₂)^*[ModuleCat.{u + 1} A])).obj P)
              ((L((g₂)^*[ModuleCat.{u + 1} A])).obj Q) ≫
            (pre ((leftDerivedUpperStarComp
              (ModuleCat.{u + 1} A) g₁ g₂ g₁₂ hg).hom.app P)).app
              ((L((g₁)^*[ModuleCat.{u + 1} A])).obj
                ((L((g₂)^*[ModuleCat.{u + 1} A])).obj Q))) ∧
      (∀ (Y : Scheme.{u}) (P Q : _root_.DerivedCategory
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))),
        indEtaleInternalHomComparison A (𝟙 Y) P Q ≫
            (RHom(Y)[ModuleCat.{u + 1} A].obj
              (op ((L((𝟙 Y)^*[ModuleCat.{u + 1} A])).obj P))).map
              ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) Y).hom.app Q) =
          (leftDerivedUpperStarId (ModuleCat.{u + 1} A) Y).hom.app
              ((RHom(Y)[ModuleCat.{u + 1} A].obj (op P)).obj Q) ≫
            (pre ((leftDerivedUpperStarId (ModuleCat.{u + 1} A) Y).hom.app P)).app Q) ∧
      (∀ (n : ℤ),
        indEtaleInternalHomComparison A f (K⟦n⟧) M ≫
            (pre (((L((f)^*[ModuleCat.{u + 1} A])).commShiftIso n).inv.app K)).app
              ((L((f)^*[ModuleCat.{u + 1} A])).obj M) ≫
            (derivedHomShiftIso (ModuleCat.{u + 1} A)
              ((L((f)^*[ModuleCat.{u + 1} A])).obj K) n).hom.app
              ((L((f)^*[ModuleCat.{u + 1} A])).obj M) =
          (L((f)^*[ModuleCat.{u + 1} A])).map
              ((derivedHomShiftIso (ModuleCat.{u + 1} A) K n).hom.app M) ≫
            ((L((f)^*[ModuleCat.{u + 1} A])).commShiftIso (-n)).hom.app
              ((RHom(X)[ModuleCat.{u + 1} A].obj (op K)).obj M) ≫
            (indEtaleInternalHomComparison A f K M)⟦-n⟧') ∧
      (∀ (n : ℤ),
        indEtaleInternalHomComparison A f K (M⟦n⟧) ≫
            (RHom(U)[ModuleCat.{u + 1} A].obj
              (op ((L((f)^*[ModuleCat.{u + 1} A])).obj K))).map
              (((L((f)^*[ModuleCat.{u + 1} A])).commShiftIso n).hom.app M) ≫
            (Functor.commShiftIso (RHom(U)[ModuleCat.{u + 1} A].obj
              (op ((L((f)^*[ModuleCat.{u + 1} A])).obj K)))
              (self := commShiftDerivedHomObj (ModuleCat.{u + 1} A)
                (op ((L((f)^*[ModuleCat.{u + 1} A])).obj K))) n).hom.app
              ((L((f)^*[ModuleCat.{u + 1} A])).obj M) =
          (L((f)^*[ModuleCat.{u + 1} A])).map
              ((Functor.commShiftIso (RHom(X)[ModuleCat.{u + 1} A].obj (op K))
              (self := commShiftDerivedHomObj (ModuleCat.{u + 1} A) (op K)) n).hom.app M) ≫
            ((L((f)^*[ModuleCat.{u + 1} A])).commShiftIso n).hom.app
              ((RHom(X)[ModuleCat.{u + 1} A].obj (op K)).obj M) ≫
            (indEtaleInternalHomComparison A f K M)⟦n⟧') ∧
      (∀ (b N : ℤ), K.IsLE b → M.IsGE N →
        ((RHom(X)[ModuleCat.{u + 1} A].obj (op K)).obj M).IsGE (N - b) ∧
        ((RHom(U)[ModuleCat.{u + 1} A].obj
          (op ((L((f)^*[ModuleCat.{u + 1} A])).obj K))).obj
          ((L((f)^*[ModuleCat.{u + 1} A])).obj M)).IsGE (N - b) ∧
        ((RHom(X)[ModuleCat.{u + 1} A].obj (op K)).obj M).IsGE (N - b)) := by
  sorry

end Etale
end AlgebraicGeometry

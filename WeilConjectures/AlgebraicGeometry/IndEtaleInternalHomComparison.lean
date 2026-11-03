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
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude

import WeilConjectures.SixFunctors.Etale.Derived.LisseFieldDual
import WeilConjectures.AlgebraicGeometry.IndEtaleInternalHomComparisonIso
import WeilConjectures.AlgebraicGeometry.IndEtaleInternalHomComparisonCoherence

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

-- Match the coefficient braiding used inside the canonical derived internal Hom.
attribute [-instance] ModuleCat.MonoidalCategory.instBraidedCategory in
/-- Affine ind-etale pullback preserves the derived internal-Hom comparison and
its stated functorial, t-structure, and shift compatibilities.

Source: Bhatt--Scholze, Lemma 6.3.16 and its proof, pp. 47--48
(the small-etale analogue, using Lemma 6.3.14).

Proof: noetherian induction and the supported open-closed localization triangle reduce
invertibility to the dualizable case on a dense open and the comparison on its closed
complement. Ind-etale direct-image base change for bounded-below complexes handles the
open term; proper base change handles the closed term. Affine neighborhoods convert the
relative pro-etale presentation to the ring-theoretic local hypothesis of that theorem.
The comparison remains the evaluation transpose throughout. Naturality and monoidal
coherence give composition and identity; taking mates of the canonical tensor-shift
squares gives both shift formulas. The tensor-Hom adjunction and exact inverse image
give the lower bound `N - b`.
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
  constructor
  · let : UpperStarPreservesFlat (ModuleCat.{u + 1} A) :=
      upperStarPreservesFlat_moduleCat
    simpa [indEtaleInternalHomComparison] using
      (isIso_derivedHomUpperStarComparison_of_proAffineEtale
        A f hf K M hK hKtor hM)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K' q
    exact derivedHomUpperStarComparison_naturality_left
      (ModuleCat.{u + 1} A) f q M
  · intro M M' q
    exact derivedHomUpperStarComparison_naturality
      (ModuleCat.{u + 1} A) f K q
  · intro T S R g₁ g₂ g₁₂ hg P Q
    exact (indEtaleInternalHomComparison_coherence_and_bounds
      A f K M).1 g₁ g₂ g₁₂ hg P Q
  · intro Y P Q
    exact (indEtaleInternalHomComparison_coherence_and_bounds
      A f K M).2.1 Y P Q
  · intro n
    exact (indEtaleInternalHomComparison_coherence_and_bounds
      A f K M).2.2.1 n
  · intro n
    exact (indEtaleInternalHomComparison_coherence_and_bounds
      A f K M).2.2.2.1 n
  · intro b N hKb hMN
    exact (indEtaleInternalHomComparison_coherence_and_bounds
      A f K M).2.2.2.2 b N hKb hMN

end Etale
end AlgebraicGeometry

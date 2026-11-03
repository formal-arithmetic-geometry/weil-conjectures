/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClassicalDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteClassicalUnboundedComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceRightNormalForm
public import WeilConjectures.Compactification.CategoryBaseChange
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist

/-! # Affine purity with the prescribed base-change comparisons
Source: current blueprint sk-lem-geo-affine-local, clause (1), last sentences.
(blueprint: lem-geo-affine-local-normalized-affine-base-change). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits AlgebraicGeometry Scheme
namespace AlgebraicGeometry.ProEtale

/-- Affine purity can be chosen compatibly with the specified compact-support exchange
and pullback--Tate--shift comparison.
Source: current blueprint sk-lem-geo-affine-local, proof (1), counit and base-change paragraph;
Stacks Tags 0F7J, 0F7K and 0F7L.
(blueprint: lem-geo-affine-local-normalized-affine-base-change).

Proof: choose the normalized projective-line trace adjunction simultaneously on all bases.
For one coordinate compose with the exact open-extension adjunction. Its exchange is the
proper exchange followed by inverse open exchange, and the open counit equation follows
by transposing the identity. Paste it with the projective trace counit square. Iterate
along the coordinate tower, using compact-support exchange/composition compatibility.
Transport the right functor to its pullback--Tate--shift normal form. Naturality of tensor
pullback, normalized Tate pullback, the upper-star compositor and the even shift addition
identify the transported right square with etaleAffineRightBaseChange. Transfer along the
canonical affine-space/tower isomorphism and along the specified compactification comparison.
Finally conjugate through the four classical equivalences. Full faithfulness gives the two
normalized comparison maps and preserves the counit equation; mate transposition gives the
unit equation. The identity tower treats d=0, including empty bases and the zero ring. -/
theorem exists_classicalAffineBaseChange
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (hEll : IsUnit (algebraMap ℤ k (ell : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (r : ℕ) (hr : 1 ≤ r) (hAr : ((ell ^ r : ℕ) : A) = 0)
    (hpos : 0 < ell ^ r)
    (S : Scheme.{u}) [S.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (S ↘ Spec (CommRingCat.of k))]
    [IsSeparated (S ↘ Spec (CommRingCat.of k))]
    (CS : ClassicalComparisonData S A) :
    (∀ d : ℕ,
      let P := AffineSpace (ULift.{u} (Fin d)) S
      let f : P ⟶ S := P ↘ S
      ∃ (CP : ClassicalComparisonData P A) (c : Compactification f)
        (F : ProEtaleD P A ⥤ ProEtaleD S A) (G : ProEtaleD S A ⥤ ProEtaleD P A)
        (data : ClassicalAffineAdjunctionData P S A f c ell r d hAr CP CS F G),
      ∀ (S' : Scheme.{u}) (b : S' ⟶ S)
        [S'.Over (Spec (CommRingCat.of k))]
        [LocallyOfFiniteType (S' ↘ Spec (CommRingCat.of k))]
        [QuasiCompact (S' ↘ Spec (CommRingCat.of k))]
        [IsSeparated (S' ↘ Spec (CommRingCat.of k))]
        [b.IsOver (Spec (CommRingCat.of k))],
        let sq := IsPullback.of_hasPullback f b
        ∃ (CP' : ClassicalComparisonData (pullback f b) A)
          (CS' : ClassicalComparisonData S' A)
          (F' : ProEtaleD (pullback f b) A ⥤ ProEtaleD S' A)
          (G' : ProEtaleD S' A ⥤ ProEtaleD (pullback f b) A)
          (data' : ClassicalAffineAdjunctionData (pullback f b) S' A
            (pullback.snd f b) (c.ofIsPullback sq) ell r d hAr CP' CS' F' G')
          (bP : ClassicalUpperStarData (pullback f b) P A (pullback.fst f b))
          (bS : ClassicalUpperStarData S' S A b)
          (hP : IsUnit (((ell ^ r : ℕ) : Γ(P, ⊤)))),
          Nonempty (ClassicalAffineBaseChange A ell r d hpos hAr sq c hP
            CP CS CP' CS' F G F' G' data data' bP bS)) := by
  sorry

end AlgebraicGeometry.ProEtale

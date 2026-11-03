/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GeneralFiniteDiagonalReductionSource
public import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarFlatModel
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteNormalizedOrientationScalar
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation
public import WeilConjectures.AlgebraicGeometry.GeneralFiniteExceptionalIdentification
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionCompatibilities

/-! # General-field finite diagonal reduction

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-setup/sec-the-purity-statement/
sk-thm-purity-transport/sk-thm-purity-transport.proof.md, Step 1
(blueprint: lem-pur-general-finite-diagonal-reduction).

The statement uses the non-withdrawn derived pro-etale scalar extensions
`L(sheafExtendScalars φ T)` from the finite-coefficient framework.  The natural
transformation `c` is the counit-characterized exceptional comparison supplied by
`sk-lem-sp-reduction`; `lambda` is the corresponding source, pullback, Tate-line,
and shift comparison.  The conclusion records four separate compatibilities:
the gamma square, its coefficient-unit instance, the normalized orientation and
Tate-line reduction square, and the projection-formula tensor square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

local instance proEtaleEssentiallySmallMain (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _

/-- Scalar extension preserves the intrinsic ctf domain: compute it on a bounded
flat constructible model of the actual etale origin, then transport through the
specified site/scalar comparison and the invertible comparison counit. -/
private theorem scalarCtfForDiagonal
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (phi : A →+* B) (Y : Scheme.{u}) [IsNoetherian Y]
    (K : proCategory A Y) (hK : IsCtf A Y K) :
    IsCtf B Y ((proScalar phi Y).obj K) := by
  have ho := actualOriginCtf A Y K hK
  obtain ⟨a, b, ht⟩ := ho.2
  have hm := Etale.exists_etaleScalarFlatModel Y A B phi a (max a b) (le_max_left _ _)
    ⟨(origin A Y).obj K, ho.1.1⟩
    (fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr
      (ho.1.2 i))
    (Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
      (ht.mono le_rfl (le_max_right _ _)))
  obtain ⟨L, ⟨eL⟩⟩ := hm.2.2.1
  have hb : Etale.DerivedCategory.boundedConstructibleFiniteTor B Y
        ((ordinaryScalar phi Y).obj ((origin A Y).obj K)) := by
    refine ⟨⟨(_root_.DerivedCategory.TStructure.t.bounded).prop_of_iso eL L.property,
      fun i ↦ ?_⟩, a, max a b, ?_⟩
    · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp
        (hm.2.2.2.1 i)
    · exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp hm.2.2.2.2
  have := intrinsicOriginCounit A Y K hK
  exact isCtfOfIso B Y
    (((ProEtale.pbcComparisonReduction Y phi).app ((origin A Y).obj K)).symm ≪≫
      (proScalar phi Y).mapIso
        (asIso ((ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.app K)))
    (comparisonCtf B Y _ hb)

/-- Finite smooth-purity reduction over an arbitrary positive-characteristic field.

The exceptional comparison `c` is supplied together with its transported (10.15)
counit equation.  The equation uses `compactReduction`, the scalar comparison for
compact support, and is the universe-`u+1` transport of `sp_reduction`, whose CTF
categories are presented at universe `u`.  The source comparison `lambda` is the
concrete normalized pullback/tensor/Tate/shift comparison
`canonicalSourceComparison` is used at the constructible object `K`.
The Tate map is the definition
`canonicalTateLineReduction`, so it is fixed by the Kummer root-line normalization
through the dualizing scalar map.

The conclusion has four clauses: the gamma square, its unit instance, the
normalized orientation equation, and the canonical ordinary projection-formula
counit square.  The fourth clause is the actual `compactScalarProjection` map
from `EtaleCompactScalarCoherence`; it does not quantify over arbitrary projection
maps or arbitrary reduction arrows.

Proof steps (source: `sk-thm-purity-transport`, Step 1).  First use the transported
counit equation and the quotient cocycle from `sk-lem-sp-reduction`.  Then paste
the canonical derived pullback, tensor, Kummer line and shift comparisons into
`lambda`.  At the coefficient unit, apply the normalized diagonal equation and
use uniqueness of normalized orientations.  The orientation map is the canonical
`dualizingScalarMap` and the Tate map is `canonicalTateLineReduction`.  For the
last clause, apply `etaleCompactScalarCoherence` to the compactification of `f`,
whose projection map is the ordinary projection-formula counit tensor map.  Paste
these squares by associativity and naturality of derived tensor.  The cases
`M = N`, `d = 0`, `K = 0`, empty schemes and zero coefficient rings are included.

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-sp-grp-setup/sec-the-purity-statement/
sk-thm-purity-transport/sk-thm-purity-transport.proof.md, Step 1
(blueprint: lem-pur-general-finite-diagonal-reduction).
-/
theorem generalFiniteDiagonalReduction
    (ell pchar : ℕ) [Fact ell.Prime] (hp : 0 < pchar) (hℓ : pchar ≠ ell)
    (k : Type u) [Field k] [CharP k pchar]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasCompactification f] [IsSeparated f] [QuasiCompact f]
    [IsNoetherian X] [IsNoetherian Y]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (hMN : M ∣ N)
    (hA : (N : A) = 0) (hB : (M : B) = 0) (φ : A →+* B)
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ X)]
    [Functor.PreservesKFlatQuasiIso (sheafExtendScalars φ Y)]
    (geometry : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (hunitA : IsUnit (N : Γ(X, ⊤))) (hunitB : IsUnit (M : Γ(X, ⊤)))
    (αA : Etale.dualizingComplex A f ≅
      Etale.FiniteSmoothPurity.line A N hA X d)
    (αB : Etale.dualizingComplex B f ≅
      Etale.FiniteSmoothPurity.line B M hB X d)
    (hαA : Etale.FiniteSmoothPurity.OrientationNormalized A N hN hA f d
      geometry hunitA αA)
    (hαB : Etale.FiniteSmoothPurity.OrientationNormalized B M hM hB f d
      geometry hunitB αB)
    (c : Etale.FiniteSmoothPurity.exceptional A f ⋙ sideScalar φ X ⟶
      sideScalar φ Y ⋙ Etale.FiniteSmoothPurity.exceptional B f)
    (hcounit : ∀ K : Etale.FiniteSmoothPurity.proCategory A Y,
      Etale.FiniteSmoothPurity.IsCtf A Y K →
      canonicalCompactReduction f φ K ≫
          (Etale.FiniteSmoothPurity.proCompact B f).map (c.app K) ≫
          Etale.FiniteSmoothPurity.proCounit B f ((sideScalar φ Y).obj K) =
        (sideScalar φ Y).map (Etale.FiniteSmoothPurity.proCounit A f K))
    (hc : ∀ K : Etale.FiniteSmoothPurity.proCategory A Y,
      Etale.FiniteSmoothPurity.IsCtf A Y K → IsIso (c.app K))
    (tateData : KummerTateLineReductionData (X := X) φ N M d hMN hA hB)
    (K : Etale.FiniteSmoothPurity.proCategory A Y)
    (hK : Etale.FiniteSmoothPurity.IsCtf A Y K) :
    (sideScalar φ X).map
        (Etale.FiniteSmoothPurity.proGamma A f
          (Etale.FiniteSmoothPurity.line A N hA X d) αA K) ≫
        (c.app K) =
      (canonicalSourceComparison (X := X) (Y := Y) φ f N M d hMN hA hB tateData).app K ≫
        Etale.FiniteSmoothPurity.proGamma B f
          (Etale.FiniteSmoothPurity.line B M hB X d) αB
          ((sideScalar φ Y).obj K) ∧
    (sideScalar φ X).map
        (Etale.FiniteSmoothPurity.proGamma A f
          (Etale.FiniteSmoothPurity.line A N hA X d) αA
          ((Etale.FiniteSmoothPurity.comparison A Y).obj
            (Etale.ordinaryFiniteUnit A Y))) ≫
        (c.app ((Etale.FiniteSmoothPurity.comparison A Y).obj
          (Etale.ordinaryFiniteUnit A Y))) =
      (canonicalSourceComparison (X := X) (Y := Y) φ f N M d hMN hA hB tateData).app
        ((Etale.FiniteSmoothPurity.comparison A Y).obj
          (Etale.ordinaryFiniteUnit A Y)) ≫
        Etale.FiniteSmoothPurity.proGamma B f
          (Etale.FiniteSmoothPurity.line B M hB X d) αB
          ((sideScalar φ Y).obj
            ((Etale.FiniteSmoothPurity.comparison A Y).obj
              (Etale.ordinaryFiniteUnit A Y))) ∧
    (Etale.scalarExtension φ X).map αA.hom ≫
        canonicalTateLineReduction φ N M d hMN hA hB tateData =
      Etale.ExceptionalCoefficients.dualizingScalarMap φ f ≫ αB.hom ∧
    (Etale.scalarExtension φ Y).map
        (Etale.compactScalarProjection A
          (HasCompactification.compactification f)
          ((Etale.FiniteSmoothPurity.origin A Y).obj K)
          (Etale.FiniteSmoothPurity.line A N hA X d)) ≫
      (Etale.compactScalarMap φ (HasCompactification.compactification f)).app
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((Etale.upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
            ((Etale.FiniteSmoothPurity.origin A Y).obj K))).obj
          (Etale.FiniteSmoothPurity.line A N hA X d)) ≫
      (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
        (HasCompactification.compactification f)).map
        (Etale.compactScalarProjectionTarget φ f
          ((Etale.FiniteSmoothPurity.origin A Y).obj K)
          (Etale.FiniteSmoothPurity.line A N hA X d)) =
      (Etale.ExceptionalCoefficients.tensorIso φ Y).hom.app
          ((Etale.FiniteSmoothPurity.origin A Y).obj K,
            (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
              (HasCompactification.compactification f)).obj
              (Etale.FiniteSmoothPurity.line A N hA X d)) ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} B) Y).obj
          ((Etale.scalarExtension φ Y).obj
            ((Etale.FiniteSmoothPurity.origin A Y).obj K))).map
          ((Etale.compactScalarMap φ (HasCompactification.compactification f)).app
            (Etale.FiniteSmoothPurity.line A N hA X d)) ≫
        Etale.compactScalarProjection B
          (HasCompactification.compactification f)
          ((Etale.scalarExtension φ Y).obj
            ((Etale.FiniteSmoothPurity.origin A Y).obj K))
          ((Etale.scalarExtension φ X).obj
            (Etale.FiniteSmoothPurity.line A N hA X d)) := by
  sorry


end AlgebraicGeometry.ProEtale

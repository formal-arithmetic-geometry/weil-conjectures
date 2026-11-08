/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfFiniteAmplitude
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftComplete
public import Submission.WeilConjectures.CategoryTheory.Triangulated.CompactFamily
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.BrownRepresentability.ModuleCat
public import Submission.WeilConjectures.CategoryTheory.Triangulated.CompactBoundedHom
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import Submission.WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimensionAmplitude
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Triangulated.CoproductTriangle
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Localization
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Coproducts
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.LisseDual
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.FieldStagePointers
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Constructible
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Uniformizer
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The uniform `Ext` bound for constructible `𝒪_E`-sheaves

Blueprint `sk-lem-int-ext` (2). Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of
integers `𝒪_E`, uniformizer `ϖ` and residue field `𝔽_E`, and let `X` be a separated scheme of finite
type over a field `k` of characteristic prime to `ℓ` with `cd_ℓ(k) < ∞`. For every constructible
`𝒪_{E,X}`-module `M` there is `d` with `Ext^q(M, B) = 0` for `q > d` and every constructible `B`
(`hasUniformConstructibleExtBound_padicIntegersRingObj_of_hasFiniteCohomologicalDimension`).

The proof avoids derived limits:

* *Torsion targets.* By the triangle `B --ϖ--> B ⟶ B ⊗ᴸ 𝔽_E ⟶`
  (`ProEtale.exists_distinguished_regularEndCenter_derivedExtendScalars`) and the adjunction
  between derived extension and restriction of scalars along `𝒪_E ⟶ 𝔽_E`,
  `Ext^q_{𝒪_E}(M, B ⊗ᴸ 𝔽_E) = Ext^q_{𝔽_E}(M ⊗ᴸ 𝔽_E, B ⊗ᴸ 𝔽_E)`. The source is a constructible
  complex of `𝔽_E`-sheaves and the target has constructible cohomology sheaves (of étale origin) in
  degrees `[-1, 0]`, so these groups vanish for `q` large, uniformly in `B`
  (`exists_forall_eq_zero_of_constructibleFiniteTor_of_generation`, which uses `cd_ℓ(k) < ∞`).
* *Inverting `ϖ`.* Hence, for `q` large, multiplication by `ϖ` is bijective on
  `V = Hom(M, B[q])`.
* *Completeness.* On the countable power of `B`, `(xₙ) ↦ (xₙ - ϖ x_{n+1})` is an isomorphism
  (`ProEtale.isIso_sub_powShift_padicIntegersCenter_of_isConstructible`); applying `Hom(M, -[q])`,
  which commutes with products, `(xₙ) ↦ (xₙ - ϖ x_{n+1})` is injective on `V^ℕ`. For `v ∈ V` the
  sequence `xₙ = ϖ^{-n} v` lies in its kernel, so `v = 0`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

section Reduction

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

end Reduction

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) {k : Type u} [Field k]
  [Fact (ringChar k ≠ ℓ)]

/-- If `ℓ ≠ char k`, the exponent `ℓ` of the residue field `𝔽_E` is invertible on every
`k`-scheme. -/
lemma hasInvertibleExponent_residueFieldCoeff {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) :
    HasInvertibleExponent (ResidueFieldCoeff.{u} ℓ E) X := by
  have hℓ : (ℓ : k) ≠ 0 := fun h ↦
    ((Fact.out : ℓ.Prime).eq_one_or_self_of_dvd _ ((ringChar.spec k ℓ).1 h)).elim
      CharP.ringChar_ne_one (Fact.out : ringChar k ≠ ℓ)
  have : HasInvertibleExponent (ResidueFieldCoeff.{u} ℓ E) (Spec (.of k)) :=
    ⟨ℓ, (Fact.out : ℓ.Prime).pos, natCast_eq_zero_residueFieldCoeff ℓ E,
      by simpa using (Ne.isUnit hℓ).map (Scheme.ΓSpecIso (.of k)).inv.hom⟩
  exact .of_hom aX

end AlgebraicGeometry.ProEtale

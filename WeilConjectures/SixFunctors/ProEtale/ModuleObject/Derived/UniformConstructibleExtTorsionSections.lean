/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteLocallyProjective
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteZerothHypercohomologyOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralLisseLocalStructureAux
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-!
# The torsion stratum bound: the dual twist and its sections

Source: latest blueprint, sec-six-functors-basics/sk-lem-uniform-constructible-ext,
`sk-lem-uniform-constructible-ext-torsion.md`, clause (2), and paragraph (2) of its proof
(blueprint: det-uniform-constructible-ext-torsion-sections).

The dual twist (moved here from `Sheaf.Paper.UniformConstructibleExtTorsion`, which
re-exports it) and the hypercohomology bound deduced from clause (1).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]

/-- Clause (2) of the torsion stratum bound, deduced from clause (1) (the hypothesis
`_hsupport`, which is `uniformConstructibleExtTorsion_support`):
`H^q RΓ(S, (L₀^∨/π^n) ⊗ u^* RΓ_Z b_!(M₀/π^n)) = 0` for `q > cd_ℓ(j) + cd_ℓ(S) + 1`.
Source: latest blueprint, sk-lem-uniform-constructible-ext-torsion, clause (2) and
paragraph (2) of the proof (blueprint: det-uniform-constructible-ext-torsion-sections).

Proof: Put c = cd_ℓ(j), d = cd_ℓ(S), A = O_E/π^n and G the twist. If c or d is ⊤ the
claim is vacuous. In a local finite free basis of L₀ the coordinate functionals form a
basis of L₀^∨, so P = L₀^∨/π^n is finite locally free over A_S; by the tensor clause of
det-formal-closed-support-ii-limits the derived tensor with P is the termwise tensor, locally
a finite direct sum, hence exact. With exact u^* this gives H^v(G) = P ⊗ u^* H^v(RΓ_Z N),
zero outside [0, c+1] by clause (1), and classical ℓ^n-torsion (P descends by Tag 099Y and
tensor commutes with the exact comparison pullback). Global sections on A_S-module sheaves
is additive and left exact; the bounded hypercohomology spectral sequence
E₂^{p,v} = H^p(S, H^v(G)) ⇒ H^{p+v} RΓ(S, G) of thm-sp-truncation-e2 has E₂^{p,v} = 0 for
p > d (definition of cd_ℓ(S)) and unless 0 ≤ v ≤ c+1, so every term of total degree
q > c+d+1 vanishes and so does the abutment. -/
theorem uniformConstructibleExtTorsion_sections
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpℓ : p ≠ ℓ)
    (S Z V X T B : Over (Spec (.of k)))
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    (v : S ⟶ Z) (i : Z ⟶ X) (j : V ⟶ X) (kb : B ⟶ X) (vb : T ⟶ B)
    [IsOpenImmersion v.left] [IsClosedImmersion i.left] [IsOpenImmersion j.left]
    [IsClosedImmersion kb.left] [IsOpenImmersion vb.left]
    (_hij : Set.range i.left.base = (Set.range j.left.base)ᶜ)
    (L₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) S.left)
    (M₀ : FormalSupportModules (DerivedNakayama.integerRing ℓ E) T.left)
    (_hL₀ : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) L₀)
    (_hM₀ : IsLisseCoefficientModule (DerivedNakayama.integerRing ℓ E) M₀)
    (n : ℕ) (_hn : 1 ≤ n)
    (_hsupport : (∀ q : ℤ, q < 0 ∨ torsionStratumRelativeDimension ℓ k j + 1 <
        (q.toNat : WithTop ℕ) → IsZero ((DerivedCategory.homologyFunctor _ q).obj
          (torsionStratumSupport ℓ E i.left j.left kb.left vb.left M₀ n))) ∧
      (∀ q : ℤ, IsClassicalAbelian ((DerivedCategory.homologyFunctor _ q).obj
        (torsionStratumSupport ℓ E i.left j.left kb.left vb.left M₀ n)).X)) :
    ∀ q : ℤ, torsionStratumRelativeDimension ℓ k j + torsionStratumDimension ℓ k S + 1 <
        (q.toNat : WithTop ℕ) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((formalClosedSupportSections
          (DerivedNakayama.quotientRing ℓ E n) S.left).rightDerivedFunctor.obj
            (torsionStratumTwist ℓ E v.left i.left j.left kb.left vb.left L₀ M₀ n))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

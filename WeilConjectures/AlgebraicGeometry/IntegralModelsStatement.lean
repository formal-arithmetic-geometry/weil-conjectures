/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
/-! # Integral models for constructible l-adic complexes

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-reduction-finite-coefficients/
sec-integral-models/sk-lem-integral-models/_section.md, clauses (1)--(4)
(blueprint: sk-lem-integral-models).

Coefficients are the existing continuous condensed rings pulled back from the point.
The constant and completed ambient categories remain distinct. Completeness is the
existing local ringed-ideal predicate transported to the equivalent small site; the
constant-completion comparison identifies it with the canonical quotient-tower condition.

## Statement

The theorem below uses the canonical embedded coefficient predicates, six-functor operations,
and lattice-generator predicates already present in the library.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures.SixFunctors
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Integral models for bounded constructible complexes, clauses (1)--(4) of the current blueprint.

Source: literature/blueprint/latest/blueprint/part-six-operations/sec-reduction-finite-coefficients/
sec-integral-models/sk-lem-integral-models/_section.md (blueprint: sk-lem-integral-models).

Proof (the node's five steps):
1. Apply `det-prop-integral-criterion-constant-coefficients` (2) to the canonical
   constant-to-pulled-back coefficient map to obtain the equivalence on derived complete
   objects in clause (1).
2. Apply `det-lem-integral-models-stacks` to obtain the constructibility iff in clause (2).
3. Apply `det-lem-integral-models-operations` (1)--(3) for pullback, tensor, and locally
   closed extension by zero.
4. Apply `det-lem-integral-models-generators` (1)--(2) for finite-cone lattice generation
   over `E` and descent to one finite field over `Q̄_ℓ`.
5. Apply `det-lem-integral-models-generators` (3) to the same lattice generators; each
   reduction modulo `π^n` (`n ≥ 1`) of `a_!L₀` is bounded constructible with coefficients
   in `O_E/π^n`.

In Lean every clause is read off from `integral_models` (Sheaf.Paper.IntegralModels), whose
conclusion contains each of them: its opening finite-Tor equality and second iff of clause (2)
are dropped, and its reduction predicate `integralReductionHasEtaleOrigin` contains the bounded
constructibility of every positive reduction.
-/
theorem integral_models_statement
    (k : Type u) [Field k] (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime]
    [CharP k p] (hℓp : ℓ ≠ p) (X : Scheme.{u})
    [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    [IsNoetherian X] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : PadicAlgCl.integers ℓ E.1)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1)) :
    (∃ e : ObjectProperty.FullSubcategory (IntegralModelsEmbedded.completedComplete ℓ E π X) ≌
        ObjectProperty.FullSubcategory (IntegralModelsEmbedded.constantComplete ℓ E π X),
      Nonempty (e.functor ⋙ ObjectProperty.ι (IntegralModelsEmbedded.constantComplete ℓ E π X) ≅
        ObjectProperty.ι (IntegralModelsEmbedded.completedComplete ℓ E π X) ⋙
          IntegralModelsEmbedded.restriction ℓ E X)) ∧
    (∀ K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (integralCoefficientObject X ℓ E)),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X K ↔
        IntegralModelsEmbedded.stacksConstructible ℓ E π X
          ((IntegralModelsEmbedded.restriction ℓ E X).obj K)) ∧
    (∀ (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))]
      [QuasiCompact (Y ↘ Spec (.of k))] [IsSeparated (Y ↘ Spec (.of k))]
      [IsNoetherian Y] (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
      (K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (integralCoefficientObject Y ℓ E))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) Y K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X
        ((CondensedRing.moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.1)
          f).obj K)) ∧
    (∀ K M : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (integralCoefficientObject X ℓ E)),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X K →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X M →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X
        (((CondensedRing.derivedTensor (Profinite.padicIntegersRingObj ℓ E.1) X).obj K).obj M)) ∧
    (∀ (S V : Scheme.{u}) [S.Over (Spec (.of k))] [V.Over (Spec (.of k))]
      [LocallyOfFiniteType (S ↘ Spec (.of k))]
      [QuasiCompact (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
      [LocallyOfFiniteType (V ↘ Spec (.of k))]
      [QuasiCompact (V ↘ Spec (.of k))] [IsSeparated (V ↘ Spec (.of k))]
      [IsNoetherian S] [IsNoetherian V] (j : S ⟶ V) (i : V ⟶ X)
      [j.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
      [IsOpenImmersion j] [IsClosedImmersion i]
      (L : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (integralCoefficientObject S ℓ E))),
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) S L →
      constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.1) X
        ((CondensedRing.moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.1)
          i).obj (((CondensedRing.openImmersionLowerShriek
            (Profinite.padicIntegersRingObj ℓ E.1) j).mapDerivedCategory).obj L))) ∧
    (∀ K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (finiteCoefficientObject X ℓ E)),
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X K →
      (sInf {P | integralModelGenerator X ℓ E ≤ P ∧ P.IsTriangulated ∧
        P.IsClosedUnderIsomorphisms}) K) ∧
    (∀ K : DerivedCategory.{u + 1} (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (qlbarCoefficientObject X ℓ)),
      constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X K →
      ∃ E' : PadicAlgCl.FiniteIntermediateField ℓ,
        (sInf {P | qlbarModelGenerator X ℓ E' ≤ P ∧ P.IsTriangulated ∧
          P.IsClosedUnderIsomorphisms}) K) ∧
    (∀ (S V : Scheme.{u}) [S.Over (Spec (.of k))] [V.Over (Spec (.of k))]
      [LocallyOfFiniteType (S ↘ Spec (.of k))]
      [QuasiCompact (S ↘ Spec (.of k))] [IsSeparated (S ↘ Spec (.of k))]
      [LocallyOfFiniteType (V ↘ Spec (.of k))]
      [QuasiCompact (V ↘ Spec (.of k))] [IsSeparated (V ↘ Spec (.of k))]
      [IsNoetherian S] [IsNoetherian V] (j : S ⟶ V) (i : V ⟶ X)
      [j.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
      [IsOpenImmersion j] [IsClosedImmersion i]
      (L₀ : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
        (integralCoefficientObject S ℓ E)),
      CondensedRing.LocallyFree (integralCoefficientObject S ℓ E) L₀ →
      let K := (DerivedCategory.singleFunctor _ 0).obj
        (integralLowerShriek X (Profinite.padicIntegersRingObj ℓ E.1) j i L₀)
      ∀ n : ℕ, 1 ≤ n →
        let A := completedResidue ℓ E π (n - 1)
        let Kbar :=
          (Mod.extendScalars (integralModelReductionMap X ℓ E π n).hom).leftDerivedFunctor.obj K
        constantModelBoundedConstructible (Profinite.continuousMapRingObj A) X Kbar) := by
  have hall := integral_models k p ℓ hℓp X E π hπ
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hall
  refine ⟨h1, fun K => (h2 K).1, h3, h4, h5, h6, h7, ?_⟩
  intro S V _ _ _ _ _ _ _ _ _ _ j i _ _ _ _ L₀ hL₀
  have h := h8 S V j i L₀ hL₀
  unfold integralReductionHasEtaleOrigin at h
  intro K n hn
  exact (h.2 n hn).2.1

end AlgebraicGeometry.ProEtale

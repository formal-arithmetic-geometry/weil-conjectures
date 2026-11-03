/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenBaseChangeArbitrary
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale

/-! # Native compactification exchange construction

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-six-functors-basics/sec-brown-representability-for-all-coefficient-rings/
sk-prop-sf-existence/def-exchange-projection.md,
the compact-support exchange composite (blueprint: def-exchange-projection).

These are the existing native definitions extracted from
CondensedCompactificationReindexing without changing their names, signatures or bodies.
The named open-mate invertibility lemma needed to form its inverse is moved with them;
its statement and proof are unchanged and remain owned by its original theorem node.
Invertibility of the resulting compact-support exchange is not part of this definition.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarTensor leftDerivedUpperStarComp pullbackSquareComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem isIso_inverse_mate_aux
    {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
    {J : A ⥤ B} {Pj : B ⥤ A} {J' : A' ⥤ B'} {Pj' : B' ⥤ A'}
    {Pw : A ⥤ A'} {Rw : A' ⥤ A} {Pv : B ⥤ B'} {Rv : B' ⥤ B}
    (adj : J ⊣ Pj) (adj' : J' ⊣ Pj') (adjU : Pw ⊣ Rw) (adjA : Pv ⊣ Rv)
    (θ : Pj ⋙ Pw ≅ Pv ⋙ Pj')
    (hρ : IsIso ((mateEquiv adjA adjU (.mk _ _ _ _ θ.hom)).natTrans)) :
    IsIso (((mateEquiv adj adj').symm (.mk _ _ _ _ θ.hom)).natTrans) := by
  let b := ((mateEquiv adj adj').symm (.mk _ _ _ _ θ.hom)).natTrans
  have hθ : (mateEquiv adj adj' (.mk _ _ _ _ b)).natTrans = θ.hom := by
    exact congrArg TwoSquare.natTrans ((mateEquiv adj adj').apply_symm_apply _)
  have h := iterated_mateEquiv_conjugateEquiv adj adj' adjU adjA (.mk _ _ _ _ b)
  change (mateEquiv adjA adjU
    (.mk _ _ _ _ (mateEquiv adj adj' (.mk _ _ _ _ b)).natTrans)).natTrans = _ at h
  rw [hθ] at h
  have : IsIso (conjugateEquiv (adj.comp adjA) (adjU.comp adj') b) := h ▸ hρ
  exact conjugateEquiv_of_iso (adj.comp adjA) (adjU.comp adj') b

/-- Arbitrary-open base change for the normalized native inverse mate.
Source: the source proof, paragraph 1; native weakly etale base change
(blueprint: lem-fix-condensed-compactification-reindexing).
Proof: transpose the Cartesian square. Its open edges are weakly etale, so the
native derived direct-image exchange is invertible on every unbounded input.
The iterated-mate identity identifies this exchange with the conjugate of the
specified inverse open mate under the two composite adjunctions. Conjugation
reflects invertibility, proving the assertion for exactly the specified mate. -/
theorem openMate_isIso {A B A' B' : Scheme.{u}}
    {j : A ⟶ B} {j' : A' ⟶ B'} {w : A' ⟶ A} {v : B' ⟶ B}
    [IsOpenImmersion j] [IsOpenImmersion j'] (sq : IsPullback w j' j v) :
    IsIso (openMate Λ sq.toCommSq) := by
  unfold openMate
  apply isIso_inverse_mate_aux (oa Λ j) (oa Λ j')
    (derivedUpperStarLowerStarAdjunction Λ w) (derivedUpperStarLowerStarAdjunction Λ v)
    (pullbackSquareComparison Λ sq.toCommSq).symm
  have hρ : IsIso (baseChangeMap Λ sq.toCommSq.flip) :=
    isIso_baseChangeMap_of_weaklyEtale Λ sq.flip
  rw [baseChangeMap, Adjunction.exchangeRight_eq_mateEquiv,
    pullbackSquareComparison_flip] at hρ
  exact hρ

end AlgebraicGeometry.ProEtale.CondensedRing.CompactificationReindexing

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G7
-/
module

public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.DerivedPullbackTensorHom

/-! # Integral open compact support across an empty pullback

The integral vanishing step of the complementary restriction argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- Integral compact support along an open immersion restricts to zero whenever
the actual pullback open is empty.
Source: latest blueprint, sec-deligne-laumon-general/sk-l-dl-general-quasifinite,
lem-zl-quasi-finite.proof.md (1); Bhatt--Scholze, Lemma 6.1.12(2).
(blueprint: lem-zl-integral-open-empty-pullback-vanishing).

Proof: for the compactification (j,id), the identity direct image identifies the
strict compact-support tower with extension of the integral reduction tower.
The specified open-reduction comparison realizes this as completed ringed-site
extension by zero, retaining all quotient transitions. The integral/completed
pullback comparison identifies its restriction with the source of completed open
base change. Constructible integral objects are intrinsically complete, so that
base-change map is invertible. Its target is extension from the actual empty
pullback. The empty covering axiom makes all module sheaves on that scheme zero.
Exact extension, its termwise derived functor, and coefficient transport preserve
zero. Thus the target is zero, and the composite comparison proves the assertion.
The same argument covers an empty domain or target. No detection by separate
finite evaluations is used. -/
theorem integralOpenEmptyPullbackVanishing
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {U X Z : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j]
    (i : Z ⟶ X) [IsEmpty ↥(pullback j i : Scheme.{u})]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (K : sfIntegralConstructibleCategory l E U) :
    IsZero ((constructibleIntegralPullback l E i).obj
      ((sfCompactSupportFiniteIntegralFunctor l k hl
        (Compactification.ofIsOpenImmersion j) E).obj K)) := by
  sorry

end WeilConjectures

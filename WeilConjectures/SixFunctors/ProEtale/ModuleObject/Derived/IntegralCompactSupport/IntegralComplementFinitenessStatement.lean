/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Integral finiteness for the open-complement term of localization

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-i-heart/sk-thm-restriction/
`sk-thm-int-restriction-closed.proof.md` (det-thm-int-restriction-closed), line 5
“Let `j` be the open complement, quasi-compact since `X` is Noetherian” and lines 11–12
“Its third term lies in `Dbc(X, O_E)` by [det-thm-sf-pf-adic-open]”
(blueprint: lem-sfb-int-closed-complement-finiteness).

This module states only the third-term bounded-constructibility assertion. The
open complement is the canonical `i.left.openComplement.ι`; coefficients are the
current pulled-back condensed integral coefficient ring
`Profinite.padicIntegersRingObj ℓ E.val`, and the derived functors are the ordinary
module-object derived pullback and pushforward.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

/-- For a bounded constructible object, restriction to the open complement of a
closed immersion followed by derived direct image is bounded constructible.

Source: literature/blueprint/latest/blueprint/part-six-operations/
sec-constructibility-upper-shriek/sec-ladic-summary/sec-i-heart/sk-thm-restriction/
`sk-thm-int-restriction-closed.proof.md`, lines 5 and 11–12, open-complement
third-term step (blueprint: lem-sfb-int-closed-complement-finiteness).
The coefficient is `Profinite.padicIntegersRingObj`, i.e. the pulled-back
condensed ring of integers of the finite coefficient extension. The open
complement is the canonical open immersion supplied by
`Scheme.Hom.openComplement`; `K` is an arbitrary object of the ambient ordinary
derived category satisfying the bounded finite-constant constructibility
predicate, and the conclusion applies the same predicate to
`Rj_* L j^* K`.

Proof (the node's steps):
1. The field `k` is Noetherian, so the finite-type `X` is Noetherian; every open
   subscheme of `X` is Noetherian, hence `U` is quasi-compact and `j` is quasi-compact.
   A quasi-compact open immersion is of finite type, so `U → Spec k` is separated of
   finite type and `j` satisfies the standing hypotheses of the integral open-image
   theorem (lem-weil-pbc-finite-type-over-noetherian,
   lem-weil-pbc-noetherian-open-subscheme-noetherian,
   lem-weil-pbc-qc-open-immersion-finite-type, lem-weil-pbc-proper-fp-permanence).
2. Restrict a finite constructible stratification of each `H^q(K)` to `U`: the strata
   meet `U` in strata with the same finite constant local models
   `O_{E,V} ⊗_{O_E} P`. Cartesian coefficients make `j^*` exact, so
   `H^q(j^*K) = j^*H^q(K)` and the cohomological interval is unchanged; hence
   `j^*K ∈ Dbc(U, O_E)` (sk-def-sfb-constructible, sk-prop-sfb-cartesian-coefficients).
3. Apply det-thm-sf-pf-adic-open to the quasi-compact open immersion `j` and
   `j^*K ∈ Dbc(U, O_E)`. The standing hypothesis `hk : Finite k ∨ IsAlgClosed k`
   is part of the finite-or-algebraically-closed base-field convention; its final clause
   gives `Rj_*j^*K ∈ Dbc(X, O_E)`.
-/
theorem integralClosedComplementFiniteness
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (hk : Finite k ∨ IsAlgClosed k)
    [Fact (ringChar k).Prime]
    [Fact (ringChar k ≠ ℓ)]
    {Z X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (i : Z ⟶ X) [IsClosedImmersion i.left]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X.left)))
    (hK : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val)
      X.left K) :
    constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X.left
      ((moduleObjectDerivedPushforward (Profinite.padicIntegersRingObj ℓ E.val)
        i.left.openComplement.ι).obj
        ((moduleObjectDerivedPullback (Profinite.padicIntegersRingObj ℓ E.val)
          i.left.openComplement.ι).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport

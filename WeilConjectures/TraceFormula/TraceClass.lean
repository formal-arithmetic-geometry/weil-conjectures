/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Correspondence

/-!

# The trace class of a cohomological correspondence

The *trace class* of an endocorrespondence `c` of `(X, K)` is a Borel–Moore section
`Tr_c(u) : ℚ̄_ℓ,Fix(c) ⟶ ω_Fix(c)` of its fixed locus
(`ProEtale.CondensedRing.Correspondence.traceClass`, blueprint `def-trf-trace-class`,
`sk-d-trace-class`): the supported pairing of `u` against the diagonal correspondence
`(X, Δ, 1_K)`, through the Künneth–Verdier isomorphism `RHom(p₂^* K, p₁^! K) ≅ K ⊠ D_X K` and the
evaluation `K ⊗ D_X K ⟶ ω_X`.

## Main statements

- `ProEtale.CondensedRing.Correspondence.trace_globalOperator_eq_integral_traceClass`: the
  Lefschetz–Verdier formula `tr(T_c(u) | RΓ_c(X, K)) = ∫_Fix(c) Tr_c(u)` for `X` proper.
- `ProEtale.CondensedRing.Correspondence.integral_traceClass_ofEnd`: over the base point,
  `∫_s Tr(v) = tr(v)`.
- `ProEtale.CondensedRing.WeilBoundedConstructible.localTerm_traceClass_graph_eq_trace`: on a
  smooth curve, the local term of the Frobenius correspondence at a fixed point is the trace of
  the local Frobenius.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))}

namespace Correspondence

section

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)

/-- The *trace class* `Tr_c(u) : ℚ̄_ℓ,Fix(c) ⟶ ω_Fix(c)` of an endocorrespondence (blueprint
`def-trf-trace-class`): the supported pairing `⟨u, 1_K⟩_LV` of `u` against the diagonal
identity, carried out over the cartesian square `Fix(c) = C ×_{X × X} X`. It is the restriction
to `Fix(c)` of the class of `u` in
`Hom(Lc^* (K ⊠ D_X K), Rc^! ω_{X × X})`, through the Künneth–Verdier isomorphism and the
Verdier evaluation `K ⊗ D_X K ⟶ ω_X` (blueprint `lem-trf-trace-map-from-external-duality`).
See the module docstring for why it is sorried. -/
@[no_expose]
noncomputable def traceClass (F : c.FixedLocus) : BorelMooreSection ℓ F.F :=
  sorry

end

end Correspondence

namespace Correspondence

variable [QuasiCompact X.hom] [IsProper X.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (c : Correspondence ℓ K)

attribute [local instance] boundedConstructibleBraiding in
/-- **The Lefschetz–Verdier formula** (blueprint `thm-trf-fixed-point-localization`): for `X`
proper over `s`, an endocorrespondence `c` with proper ordinary leg `c₂` and proper fixed locus,
the trace of the global operator is the integral of the trace class,
`tr(T_c(u) | RΓ_c(X, K)) = ∫_Fix(c) Tr_c(u)`. -/
theorem trace_globalOperator_eq_integral_traceClass [IsProper c.c₂.left]
    (F : c.FixedLocus) [IsProper F.F.hom]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj K)] :
    trace c.globalOperator = (c.traceClass F).integral :=
  sorry

instance (v : K ⟶ K) : IsProper (fixedLocusOfEnd v).F.hom :=
  inferInstanceAs (IsProper X.hom)

attribute [local instance] boundedConstructibleBraiding in
/-- **Point normalization of the pairing** (blueprint `prop-trf-pairing-point-normalization`):
over the base point, the trace class of the diagonal correspondence of an endomorphism `v` of
a perfect complex integrates to the categorical trace of `v`, `∫_s Tr(v) = tr(v)`. -/
theorem integral_traceClass_ofEnd {K : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    [HasRightDual K] (v : K ⟶ K) :
    ((ofEnd K v).traceClass (fixedLocusOfEnd v)).integral = trace v :=
  sorry

end Correspondence

variable [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace WeilBoundedConstructible

variable {Φ : X ⟶ X}

attribute [local instance] boundedConstructibleBraiding in
/-- **The local term of the Frobenius correspondence on a curve** (blueprint
`thm-trf-frobenius-local-term`): let `X` be smooth of relative dimension one over `s` with the
model Frobenius `Φ` of a model `X₀` over a finite field, let `x` be a rational point fixed by
`Φ_m` and let `j : B ⟶ Fix(c_m)` be an open and closed subscheme of the fixed locus of the graph
correspondence, proper over `s`, whose underlying set is the point `x`. Then the local term of
the trace class of `φ_m` along `B` is the trace of the local Frobenius `F_{x,m}` on the
geometric stalk `K_x̄`. No local constancy of `K` at `x` is assumed. -/
theorem localTerm_traceClass_graph_eq_trace [SmoothOfRelativeDimension 1 X.hom]
    {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
    {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀} (hΦ : IsModelFrobenius Φ f₀ p)
    (K : WeilBoundedConstructible ℓ Φ) {m : ℕ} (hm : 1 ≤ m) (F : (K.graph m).FixedLocus)
    [IsProper F.F.hom] (x : RationalPoint X) (hx : x ≫ frobeniusIterate Φ m = x)
    {B : Over (Spec (.of k))} [QuasiCompact B.hom] [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (hB : Set.range j.left.base =
      {(K.fixedLocusPoint m F x hx).left.base (default : Spec (.of k))})
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      K.carrier)] :
    ((K.graph m).traceClass F).localTerm j = trace (K.stalkFrobenius m x hx) :=
  sorry

end WeilBoundedConstructible

end AlgebraicGeometry.ProEtale.CondensedRing

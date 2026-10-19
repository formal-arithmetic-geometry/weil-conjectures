## Worker report

The module `Sheaf.LinearAlgebra.FrobeniusModuleMixedSubquotient` states
`FrobeniusModule.IsMixedOfWeightsAtMost.subquotient`, with its proof postponed by `sorry`.
It uses the recorded filtration-based definition of mixedness; no new definition,
dependency module, or statement correction is needed. The current blueprint statement
and proof in `main-20261015`, and the DAG's expanded three-step proof, were read.
There is no repair note for this item.

Hypothesis and conclusion correspondence:

- The fixed coefficient context of `def-weil-frobenius-module-weights` is retained in full:
  `(p a ell : ℕ)`, the two `Fact (Nat.Prime ...)` instances, `ha : 1 ≤ a`,
  `hellp : ell ≠ p`, `Qlb : Type v`, `[Field Qlb]`, `[Algebra (ℚ_[ell]) Qlb]`,
  `hQ : IsAlgClosure (ℚ_[ell]) Qlb`, and `iota : Qlb ≃+* ℂ`. The prime power is
  `p ^ a` inside the recorded mixedness predicate; it is the same in premise and conclusion.
- The finite-dimensional vector space and invertible linear Frobenius are bundled in
  `M : FrobeniusModule.{u, v} Qlb`. Its carrier's and coefficient field's universes
  remain independent. The bound is an unrestricted `w : ℝ`.
- "If `(V,F)` is mixed of weights at most `w`" is exactly
  `hM : IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota M w`.
- "Every Frobenius-stable subquotient" is quantified by `S : Submodule Qlb M.carrier`,
  `hS : S.map M.frobenius.toLinearMap = S`, `U : Submodule Qlb S`, and
  `hU : U.map (M.frobenius.ofSubmodules S S hS).toLinearMap = U`.
  Taking `U` as a subspace of `S` directly encodes the inclusion `U ⊆ S ⊆ V`.
  The equality conditions express stability under the automorphism, as in the dependency
  definition. In finite dimension, preservation by inclusion is equivalent to these
  equalities, since the Frobenius restricts to an injective endomorphism.
- The carrier in the conclusion is literally `S ⧸ U`. Its Frobenius is
  `Submodule.Quotient.equiv U U (M.frobenius.ofSubmodules S S hS) hU`.
  These Mathlib constructions restrict the original `F` to `S` and send `[x]` to `[F x]`
  on the quotient. This is the induced action, with no arbitrary map or extra action datum.
- "Is mixed of weights at most `w`" is exactly the same recorded
  `IsMixedOfWeightsAtMost p a ell ha hellp Qlb hQ iota ... w` in the conclusion.
  It asserts a finite stable filtration with pure graded pieces, rather than merely
  an eigenvalue bound. There is no extension clause in the node's statement despite
  its identifier, so none is added.

Dependency declarations and imports:

- `Sheaf.LinearAlgebra.FrobeniusModuleWeights`,
  `FrobeniusModule.IsMixedOfWeightsAtMost`: the recorded statement dependency, read in full.
  Its purity predicate is upstream `FrobeniusModule.IsPureOfWeight` from
  `WeilConjectures.ZetaLinearAlgebra.FrobeniusModule`, also read with its full signature.
- `Mathlib.Algebra.Module.Submodule.Equiv`, `LinearEquiv.ofSubmodules`: canonical
  restriction of a linear equivalence carrying one submodule onto another.
- `Mathlib.LinearAlgebra.Quotient.Basic`, `Submodule.Quotient.equiv`: canonical induced
  quotient equivalence, already publicly imported by the statement dependency.
- Proof-only import `WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic` supplies
  `LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ` for `p-linear-filtration`.
  Its full signature and the node's current blueprint update were inspected.
- Proof-only import `WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact` retains the
  upstream material attached to `lem-a1-punctual-bound-module-mixed`. Its current source
  was read using `scompile.py --source`. The upstream
  `FrobeniusModule.hasWeightsAtMost_of_forall_hasEigenvalue` concludes the eigenvalue-based
  `HasWeightsAtMost`, so it is not silently used as the filtration-based mixedness
  criterion. The complete mathematical filtration argument is retained in the theorem's
  proof docstring. This proof dependency has no recorded `lean` field to repair here.

Edge cases checked mathematically before writing:

- `S = 0`, `U = ⊤`, and `M = 0` give the zero quotient and permit the empty mixed filtration.
- `U = ⊥` gives a stable submodule; `S = ⊤` gives an ambient quotient.
- `U = ⊤` within `S` is the ambient `U = S` case; no nonzero, strict-inclusion,
  semisimplicity, or complement hypothesis excludes it.
- Negative and zero real weights remain allowed, and `a = 1` is included.
- No continuity of `iota` or equality between the two universes is imposed.

Searches for an existing statement (all performed for this delivery):

- `msearch.py leanfinder`: "Frobenius stable subquotient of a mixed module with weights
  at most w is mixed with weights at most w". Eight hits, all Lie-module weight-space
  results (`LieModule.genWeightSpace_le_genWeightSpaceChain`, etc.); none match.
- `msearch.py loogle`: `FrobeniusModule.HasWeightsAtMost,
  FrobeniusModule.IsMixedOfWeightsAtMost`. Zero hits; the service reports the first
  identifier unknown, so this query alone is inconclusive.
- `msearch.py leansearch`: "a mixed Frobenius module remains mixed with the same upper
  weight bound on invariant subquotients". Eight hits include semisimple restrictions,
  invariant-submodule API, module filtrations, and a number-field bound; none state this lemma.
- `msearch.py grep`: `IsMixedOfWeightsAtMost|mixed.*subquotient|subquotient.*mixed`.
  Zero Mathlib hits. Direct `rg` over Mathlib also found no mixed Frobenius-module theorem.
- Direct `rg` over `WeilConjectures` and `lean/Sheaf` for mixedness and subquotient weights
  finds the dependency definition and unrelated Weil-sheaf/representation statements.
  The upstream FrobeniusModule file provides only the eigenvalue-based upper-bound
  predicate, not this finite-filtration mixedness result. Direct item-id search in
  `WeilConjectures` finds no attachment. The upstream name inventory has no theorem of
  this name. Searches for the proposed fully qualified name and module name in Mathlib,
  upstream, and `lean/Sheaf` find no collision.

No statement dispute or node fault was found. Only the item's `lean` field changes.

Validation: the module is compiled individually using the prescribed `scompile.py`
wrapper. The required `deliver2.py --no-push` preflight is run before delivery.

## Second reading by Q46

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

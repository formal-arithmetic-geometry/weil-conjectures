## Worker report

The module Sheaf.RingTheory.SplitCompletionLocalInvariantDescent states every clause of
lem-sfb-split-completion-local-invariant-descent, in two theorems. No mathematical
statement, dependency, or proof was changed. All theorem proofs are `sorry`.
The helper definitions have actual data and belong to this node's own canonical
constructions, as authorized by the missing-helper rule.

Hypotheses and constructions:

- `k : Type u`, `[Field k]`, `S : Type v`, `[CommRing S]`, `[Algebra k S]`,
  `[Algebra.FiniteType k S]` give the arbitrary field and finitely generated algebra.
- `p : Ideal S`, `[p.IsMaximal]` give the maximal ideal. The quotient `S ⧸ p`
  is exactly F, with its canonical k-algebra and field instances. The binders
  `[FiniteDimensional k (S ⧸ p)]` and `[Algebra.IsSeparable k (S ⧸ p)]`
  give precisely finite separability. No assumption is made on the dimension of S.
- `Localization.AtPrime p` is A, with its canonical localization algebra map.
- `K : Type w`, `[Field K]`, `[Algebra k K]` allow any extension field,
  independently of the universes of k and S. `ι : (S ⧸ p) →ₐ[k] K` is the
  specified k-embedding: a field algebra hom is automatically injective.
- `evaluation p ι` is the tensor-product lift of the quotient map followed by ι,
  and the identity of K. The tensor-product lift formula sends a pure tensor to
  `ι (s mod p) * λ`, exactly as required. This is a constructed map, not a parameter.
- `evaluationPoint p ι` bundles its actual kernel with Mathlib's proof
  `RingHom.ker_isPrime`. `geometricStalk p ι` is the localization at that kernel.
- `completedGeometricStalk p ι` is `AdicCompletion` for the ideal obtained by mapping
  that kernel into B. Thus the ideal is literally n = qB, rather than an unspecified
  ideal or a second completion. Mathlib's `Localization.AtPrime.map_eq_maximalIdeal`
  also identifies it with the maximal ideal when the completion proof is undertaken.

Conclusions, clause by clause:

1. `split_node_axes` quantifies over every field L independently of the local-algebra
   data. `IsReduced` of the displayed `MvPowerSeries (Fin 2) L` quotient by the span
   of `X 0 * X 1` says that this ring has no nonzero nilpotents. The existential ring
   hom E is injective, and the two coefficient equalities, for every h and n, identify
   its composite with the quotient map with h(u,0) and h(0,v), respectively. For n=0
   both coefficient indices are zero, so the constants agree automatically. Specifying
   every coefficient determines the map uniquely; no arbitrary embedding is substituted.
2. `split_completion_local_invariant_descent` gives a ring map f from A to B, with
   its exact equation on every s in S, and `Function.Injective f`. The equation
   determines f uniquely: maps out of the localization are determined on S, as in
   Mathlib's `Localization.localRingHom_unique`. In particular it forces
   s/u to map to (s tensor 1)/(u tensor 1). Its existence is part of the conclusion,
   with no new hypothesis or externally chosen map. The next `Function.Injective`
   is for the actual `algebraMap B (completedGeometricStalk p ι)`, the completion map.
3. `Nonempty (completedGeometricStalk p ι ≃+* (...))` is existence of a ring
   isomorphism with the split-node model, with no K-linearity. The implication gives
   `IsReduced` of the completion, B, and A in that order, exactly the three conclusions.

Sources read: literature/stacks-project/curves.tex, lemma-nodal-algebraic (Tag 0C49),
particularly the opening of the proof of (3) => (1), and lemma-nodal (Tag 0C4D),
the arbitrary-field flat-descent paragraph. These justify reducedness of the split
model and descent through the specified geometric stalk. The node proof is included
step by step in the two theorem docstrings.

Dependency interfaces read and used:

- def-weil-pbc-finite-type-algebra: Mathlib.RingTheory.FiniteType,
  `Algebra.FiniteType`; its recorded `RingHom.FiniteType` is definitionally the same
  predicate on `algebraMap k S`.
- def-weil-pbc-separable-algebraic-extension: Mathlib.FieldTheory.Separable,
  `Algebra.IsSeparable`.
- def-weil-pbc-localization-at-prime: Mathlib.RingTheory.Localization.AtPrime.Basic,
  `Localization.AtPrime` and its canonical `algebraMap`.
- def-weil-pbc-module-tensor-product: Mathlib.LinearAlgebra.TensorProduct.Defs,
  `TensorProduct`; the algebra structure and canonical lift are from
  Mathlib.RingTheory.TensorProduct.Maps, `Algebra.TensorProduct.lift`.
- def-weil-pbc-adic-completion: Mathlib.RingTheory.AdicCompletion.Basic,
  `AdicCompletion`, with the actual ring and algebra structures from
  Mathlib.RingTheory.AdicCompletion.Algebra.
- def-weil-pbc-multivariate-power-series: Mathlib.RingTheory.MvPowerSeries.Basic,
  `MvPowerSeries`, `MvPowerSeries.X`, and `MvPowerSeries.coeff`; one variable uses
  Mathlib.RingTheory.PowerSeries.Basic, `PowerSeries` and `PowerSeries.coeff`.
- def-weil-pbc-algebra-hom-quotient: Mathlib.Algebra.Algebra.Hom, `AlgHom`, and
  Mathlib.RingTheory.Ideal.Quotient.Operations, `Ideal.Quotient.mkₐ`, with
  `Ideal.span`, the quotient ring and its canonical map.

Proof-only imports carry the available proof interfaces:
Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors (`MvPowerSeries.instNoZeroDivisors`),
Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
(`Ideal.comap_map_eq_self_of_faithfullyFlat`), and
Mathlib.RingTheory.AdicCompletion.AsTensorProduct plus LocalRing
(`AdicCompletion.flat_of_isNoetherian`, the local-ring and local-hom instances,
then `Module.FaithfullyFlat.of_flat_of_isLocalHom`). The existing proof dependency
lem-trf-separable-evaluation-local-base-change has no Lean record, Mathlib match,
or upstream closed declaration in the read node; consequently there is no module
of that proof dependency to import. It is not needed to type this statement.

Edge cases checked before writing: characteristic two (uv and the kernel calculation
use no division by 2); K=k; nonalgebraically closed K; nonreduced S such as dual
numbers, where the injections still hold but the split-completion hypothesis fails;
S a field, where injectivity remains and the conditional split-node premise fails;
the zero algebra, which admits no maximal ideal and thus introduces no spurious case;
constant terms and the zero series in the axis map; separate arbitrary universes u,v,w.

Searches actually run using msearch.py for this item:

- LeanSearch: "The quotient of bivariate formal power series by xy injects into the
  product of power series on the axes and is reduced". Eight hits, including
  `Ideal.injective_quotient_le_comap_map` and `MvPolynomial.coe_injective`, but no
  statement of the axis-map kernel, split-quotient reducedness, or the complete item.
- LeanFinder: "A finite type local algebra injects into the completion of its
  localization after extension of the base field at a separable rational point".
  Eight hits including Noether normalization and formally unramified algebra results;
  none is this statement.
- Loogle: `MvPowerSeries, "ker"`. Two hits, `MvPowerSeries.ker_map_of_fg` and
  `MvPowerSeries.ker_mapAlgHom_of_fg`; both concern coefficient maps, not axis restriction.
- Mathlib grep: `IsReduced|subst.*ker|axis|axes` under RingTheory/MvPowerSeries;
  zero hits. Direct rg searches of lean/WeilConjectures and lean/Sheaf for split-node,
  axis, evaluation-localization, and the item id found existing split-node model
  definitions and geometric-fibre statements, but no statement with these three clauses.
  The model in AlgebraicGeometry.NodalFiber.powerSeriesQuotient was read; the present
  theorem uses the underlying Mathlib quotient directly and does not redefine that model.
  Full proposed declaration names were also searched in both libraries and
  dag/lean_names_upstream.json, with no conflicts.

Validation: scompile.py compiled the module in module mode against the live server
library cleanly, with no errors or non-sorry warnings. No global build was run.
No statement dispute, correction, new independent notion, or unusable dependency interface.

## Second reading by Q100

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

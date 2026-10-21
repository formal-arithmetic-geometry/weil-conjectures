## Worker report

The module `Sheaf.RingTheory.IntegralClosureIndEtaleBaseChange` states
`TensorProduct.toIntegralClosure_bijective_of_indEtale`, with its proof `sorry`.
It uses the actual canonical comparison `TensorProduct.toIntegralClosure`, rather
than choosing an unspecified algebra isomorphism. Its bijectivity is exactly
that this S-algebra map is an isomorphism: `AlgEquiv.ofBijective` provides the
inverse without changing the forward map. Nothing is proved in this delivery,
and no definition or helper axiom is introduced.

The earlier attempt's supersession diagnosis concerned the stage-1 split. The
live node is split and reviewed PASS, but has no `lean` record; stage 2 remains
necessary. This packet leaves that split, its statement, and all dependencies
unchanged. No repair note exists for this item.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Commutative rings R, B, S | `(R : Type u) (S : Type v) (B : Type w)` and their three `CommRing` instances, with explicit independent universes |
| Ring maps R to B and R to S | `[Algebra R B] [Algebra R S]`; a ring map of commutative rings defines exactly such an algebra structure via `RingHom.toAlgebra` |
| R to S is ind-etale, a filtered colimit of finitely presented etale algebras | `hS : RingHom.IndEtaleAcrossUniverses (algebraMap R S)`, the dependency's recorded predicate; it is `RingHom.IndEtale` on the canonical ULift map into the common maximum universe, and ultimately `Algebra.IndEtale.exists_colimitPresentation`; `Algebra.Etale` includes finite presentation |
| C is the integral closure of R in B | `integralClosure R B`, in the source of `TensorProduct.toIntegralClosure R S B`; its carrier is exactly `{x | IsIntegral R x}` |
| S tensor B has its tensor-product algebra structure and multiplication | Mathlib's algebra tensor-product ring and S-algebra instances, used by `TensorProduct.toIntegralClosure`; they give `(s tensor b) * (s' tensor b') = (s*s') tensor (b*b')` |
| C_S is the integral closure of S in S tensor B | Codomain `integralClosure S (S ⊗[R] B)` of that canonical map |
| Canonical S-algebra map S tensor C to C_S, s tensor c maps to s tensor c | `TensorProduct.toIntegralClosure R S B`, whose full definition is `(Algebra.TensorProduct.map (.id _ _) (integralClosure R B).val).codRestrict ...`; the codomain restriction changes only the integrality proof |
| This canonical map is an isomorphism | `Function.Bijective (TensorProduct.toIntegralClosure R S B)`; for an algebra hom this is equivalent to being an algebra isomorphism, with that same map, using `AlgEquiv.ofBijective` |
| No injectivity, domain, Noetherian, finiteness, nonemptiness or local-ring assumption | None of these is a binder or instance. There are only the displayed commutative ring and algebra structures and the single ind-etale hypothesis |

Dependency declarations read and used:

- `def-weil-pbc-ind-etale-algebra`: `Sheaf.RingTheory.IndEtaleUniverseTransport`,
  `RingHom.IndEtaleAcrossUniverses`; its public import is
  `Sheaf.RingTheory.IndPrincipalZariski`, which exposes
  `WeilConjectures.RingTheory.ProEtale.IndEtale` and `Algebra.IndEtale`.
  The latter's class field gives a filtered colimit presentation with etale terms.
- `def-weil-pbc-integral-closure`:
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `integralClosure` and
  `IsIntegral` (publicly reached through Smooth.IntegralClosure).
- `def-weil-pbc-module-tensor-product`: its Mathlib leaf is `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, with the tensor algebra structure
  and canonical map supplied by `Mathlib.RingTheory.Smooth.IntegralClosure`.
  This dependency has a `mathlib_match` and needs no new `lean` record.
- The finite-etale proof dependency is a Mathlib leaf:
  `Mathlib.RingTheory.Smooth.IntegralClosure`,
  `TensorProduct.toIntegralClosure_bijective_of_smooth`, specialized using
  etale implies smooth as recorded in its match.
- Proof import `WeilConjectures.CategoryTheory.ExistsDirectedReindexing`:
  `CategoryTheory.exists_directed_reindexing`.
- Proof import `WeilConjectures.RingTheory.FilteredColimitAlgebrasTensorElementwise`:
  `CommAlgCat.filteredColimit_tensorProduct_elementwise` and its companion
  universal and ring-hom clauses.
- Proof import `WeilConjectures.RingTheory.IntegralElementsColimitDescent`:
  `RingHom.exists_integral_tensor_generators_of_colimit`.

All five proof steps of the reviewed node are in the theorem docstring:
reindex the presentation and identify the etale-stage comparisons; lift tensor
elements and map monic equations; use eventual zero and stage injectivity;
descend a singleton integral element on an upper tail (including the passage
from an algebra colimit to a ring colimit and tensor cancellation); use stage
surjectivity. The docstring also explains the canonical ULift transport back
for the independent ring universes. No stronger smoothness hypothesis is used
in the theorem statement.

Edge cases checked before writing:

- S = 0: both the source and target comparison rings are zero; no nonzero-ring
  instance is required. B = 0 behaves in the same way. R = 0 admits only the
  compatible trivial target algebras, which are included.
- R to B need not be injective (for instance Z to Z/2 with S = R). The integral
  closure and canonical tensor comparison use algebra maps, never inclusions
  of R in B. R to S may also be noninjective; it is only assumed ind-etale.
- Noninjective transitions in the filtered presentation cause no problem:
  eventual-zero, rather than injective transition maps, is used in the proof.
- The tensor-product ring multiplication and the S-algebra structure are the
  standard ones, with no extra tower or flatness hypothesis added.
- Filteredness already supplies a nonempty indexing category, and there is no
  externally quantified index or additional nonempty-ring hypothesis.
- Independent u, v, w retain all ring sizes. The recorded ULift predicate
  transports R and S to max u v rather than imposing u = v.
- S = R with its identity algebra map is covered, as are arbitrary etale
  algebras and filtered colimits of etale stages that are not themselves
  finitely presented. The smooth Mathlib theorem alone does not cover the last
  case, so recording it as an existing match for this item would be incorrect.

Searches for existing statements (2026-10-21 UTC):

- `msearch.py ... leanfinder "Integral closure commutes with base change by a
  filtered colimit of etale algebras"`: 8 hits, including
  `TensorProduct.toIntegralClosure`, localization base change and integrality
  base change. None asserts the ind-etale comparison is bijective.
- `msearch.py ... loogle '"toIntegralClosure"'`: 7 hits: the map, smooth,
  localization, polynomial, tower and flat injectivity statements. No ind-etale
  or filtered-colimit bijectivity statement.
- `msearch.py ... grep
  'toIntegralClosure_bijective|integralClosure.*[Cc]olimit|[Ii]ndEtale.*[Ii]ntegral'`:
  6 hits, all for smooth/localization/tower versions in Mathlib, not this item.
- `msearch.py ... leansearch "Integral closure commutes with ind etale base
  change"`: 8 hits (`integralClosure`, `IsIntegralClosure`,
  integrality and etale base-change facts); no exact ind-etale comparison theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for integral-closure/tensor
  and ind-etale combinations: normalization localization/stalk results,
  integral Dedekind results and a henselian integrality statement, none with
  the present assertion. The item's id occurs in
  `Sheaf.AlgebraicGeometry.SNCTameRootEtaleExtension` only in proof docstrings.
  Searching the exact new declaration name finds no existing declaration.
- Read Stacks `literature/stacks-project/algebra.tex`,
  `lemma-integral-closure-commutes-colim-smooth` (Tag 0CBF), directly. It asserts
  the same canonical-map isomorphism for filtered colimits of smooth algebras;
  the item's etale specialization is valid without additional hypotheses.

No statement fault or STATEMENT-DISPUTED issue was found. No new nodes,
dependency modules or statement corrections are needed.

Validation: the prescribed `scompile.py` server check passed for both the
sandbox and library-module views (3.8 s and 2.9 s), with no errors or warnings.
The prescribed `deliver2.py --no-push` check returned OK: the packet passes
server preflight and compiles. Only the item's `lean` field changes; the delivery
contains one Lean module, its node copy, and this report.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

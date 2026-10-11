## Worker report

The module states `Algebra.Extension.smooth_conormal_sequence_exact` in
`lean/Sheaf/RingTheory/SmoothConormalSequenceExact.lean`. Its binders are commutative rings
`A`, `B`, `C`, algebra structures for the maps `A → B`, `B → C`, and `A → C`, and the scalar
 tower expressing commutativity, together with smoothness of `A → B` and surjectivity of `A → C`.
The existential `hβ` records the induced surjectivity of `B → C`. The two existential clauses
record the `C`-linear map from the cotangent module of `ker(A → C)` to that of `ker(B → C)`.
The displayed generator equation renders the map induced by `A → B`; `Function.Injective u`
renders exactness at the first term. `Function.Exact u cotangentComplex` renders exactness at
`J/J²`, and `Function.Surjective cotangentComplex` renders exactness at the final differential
module. Mathlib's `Algebra.Extension.Cotangent` is `I/I²`, and its `cotangentComplex` sends a
class to `1 ⊗ db`; this is the tensor-order equivalent of `db ⊗ 1` in the node.

The statement uses Mathlib's `Algebra.Smooth` (the node dependency
`def-weil-pbc-smooth-ring-map`) and the Mathlib Kähler differential and extension declarations
(the node dependency `def-weil-pbc-kahler-differentials`):
`Algebra.Extension.ofSurjective`, `Algebra.Extension.Cotangent`,
`Algebra.Extension.Cotangent.mk`, and `Algebra.Extension.cotangentComplex`.
The proof is `sorry`, as required at stage 2; its docstring gives the five proof steps from
Stacks Tags 06A9, 06A7, and 065V.

Edge cases checked: `A → C` may have zero kernel; `B → C` is not assumed separately because
surjectivity follows from the scalar tower; the index-free conormal modules allow zero rings and
zero modules; no finiteness or characteristic hypotheses were added.

Searches for an existing statement or definition: `msearch.py leanfinder` query “smooth algebra
A B surjective A C exact conormal sequence I/I² J/J² Kähler differentials” returned only general
Mathlib cotangent and formal-smoothness lemmas, with no exact sequence. `msearch.py loogle`
query “Ideal.mapCotangent, Algebra.Smooth” returned no direct match. `msearch.py grep` query
“conormal|mapCotangent|kerCotangentToTensor” in `RingTheory` found only the general maps and
exactness lemmas, not this smooth three-ring sequence. `rg` over Mathlib and
`WeilConjectures/` found no declaration for this node. The Stacks pages confirm Tag 06A9 states
`0 → I/I² → J/J² → Ω_{B/A} ⊗_B B/J → 0`, while Tag 065V gives the right-exact sequence.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader. The module and node were checked against each clause of
Tags 06A9 and 065V before compilation; no statement correction or disputed-statement marker is
needed.

## Second reading by F1

I independently opened the sandbox node and module, both statement-dependency nodes, and
their recorded Mathlib declarations. The repository has no local Stacks checkout. I read
the published Tags [06A9](https://stacks.math.columbia.edu/tag/06A9),
[065V](https://stacks.math.columbia.edu/tag/065V), and
[06A7](https://stacks.math.columbia.edu/tag/06A7), then fetched the upstream `algebra.tex`
into the sandbox scratchpad. Its labels and line numbers agree with the node:
`lemma-application-NL-smooth` at 38386, `lemma-application-NL` at 35519, and
`lemma-application-NL-formally-smooth` at 38079. I also read the conventions at line 36
and the introductions to the relevant sections. Rings are commutative with unity,
including the zero ring; no Noetherian, field, characteristic, or local-ring hypotheses
are assumed throughout these sections.

The following is my object/hypothesis/conclusion inventory and matching verdict.

| Node object or clause | Lean rendering and verdict |
| --- | --- |
| Commutative rings A, B, C | `{A : Type u} {B : Type v} {C : Type w}` and three `CommRing` instances. Exact; three independent universes, no nonzero assumption. |
| Ring map A → B | `[Algebra A B]`, with `algebraMap A B`. Exact: any unital map of commutative rings induces this algebra structure. |
| Ring map π : A → C, surjective | `[Algebra A C]` and `hπ : Function.Surjective (algebraMap A C)`. Exact; surjectivity is an input, not inferred from smoothness. |
| Ring map β : B → C | `[Algebra B C]`; `IsScalarTower.toAlgHom A B C` has underlying map `algebraMap B C`. Exact; β is universally quantified through its algebra structure, not selected existentially. |
| β composed with A → B equals π | `[IsScalarTower A B C]`. Exact: for these commutative algebra structures this expresses the commuting triangle, without assuming any map injective. |
| A → B smooth | `[Algebra.Smooth A B]`. Exact recorded declaration of `def-weil-pbc-smooth-ring-map`; it combines formal smoothness and finite presentation. |
| Induced surjectivity of β | `∃ hβ : Function.Surjective (IsScalarTower.toAlgHom A B C)`. Exact derived fact; no extra input hypothesis. The witness is a proof used to construct the second extension. |
| I = ker π and J = ker β | `.ker` of `ofSurjective (Algebra.ofId A C) hπ` and `ofSurjective (IsScalarTower.toAlgHom A B C) hβ`. Exact; I is the kernel in A, J the kernel in B, not kernels of polynomial presentations. |
| C-modules I/I² and J/J² | The two extensions' `.Cotangent`. Exact: `Extension.Cotangent` is the type synonym of `P.ker.Cotangent`; `Cotangent.mk_eq_zero_iff` identifies its killed submodule with the square ideal. Its C-action is quotient descent using the surjective extension, not a different scalar action. |
| u induced by A → B, C-linear | `∃ u : ...Cotangent →ₗ[C] ...Cotangent`, together with the equation for every `a : I`, `b : J` satisfying `b.1 = algebraMap A B a.1`. Exact. The commuting triangle supplies such b for every a, and `Cotangent.mk_surjective` shows the equation fixes u on the entire domain. The existential does not allow an unrelated map. |
| v sends b mod J² to db ⊗ 1 | The second extension's `.cotangentComplex`. Exact: its signature is C-linear into `C ⊗[B] Ω[B⁄A]`, and `cotangentComplex_mk` is `1 ⊗ D A B b`. Tensor symmetry identifies this canonically with the node's `Ω[B⁄A] ⊗[B] C` and the stipulated generator formula. C is canonically B/J via β. |
| Exactness at I/I² | `Function.Injective u`. Exact equivalent of the initial zero term. |
| Exactness at J/J² | `Function.Exact u ...cotangentComplex`. Exact: Mathlib's additive `Function.Exact` says `v y = 0 ↔ y ∈ Set.range u`, including vanishing of the composite. |
| Exactness at the differential module | `Function.Surjective ...cotangentComplex`. Exact equivalent of the final zero term. No splitting or freeness is added to the conclusion. |

Dependency audit: I read `Smooth/Basic.lean` lines 65–78 and 530–550, not just the
name `Smooth`. Its formal smoothness fields are projectivity of the Kähler module and
vanishing of `H1Cotangent`, with finite presentation supplying the finiteness in the
node's smoothness definition. I read `Kaehler/Basic.lean` for `KaehlerDifferential`,
`KaehlerDifferential.D`, and `linearMapEquivDerivation`: these give exactly the pair
and universal property in `def-weil-pbc-kahler-differentials`. I additionally read
`Extension/Basic.lean` for `ofSurjective`, `Cotangent`, its C-module instance and
`Cotangent.mk`, and `Extension/Cotangent/Basic.lean` lines 58–68 for the second map.
Both recorded dependencies are usable through the module's Mathlib import. No new
definition nodes, private copies, or dependency modules are needed or delivered.

Edge cases: if π is an isomorphism, I/I² is zero and the formulation still asserts
the expected injectivity and middle exactness. Taking A = B and β = π makes u the
identity on I/I² and Ω[B/A] zero. Taking C the zero ring is permitted: I = A and
J = B have I² = I and J² = J, and all three terms are zero. The zero source ring
forces zero target rings under unital maps, also permitted. No positive-characteristic
case is excluded. The rings have separate declared universes and there is no
quantification over smaller-universe test objects. Empty schemes, empty index sets,
and n = 0 introduce no extra requirements here: the statement has no schemes,
index families, or integer parameter, and makes no positive generator-count demand.

Independent searches (recorded in `searches.jsonl`):

- LeanFinder: “A commutative triangle of ring homomorphisms with smooth first arrow
  and surjective composite gives an injective map of kernel cotangent modules and
  a short exact sequence”. Eight hits; I opened the relevant
  `Algebra.FormallySmooth.iff_split_injection`, `kerCotangentToTensor_injective_iff`,
  `Algebra.Extension.cotangentComplex_injective_iff`, and Jacobi–Zariski exactness
  statements. These concern injectivity of J/J² into a tensor of differentials,
  or the H1 sequence, not this injective I/I² → J/J² with all three clauses.
- LeanSearch: “The conormal modules of compatible quotients of a ring and its smooth
  algebra form a short exact sequence with relative differentials”. Service returned
  Internal Server Error; this is recorded as unavailable, with no search verdict.
- Mathlib grep: `split.*[Cc]otangent|[Cc]otangent.*(injective|exact)|06A9|065V` in
  RingTheory. Found standard-smooth presentation maps, general cotangent criteria,
  Jacobi–Zariski, and flat tensor-cotangent base change; none states the whole item.
- Independent `rg` on `WeilConjectures/` and repository `lean/Sheaf` for
  `smooth_conormal|06A9|065V|conormal|mapCotangent`: found scheme conormal definitions,
  localization and regular-sequence results, and other different conormal lemmas.
  None states this triangle-of-rings theorem. Searches by the item id and declaration
  in `WeilConjectures/` and `dag/lean_names_upstream.json` had no match.

H5–H9: there are no definitions in the delivery and the only theorem proof is `sorry`.
The module and theorem docstrings have the source and exact blueprint id. I matched
the five docstring proof steps to the node: maps and surjectivity; square-zero lift σ;
left inverse r; derivation δ and factorization s giving middle exactness; conclusion.
The full declaration name is under `Algebra.Extension` with no `Sheaf` prefix or
file-local notation/instance. All object and universe variables are explicitly bound;
the map variable named u merely shadows the universe name in a separate syntactic
class. Every Lean line meets 100 characters. The node's `lean.statement` is verbatim
equal to the source signature, verified by direct string comparison.

Mismatches found: none. I preserved the Lean file and node record and appended this
independent review, leaving `## Worker report` and the explicitly superseded earlier
section intact. No statement correction is required. Server compilation with the
prescribed `scompile.py` command passed in 1.5 seconds, with exit code 0 and no
reported warnings or errors. The stage-2 proof remains intentionally `sorry`.

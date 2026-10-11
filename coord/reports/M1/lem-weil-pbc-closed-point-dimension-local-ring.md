## Worker report

The module `Sheaf.RingTheory.ClosedPointDimensionLocalRing` states
`AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_localizationAtMaximal`.
Its only theorem has a `sorry` proof; its docstring carries all six steps of the node's proof
and the dependency ids used in them. No definitions or extra nodes are needed, and the item's
node copy changes only its `lean` record.

Hypothesis and clause correspondence:
- A field k: `{k : Type u} [Field k]`.
- A commutative k-algebra S: `{S : Type v} [CommRing S] [Algebra k S]`.
- Finitely generated, a quotient of a polynomial ring in finitely many variables:
  `hfg : ∃ (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] S), Function.Surjective f`.
  This is precisely finite generation, rather than a choice of presentation: Mathlib's
  `Algebra.FiniteType.iff_quotient_mvPolynomial''` has this exact right-hand side.
- A maximal ideal m of S: `(m : Ideal S) [m.IsMaximal]`. Maximality supplies primality.
- Its associated closed point in Spec S: `⟨m, inferInstance⟩ : Spec (CommRingCat.of S)`.
  The underlying space of this scheme is definitionally `PrimeSpectrum S`.
- Topological dimension at this point: `topologicalKrullDimAt` of that point, the infimum
  of dimensions of its open neighbourhoods, exactly the recorded dependency definition.
- Localization at m: `Localization.AtPrime m`, the canonical localization at its complement.
- Krull dimension of this ring: `ringKrullDim (Localization.AtPrime m)`.
- The node's equality: the equality of these two expressions in `WithBot ℕ∞`.

Dependency declarations read and used:
- `def-weil-pbc-mv-polynomial-ring`: Mathlib match `MvPolynomial` in
  `Mathlib.Algebra.MvPolynomial.Basic` (its abbreviation and docstring read); its recorded
  universal-property declarations `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval`
  and `MvPolynomial.algHom_ext` in Basic were also read. Only the polynomial type is needed.
- `def-weil-pbc-localization-at-prime`: Mathlib match `Localization.AtPrime` in
  `Mathlib.RingTheory.Localization.AtPrime.Basic` (full abbreviation and surrounding
  `IsLocalization.AtPrime` signature read). Residue fields and fibre rings are not clauses
  of this item and are not used.
- `def-weil-affine-spectrum`: Mathlib match `AlgebraicGeometry.Spec` in
  `Mathlib.AlgebraicGeometry.Scheme` (full definition and `Spec.map` read).
- `def-kun-topological-dimension-at-point`: recorded `topologicalKrullDimAt` in
  `WeilConjectures.Mathlib.Topology.KrullDimension` (full definition and docstring read).
- `def-weil-pbc-krull-dimension-ring`: recorded `ringKrullDim` in
  `Mathlib.RingTheory.KrullDimension.Basic` (full definition and docstring read).

Edge cases checked before writing: n = 0 is allowed (Fin 0, so a quotient of k itself).
S = k gives both dimensions zero. A zero algebra has no maximal ideal, so the theorem has
no instance at such an ideal, as in the source; no explicit Nontrivial assumption is added.
Finite products, nonreduced algebras and components of differing dimensions are allowed:
no domain, reducedness or equidimensionality hypothesis is present, and the proof removes
only components not passing through m. The field has arbitrary characteristic and need
not be algebraically closed. The two universes u and v are independent. Both dimension
expressions retain the extended values, with no finiteness or natural-number coercion
assumption. Maximality is essential: the generic point of Spec k[t] has local topological
dimension one but its localization is a field, of dimension zero.

Searches (2026-10-11):
- `msearch.py leansearch`, query "dimension of spectrum at a closed point of a finite type
  algebra over a field equals dimension of local ring": unavailable, Internal Server Error;
  no verdict assigned to this unavailable service.
- `msearch.py leanfinder`, query "Krull dimension of Spec of a finitely generated algebra
  over a field at a closed point equals dimension of the localization at the maximal ideal":
  eight hits, including `IsLocalization.AtPrime.ringKrullDim_eq_height`,
  `Ring.krullDimLE_of_isLocalization_maximal` and local-ring height/dimension results;
  none states the local topological dimension equality.
- `msearch.py loogle`, query "topologicalKrullDim, ringKrullDim": only
  `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`, the global equality, not this statement.
- `msearch.py grep`, query `topologicalKrullDimAt|ringKrullDim_eq_height`: five hits for
  localization/height and applications, no local dimension definition or equality in Mathlib.
- `rg` of `topologicalKrullDimAt|closed.point.*dimension|dimension.*closed.point` in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's `lean/Sheaf`:
  the recorded local dimension definition and smooth-relative-dimension statements;
  no theorem for arbitrary finite type algebras. `grep -rn` of the item's id in the
  source project returned no hits.
- `rg` of the proposed name and of `topologicalKrullDimAt.*AtPrime` in
  `dag/lean_names_upstream.json`, the source project and `lean/Sheaf`: no hits.

The local literature file `literature/stacks-project/algebra.tex` is absent on this machine.
Read the primary-source pages https://stacks.math.columbia.edu/tag/00OU and
https://stacks.math.columbia.edu/tag/00OT instead: 00OU is exactly this statement, and
00OT supplies the proof specialized to a maximal ideal. No statement fault, correction or
dispute was found.

Server validation: `scompile.py M1 lem-weil-pbc-closed-point-dimension-local-ring` on this
module exited 0, compiled in 1.5 seconds, and emitted no warnings or errors.

## Second reading by M1

Independent second reading, 2026-10-11. I opened the delivered node and module,
all five statement dependency nodes and their recorded source declarations.
The local Stacks checkout is absent. I independently read the primary-source
`algebra.tex` from https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
including the section introduction, `lemma-dimension-closed-point-finite-type-field`
(00OU), and `lemma-dimension-at-a-point-finite-type-over-field` (00OT), its proof.
The rendered tags https://stacks.math.columbia.edu/tag/00OU and
https://stacks.math.columbia.edu/tag/00OT agree. No additional ambient hypothesis
is assumed in this section: Noetherian and Jacobson properties are consequences.

Object/hypothesis/conclusion checklist, written from the node before comparison:

- Field k: `{k : Type u} [Field k]`. Exact; no algebraic closure or characteristic
  restriction is assumed.
- Commutative k-algebra S: `{S : Type v} [CommRing S] [Algebra k S]`. Exact;
  no domain, reducedness, equidimensionality, or separate Noetherian instance.
- Finite generation, equivalently a quotient of k[x_1,...,x_n]:
  `(hfg : ∃ (n : ℕ) (f : MvPolynomial (Fin n) k →ₐ[k] S), Function.Surjective f)`.
  Exact. I read `Algebra.FiniteType.iff_quotient_mvPolynomial''` in
  `Mathlib/RingTheory/FiniteType.lean:174`: its right-hand side is precisely this
  hypothesis, so this does not impose a stronger presentation condition.
  The witnesses n and f are existential inside hfg, not extra fixed data.
- Maximal ideal m of S: `(m : Ideal S) [m.IsMaximal]`. Exact. The inferred prime
  proof supplies the associated point and localization; no independent primality
  assumption is added.
- X = Spec S and its associated closed point: the type annotation
  `(⟨m, inferInstance⟩ : Spec (CommRingCat.of S))`. Exact. I read `Spec` in
  `Mathlib/AlgebraicGeometry/Scheme.lean:470`; its underlying space is the prime
  spectrum with the Zariski topology, so this point is the original ideal m.
  X and x are determined objects in the source, not separately quantified choices.
- Localization S_m: `Localization.AtPrime m`. Exact. I read the abbreviation
  in `Mathlib/RingTheory/Localization/AtPrime/Basic.lean:57` and its surrounding
  `IsLocalization.AtPrime` declaration: localization at `m.primeCompl`.
  The dependency's residue-field and fibre-ring clauses are not needed here.
- Topological dimension at x: `topologicalKrullDimAt` applied to the above point.
  Exact. I read its definition at
  `WeilConjectures/Mathlib/Topology/KrullDimension.lean:333`, with its ambient
  `{X : Type*} [TopologicalSpace X]`: the infimum over open neighbourhoods of
  their topological Krull dimensions with the subspace topology. This is the
  minimum in the dependency node since the extended natural values are well ordered.
- Ring dimension of S_m: `ringKrullDim (Localization.AtPrime m)`. Exact.
  `Mathlib/RingTheory/KrullDimension/Basic.lean:30` defines this as
  `Order.krullDim (PrimeSpectrum R)`, the supremum of strict prime-chain lengths.
- Conclusion: equality of the preceding dimensions in `WithBot ℕ∞`. Exact;
  neither an inequality, nor equality to the global dimension of S, nor a
  coercion to finite natural dimensions. Quantifier order agrees with the node.

Dependency audit (H4, H12, H13): the polynomial type is the recorded
`MvPolynomial` in Basic.lean:82, an additive monoid algebra on finitely supported
exponent vectors. I also opened its recorded universal-property declarations
`MvPolynomial.aeval` in Eval.lean:593 and `MvPolynomial.algHom_ext` in Basic.lean:436;
no replacement definition is present. The other four recorded notions are the
ones named in the checklist. Each is usable for these objects and universes.
There are no new definition nodes or replacement dependency modules to audit.
The delivered item has no `statement_change`; its natural-language statement,
proof, and dependencies are unchanged, so a correction/citer audit is inapplicable.

Edge cases: n = 0 and its empty variable set are allowed by `Fin n`; a quotient
of k that has a maximal ideal is a field, with both dimensions zero. S = 0 and
its empty spectrum have no maximal ideal and hence supply no input m, exactly
as in the source. There is no unrelated index family quantified here. Products,
nilpotents and components of different dimensions are permitted. Both field
characteristics, finite or infinite fields, and non-algebraically-closed fields
are covered. Universes u and v are independently declared and bound. The
extended-valued equality imposes no hidden finiteness hypothesis. Opens through
m are nonempty, so their dimensions do not invoke the empty-space bottom case.
A merely prime generic point is deliberately excluded by maximality, as required.

Independent searches, with different wording from the worker's queries:

- `msearch.py ... leanfinder "local dimension at a maximal prime of an affine
  variety agrees with Krull dimension of the stalk"`: eight hits, including
  `IsLocalization.AtPrime.ringKrullDim_eq_height`, local maximal-ideal height
  identities, and localization dimension bounds. None equates dimension at a
  point of the topological spectrum with dimension of its local ring.
- `msearch.py ... loogle "topologicalKrullDimAt"`: unknown identifier in Mathlib;
  no hits. This is a source-project definition, not a Mathlib one.
- `msearch.py ... leansearch "local topological dimension of an affine scheme
  of finite type at a maximal ideal equals dimension of localization"`:
  service unavailable (Internal Server Error); no mathematical verdict inferred.
- Independent `rg` over Mathlib, WeilConjectures and repository `lean/Sheaf` for
  `topologicalKrullDimAt|dimAt.*(local|closed|maximal)|local.*topologicalKrullDim`:
  only the source local-dimension definition, open-invariance, and smooth
  relative-dimension results. I opened the smooth theorem's signature in
  Morphisms/Smooth.lean:452; its smoothness and relative-dimension assumptions
  prevent its being this arbitrary finite type statement.
- `rg` for the proposed full-name suffix and the item's blueprint id in
  `dag/lean_names_upstream.json`, WeilConjectures and `lean/Sheaf`: no matches.
  The existing local-dimension definition remains reused through its DAG node.

H5/H6/H8/H9: one named theorem with a `sorry` proof and no definitions; no proof
or data axiom added. Both docstrings name 00OU/00OT and the blueprint id. The
statement docstring follows all six node proof steps: Noetherianity and finitely
many minimal primes; primes below m lie in each neighbourhood; lower bound by
closures of their chains; remove components not containing m; upper bound by
passing to S/q and lifting local chains; conclude using the neighbourhood
infimum. The imports supply the types and notions used. Namespace and topic
follow the contract, lines are at most 100 characters, all variables/universes
are bound, and the recorded `lean.statement` equals the file's signature verbatim.

No mathematical, statement, dependency, or convention mismatch was found.
I changed only this report by adding the independent second reading; the Lean
module and node record were retained. Independent server compilation with
`scompile.py M1 lem-weil-pbc-closed-point-dimension-local-ring` of the delivered
module exited 0 in 3.5 seconds with no errors or warnings.

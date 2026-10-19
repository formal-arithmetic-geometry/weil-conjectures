## Worker report

The one delivered module `Sheaf.AlgebraicGeometry.LisseTrivializedFiniteEtale`
states `AlgebraicGeometry.exists_finite_etale_surjective_trivializing_lisse`.
Its only proof is `sorry`. The declaration docstring contains all five proof
steps of the node, including linear monodromy, the open action kernel, the
pointed-cover comparison, positive-degree surjectivity and coproduct assembly.
No definition, statement correction, new node, or dependency replacement is needed.
The JSON copy changes only `lean`.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| X of finite type over a field | `(k : Type u) [Field k]`, `(X : Scheme.{u}) [X.Over (Spec (.of k))]`, `[LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]` |
| Λ a finite commutative ring | `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` |
| L a finite locally constant Λ-module sheaf | `(L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (hL : Scheme.IsFiniteLocallyConstantSheaf L)` |
| There is p:P→X | `∃ (P : Scheme.{u}) (p : P ⟶ X)` |
| Finite, étale, surjective | `IsFinite p ∧ Etale p ∧ Surjective p` |
| Constant on each connected component of P | For every `x : P`, an open `U : P.Opens` with `(U : Set P) = connectedComponent x`, and an isomorphism from the restriction of `p^*L` to a constant module sheaf on `U.toScheme.smallEtaleTopology` |
| Finite Λ-module fibre | `∃ M : ModuleCat.{u + 1} Λ, Finite M ∧ Nonempty (... ≅ (constantSheaf ... (ModuleCat.{u + 1} Λ)).obj M)` |
| If X connected, one common finite module on all P | `ConnectedSpace X → ∃ M, Finite M ∧ Nonempty ((Etale.upperStar ... p).obj L ≅ (constantSheaf P.smallEtaleTopology ...).obj M)` |

There is no assumption that L is free, that k is finite or algebraically closed,
or that X is separated or nonempty. The common-module conclusion is inside the
same existential for p. A single global constant-sheaf isomorphism expresses
common finite module value on all components: P has finitely many clopen
components, so componentwise isomorphisms to one fixed constant module glue,
and conversely a global isomorphism restricts to each component. No connectedness
of P is required. The open representative is not an extra geometric hypothesis:
P is finite over finite-type X and hence Noetherian; its connected components are
open and closed. Quantification over all its points covers every component,
including repeated choices of a point in the same component.

Dependency declarations read and used:

- `def-weil-pbc-constructible-complexes` records
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes` and
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
  The module is publicly imported. Its definition of bounded constructibility
  is not substituted for the lisse hypothesis. The lisse clause explicitly
  cites transitive node `def-constructible-finite-locally-constant`, whose actual
  recorded declaration is `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf`
  in `WeilConjectures.ConstructibleSheaf.Defs`. That declaration, its two parent
  classes `IsLocallyConstantSheaf` and `IsFiniteSheaf`, and their docstrings were
  read. It means an étale trivializing cover and finitely generated geometric
  stalks; over finite Λ these are precisely finite stalks. The existing
  `finite_locally_constant_module_values_iff` was also read as confirmation of
  agreement with finite local constant module values. No second lisse definition.
- `def-weil-pbc-scheme-conventions` is convention-only, with no declaration to
  import. Its named existing leaves are used: `Scheme`, `LocallyOfFiniteType`,
  `QuasiCompact`, `IsFinite`, `Etale` and `Surjective` in Mathlib's algebraic
  geometry modules. In particular surjectivity is the scheme-morphism class.
- `def-weil-pbc-constant-sheaf` is exactly
  `CategoryTheory.constantSheaf` in `Mathlib.CategoryTheory.Sites.ConstantSheaf`;
  its definition is sheafification of the constant presheaf, used here at
  `ModuleCat.{u + 1} Λ`. The definition and docstring were read.
- `def-weil-connected-scheme` has `mathlib_match = ConnectedSpace` in
  `Mathlib.Topology.Connected.Basic`. Its class extends preconnectedness and
  nonemptiness, exactly including the node's empty-space exclusion.
- Pullback is the existing `AlgebraicGeometry.Etale.upperStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, read with its signature
  and construction as sheafified left Kan extension. Both the pullback along p
  and restriction along the component inclusion use this same functor.

The stated proof dependencies are imported without `public`: `OpenSubgroups`,
`FiberEquivalence`, `LocallyConstantEquivalence`, and upstream `FiberDegree`.
The Mathlib proof inputs for Noetherianity, irreducible components, coproducts
and finiteness local on the target are imported too. The direct statement
imports remain public, as required by the stage-2 import rule.

Edge cases checked: if X is empty, take the identity empty cover, so the
component assertion is vacuous; the connected-base implication does not apply.
For nonempty X, surjectivity excludes empty P. Zero modules and the zero
coefficient ring are allowed; no positive module rank, nontriviality or
freeness is imposed. Nonfree finite modules are included. Disconnected bases
may have different finite module values on different components. The field,
schemes and component points use universe u; modules and coefficients use
u+1, following the existing étale constructible-sheaf convention. There is no
extra smallness or equality of site object and morphism universes.

Searches actually run by this worker:

- `msearch.py N2 fin2-lem-lisse-trivialized-finite-etale leanfinder
  "finite locally constant module sheaf on a scheme is trivialized by a finite etale surjective cover"`:
  eight hits, for generic finite-type sheaves of modules and condensed locally
  constant modules; no scheme finite-étale trivialization theorem.
- `msearch.py ... loogle '"IsConstant", "Sheaf"'`: twelve hits in
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`, for the generic constant-sheaf
  predicate and criteria, with no finite-étale cover existence theorem.
- `msearch.py ... grep 'finite.*locally constant.*sheaf|trivializ.*sheaf'
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch
  "A finite locally constant etale module sheaf admits a finite etale surjective cover on which it is constant on connected components"`:
  service unavailable (Internal Server Error); no absence verdict from this.
- Direct `rg` over Mathlib, `WeilConjectures/`, `lean/Sheaf/`, and
  `dag/lean_names_upstream.json` for the proposed full declaration and
  trivialization/lisse/finite-étale variants found related local constancy,
  finite-set descent, finite-étale Yoneda trivializations and twist results,
  but no exact declaration. The existing local-constancy definitions were reused.
- `grep -rn 'fin2-lem-lisse-trivialized-finite-etale'` in upstream
  `WeilConjectures/` found no attachment.
- `rg -l '"fin2-lem-lisse-trivialized-finite-etale"' dag/nodes` found this node
  and the citers `lem-per-dual-lisse-tensor` and `lem-fin-normal-open-lisse-image`;
  no second declaration of this statement was found.

The referenced blueprint Markdown file is not installed in this shared
read-only clone (literature holds its index files and import tools). The
statement and full five-step proof in the assigned DAG node were read
verbatim; no source-dependent correction is being asserted.

Validation: the final module, including all proof imports, compiled cleanly
through `scompile.py`: 5.8 seconds for the sandbox and 5.9 seconds for the
library-path check. The initial dry run caught the unowned scratch `Test.lean`;
it was moved outside `lean/` into `scratchpad/` before the final dry run.
No independent second-reading section is written by this worker.

## Second reading by N2

Independent second reader, 2026-10-16. Verdict: pass; no mathematical or Lean
signature repair is needed. The worker's module and node record are retained.

Objects, hypotheses and conclusions, transcribed from the node before comparison:

| Node item | Lean rendering and verdict |
| --- | --- |
| A field k | `(k : Type u) [Field k]`: exact; no finiteness, perfection or characteristic restriction. |
| A scheme X of finite type over k | `(X : Scheme.{u}) [X.Over (Spec (.of k))]`, with `LocallyOfFiniteType` and `QuasiCompact` on the structure morphism: exact finite type; no separatedness or extra Noetherian hypothesis. |
| A finite commutative coefficient ring Λ | `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`: exact; not specialized to a field or prime ring. |
| A Λ-module sheaf L on the small étale site of X | `L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`: the prescribed module-valued encoding. |
| L finite locally constant | `hL : Scheme.IsFiniteLocallyConstantSheaf L`: the recorded transitive dependency, with local constancy and finite stalks, as checked below. |
| There exist a scheme P and p : P → X | `∃ (P : Scheme.{u}) (p : P ⟶ X)`: the cover is chosen after all input data and hypotheses. |
| p finite, étale, and surjective | `IsFinite p ∧ Etale p ∧ Surjective p`: the scheme-morphism predicates, exact. |
| On every connected component of P, p*L is constant | `∀ x : P, ∃ U : P.Opens, (U : Set P) = connectedComponent x ∧ ...`; restriction is `(Etale.upperStar ... U.ι).obj ((Etale.upperStar ... p).obj L)` and an isomorphism to `constantSheaf` is asserted. Every component contains a point, so this covers all components. Openness is available because P is Noetherian, finite over finite-type X. |
| Each component has a finite Λ-module value | `∃ M : ModuleCat.{u + 1} Λ, Finite M ∧ Nonempty (... ≅ (constantSheaf ...).obj M)`: M may vary with the component, is not required to be free. The isomorphism is in module sheaves. |
| If X is connected, one common finite module works on all P | Within the same existential for P and p, `ConnectedSpace X → ∃ M, Finite M ∧ Nonempty (p*L ≅ (constantSheaf ...).obj M)`: exact. Component isomorphisms with one fixed value glue over the disjoint open components, so the global form is equivalent to the node's wording. It does not assert that P is connected. |

Source reading: the node's source is a blueprint Markdown file, not a Stacks tag;
that Markdown is absent from this read-only checkout. I read the complete statement
and five-step proof in the node itself. The local Stacks directory is also absent.
I obtained the official `stacks/stacks-project` sources `etale-cohomology.tex` and
`morphisms.tex` into this sandbox's scratchpad, and read the surrounding sections
and the passages `definition-finite-locally-constant`,
`lemma-locally-constant-on-connected` (0DV5),
`remark-functorial-locally-constant-on-connected` (0DV6), and
`lemma-finite-type-noetherian` (01T6).
The locally constant section imposes no standing finite-type, separatedness or
characteristic condition. The representation correspondence assumes a connected
scheme and a geometric point, and its module clause assumes a finite ring.
These are used componentwise in the node's proof; connectedness is not a missing
input hypothesis on X. The pullback remark covers the module case too.
The Noetherian input follows from finite type over a field.
Primary source checks: [0DV5](https://stacks.math.columbia.edu/tag/0DV5),
[0DV6](https://stacks.math.columbia.edu/tag/0DV6),
[01T6](https://stacks.math.columbia.edu/tag/01T6).

Dependency/interface reading:

- Opened all four direct statement dependency node records, including their
  statements, `lean` and `mathlib_match`. Opened
  `BoundedConstructibleComplexes.lean`; its bounded-derived predicate is not
  mistakenly being used as local constancy. The node explicitly cites the
  transitive `def-constructible-finite-locally-constant` for that clause.
- Opened upstream `ConstructibleSheaf/Defs.lean`: `LocallyConstantDatum` is an
  étale trivializing cover, `IsLocallyConstantSheaf` asserts existence of such
  data, `IsFiniteSheaf` asserts finitely generated geometric module stalks,
  and `IsFiniteLocallyConstantSheaf` extends both. Over finite Λ, a finitely
  generated module is a finite set. Read the shared
  `finite_locally_constant_module_values_iff` signature and proof explanation
  as an independent confirmation that this encoding is the finite-value notion.
- Opened `Etale.upperStar` and its surrounding universe assumptions and
  construction: it is the canonical sheafified inverse image along the given
  scheme morphism. Both p and the component inclusion use it. No arbitrary
  pullback functor or map is introduced.
- Opened Mathlib `constantSheaf`: sheafification of the constant presheaf.
  Opened `ConnectedSpace`: preconnected and nonempty, matching the dependency's
  explicit exclusion of the empty space. Read the affine-local signatures of
  `IsFinite`, `Etale`, `LocallyOfFiniteType`, and `QuasiCompact`.
- Read the proof-dependency records and the actual signatures in
  `OpenSubgroups`, `FiberEquivalence`, and `LocallyConstantEquivalence`.
  Their marked-cover, degree, Yoneda, fibre, and base-change clauses are the
  ones used in the five-step proof. All recorded proof modules are imported;
  the Mathlib-only inputs are covered by Noetherian, Limits and morphism imports.
  No dependency replacement or new notion is necessary (H12/H13 do not apply).

Edge cases: empty X is allowed, with the empty identity cover and vacuous
component assertion; `ConnectedSpace X` is then false. For nonempty X,
surjectivity excludes an empty P. Zero L, the zero ring, nonfree finite modules,
and every field characteristic are admitted. There is no n or auxiliary index
binder, hence no omitted rank-zero or empty-index case. Disconnected X can have
different module values on its different components. Schemes use universe u;
the small étale site and module coefficients use the established u+1 convention.
The theorem adds no universe equality, site smallness or extra instance
hypothesis. Every displayed variable and universe is explicitly bound.

Independent searches, using different wording from the worker:

- `msearch.py ... leanfinder 'finite etale surjective trivializing lisse module sheaf'`:
  eight hits for standard/formal étaleness and generic finite-type module
  sheaves; no exact trivializing-cover theorem.
- `msearch.py ... loogle '"constantSheaf"'`: twelve hits, including the exact
  reused constant-sheaf functor and general adjunction criteria; no cover theorem.
- `msearch.py ... grep 'monodromy|trivializing|trivialization' AlgebraicGeometry`:
  no Mathlib hits. Direct `rg` over Mathlib, upstream `WeilConjectures`, and
  this project's `lean/Sheaf` additionally used `exists_.*constant`,
  `finite etale.*constant`, `trivializ`, `monodromy`, and the proposed full name.
- Opened the closest project theorem,
  `Scheme.IsFiniteLocallyConstantSheaf.exists_finite_monodromy_trivializing_torsor`:
  it restricts coefficients to `ULift (ZMod ℓ)` with ℓ prime and a connected
  base. It does not state this arbitrary-finite-commutative-ring and
  disconnected-base result. The cover-filtration and trace-retraction
  neighbours are also specialized prime-field statements with other conclusions.
  No exact declaration exists to attach with `existing: true`.

Mismatch/change ledger: none in the mathematics, signature, imports, docstrings
or node record. Only this independent reading section was appended. There is no
`statement_change`, and no target or citer change. There are no definitions,
private aliases, local notations, local instances, or proved theorems in the
delivery. The sole postponed theorem has a source/blueprint docstring containing
all five proof steps. The module header and namespace follow the conventions,
and every line is at most 100 characters. A direct extraction confirms
`lean.statement` equals the complete source signature verbatim, and only the
item's `lean` differs from the shared node.

Validation repeated by this reader: prescribed `scompile.py` compiled the sole
delivered module in sandbox and library-path modes, 4.8 s and 5.8 s respectively,
with no errors or warnings. The only proof remains the intended `sorry`.

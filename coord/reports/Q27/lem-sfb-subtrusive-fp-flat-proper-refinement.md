## Worker report

This is a stage-2 delivery of `lem-sfb-subtrusive-fp-flat-proper-refinement`.
The inherited BLOCKED ending concerned stage-1 deliver.py and an already accepted split.
The current node has no Lean record; coord/queue.tsv assigns stage 2, and the
2026-10-22 handoff in coord/brief-stage2.md explicitly permits this work.
The accepted statement and all eleven proof steps are preserved. Only `lean` and the
addition of the new definition id to `stmt_deps` change in the item.

`Sheaf.AlgebraicGeometry.SubtrusiveFlatProperRefinement` states
`AlgebraicGeometry.exists_flat_proper_refinement_of_isUniversallySubtrusive`.
Its single theorem has proof `sorry`; both definitions in the helper module have real data.

Clause-by-clause correspondence:

| Node clause | Lean |
| --- | --- |
| Schemes X,Y and scheme map f | `{X Y : Scheme.{u}} (f : X ⟶ Y)` |
| Y affine | `[IsAffine Y]` |
| f locally of finite presentation | `[LocallyOfFinitePresentation f]` |
| f quasi-compact | `[QuasiCompact f]` |
| f quasi-separated, i.e. its diagonal quasi-compact | `[QuasiSeparated f]` |
| Constructible topology locally generated on scheme charts | `Scheme.localConstructibleTopology`, final topology from every affine open with Mathlib `constructibleTopology` |
| Every affine base change | `∀ (T : Scheme.{u}) (_ : IsAffine T) (g : T ⟶ Y)` in `IsUniversallySubtrusive` |
| Surjective and quotient on constructible topologies | `@Topology.IsQuotientMap ... (pullback.snd f g)`; IsQuotientMap includes its surjective field |
| Every specialization pair lifts | `∀ t₀ t₁, t₁ ⤳ t₀ → ∃ x₀ x₁, p x₀ = t₀ ∧ p x₁ = t₁ ∧ x₁ ⤳ x₀` |
| Universally subtrusive f | `(hf : IsUniversallySubtrusive f)` |
| X₁,Y₁ and u,a,b | `∃ (X₁ Y₁ : Scheme.{u}) (u : X₁ ⟶ X) (a : X₁ ⟶ Y₁) (b : Y₁ ⟶ Y)` |
| fu=ba | `u ≫ f = a ≫ b` |
| a faithfully flat | `Flat a ∧ Surjective a` |
| a of finite presentation | `LocallyOfFinitePresentation a ∧ QuasiCompact a ∧ QuasiSeparated a` |
| b proper and surjective | `IsProper b ∧ Surjective b` |
| b of finite presentation | `LocallyOfFinitePresentation b ∧ QuasiCompact b ∧ QuasiSeparated b` |
| ba is a surjective refinement | `Surjective (a ≫ b)` together with the factorization equality |
| No Noetherian or flat-f hypothesis | No such binders occur |

Recorded statement dependencies used, with full declarations and docstrings read:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, the affine-local ring-map property.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `AlgebraicGeometry.Flat`, equivalent to
  flat stalk maps as the recorded dependency explains.
- Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap: `AlgebraicGeometry.Surjective`.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: `AlgebraicGeometry.IsProper`, extending
  separated, universally closed and locally finite type. Universal closedness implies
  quasi-compactness, so this is the node's finite-type definition of properness.
- Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated: `AlgebraicGeometry.QuasiSeparated`
  means precisely `QuasiCompact (pullback.diagonal f)`; QuasiCompact is the existing
  morphism predicate from Morphisms.QuasiCompact.
- New module Sheaf.AlgebraicGeometry.UniversallySubtrusive:
  `AlgebraicGeometry.IsUniversallySubtrusive`.

For the new definition node, use the existing `CategoryTheory.Limits.pullback` and
`pullback.snd` (Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback), with scheme
pullbacks supplied by Mathlib.AlgebraicGeometry.PullbackCarrier; the existing Mathlib
`constructibleTopology` (Mathlib.Topology.Spectral.ConstructibleTopology) on affine charts;
`Topology.IsQuotientMap` (Topology.Defs.Induced); and `Specializes` (Topology.Defs.Filter).
The specialization direction was checked in its docstring: `x ⤳ y` means y lies in the
closure of {x}. No global instance changes the Zariski topologies used for these pairs.

All already recorded proof-dependency modules are imported privately, including
FlatteningByAdmissibleBlowup, DescendFlatFinitePresentation, DescendSurjective,
EventuallyProper, ProperFinitePresentationClosedLimit, integral finite-presentation
approximation, the blowup modules and AffineTransitionLimit. The Mathlib proof leaves
are imported as recorded. Four proof-only nodes have no recorded module yet:
lem-a1-map-over-base-finite-presentation, lem-sfb-affine-integral-compact-generics-cover,
lem-sfb-compact-generics-flat-open, lem-sfb-subtrusive-topological-descent-calculus.
No import can be added for them yet; the maintainer can add their proof imports upon landing.
They are not prerequisites to typing this theorem. In particular the algebraic-space
calculus is not needed to define the scheme-only hypothesis.

Edge cases checked before writing:

- Empty Y forces X empty; take X₁=Y₁ empty, with the unique maps. Surjectivity is
  vacuous and empty identities satisfy the requested geometric properties.
- A nonempty Y cannot be reached by an empty universally subtrusive source:
  the affine identity test and the quotient-map surjectivity already rule that out.
- The identity of an arbitrary affine scheme satisfies the hypothesis; choose
  identity factors, without imposing any Noetherian, reducedness or field hypothesis.
- For a field base, the generic-to-special pair is reflexive; lifting it includes
  the expected existence of a source point. No distinct-points hypothesis was added.
- Tests have the same scheme universe u, so the identity test is always admitted;
  there is no smaller independent test universe making the hypothesis vacuous.
- The definition is valid for arbitrary schemes, including non-quasi-separated ones:
  constructible openness is tested locally on affine open charts, rather than assuming
  that every scheme has the globally generated patch topology of a spectral space.
  The theorem's fp hypothesis makes the relevant sources qcqs over affine tests,
  where this agrees with the usual patch topology.
- The refinement map u is unconstrained, as in the node; it need not itself be
  surjective, flat or finitely presented.

Searches performed through msearch.py, with exact machine output in the new node's
mathlib_searches and sandbox searches.jsonl:

- LeanFinder: “A universally subtrusive morphism of finite presentation has a faithfully
  flat finite presentation refinement followed by a proper surjective finitely presented
  morphism”: eight related hits, including UniversallyOpen.of_flat and
  LocallyOfFinitePresentation, no exact statement.
- Loogle: `"Subtrusive", "IsProper"`: zero hits.
- Mathlib grep: `subtrus|[Ff]lattening|[Pp]roper.*[Rr]efinement`, AlgebraicGeometry:
  zero hits; `IsUniversallySubtrusive|subtrus|localConstructibleTopology`, all Mathlib:
  zero hits.
- LeanSearch: “Universally subtrusive scheme morphisms lift specialization pairs after
  every affine base change and are quotient maps in the constructible topology”:
  eight related hits (UniversallyClosed, specializing maps, spectrum quotient maps),
  none defines the pair-lifting property.
- LeanFinder: “Define universally subtrusive scheme morphisms using quotient constructible
  topology and lifting specializations”: eight related hits, no definition.
- `rg -n -i subtrus lean/WeilConjectures lean/Sheaf`: no declarations or definitions.
  DAG grep finds statement/proof text only; `tools/blueprint_refs.py search subtrusive`
  reports zero blueprint nodes. The existing constructible-topology definition node
  is reused, not duplicated. Exact proposed names were also searched in both Lean
  trees and dag/lean_names_upstream.json, with no hits.

Source read online: https://davidrydh.se/papers/submersion20100305.pdf,
Section 1, Proposition (2.1), Definition (2.2), Proposition (2.4), and Theorem (3.10),
printed p.14. Theorem (3.10)'s affine case has exactly the claimed factorization.
Its extra universally-open/nil-immersion clause is not part of this node.
No statement correction or STATEMENT-DISPUTED issue.

Validation: scompile.py compiled each delivered module separately in dependency order,
including both sandbox and canonical library names. Both files compile without errors
or warnings. The first delivery preflight requested the new-node schema field
`import_flags`; the new definition now records the empty list required by the live gate. The initial elaboration probe required an explicit scheme annotation on
pullback carriers, and the topology definition required instance_reducible; both were fixed.

## New nodes

`def-sfb-universally-subtrusive-scheme-morphism` defines precisely the scheme-only
universal-subtrusiveness notion already spelled out inline in the item. Its module is
Sheaf.AlgebraicGeometry.UniversallySubtrusive. It also provides the owning helper
`Scheme.localConstructibleTopology` by a genuine supremum of coinduced affine-chart
constructible topologies, using Mathlib's existing patch topology on each chart.
It uses existing nodes for schemes, fibre products, surjectivity and constructible topology.
Rydh Section 1 and Definition (2.2), with Proposition (2.4)'s locality, give the source.
No independent DAG definition node carries universal subtrusiveness; the existing
algebraic-space calculus node is a multi-clause theorem with no recorded Lean interface,
not a definition node to duplicate. Three search kinds and project/DAG searches are
recorded above and in the new node. The ancestor tool returns None; the new node preserves
that inherited null blueprint anchor and prepends the current item to its via chain.

## Second reading by Q27

I reread the finished node and both Lean files in a separate pass. This is a worker
self-check; the maintainer's independent review remains responsible for acceptance.
The table above checks every hypothesis and conclusion against the actual signature.
The key direction check is `t₁ ⤳ t₀` and `x₁ ⤳ x₀`: reversing either would be wrong.
Quotient surjectivity uses the exact IsQuotientMap structure, not only continuity.
Final topology over all affine opens expresses local constructibility without imposing
quasi-separatedness. The helper's two definitions both have actual terms, no sorry.
The theorem has one sorry and includes all three finite-presentation clauses on each
of f,a,b; properness has the recorded Mathlib meaning. Explicit composite surjectivity
retains the node's final clause; no properties of the refinement map u were introduced.
Every scheme variable and universe is explicitly bound, and the statement introduces
no let, local notation, private definition or file-local instance. The accepted split
is retained verbatim in the theorem docstring, step by step. No mismatch remains in
this pass; no other agent was started, in accordance with the dispatcher brief.

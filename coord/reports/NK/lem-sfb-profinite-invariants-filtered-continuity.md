## Worker report

The delivery states the reviewed stage-1 node without changing its mathematical statement,
statement dependencies, or proof. The previous worker's stale-assignment diagnosis confused
`reviewed` (a stage-1 split review) with `reviewed_lean`. The current node has the former,
no `lean` and no `reviewed_lean`; it remains a stage-2 item. No split is repeated.

Module: `Sheaf.CategoryTheory.ProfiniteInvariantsFilteredContinuity`.
It contains a real helper definition `higherInvariants`, and two statements with `sorry`:
`forgetCreatesFilteredColimit` and `higherInvariants_filteredColimit_isIso`, all in
`CategoryTheory.CondensedDerivedRestriction`. Both postponed statements are clauses of
this one DAG node; each docstring contains its source and complete proof outline.

Clause-by-clause correspondence:

- A commutative condensed ring is `A : CondensedBar.Ring.{u}`. This is the existing
  `CommMon` bundling of `Profinite.CondensedRing`, not a topological presentation or
  a discrete coefficient ring. The commutativity proof is the bundle's `comm` field.
- A profinite group is `J : Type u` with `Group`, `TopologicalSpace`,
  `IsTopologicalGroup`, `CompactSpace`, `T2Space`, and `TotallyDisconnectedSpace`.
  No discreteness, finite generation, completeness, or dimension bound occurs.
- The internal action category is `Equivariant A J`, definitionally the dependency's
  `Profinite.CondensedAction.ActionModule A.toMon J`. The underlying category is
  `Modules A`, definitionally the dependency's internal `CategoryTheory.Mod`.
  These retain the action by every `C(S,J)` and naturality in profinite restrictions.
- Fixed after every profinite base change is the normalized existing
  `invariants A J`, whose `Invariants.image` is exactly `FixedAll`. The chosen
  inclusion/adjunction determines the invariant submodule by its universal property.
- The ordinary total right derived functor is the recorded `derived A J`.
  The real definition `higherInvariants A J q` is
  `(DerivedCategory.singleFunctor (Equivariant A J) 0 ⋙ derived A J) ⋙
  DerivedCategory.homologyFunctor (Modules A) (q : ℤ)`.
  Thus `q : ℕ` expresses precisely every nonnegative cohomological degree.
- A compatible small filtered diagram is `I : Type (u + 1)`, `[SmallCategory I]`,
  `[IsFiltered I]`, `N : I ⥤ Equivariant A J`. Mathlib's `IsFiltered` includes
  nonemptiness and the finite-diagram common-target/equalization requirements.
- `Nonempty (CreatesColimit N (CondensedBar.forgetAction ...))` is the assertion
  that the forgetful functor creates this colimit, including its lifted cocone
  and reflection of the colimit universal property. Existence of the underlying
  sheaf-module colimit and of both colimits in the comparison is supplied by
  the dependency's Grothendieck structures; no colimit-existence assumption is added.
- `IsIso (colimit.post N (higherInvariants A J q))` is exactly the stated internal
  module comparison. `colimit.post` is defined in Mathlib as descent from
  `(higherInvariants A J q).mapCocone (colimit.cocone N)`.
  Its standard equation `colimit.ι_post` says that its i-th leg is exactly
  `(higherInvariants A J q).map (colimit.ι N i)`. No arbitrary comparison map
  or unnormalized isomorphism is substituted.
- The site is `Profinite.{u}`, section groups live in `Type (u + 1)`, and the
  indexing category is small in that same coefficient universe. This follows
  the existing action/derived interface and the size convention, and includes
  all smaller shapes through cumulative universes. No extra universe equality is assumed.

Dependency declarations read and used:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its action and morphisms.
- `Sheaf.CategoryTheory.CondensedActionModule`: `ActionModule`, `forgetAction`,
  `FixedAll`, `Invariants` in `Profinite.CondensedAction`.
- `Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus`: the recorded derived
  calculus interface, including `boundedBelowComputation`, `restrictionDegreeZero`;
  its public dependency `Sheaf.CategoryTheory.CondensedDerivedInvariants` supplies
  `invariants`, `derived`, `actionGrothendieck` in
  `CategoryTheory.CondensedDerivedRestriction`. The public
  `CondensedEquivariantBarData` supplies `Ring`, `Modules`, `Equivariant` and
  `forgetAction` in `CategoryTheory.CondensedBar` as transparent existing specializations.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`; the homology and single functors are publicly available
  from the recorded derived calculus imports.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `colimit`, `colimit.post`, `colimit.ι_post`.
- `def-weil-size-convention` is a recorded convention, with no module or declaration.

Proof-only modules are imported without `public` for every recorded proof dependency
that has a module or Mathlib match: site filtered-colimit sections, module-sheaf
colimits, cohomology of colimit sites, colimit sites, injective-module abelian
acyclicity, acyclic-comparison naturality, sheafification, enough injectives and
Leray acyclicity. `lem-sfb-profinite-action-coherent-presentation` has no Lean
record yet, so its future module cannot be imported; it is named in the proof
docstring and remains in the unchanged proof_deps for the maintainer to add when stated.
No new interface or dependency repair is needed to state this node.

Edge cases checked before writing: q=0 is ordinary invariants with the existing
unit normalization; trivial J reduces to ordinary module filtered colimits;
finite J is included without restricting the general profinite case; singleton
I gives the canonical identity comparison; zero modules give zero comparisons;
the empty profinite test object is included by ActionModule and FixedAll. An
empty I is excluded exactly because filtered categories are nonempty. Parallel
arrows and non-poset filtered categories are permitted by SmallCategory and IsFiltered.
No evaluation-exactness assertion is made on an arbitrary profinite test object.

Searches actually run:

- msearch leanfinder: `For a profinite group acting internally on condensed modules
  all higher derived invariants preserve filtered colimits`: 8 hits, including
  Condensed.instAB5CondensedMod and condensed free/solid functors; none states
  preservation of filtered colimits by higher internal invariants.
- msearch loogle: `"invariants", "colimit"`: 0 hits.
- msearch grep: `(invariant|fixedPoint).*(colimit|filtered)|(colimit|filtered).*(invariant|fixedPoint)`:
  1 hit, an unrelated comment on invariance of exact-colimit axioms under equivalences.
- Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for the item id and profinite /
  filtered-colimit terms: no declaration for this item. The existing
  ProfiniteDerivedFunctionsFilteredColimit theorem concerns derived internal
  functions on a parameter, not this action-module higher-invariant functor.
- Read the source for Mathlib's `CreatesColimit`, `colimit.post`, `colimit.ι_post`,
  module objects, derived localization and derived homology. Read Stacks
  `sites-cohomology.tex` at lemma-colim-works-over-collection and
  lemma-higher-direct-image-colimit, and the current blueprint direct-images proof.

All group, compactness and separation hypotheses are explicit declaration binders,
so Lean cannot discard them as unused section variables.

No STATEMENT-DISPUTED flag, statement correction, new node, or dependency module.
Initial server compile through scompile.py passed cleanly, both sandbox and library
module modes (only expected sorry proofs). Final preflight is run through deliver2.py.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

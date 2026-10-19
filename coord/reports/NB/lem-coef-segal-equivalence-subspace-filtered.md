## Worker report

The module `Sheaf.CategoryTheory.SegalEquivalenceSubspaceFiltered` states
`SSet.SegalFiltered.segal_equivalence_subspace_filtered`. Its sole postponed
mathematical assertion is this named theorem. The helper definitions construct
coherent presheaves with their actual equivalence-subspace inclusions. They do
not choose any data from an existence theorem. The node's statement, proof and
proof dependencies are unchanged; statement dependencies gain only the already
landed nodes owning the interfaces used below.

Clause-by-clause correspondence:

- Nested universes and small spaces: `universe u`, `RezkLocalModel.Spaces.{u}`,
  the coherent nerve of all `u`-small Kan complexes, in universe `u+1`.
  `RezkLocalModel.Presheaves.{u}` is the full coherent functor simplicial set
  from the lifted ordinary nerve of `SimplexCategoryᵒᵖ` to those spaces.
  No homotopy category of diagrams replaces this functor simplicial set.
- Segal objects without completeness: `segalObjects q` is the full subcategory
  saturated under `EquivalentObjects` of the images of
  `HomotopySegal.IsHomotopySegalSpace W`. That existing predicate says that every
  level is Kan and that all consecutive-edge comparisons in degrees `n+2`
  are weak equivalences to the explicit homotopy edge products. Saturation
  allows arbitrary coherent simplicial-space representatives. No Reedy or
  completeness hypothesis is imposed on `W`.
- The homotopy category, both inverse equations, and the entire union of
  components: `modelPair q W` uses exactly
  `(SegalInverse.invertibleArrows W).ι`. Its predicate uses
  `SegalInverse.IsInvertibleClass`, `HomotopySegal.Composes` and
  `HomotopySegal.identity` on components of the fixed-endpoint homotopy fibers.
  It then saturates by `π₀` equality, rather than selecting only vertices.
  All these are existing declarations, not new inverse-witness definitions.
- Functoriality for every map: `pairs` is the pullback of degree-one evaluation
  and target evaluation on the whole arrow infinity category of spaces.
  Thus its simplices retain the map of simplicial spaces, the map of subspaces,
  and their entire coherent compatibility square. `equivalenceSubspaces q`
  is the full subcategory saturated from the concrete `modelPair`s **in this
  pullback**, so the inclusion into degree one is retained during transport.
  The theorem's first conjunct supplies an equivalence `r` from all Segal
  objects to these annotated objects, normalized by the coherent equivalence
  `r ≫ forgetSubspace q ≃ (segalObjects q).ι`. Thus annotations are the canonical
  subspaces; their existence or compatibility is not an extra hypothesis on
  the mathematical diagram. Every coherent Segal diagram is covered, including
  all its higher transformation simplices.
- Any small filtered quasicategory: `(I : SSet.{u+1}) [Quasicategory I]`,
  `Presentability.IsSmall.{u,u+1} I`, and
  `Presentability.IsKappaFiltered Cardinal.aleph0 I`. The latter tests all finite
  nondegenerate-simplex shapes, including the empty shape. No ordinary-category
  nerve, poset, discreteness, injectivity or separate nonemptiness hypothesis
  replaces the quasicategory.
- Coherent diagram and induced simplicial operators: `F : I ⟶
  (equivalenceSubspaces q).toSSet` and the full coherent cocone vertex `c`.
  Its image under `forgetSubspace q` retains the complete simplicial diagram,
  not just the levels separately. The apex of `c` belongs to the same Segal
  category: this is precisely the hypothesis that the pointwise colimit is
  Segal.
- Pointwise space colimit in every degree: the hypothesis `∀ n :
  SimplexCategory, Enhanced.IsColimiting (F ≫ subspaceLevel q n)
  (Spaces.mappedCocone (subspaceLevel q n) F c)`. The mapped cocones use the
  actual apex and full transformation of `c`. They therefore share the specified
  simplicial operators and comparison maps.
- Canonical comparison is an equivalence over `X₁`: the conclusion is
  `Enhanced.IsColimiting (F ≫ equivalenceSpace q)
  (Spaces.mappedCocone (equivalenceSpace q) F c)`. This says the specified
  cocone with apex `X_eq` is a universal space colimit. Equivalently the
  comparison from any colimit of the stage subspaces induced by these very
  cocone legs is an equivalence. It is the canonical comparison, not the bare
  existence of an unrelated equivalence between its endpoints. The inclusion
  into degree one is stored by `(equivalenceSubspaces q).ι ≫ inclusion`;
  the defining equation of `pairs` identifies its target with `subspaceLevel
  q ⦋1⦌` on every simplex. Hence this conclusion is also the colimit assertion
  in spaces over the degree-one apex `X₁`, since slice colimits are computed in
  spaces. This universal-cocone wording includes the full compatibility over
  `X₁` without choosing a colimit object or a noncanonical comparison.
- No further conditions: the theorem and both object predicates contain no
  completeness, nonempty-space, discreteness, monomorphism or transition-map
  injectivity predicate. The annotation is a union of components of a space,
  not an assumption on transition maps.

The localization parameter `q` and `IsLocalization` specify the interpretation
of the ordinary simplicial models in the existing space infinity category. They
are model/presentation data, not an extra mathematical hypothesis: the recorded
complete-Segal comparison theorem supplies precisely such a localization. The
assertion quantifies over every such presentation. The raw simplicial models
are used only to specify the existing notion on representatives; actual input
`F` is an arbitrary coherent diagram in the saturated presheaf model.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.fullSubcomplex`, `diagramVertex`, `evaluation`,
  `IsWeakHomotopyEquivalence`, `IsFunctorEquivalence`,
  `AreNaturallyEquivalent`, `coconeCategory`, `IsColimiting`.
- `Sheaf.CategoryTheory.PresentableInfinityCategory`:
  `SSet.Presentability.IsSmall`, `IsKappaFiltered` (at `Cardinal.aleph0`).
- `Sheaf.CategoryTheory.CompleteSegalQuasicategoryComparison`:
  its comparison theorem and its imported coherent presheaf model; the theorem
  supplies the space localization presentation and establishes the intended
  coherent functor interpretation. Its full signature and docstring were read.
- `Sheaf.CategoryTheory.HomotopySegalSpace`:
  `SSet.HomotopySegal.IsHomotopySegalSpace`, the explicit homotopy comparisons,
  mapping fibers, identity and composition graph. Added its already-landed
  owner `def-coef-homotopy-segal-space` to `stmt_deps`.
- `Sheaf.CategoryTheory.SegalInverseEvaluation`:
  `SSet.SegalInverse.invertibleArrows` and its existing inverse-class predicate.
  Added owner `lem-coef-segal-inverse-evaluation` to `stmt_deps`.
- `Sheaf.CategoryTheory.RezkLocalModel`:
  `SSet.RezkLocalModel.Spaces`, `Presheaves`; the full presheaf model is used,
  not its complete-Segal full subcategory. Added owner
  `lem-coef-rezk-local-model` to `stmt_deps`.
- `Sheaf.CategoryTheory.FiniteReedyLocalization`:
  `HomotopicalAlgebra.FiniteReedy.largeNerve`, `diagram`, `IsLocalization`,
  `EquivalentObjects`. Added owner `lem-coef-finite-reedy-localization` to
  `stmt_deps`.
- Proof-only import `Sheaf.CategoryTheory.SpacesKappaLimitFilteredColimit`:
  `CategoryTheory.Spaces.spaces_kappa_limit_filtered_colimit`, used at aleph_0
  for finite inverse witnesses and for the diagonal pullback. Its full
  signature and proof docstring were read. The existing
  `CategoryTheory.Spaces.mappedCocone` provides the prescribed image cocone.

Edge cases checked before writing:

- All levels empty: the equivalence subspace is empty, the constant diagram
  over any filtered index has empty pointwise colimit, and the conclusion is
  the empty colimit cocone. No vertex of an empty space is chosen.
- Terminal Segal space and constant Kan-space simplicial objects: all relevant
  components are equivalences, and the assertion reduces to its given
  pointwise space colimit.
- Discrete nerve of a nontrivial group: this is generally not Rezk complete;
  it is still included. No `X₀ ≃ X_eq` premise appears.
- Arrows can acquire inverses at later stages: two-sided inverse witnesses
  must be represented at a common stage. The statement does not assert that
  a noninvertible arrow at an earlier stage stays noninvertible.
- A group mapping to the trivial group gives noninjective transition maps;
  no clause excludes it. Spaces with higher homotopy groups are equally
  allowed, since every comparison is in the coherent category of spaces.
- Degrees zero and one are included in the pointwise-colimit hypothesis;
  Segal comparisons are only degrees `n+2 ≥ 2`.
- The empty index cannot satisfy the stipulated filteredness (the empty test
  diagram requires a cocone). This is the definition's index nonemptiness,
  not an added nonemptiness condition on any space.

Searches for reuse:

1. `msearch.py ... leanfinder`: “For a filtered diagram of Segal spaces the
   subspace of invertible arrows in its pointwise colimit is the colimit of
   the subspaces of invertible arrows”. Eight hits, chiefly
   `SSet.StrictSegalCore`, `SSet.StrictSegal.ofCore`, ordinary strict Segal
   nerves, and stability of simplicial-set monomorphisms. None states the
   coherent homotopy-colimit assertion.
2. `msearch.py ... loogle '"Segal", "colimit"'`: zero hits.
3. `msearch.py ... grep 'SegalSpace|CompleteSegal|equivalenceSubspace'`:
   zero Mathlib hits.
4. `msearch.py ... leansearch`: “Equivalence edge spaces of Segal objects
   commute with filtered homotopy colimits”. Eight hits concerning ordinary
   categorical limit/colimit interchange, including `colimitLimitIso`; none
   concerns coherent Segal-space subspaces.
5. `rg` of the upstream source for
   `SegalSpace|CompleteSegal|equivalenceSubspace`, and the required upstream
   node-id search: no match. `rg` of upstream and `lean/Sheaf` for
   `segal.*filtered|filtered.*segal|equivalence_subspace_filtered`: no existing
   theorem. The new namespace/declaration names were also checked against
   `dag/lean_names_upstream.json`, upstream and project source; no clash.
6. Project-source search located `SegalSpace.lean` (Reedy-fibrant strict-fiber
   convention), `HomotopySegalSpace.lean` (the needed non-Reedy convention),
   `SegalInverseEvaluation.lean` (the actual invertible component inclusion),
   `RezkLocalModel.lean` and the recorded complete-Segal comparison. These
   were read and reused. The new helpers only present the item's coherent
   subspace inclusion and its evaluation; they do not redefine any of those
   notions. `segalObjects` differs from the existing `completeSegalObjects`
   exactly by omitting completeness and using the existing homotopy Segal
   predicate.

The source https://arxiv.org/html/math/9811037 was opened, with Sections
5.3, 5.5, 5.7 and Lemma 5.8 read for the conventions. The filtered assertion
is explicitly the DAG's agent argument, not attributed to a theorem of Rezk.
The proof docstring contains all five DAG proof steps, including the precise
finite inverse-witness construction, component surjectivity, the diagonal
monomorphism argument and the over-degree-one conclusion.

No statement dispute or node correction was needed. No new independent
notion/node or replacement dependency module was introduced. The added landed
dependencies were checked not to create a dependency path back to the item.
All universes and variables are explicit (`autoImplicit false`); every helper
has real data and a source/blueprint docstring; lines are at most 100 characters.

Validation: `scompile.py` checked the sandbox and library module. After
removing the two unused simp arguments, `deliver2.py --no-push` recompiled
the final module cleanly and passed the server preflight (dry-run commit
`0de82e674d`). Exactly one sorry remains, in the main theorem. The JSON delta
was checked to contain only `lean` and the four added landed `stmt_deps`;
the recorded signature is extracted verbatim from the module. No global
build, direct repository mutation or upstream edit was performed.

## Second reading by NB

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

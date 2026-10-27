## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties` states
`AlgebraicGeometry.scheme_etale_source_target_properties`. Its only theorem proof is
`sorry`. The delivery now also records a definition node owning the already landed
locality predicate, without defining it again. The source is the local Stacks `descent.tex`,
Definition 04QZ, Lemma 04R1 (a),(c),(d),(f), and Remark 04R3, all opened and read.
I also read the current blueprint unit under `literature/blueprint/latest/`:
`blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`. This item is a supporting
scheme lemma, not that unit's statement. There is no statement correction or dispute.

This repairs independent review L of immutable head `d9999de224cb`. The saved
packet passed the initial dry run as `e7c54e6ade6`, but the reviewer correctly
required a definition node owning the plain locality predicate. The current base
has no Lean record for this item, and its accepted mathematical split is preserved.

Hypothesis and clause correspondence:

- Schemes and morphisms use `Scheme.{u}` and `X ⟶ Y`, with every universe and variable
  bound explicitly and `autoImplicit false`.
- “Let P be any one of” is `(P : MorphismProperty Scheme.{u})` together with the
  five-way disjunction `hP`: equality with `@Smooth`, `@Etale`, `@Flat`,
  `@LocallyOfFinitePresentation`, or `@LocallyOfFiniteType`. Thus P is exactly one
  of the specified existing properties; no independent locality or invariance
  hypothesis is assumed.
- The first conclusion is the existing `IsEtaleLocalOnSourceAndTarget P`.
  Its definition in `SpaceEtalePresentationPropertyCriterion.lean` was read in full:
  clause (i) is `Etale a → P f → P (a ≫ f)`;
  clause (ii) is `P f → Etale b → P (Limits.pullback.snd f b)`;
  clause (iii) is `P f ↔ ∀ x : X, ∃ (U V : Scheme.{u}) (a : U ⟶ X)
  (b : V ⟶ Y) (h : U ⟶ V) (u : U), Etale a ∧ Etale b ∧ a.base u = x ∧
  a ≫ f = h ≫ b ∧ P h`. These are precisely the node's three clauses,
  including the pointed chart and both vertical étaleness conditions.
- The second conclusion quantifies over `X Y U V`, the four maps, `Etale a`,
  `Etale b`, and `a ≫ f = h ≫ b`. Composition is written in Lean's left-to-right
  order, so this equality is the node's fa=bh. The conjunct `P f → P h` is the
  forward square implication. The conjunct `Surjective a → P h → P f` is the
  converse, with surjectivity imposed only on the source chart. `Surjective` is
  Mathlib's class whose field is surjectivity of the underlying point map.
- The third conclusion quantifies over `(I : Type v)`, `(U : I → Scheme.{u})`,
  and `(a : ∀ i : I, U i ⟶ X)`. Its first assumption is pointwise étaleness
  `∀ i : I, Etale (a i)`; its second is exactly joint surjectivity,
  `∀ x : X, ∃ (i : I) (u : U i), (a i).base u = x`. Its result is
  `P f ↔ ∀ i : I, P (a i ≫ f)`. The index universe v is independent of u,
  so no smallness or nonemptiness restriction was inserted.
- There are no Noetherian, separation, compactness, quasi-compactness, or target
  surjectivity assumptions.

Dependency declarations used, with their recorded modules and signatures/docstrings read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, whose
  `Flat.iff_flat_stalkMap` identifies it with the node's stalkwise notion.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`. This is the locally finite type
  alternative, not its stronger conjunction with quasi-compactness.
- `Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion`:
  `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget`. This is already recorded in
  `lem-sfb-space-etale-presentation-property-criterion.lean.declarations` and is
  actual propositional data, with no postponed proof. The new definition node
  `def-sfb-etale-local-source-target-property` now owns this declaration via an
  `existing: true` record and is the item's statement dependency. The theorem
  node is removed from the saved packet's `stmt_deps`; its own record is untouched.
  The existing module import supplies the same declaration. The new node depends
  only on `def-pc-scheme` and `def-weil-etale-morphism`, so it adds no cycle.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`:
  `AlgebraicGeometry.Surjective`, used in the square's converse, now explicitly
  cited through the landed definition node `def-weil-surjective-morphism`.

The plain proof imports retain the stated proof dependencies: étale smoothness,
unramified morphisms, open immersions, composition/base-change and source-local
Mathlib facts, smooth and étale source descent, fppf-source local finite presentation,
flat-lfp-source local finite type, flat permanence, and scheme coproducts/pullbacks.
Their declaration modules include `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`,
`Sheaf.AlgebraicGeometry.UnramifiedMorphism`,
`Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource`,
`Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover`,
`Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFinitePresentationFppfSource`,
`Sheaf.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeOfFlatLfpSource`, and
`WeilConjectures.RingTheory.FlatPermanence`. The proof dependency
`lem-sfb-etale-stalk-invariants` currently has no recorded declaration or Mathlib
match, so there is no module to import for it; it is a proof prerequisite, not
an object needed to type this statement. Its faithful-flatness input and all
nine proof steps are preserved in the theorem docstring. The docstring additionally
explains that a large-index family can first be reduced to a point-indexed
jointly surjective subfamily before forming its scheme coproduct.

Edge cases checked before drafting and in the second pass:

- For empty I, the joint-surjectivity assumption forces X empty. The family
  property is vacuous and the equivalence correctly asserts P(f) for empty source.
  Each of the five affine-local properties holds for maps from the empty scheme.
- Empty X makes the locality predicate's pointwise chart condition vacuous, as
  required. Nonempty sources have identity pointed charts in the forward direction.
- An empty U does not descend any nontrivial square claim unless a is surjective,
  in which case X is empty. No surjectivity is required of b.
- Nonseparated étale target maps are allowed: the proof uses an étale graph section,
  not a closed graph. Infinite and non-quasi-compact source covers are allowed.
- No relative-dimension assertion or implicit finite-type strengthening is added.
  All characteristics and arbitrary schemes in a common scheme universe are included.

Searches actually run through `/home/ubuntu/weil-launcher-all/batch2/msearch.py`:

- `leanfinder`, query: “Smooth etale flat locally of finite presentation and locally
  of finite type scheme morphisms are etale local on source and target”. Eight
  hits, including étale-to-smooth and permanence/local ring facts; no whole-item match.
- `loogle`, query: `AlgebraicGeometry.Etale, AlgebraicGeometry.Smooth`. One hit,
  `AlgebraicGeometry.Etale.instSmooth`, only an implication between two properties.
- `grep`, query: `([Ee]tale[Ll]ocal|[Ll]ocalOnSourceAndTarget|etale_local)` in
  `AlgebraicGeometry`. Zero Mathlib hits.
- `leansearch`, query: “Etale locality on source and target of smooth flat locally
  of finite type locally of finite presentation scheme morphisms”. Eight hits,
  including the existing property definitions, smooth implies lfp, and lfp implies
  lft; none states the required locality and square/family conclusions. Search
  services also returned obsolete IsSmooth/IsEtale aliases; I read and used the
  current source declarations Smooth/Etale instead.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf`, by item id and locality
  names, found no whole-item declaration. The precise locality-name search found
  `SpaceEtalePresentationPropertyCriterion.lean`, whose definition is reused.
  The proposed declaration name was also searched in Mathlib/project sources
  and `dag/lean_names_upstream.json`, with no duplicate found.

Validation: `scompile.py N5 lem-sfb-scheme-etale-source-target-properties` compiled
both the sandbox and intended library-module names cleanly (the final run took
1.7 s and 1.6 s respectively). No global build or direct live-repository mutation
was used. The final delivery dry run and push are run after this report is saved.

## Second reading by N5

I made a separate second pass with the sandbox declaration, the unchanged node
statement and the reused locality definition open. This is the dispatched worker's
second reading; the maintainer supplies the independent review after delivery.
I checked the five disjuncts individually: Smooth, Etale, Flat,
LocallyOfFinitePresentation and LocallyOfFiniteType, all with their existing scheme
meanings. I unfolded the reused definition on the page: its first conjunct is exactly
precomposition by an étale map, its second is base change of f along b (the second
pullback projection), and its final equivalence has every pointed-chart datum and
both étaleness conditions from the node. I checked the square's composition order
against fa=bh, the source-only surjectivity assumption in the reverse implication,
and the absence of target surjectivity. In the family clause I checked that each
map has domain U i, joint surjectivity quantifies over every point of X, and the
right side concerns the composite a i ≫ f. There is no Nonempty I or Small I
hypothesis, and the source and index universes are explicit and independent.

No mismatch required changing the accepted node statement, proof, or proof_deps.
The repaired dependency list cites the new definition owner of the unchanged
locality predicate and the existing surjectivity definition node. No dependency
module is needed. Every original hypothesis and conclusion is accounted for above;
no mathematical statement correction or dispute remains.

## New nodes

`def-sfb-etale-local-source-target-property` owns
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget` in
`Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion`, with
`existing: true`. This is the unchanged landed declaration, not a choice from a
postponed theorem. Q19's node and module are untouched. It depends exactly on
`def-pc-scheme` and `def-weil-etale-morphism`; its source is Stacks 04QZ in
`literature/stacks-project/descent.tex`, read at lines 7144–7177.

I reread all three conjuncts against that source: precomposition has exactly the
etale hypothesis on a; base change is `Limits.pullback.snd f b`, the projection
to V; locality quantifies over every point x and supplies all U, V, a, b, h, u,
both etaleness conditions, `a.base u = x`, `a ≫ f = h ≫ b`, and P(h).
There is no isomorphism-invariance assumption in this definition. Empty sources
make the pointwise condition vacuous, just as in 04QZ; no Nonempty assumptions
are inserted. All variables and the universe u are explicitly bound upstream.

Fresh searches for this definition used msearch.py:

- LeanSearch, “Property of scheme morphisms etale local on the source and target”:
  8 hits, including IsLocalAtTarget and affine-local constructions, none this
  three-clause definition.
- LeanFinder, “Property of scheme morphisms etale local on source and target
  precomposition base change pointed charts”: 8 hits, concerning etale permanence
  and IsLocalAtSource, none the full definition.
- Mathlib grep, `IsEtaleLocalOnSourceAndTarget|[Ll]ocalOnSourceAndTarget|etale_local`
  in AlgebraicGeometry: 0 hits. Direct exact-name rg over Mathlib,
  WeilConjectures, Sheaf and dag/lean_names_upstream.json finds only the landed
  Sheaf declaration and its consumers in that module. DAG 04QZ/name search
  finds theorem nodes but no definition owner. `tools/blueprint_refs.py search`
  for “étale local on the source-and-target” gives 0 matches. The new node records
  these searches and the names returned, without treating the remote services'
  obsolete IsEtale alias as the pinned library definition.

The helper's blueprint ancestor command returns None, matching the item's
`blueprint.from.node = null`; its via is the item's id followed by the item's via.
No new module is supplied because one definition per notion requires reuse.

## Repair of L's return

The single mandatory point is repaired by the new definition node and replacing
the saved packet's theorem-node statement dependency with that definition node.
The advisory is also addressed by citing `def-weil-surjective-morphism`. The Lean
file, verbatim theorem signature, nine-step proof docstring, mathematical statement,
proof and proof_deps remain unchanged. I read the live module with
`scompile.py --source Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion`
and confirmed the reused definition is unchanged from the returned version.
The fresh `scompile.py` server compile passed for both the sandbox module (1.7 s)
and its intended library module name (1.6 s), without errors or unexpected warnings.
The signature matches the node record verbatim; the existing definition signature
also matches its source verbatim. Only lean and stmt_deps change in the item.
The repaired delivery dry run and push follow this saved report.


The repaired dry run first required the schema key `import_flags` on the new
definition node; added it as `[]` and reran the prescribed delivery wrapper.

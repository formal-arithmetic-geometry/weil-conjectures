## Worker report

Stage 2, Q04, item `lem-sfb-space-fppf-covering-calculus`, 2026-10-23.

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus` defines
`AlgebraicGeometry.AlgebraicSpace.IsFppfCover` and states six theorems, all with
`sorry` proofs. The predicate is the definition introduced by this very node,
not a new independent notion. No mathematical statement correction, new node,
or dependency interface repair is needed. The accepted stage-1 split is retained.
The inherited stage-1 unchanged-item refusal is superseded by the explicit
stage-2 handoff in `coord/brief-stage2.md` section 0.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Base scheme S | `{S : Scheme.{u}}` in every declaration |
| Algebraic spaces over S and their morphisms | `X X' : AlgebraicSpace S`, `Xᵢ : I → AlgebraicSpace S`, maps `Xᵢ i ⟶ X` |
| Set-indexed families, with the size convention | `I : Type w`, and `K : I → Type v` in composition; no `Small`, `Nonempty`, finite or countability assumptions |
| Each map flat on étale scheme charts | `∀ i, MapIsFlat (f i)` in `IsFppfCover`; the dependency expands this to `MapIsLocally (@Flat)` |
| Each map locally of finite presentation on charts | `∀ i, MapIsLocallyOfFinitePresentation (f i)` in the same predicate |
| Jointly surjective on field-valued point classes | `IsJointlySurjective (fun i ↦ (f i).hom.hom)`, exactly the recorded field-extension-lifting predicate |
| Étale means representable étale | `IsEtale (f i).hom.hom`, the recorded representable scheme-test predicate |
| (1) Every jointly surjective étale family is fppf | `isFppfCover_of_isEtale`, with precisely the two hypotheses `he` and `hs` |
| (2) Arbitrary algebraic-space base change | `isFppfCover_pullback`, with `hf : IsFppfCover f` and unrestricted `a : X' ⟶ X` |
| The specified sheaf fibre product and its projection | `enlargedFibreProductFst a (f i)`; its domain is the existing `enlargedFibreProduct a (f i)`, whose underlying sheaf is literally `Limits.pullback a.hom (f i).hom` |
| (3) A covering over each covering member | `isFppfCover_comp`, with `hf : IsFppfCover f` and `he : ∀ i, IsFppfCover (e i)` |
| Composite family indexed by pairs (i,k) | `fun j : Sigma K ↦ e j.1 j.2 ≫ f j.1`, including different index universes |
| (4) Sources and target are schemes over S | `T : Over S`, `Tᵢ : I → Over S`, and `f : ∀ i, Tᵢ i ⟶ T` in `isFppfCover_scheme_iff` |
| Equivalence with an fppf covering of schemes | The left uses the actual `schemeSpace` objects and `yoneda.map (f i)`; the right is `Presieve.ofArrows ... ∈ Scheme.fppfPrecoverage T.left`, not merely membership of a generated sieve in the topology |
| Empty index sets precisely over the empty target | `isFppfCover_empty_index_iff` assumes only `[IsEmpty I]` and gives the equivalence with `Nonempty (X ≅ schemeSpace (Over.mk (Scheme.emptyTo S)))` |
| Empty covering members allowed | `isFppfCover_remove_empty_member_iff` identifies covering before and after removing an index whose source is isomorphic to the empty scheme space; thus inserting it imposes no extra condition |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, with
  `Flat.iff_flat_stalkMap` confirming the node's stalkwise interpretation.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`; the former is precisely the covering-family condition.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsEtale`, and the underlying sheaves and full-subcategory maps.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`: `IsJointlySurjective`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback` and
  `etale_fibreProduct_isScheme`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`,
  `MapIsFlat`, `MapIsLocallyOfFinitePresentation`.
- `def-trf-scheme-algebraic-space` owns `schemeSpace`, in
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`. Its actual data is the fppf
  Yoneda sheaf; `schemeSheaf_isAlgebraicSpace` supplies only its Prop-valued
  algebraic-space property.
- `def-sfb-space-sheaf-fibre-product` owns `enlargedFibreProduct` and
  `enlargedFibreProductFst`, in the same module. Their actual data is respectively
  `Limits.pullback f.hom g.hom` and `Limits.pullback.fst f.hom g.hom`; only the
  algebraic-space property comes from `fibreProduct_isAlgebraicSpace`.
  The unchanged import `Sheaf.AlgebraicGeometry.SmallEnlargedEtaleModules`
  publicly imports this defining module, so the same declarations remain visible.
  These two existing definition nodes are added to `stmt_deps`; the theorem node
  `lem-trf-space-enlarged-etale-ringed-site-model` is not a statement dependency.
  The signature uses these plain constructions, not that theorem's conclusion.
- `def-weil-size-convention` is recorded as a metatheoretic convention; explicit
  universes `u w v` implement it and no import is specified by that node.

Proof dependencies already stated are imported as plain imports:
`Mathlib.AlgebraicGeometry.Morphisms.Etale` (étale scheme properties),
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (qcqs permanence),
`Mathlib.AlgebraicGeometry.ResidueField` (`Scheme.SpecToEquivOfField` and the
residue-field factorization),
`Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`
(`representable_etale_scheme_tests`),
`Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties`
(`scheme_etale_source_target_properties`), and
`Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion`
(`etalePresentation_property_criterion`). Flat composition/base change and local
finite presentation composition/base change are in the already public-imported
Mathlib modules. The proof dependency `lem-sfb-space-local-properties-chart-test`
has no Lean record or Mathlib match, so it has no module to import yet; this is a
proof dependency only and is not required to type any delivered statement. Its
role is fully retained in the theorem proof docstrings. No upstream proof-import
edits are attempted outside the sandbox.

Edge cases checked before writing:

- Empty indexing is allowed in the predicate and all four numbered clauses.
  Flatness and finite-presentation clauses are vacuous, but joint surjectivity is
  not; the empty-index theorem forces precisely the empty target space.
- An empty source is étale-locally empty, hence flat and locally finitely presented,
  and contributes no field-valued point. The removal theorem treats any empty
  member, with no assumption on the other sources or on the target.
- Composition permits empty outer and empty inner index types. A nonempty outer
  covering member cannot itself be covered by an empty inner family; the inner
  covering hypothesis expresses precisely that condition.
- Base change has no representability, flatness, étaleness, surjectivity or size
  restriction on the map `a`. Its fibre product is the sheaf fibre product, not a
  scheme fibre product incorrectly assumed to exist in schemes.
- Scheme comparison uses maps in `Over S`, not arbitrary unrelated Yoneda maps,
  and compares with the precoverage rather than a potentially larger topology.
- Family universes are independent of the scheme universe; no coproduct of all
  members is constructed, so large index types introduce no false smallness
  condition. The dependent-sum index has universe `max w v`. Field-valued points
  use exactly the test-field universe of the recorded algebraic-space interface.

Searches (all through the authorized tools, plus read-only source searches):

1. `msearch.py ... leansearch "Fppf coverings of algebraic spaces form a
   pretopology agreeing with schemes"`: eight scheme-site results, including
   `Scheme.overPretopology`, `smallPretopology`, and
   `jointlySurjectivePretopology`; none is this algebraic-space statement.
2. `msearch.py ... leanfinder "Fppf covering families of algebraic spaces stable
   under arbitrary base change and composition and equivalent to fppf coverings
   of schemes"`: eight scheme-cover results, none for algebraic spaces.
   A second shorter stability query likewise returned scheme precoverages only.
3. `msearch.py ... loogle "AlgebraicGeometry.Scheme.fppfPrecoverage,
   AlgebraicGeometry.AlgebraicSpace"`: no hits; the algebraic-space identifier is
   unknown to Mathlib. `loogle '"fppfPrecoverage"'` returned seven scheme-only
   declarations, including the two stability instances and singleton-cover lemma.
4. `msearch.py ... grep 'IsFppfCover|fppfCover|FppfCover|AlgebraicSpace'
   AlgebraicGeometry`: no hits in its search index. Direct read of Mathlib's
   `AlgebraicGeometry/Sites/Fpqc.lean` confirms its coverage is on `Scheme`.
5. `rg` searches of `lean/WeilConjectures` and `lean/Sheaf` for
   `IsFppfCover|fppfCover|FppfCover` found unrelated stack and group-quotient
   predicates but no algebraic-space covering predicate or calculus.
   Searching the item's id in `lean/WeilConjectures` found no declaration.
6. Direct `rg` searches of the algebraic-space modules found and allowed reuse of
   `MapIsFlat`, `MapIsLocallyOfFinitePresentation`, `schemeSpace`, and
   `enlargedFibreProductFst`; no duplicate notions were written.

Read the source `literature/stacks-project/spaces-topologies.tex`, definition
`definition-fppf-covering` (03Y8), its scheme comparison paragraph,
`lemma-zariski-etale-smooth-syntomic-fppf` (0DFC), and `lemma-fppf` (03Y9).
The statements match the accepted node. No statement dispute or node fault found.

Validation: prescribed `scompile.py Q04 lem-sfb-space-fppf-covering-calculus <file>`
passed for the sandbox module (9.5 s) and final module path (7.3 s), with no error
or unexpected warning. Every variable and universe is explicitly bound;
`set_option autoImplicit false` enforces this. All lines are at most 100 characters.
All six theorem proofs are `sorry`; the definition is full propositional data.

## Second reading by Q04

A second clause-by-clause reading of the current node, source text, dependency
signatures, and final module checked the six rows of conclusions against the four
numbered clauses and the final empty-case sentence. The order of composition is
`e ≫ f` (the node's `f e`), and the first projection is from `X' ×_X Xᵢ` to `X'`.
The scheme morphisms are Yoneda maps of exactly the same `Over S` arrows whose
underlying scheme arrows occur on the right. The empty-index conclusion is an
isomorphism to the actual empty scheme space, rather than just an uninterpreted
emptiness predicate. The empty-member equivalence deletes only that member and
retains all remaining arrows. The family definition uses each recorded dependency
unchanged. No mismatch was found and no mathematical correction was made.

This is the dispatched worker's second pass; no independent worker was started,
as the dispatch expressly forbids subagents. The maintainer's independent delivery
review remains separate from this pass.

## Repair of returned delivery fcdc0805625a

The maintainer returned H2/H12: the saved packet cited the enlarged-ringed-site
theorem only to access plain definitions already owned by definition nodes.
Replaced that theorem in the saved packet's `stmt_deps` with the existing nodes
`def-trf-scheme-algebraic-space` and `def-sfb-space-sheaf-fibre-product`.
Read both current node records and the full definitions and docstrings in
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` (schemeSpace at lines 68–77;
fibre product and first projection at lines 226–239). These provide precisely the
actual representable sheaf and sheaf-pullback maps used by the unchanged signature.
No new node or dependency module was created. Updated `lean.note` to explain the
ownership correction; the item was rebased by retaining current live node fields
and applying only this delivery's `stmt_deps` additions and `lean` record.
The prescribed delivery wrapper builds the commit on current `sheaf-dag`.

The Lean file is byte-identical to the retained returned packet, SHA256
`b0a34e522064844f5e886da9de87354d97d2e5994c87509dbc489ea1a27448b8`.
Its definitions, all six theorem statements and sorry proofs, docstrings and
imports are unchanged. A fresh self-check found the same four numbered clauses,
the empty-index characterization and the empty-member equivalence; the definition
owners change no hypotheses, universes, constructions or conclusions. The only
node fields changed against current live are `stmt_deps` and `lean`.

The initial saved-packet dry run passed (commit `486a748fa7a`, nothing pushed).
That mechanical pass did not repair the independent H2/H12 return; the ownership
correction above is the substantive repair. Fresh prescribed `scompile.py` validation passed cleanly for both the sandbox
module (11.4 s) and the final library path (5.4 s). The local packet self-check
verified the exact recorded signature, the two definition-owner dependencies,
only the authorized node-field changes, the unchanged Lean SHA256, six sorry-only
theorems, explicit binders and the 100-character line bound. The prescribed final
`deliver2.py --no-push` preflight and compile gate runs before the actual push.

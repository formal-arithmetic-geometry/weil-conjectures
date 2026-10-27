## Worker report

The theorem `AlgebraicGeometry.exists_intrinsic_resolution_of_embedded` in
`Sheaf.AlgebraicGeometry.EmbeddedToIntrinsicSmoothResolution` states the conditional
embedded-to-intrinsic reduction. Its only proof is `sorry`. The companion definition
module `Sheaf.AlgebraicGeometry.IntrinsicLabeledResolution` supplies the missing intrinsic
interface, using the published ordinary and embedded towers without copying them.
All its definitions have real data; there are no postponed helper theorems.

Hypothesis and clause correspondence:

- The fixed totally ordered set is `(L : Type w) [LinearOrder L]`, with an independent
  label universe. The specified assignment is
  `(E : SynchronizedEmbeddedResolution.{u, w} L)`, not an existence assumption about
  some other algorithm.
- Work over Q, reducedness, finite type and the absence of a separation condition on
  inputs are `RationalResolutionInput`: `scheme`, `structureMap` to the universe lift
  of Spec Q, `reduced`, `finiteType`, `quasiCompact`.
- Membership in C is `EmbeddableResolutionInput`, the subtype with
  `Nonempty (RationalResolutionEmbedding S)`. Its witnesses are the existing
  `EmbeddedResolutionPair` and an input isomorphism respecting the Q-structure.
  `EmbeddedResolutionPair` requires a closed immersion and a smooth separated
  finite-type ambient (the last condition is LocallyOfFiniteType + QuasiCompact).
  Membership is a property, so the assignment is not indexed by chosen embeddings.
- The first theorem conjunct gives embeddings for all affine inputs. The second
  gives them for every finite family `Fin n`, each member affine, and every coproduct
  cocone `IsColimit (Cofan.mk T.scheme j)`. This includes arbitrary isomorphic models
  of the finite disjoint union, and includes n = 0. It does not select a coproduct
  object or require component embeddings as extra assumptions.
- The third conjunct is `Nonempty (IntrinsicResolutionOfEmbedded L E)`, one assignment
  on every member of C simultaneously.
- `IntrinsicLabeledOrdinaryTower.ordinary` is the recorded `OrdinaryBlowupTower`.
  `resolves` is its recorded `IsRegularResolution`: finite-type quasi-coherent ideal
  centers, nonempty closed supports, `IsNowhereDense` closed supports, regular center
  schemes and a regular last scheme. Because the supports are closed, nowhere dense
  is precisely empty interior. The additional `coherent` field records the full
  finite-type-and-finite-type-kernel condition, not merely finite presentation.
- `label : Fin ordinary.length ↪o L` gives precisely a finite strictly increasing
  list. It keeps an active center even if its ordinary blowup is an isomorphism.
  `index_labels`, `index_bot`, `index_top`, `index_before` identify the cut index
  with the number of active labels in that cut. `stage` and `stage_naturality`
  identify the entire cut diagram with the finite ordinary tower, including every
  transition. `center_ordinary` transports the actual ideal at every retained
  label, and `center_absent` inserts exactly unit ideals at missing labels.
- `regular_input` and `empty_input` require ordinary length zero, with no nonempty
  input assumption and no requirement that L itself be nonempty.
- `IntrinsicEmbeddedResolutionIdentification.iso`, `initial`, `labels`, `centers`
  identify the intrinsic diagram with E's entire strict-transform diagram over the
  specified input isomorphism, preserving the actual intrinsic kernel ideals and
  labels. `IntrinsicResolutionOfEmbedded.embedding` gives this for every embedding;
  `cocycle` equates the composite through E's specified intrinsic comparison with
  the other identification. Thus it is the supplied change-of-embedding cocycle,
  not an arbitrary isomorphism between final schemes.
- `comparison` quantifies over every Q-morphism `h` between members of C with
  `[Smooth h]`. There is no `[IsSeparated h]`, surjectivity or fixed relative
  dimension assumption. `IntrinsicLabeledResolutionPullback.map` is a natural
  transformation at every cut, so it respects all transitions. `cartesian` is an
  actual `IsPullback` square over h at every cut, including repeated levels.
  `centers` says equality with `IdealSheafData.comap` for every label. `retained`
  says exactly that a source label is a target label with nonunit extended ideal;
  no label is renumbered or reordered. Combined with `center_ordinary`, these
  comparisons identify the contracted finite ordinary pullback towers.
- `ambient` conjugates this natural transformation by the specified embedding
  identifications and equates it to `(E.pullback f).intrinsic`. Here f is the recorded
  `EmbeddedResolutionSmoothMap`, so the initial ambient square is cartesian. This
  includes open restrictions, using the ambient open constructed in proof Step 3.
- `unique` states uniqueness among these cartesian center-preserving comparisons.
  This expresses canonicity and the assertion that changing charts/lifts cannot
  change the maps or ideals. It is justified by the blowup rigidity argument of
  node Steps 2 and 9, and adds no hypothesis to the conditional theorem. The chart
  restrictions are covered by `ambient` and the open case; uniqueness gives their
  independence and the compatibility for identities and composites.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.OrdinaryResolutionRule`: `RationalResolutionInput`,
  `OrdinaryBlowupTower`, `OrdinaryBlowupTower.toBase`,
  `OrdinaryBlowupTower.IsRegularResolution`; the general
  `OrdinaryResolutionComparison` was also read. The new comparison uses the shared
  cut representation to avoid dropping labels when comparing different lengths.
- `Sheaf.AlgebraicGeometry.LabeledEmbeddedResolution`: `EmbeddedResolutionPair`,
  `EmbeddedResolutionSmoothMap`, `LabeledEmbeddedResolutionTower`,
  `LabeledEmbeddedResolutionPullback`,
  `LabeledEmbeddedResolutionIntrinsicComparison`, `SynchronizedEmbeddedResolution`.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`; the ordinary tower
  includes its specified blowup isomorphisms and structure-map equations.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `IsRegularScheme`, the conjunction
  of local Noetherianity and regular stalks.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the repaired public coherence
  interface was read. As in the existing embedded tower, the exact scheme-side
  `Scheme.Modules.IsFiniteTypeWithFiniteTypeKernels` from
  `WeilConjectures.AlgebraicGeometry.Cohomology.FiniteFibre` renders Stacks 01BV;
  its full signature and docstring were read. The Q25 conjunction alone would
  not express its kernel clause. No duplicate coherence predicate is defined.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`: `IdealSheafData.comap`,
  the kernel ideal of the pullback closed immersion, and `comapIso`.
- Mathlib: `IsReduced` (Properties), `LocallyOfFiniteType` (FiniteType),
  `QuasiCompact` (QuasiCompact), `Smooth` (Smooth), `IsClosedImmersion`
  (ClosedImmersion), `IsSeparated` and `IsProper` (Separated/Proper),
  `IsOpenImmersion` (OpenImmersion), and `Limits.pullback` and its projections
  (Pullback.HasPullback). Their source signatures/docstrings were read. These
  notions are also exposed by the existing embedded/ordinary modules.

The theorem imports every recorded, available proof-dependency module (including the
strict-transform/blowup, principalization, universal-property, flat-base-change,
standard-smooth quotient lift, etale/smooth and Noetherian modules). Other proof
primitives reside in the existing public imports. No import of the downstream
smooth-functorial ordinary-resolution theorem is made.

Sources read: the local ILO PDF, converted in the item scratchpad, VIII 2.1.1--2.1.9
and 2.3.4--2.3.13. In particular 2.1.1 states rigidity, 2.1.3(ii) the intrinsic
blowup identification, 2.1.9 flat base change, and 2.3.13 the synchronization issue
for varying relative dimension. This is a conditional agent-supplied reduction,
not a separately quoted ILO theorem. The latest blueprint locality statement was
also read: it uses contracting correspondences. This delivery retains the recorded
historical resolution branch and does not change the blueprint unit.

Edge cases checked: empty input; n = 0 and the empty coproduct; regular input; empty
label type or no active labels; opens missing all centers; a nonempty Cartier center
whose blowup is an isomorphism (its label remains); a nonsurjective smooth map;
charts of different relative dimension; smooth maps without a separation hypothesis;
arbitrary label universe; no nilpotence assumption on the chart quotient. All centers
remain ideal sheaves, not just reduced supports or arbitrary blowup morphisms.

Searches (2026-10-24):

- msearch LeanFinder, `A synchronized embedded resolution induces an intrinsic
  ordinary blowup resolution functor compatible with smooth morphisms`: 8 hits,
  residue immersions and categorical left resolutions, no match.
- msearch Loogle, `SynchronizedEmbeddedResolution, OrdinaryBlowupTower`: no match,
  identifier unknown to the Mathlib search service.
- msearch grep, `embedded.*resolution|resolution.*ambient|OrdinaryBlowupTower`,
  AlgebraicGeometry: 0 hits. Same concept search in WeilConjectures found only an
  unrelated self-Tor comment. The exact item-id search there found no declaration.
- msearch LeanSearch, `Intrinsic labeled ordinary blowup resolution tower with
  canonical smooth pullback comparisons`: 8 hits, generic pullback/open immersion,
  smooth-base-change and comapIso declarations, no labeled-resolution interface.
- msearch grep of the three proposed interface names: 0 hits.
- DAG, Sheaf, WeilConjectures and upstream-name searches for the proposed names
  found no declaration. The concept occurs in the parent theorem's prose but has
  no definition node. Sheaf's ordinary and labeled embedded modules were found,
  opened in full and reused. `blueprint_refs.py search` for `intrinsic resolution`
  and `labeled ordinary` returned 0 blueprint nodes.

Validation: both modules compiled separately in dependency order via scompile.py,
including their library module names and the private sibling overlay. No errors
or unexpected warnings. The dry-run and delivery results are recorded below.

## New nodes

`def-trf-intrinsic-labeled-resolution` owns the missing intrinsic labeled assignment
interface and its immediately associated embedding, tower, pullback and identification
structures in `IntrinsicLabeledResolution.lean`. Source: ILO VIII 2.1.4--2.1.9,
2.3.4--2.3.5, 2.3.11--2.3.13, as the interface for this conditional reduction.
The ordinary and embedded tower notions already exist and are reused. Neither the
DAG nor Mathlib nor either Lean source root supplies the interface linking an actual
finite ordinary tower to E's cut diagrams with the requested ideal-preserving
comparisons. The new node records all search outputs and cites the existing notions.
It asserts no existence and contains no sorry or arbitrary choice.

## Statement corrected

The old clause said: "The comparison restricts to the canonical embedded comparison
wherever h extends to a smooth map of ambient schemes". The corrected clause adds
"in a cartesian square of embedded pairs". The entire original statement is preserved
verbatim in `statement_change.old_statement`.

Without this condition, the named embedded comparison is undefined. For example,
embed Spec Q at the origin in A^1 and in A^2. Projection A^2 to A^1 is smooth and
extends the identity of Spec Q, but its inverse image of the origin is A^1, rather
than the given point in A^2. E's smooth comparison, by its recorded definition, is
only supplied for cartesian squares. ILO VIII 2.1.9 and 2.3.4--2.3.5 concern precisely
base-change towers; Step 5's quotient lifts produce those cartesian squares. The
previous stage-1 review already explicitly noted this same intended interpretation.
No case of the intrinsic comparison for arbitrary smooth h is removed.

The full citer search found exactly one other node:
`lem-trf-smooth-functorial-ordinary-resolution` (holds: true). Its Step 1 uses the
intrinsic assignment on embeddable inputs, finite disjoint unions of affines and
arbitrary smooth/open comparisons, all retained. Subsequent affine chart comparisons
use cartesian quotient lifts. Its statement, proof and Lean source are not edited.
The added statement dependency names the new intrinsic interface; old_stmt_deps is
recorded, while proof and proof_deps remain unchanged.

## Second reading by Q56

This is a second pass by the author; the dispatch brief forbids spawning another
agent, and the maintainer supplies the independent review. I reopened both module
texts, the item, and the new node and checked the correspondence above. In particular:
`index_labels` prevents any extra cut-level stages; `stage_naturality` compares all
transitions; `center_ordinary` compares actual ideals; `retained` excludes new labels
and deletes exactly unit ideals; `ambient` uses the specified E map, not a chosen
isomorphism. The assignment's index is a property subtype, not chosen embeddings.
The only mismatch found was the missing cartesian condition, corrected with the full
citer audit above. No dependency-record repairs, hidden axioms, hollow definitions,
local notation, auto-bound variables, universe equalities or target changes were made.

Dry run: deliver2.py --no-push returned OK for commit 2758fb6a811; server preflight
and both per-file compiles passed.

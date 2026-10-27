## Worker report

The module `Sheaf.AlgebraicGeometry.MaximumHistoryIntrinsicCocycle` states
`AlgebraicGeometry.exists_maximum_history_intrinsic_cocycle`, with one `sorry` and no
proofs. Its auxiliary predicate `IsIntrinsicBlowupHistoryComparison` spells out the
ordinary-blowup characterization of the next component, including uniqueness of the
induced map. No object or definition has postponed data.

I read the three statement dependency nodes and the signatures and docstrings in
`ResolutionInvariantCalculusData.lean`, `EmbeddedResolutionHistory.lean` and
`LabeledEmbeddedResolution.lean`. I read ILO Expose VIII printed pp.91--94 (PDF pages
97--100), particularly the first-regular convention in 2.3.11 and the deletion and
synchronization discussion in 2.3.4--2.3.5. I also read the current blueprint's
`lem-trf-local-term-locality.proof.md`: the node's blueprint ancestry is historical,
as its recorded `blueprint.from.place` explains; the actual conditional history source
is ILO plus the explicit induction in this node, not the present trace-locality proof.
The example CompactObject module has been withdrawn in the current clone; I followed
the module headers and public declarations of the three actual dependencies instead.

Hypotheses and clauses, in the order of the node:

- The order and bottom are `{V : Type w} [LinearOrder V] [OrderBot V]`;
  `ν : ResolutionInvariantCalculus.{u} V` is the recorded calculus, with independent
  scheme and invariant universes. No well-foundedness or relative dimension is assumed.
- `A B : EmbeddedResolutionPair.{u}` are exactly the reduced closed rational pairs
  of the dependency, including disconnected and empty pairs; `e : A.X ≅ B.X` is the
  initial scheme isomorphism, with no ambient isomorphism or rationality restriction
  imposed on this intrinsic isomorphism.
- `H K : FiniteMaximumLabeledHistory ν ...` package the given finite histories and
  their label realizations. `prefixHistory`, `extension`, `maximum` and `admissible`
  give the empty-started maximum-prefix sequence. `firstRegular` and `finalRegular`
  express stopping precisely at first regularity. `labelMaximum` and `increasing`
  label the actual extensions by their positive maxima in the reverse order.
- The existential family `c` gives actual natural-isomorphism comparisons for every
  pair of supplied histories and every initial isomorphism. Its codomain is the
  dependency's `LabeledEmbeddedResolutionIntrinsicComparison`, whose `initial`
  field gives the specified initial component, `labels` gives the same active labels,
  and `centers` is the equality of ideal sheaves under actual `comap`.
- `H.length = K.length` states simultaneous stopping. The pointwise equality of
  `valueAtCut` for every cut states identification of the local invariant functions
  before every label, and also at terminal and intermediate cuts. Since these
  components are scheme isomorphisms, it identifies the value ranges and hence their
  greatest elements. `labelMaximum` and equality of active label sets also identify
  the labeled positive maximum values explicitly.
- Intrinsic center ideals are `(tower.centerToIntrinsic l).ker`. The comparison's
  `centers` field says exactly `I = J.comap a_i.hom`, the ideal-sheaf rendering of
  `I = a_i^* J O_X`. The input maximum conditions give their reduced maximum-locus
  structures; these are ideals rather than equality of supports alone.
- At each active label `IsIntrinsicBlowupHistoryComparison` supplies identifications
  `s,t` of the next strict transforms with the ordinary intrinsic blowups, over the
  preceding stages. Its last equivalence says that a map between these intrinsic
  blowups lies over the preceding comparison if and only if it agrees with the next
  comparison through `s,t`. This characterizes precisely the induced ordinary-blowup
  map, including its uniqueness. The input tower's `strictTransform`,
  `strictTransformMap` and `strictTransformToSource` already identify these next
  objects with the given strict transforms in the two ambient blowups.
- Transition compatibility is the naturality of `c.iso`; all lower-cut transitions,
  not just individual successor arrows, are included. The raw history and tower
  keep each center separately. `increasing` concerns labels only, so an intrinsic
  blowup which is an identity still keeps its center and chronological place.
- For two embeddings of the same scheme one specializes `e` to its identity;
  the second conjunct states that for the same history the resulting natural
  isomorphism is the identity. For three pairs the next conjunct says precisely
  `c H M (e ≪≫ f) = c H K e ≪≫ c K M f`, as natural isomorphisms.
- The final conjunct quantifies over both smooth ambient maps of initial pairs,
  the original and pulled-back histories, and their specified labeled pullback
  comparisons `p,q`. `IsPullback e'.hom f.intrinsic g.intrinsic e.hom` is the
  cartesian square of initial intrinsic isomorphisms. The displayed equality of
  natural transformations is the commuting comparison square on every cut.
  The dependency's pullback structure already requires cartesian stage diagrams,
  ideal extension and deletion of exactly the empty centers. Thus this compares
  the identified pulled-back histories as in the node, and includes restrictions
  because open immersions are smooth. The existence/description of those smooth
  comparisons is the separate proof dependency, not an extra assertion proved here.
- The index category is all `LowerSet (OrderDual {v : V // v ≠ ⊥})`, so no cut or
  absent-label stage is omitted. `stageCount` selects exactly the number of active
  labels in the cut, and the realization is a natural isomorphism with that raw
  stage diagram. At absent labels the dependency tower has the unit center and
  identity stages up to its specified diagram isomorphisms.

Dependency declarations actually used:

- `Sheaf.AlgebraicGeometry.ResolutionInvariantCalculusData`:
  `AlgebraicGeometry.ResolutionInvariantCalculus` and its `value`.
- `Sheaf.AlgebraicGeometry.EmbeddedResolutionHistory`:
  `EmbeddedResolutionHistory`, `Extension`, `IsMaximumStep`, `Admissible` and `X`.
- `Sheaf.AlgebraicGeometry.LabeledEmbeddedResolution`:
  `EmbeddedResolutionPair`, `EmbeddedResolutionSmoothMap`,
  `LabeledEmbeddedResolutionTower`, `LabeledEmbeddedResolutionPullback`,
  `LabeledEmbeddedResolutionIntrinsicComparison`.
- The new definition module publicly imports the recorded calculus module, which
  publicly supplies the other two recorded dependencies. The item publicly imports
  this definition module, exposing those same dependency declarations.

The stated proof dependencies are imported privately from
`WeilConjectures.Compactification.StrictTransformBlowup`
(`Scheme.IdealSheafData.exists_blowup_comap_iso_strictTransform`),
`WeilConjectures.Blowup.Principalization`
(`Scheme.IdealSheafData.isInvertible_comap_blowupMap`) and
`WeilConjectures.Blowup.BlowupUniversal`
(`Scheme.IdealSheafData.exists_lift_blowup`,
`Scheme.IdealSheafData.hom_ext_of_isInvertible_comap`). Their actual signatures and
source docstrings were read. The smooth-deletion proof dependency has no Lean
record on this base, so there is no module to import; its mathematical conclusion
is used in step 8 of the proof docstring. The present statement quantifies over the
identified pullback histories rather than needing to construct them as data.

Edge cases checked before drafting: length zero has one raw stage and no centers;
regular or empty inputs force length zero by `firstRegular`, with all cuts selecting
stage zero. Empty source in a smooth pullback deletes all centers; the pullback
structure permits this without a nonempty hypothesis. The value order may consist
only of bottom, so the label type may be empty. Arbitrary lower cuts, repeated
identity transitions, identity intrinsic blowups, disconnected inputs of different
dimensions and ambient embeddings of different dimensions are allowed. No equality
of ambient schemes appears anywhere in the comparison. Prefix-extension coherence
was added during the author's review so that the actual supplied extensions refer
to the same earlier diagrams, rather than to unrelated isomorphic prefixes.

Searches actually performed:

- `msearch.py leanfinder`, query "Intrinsic comparison and cocycle for finite
  maximum-extension embedded resolution histories": complex-extension and generic
  homological declarations, no resolution-history theorem.
- `msearch.py loogle`, query `"blowup"`: zero hits.
- `msearch.py leansearch`, query "Finite embedded blowup maximum histories stopping
  at first regular scheme": finite-morphism declarations, no match.
- LeanSearch and LeanFinder, query "Finite maximum-extension embedded blowup
  history with all raw prefixes stopping at first regular strict transform and
  labeled lower-cut realization": Hahn embedding/Finset maxima/finite morphisms
  and complex embeddings, no matching notion. Their actual logged records are in
  the new definition node's `mathlib_searches`.
- `msearch.py grep`, patterns `maximum.history|MaximumHistory|IntrinsicComparison`
  and `FiniteMaximumLabeledHistory|resolutionHistoryPrefixIndex|IsIntrinsicBlowupHistoryComparison|exists_maximum_history_intrinsic_cocycle`:
  zero Mathlib hits. Direct `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` found no declaration under the proposed names;
  the conceptual `IntrinsicComparison` matches in Sheaf were the recorded raw
  history structure and unrelated pro-etale coefficient comparisons.
- Direct grep for this item id in `lean/WeilConjectures`: no declaration.
  DAG grep found the three existing conditional maximum-history statements but no
  definition connecting their raw histories to cut realizations.
  `blueprint_refs.py search 'maximum history'` and `'finite maximum'` returned zero
  blueprint nodes. `blueprint_refs.py ancestor` returned `lem-trf-local-term-locality`.

No statement correction, disputed statement, dependency replacement, or axiom is
introduced. Every variable and universe is explicit and `autoImplicit` is false.

## New nodes

`def-trf-finite-maximum-labeled-history` defines the supplied stopped maximum-prefix
sequence together with its actual raw history and labeled realization. Source: ILO
VIII 2.3.1, 2.3.4--2.3.5, 2.3.11--2.3.13, pp.91--94, and the explicit lower-cut
convention of the item's statement. Existing nodes define raw histories and labeled
towers separately; neither connects the actual maximum prefixes and their values
to the cut-indexed tower. The definition reuses both existing structures, with
natural identification data and explicit coherence of prefix extensions. Its two
helper definitions are the increasing prefix-stage inclusion and the transported
invariant function at a cut. They have real formulae, no choices or postponed data.
The searches above and in `mathlib_searches` found no existing definition of this
combined input notion. Its regularity and label conditions express the supplied
first-regular maximum histories, not an existence assertion or an assumption of
any comparisons between different histories.

## Second reading by Q34

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

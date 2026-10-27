## Worker report

The item is stated by `AlgebraicGeometry.GenericallyReducedResolution.exists_calculus` in
`Sheaf.AlgebraicGeometry.GenericallyReducedRationalInvariantCalculus`. Its sole theorem proof
is `sorry`; its docstring retains all nine complete proof steps and their dependency names.
The node's statement and proof are unchanged. One definition node supplies the missing
nonreduced-input history and calculus interface; it has actual structure data and no sorry.

Hypotheses and clauses, checked with the node and the complete declaration bodies open:

- Work over Q: `Pair.base : P ⟶ Spec (.of (ULift.{u} ℚ))`. The lift places the rational field
  in the scheme universe and imposes no mathematical field extension. `Pair.closed` is the
  closed immersion; `smooth`, `separated`, `finiteType`, `quasiCompact` are precisely the
  ambient hypotheses. `finiteTypeIntrinsic` and `quasiCompactIntrinsic` give finite type
  of X. `genericallyReduced` uses `genericPoints X` and reducedness of the actual stalks.
  There is no `IsReduced X` hypothesis, connectedness hypothesis, dimension bound or
  equidimensionality condition. Thus finite disjoint unions of the indicated pairs are
  among the same inputs, with the same value type and assignment.
- A `History` records two functors indexed by the opposite finite ordered set, their
  closed inclusions, identified initial pair, each actual ambient ideal and its closed
  map into the intrinsic scheme, and isomorphisms with the ordinary blowup and the
  scheme-theoretic strict transform. Both maps from the strict transform are retained,
  excluding a replacement by a topological closure or a reduction. `History.Extension`
  retains the complete earlier diagrams and the ordered ideal centers. An identity
  intrinsic blowup does not erase its earlier ideal.
- `ValueFamily` is simultaneous on all finite raw histories; assertions are restricted
  to the least generated `Admissible` class. It starts with empty histories, closes under
  `MaximumStep`, ambient smooth pullback and intrinsic smooth comparison. Open restrictions
  are included because open immersions are smooth. Prefixes of maximum constructions are
  obtained at each construction step, and restriction/pullback comparisons retain all
  stages except precisely those with unit pulled-back ideal. Both comparison structures
  use a monotone surjection of stage indices and test emptiness at each transition.
- Clause (1), one total value set with least element: `exists_calculus` quantifies over a
  `LinearOrder V` and `OrderBot V`. Here V already denotes the augmented set V union bottom;
  there is no well-foundedness assumption. `Calculus.finiteImage` and `closedUpper` give
  finite range and closed upper strata on every admissible finite-type history. The values
  are synchronization values, with their normalization expressed by `ambientValues` and
  `intrinsicValues`, including projection from an adjoined smooth factor. No equality to
  raw Hilbert--Samuel functions is imposed.
- Nonbottom maximum: `MaximumStep` says the center is reduced and its whole intrinsic
  image is exactly the full maximum level, with `IsGreatest` and strict inequality over
  bottom. `maximumExists` provides an extension at each such maximum. `maximumGeometry`
  gives nonemptiness, `IsRegularScheme`, empty interior of its closed image (hence nowhere
  density), actual `RingedSpace.IsCoherent` of both the ambient and intrinsic center
  ideals, and avoidance of every point mapping to the INITIAL regular locus. The ambient
  ideal is transported back along the extension's recorded ambient isomorphism.
- The allowed extension is an ordinary ambient blowup by `History.ambientBlowup`, with
  actual scheme-theoretic strict transform and its maps by the three strict-transform
  fields. `Admissible.step` includes this extension, and `stageGeometry` supplies smooth,
  separated finite-type ambient and finite-type generically reduced strict transform at
  every admissible stage. `bottomRegular` gives the all-bottom conclusion; `regularInput`
  and `regularPoint` exclude active strata on initially regular schemes. Empty X has no
  points and therefore no positive maximum, without requiring it to be nonempty.
- Clause (2), open and smooth comparison: `ambientPullbackExists` and
  `intrinsicPullbackExists` provide compared histories with empty stages deleted.
  `ambientValues` and `intrinsicValues` compare actual pointwise values on them. There is
  no relative dimension parameter or constant-relative-dimension restriction. Intrinsic
  comparisons do not require an ambient morphism, so differing local embeddings are
  admitted. `StratumIdeal` describes the reduced ideal of ANY individual stratum on ANY
  open where it is closed, not only the maximum or its closure in all of X. `StrataPullback`
  compares the actual pulled-back ideal, including the unit ideal for an empty inverse
  image. `ambientIdeals` and `intrinsicIdeals` assert this for the intrinsic schemes;
  `AmbientStratumIdeal`, `AmbientStrataPullback` and `ambientStratumIdeals` include the
  reduced ideal in the local ambient charts as well. These predicates quantify over every
  representing reduced ideal and make no arbitrary choice of ideals.
- Same intrinsic history and earlier ordered centers, different embeddings:
  `History.IntrinsicComparison` retains the natural isomorphism of whole intrinsic
  diagrams and equality of the intrinsic center kernel ideals at every earlier stage.
  `embeddingValues` compares functions pointwise and `embeddingIdeals` compares each
  individual reduced stratum ideal via the final intrinsic isomorphism. Ambient ideals
  are their reduced image ideals as specified by `AmbientStratumIdeal`; they live in
  different ambient rings, so their meaningful comparison is through these local charts.
  Comparisons with a third embedding and further pullbacks are equalities of the same
  values and the same pulled-back reduced ideals. Equality is transitive and ideal
  comap is functorial; no unrelated chosen identification requires a further axiom.
- Clause (3): `termination` forbids an infinite sequence of length-n histories starting
  at length zero and extended by full positive maximum steps. Every length-zero history
  is admissible and all later histories are generated by the steps. With `maximumExists`
  and `bottomRegular`, this is finite termination at a regular strict transform. There
  is no intrinsic blowup substituted for the ambient blowup and no passage to reduction.
  The clause permits omission of optional exceptional-divisor cleanup; the given DAG
  proof explicitly chooses to stop at regularity. This implementation takes that option.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `QuasiCompact`:
  `AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced` for schemes and
  `_root_.IsReduced` for the generic stalks; `Mathlib.Topology.Sober.genericPoints`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsSeparated`, via its
  separated-morphism public dependency. Properness itself is not a hypothesis.
- `WeilConjectures.Blowup.Gluing`: `Scheme.IdealSheafData.blowup`, `blowupMap`.
- `WeilConjectures.Compactification.StrictTransform`: the recorded general `strictTransform`
  and its exact specialization `Scheme.IdealSheafData.strictTransform`, with
  `strictTransformMap` and `strictTransformToSource`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` publicly supplies the recorded coherence
  interface, including `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`. The coherent ideal is the module
  `Scheme.IdealSheafData.toModules` of the actual quasi-coherent ideal.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.

The recorded, already stated proof-dependency modules are imported non-publicly. Proof
nodes without a declaration are not invented as hypotheses. In particular the reduced-only
smooth-center blowup theorem is not applied to a generically reduced strict transform;
its ambient part is the only part used in the natural-language proof. No proof dependency
is needed merely to type the statement, so these unstated proofs do not prevent stating it.

Edge cases checked: empty scheme, length-zero history, all centers disappearing under
pullback, empty individual strata (unit ideals), smooth maps with varying relative
dimension, disconnected inputs of different dimensions, a regular input with a divisor
center whose intrinsic blowup is an identity, and embedded nilpotents. For example
Q[x,y]/(x^2,xy) has a reduced generic local ring on its line but a nonregular embedded
nilpotent at the origin; it is admitted by `GenericallyReduced` and its scheme-theoretic
strict transforms are retained. Q[x]/(x^2) is NOT generically reduced and is excluded.
A regular input cannot start a positive maximum step; no irrelevant cleanup step is
forced. The value type at universe u+1 accommodates the fixed numerical alphabet and
any needed uniform labels without restricting the universe of schemes.

Searches performed through msearch.py (actual results are in the new node):

- LeanFinder: “generically reduced scheme functorial resolution singularities Hilbert
  Samuel marked ideal invariant maximum stratum smooth pullback”: eight hits, only
  normalization, reducedness, smoothness and etale basics; no calculus.
- Loogle: “AlgebraicGeometry.strictTransform,
  AlgebraicGeometry.Scheme.IdealSheafData.blowup”: no hits, strictTransform unknown to
  the Mathlib-only service. The actual project declarations were read directly and used.
- Mathlib grep in AlgebraicGeometry: “ResolutionHistory|MarkedIdeal|HilbertSamuel|
  GenericallyReduced|[Ii]nvariant[Cc]alculus”: no hits.
- LeanSearch: “generically reduced embedded resolution histories invariant smooth
  functoriality”: eight hits, smoothness/reducedness and unrelated categorical resolutions.
- Project grep in BOTH WeilConjectures and Sheaf found the reduced-only
  `EmbeddedResolutionPair`, `EmbeddedResolutionHistory`, `ResolutionInvariantCalculus`,
  which were read in full; `EmbeddedResolutionPair.reduced` excludes the item. Searches
  for `GenericallyReduced`, `genericallyReduced`, `generically_reduced` found no reusable
  project definition. The item id has no occurrence in WeilConjectures.
- DAG grep for generically reduced and blueprint_refs.py search “generically reduced”:
  existing theorem nodes mention this condition, but no definition node carries this
  generically reduced history/calculus interface. The blueprint search returned zero.

Source read: current latest ancestor blueprint statement and proof, plus the cited
arXiv:0905.3580v1 PDF, pp. 12--15, Theorem/Addendum 6.1 and sections 6.1--6.3.
No statement correction or STATEMENT-DISPUTED fault was found.

Validation: both delivered modules compiled separately through scompile.py, in dependency
order against the live published server library, with no errors or non-sorry warnings.

## New nodes

`def-per-generically-reduced-invariant-calculus-data` defines `Pair`, `History`, its ordered
extensions and smooth/intrinsic comparisons, the simultaneous `ValueFamily`, generated
`Admissible` histories, local reduced stratum ideals and `Calculus`. Source: the item's
BMT Theorem/Addendum 6.1, sections 6.1--6.3. The LeanSearch, LeanFinder, Loogle and Mathlib
and project grep searches above found no such interface. Existing trace-formula history
and calculus nodes are specifically for reduced inputs, require `IsReduced X`, and cannot
be instantiated on the embedded-nilpotent example above. This is a different input class,
not a private copy of a usable dependency. All basic geometric notions and constructions
are the recorded dependency declarations. The new node cites exactly those nine original
statement dependencies and the item adds only this new definition dependency.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

This repairs returned head 4e9e16fdec10, retaining the accepted Lean statement and the
earlier substantive repair of 3bed5c56b097. The module states the exceptional coefficient
comparison on the recorded intrinsic Dctf categories. Its map is uniquely specified by
the counit identity with the actual `reductionDirectImageComparison φ j p`. The chart
clause is `ReductionExceptionalChartEquation`, including its coefficient-origin square
and the equality of the two actual chart morphisms. All definitions have real data;
all postponed results are named theorems with source and natural-language proof.

Hypothesis and clause correspondence:

- `ℓ pchar`, `Fact ℓ.Prime`, `hp`, `hℓ`, `Field k`, and `CharP k pchar` give the
  characteristic and prime assumptions. `pchar ≠ ℓ` is the symmetric form of ℓ ≠ p.
- The `Over`, `IsOver`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`
  instances give separated finite-type schemes and morphisms over k. `Z` is the
  compactification scheme. Its finite-type and separated properties follow from
  properness over the standing Y. `j`, `p`, and `hf` fix one compactification for
  both coefficient rings, rather than selecting coefficient-dependent ones.
- `d : ℕ` and `SmoothOfRelativeDimension d f` give smoothness of pure dimension d.
- `A B : Type u`, their `CommRing` and `Finite` instances, `hA`, `hB`, and
  `φ : A →+* B` give the exact coefficient assumptions. The annihilator uses nsmul:
  for rings, annihilation of all elements by ℓ^n is equivalent to ℓ^n = 0.
- `spFiniteConstructibleTorCategory T R` is the full subcategory for the recorded
  `spFiniteConstructibleTor`: bounded cohomology, intrinsic constructibility of
  every cohomology sheaf, and `HasFiniteProEtaleTorAmplitude`. K is an object of
  this category, without extra D-plus or etale-origin hypotheses.
- `reductionCtfCompactSupport` and `reductionCtfScalar` restrict the actual
  `reductionCompactSupport` and `scalarExtensionFunctor`; the membership witnesses
  `hFA`, `hFB`, `hSX`, `hSY` are conclusions. The exceptional functors and their
  restricted adjunctions are also conclusions. There is no assumed
  `HasBoundedBelowUpperShriek` instance.
- `ReductionExceptionalRealization` records ordinary-etale origins and right
  adjoints for that identical compactification. Its `counit` equation fixes the
  comparison with each constructible right adjoint by the actual transported
  ordinary counit. This is additional interface data for the existing adjunction,
  rather than an arbitrary exceptional functor or arbitrary chart orientation.
- `hb` is invertibility of the actual named b only at `(GA.obj K).obj`, which is
  Dctf. No arbitrary natural transformation b or ambient invertibility assumption
  occurs. The displayed equation with `@inv ... (hb K)` is exactly the source's
  transpose equation. `c` is a natural transformation, so naturality is included;
  its componentwise `IsIso` clause supplies the asserted isomorphism.
- On charts, `reductionEtaleChartAdjunction` composes the actual derived
  sum/evaluation adjunction with `affineTraceAdjunction`. The latter is the
  recorded ordered-coordinate expression of p* K(d)[2d], including d = 0.
  `reductionEtaleChartLeftIso` uses the graph-normalized compact-support family,
  proper/open composition and common refinement. `reductionEtaleChartRightIso`
  is `rightAdjointUniq` for that left comparison; hence it preserves precisely
  the specified counits. `reductionIntrinsicChartIso` transports this map with
  the canonical site/pullback and coefficient-realization comparisons.
- The right side of `ReductionExceptionalChartEquation` is the explicit
  canonical scalar/pullback/Tate reassociation. It uses `tensorIso`,
  `scalarPullbackIso`, the Tate map normalized on every root generator, and the
  scalar commutation with shift. `reductionEtaleAffineScalarIso` pastes these
  factors coordinate by coordinate. Its base case is the identity. The origin
  comparison `o` is fixed by its displayed equation after site inverse image;
  it cannot insert a scalar automorphism. The left side restricts the actual c
  using `directImageScalarPullbackIso`. This gives the requested chart equality.
- The ordinary coefficient rings are only `ULift A` and `ULift B` inside the
  canonical fixed-scalar realization equivalence. They do not replace A and B
  in the theorem or introduce another scalar-extension functor. The actual
  intrinsic scalar adjunction is used in `reductionRealizationScalarMap`.

Declarations used in the statement and constructions:

- `Sheaf.SecSmoothPurity.ReductionDirectImage`: `reductionCompactSupport` and
  `reductionDirectImageComparison` (the named b, including its orientation).
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: `scalarExtensionFunctor`;
  `Sheaf.SecSmoothPurity.DirectImageScalarExchange`: `directImageScalarPullbackIso`.
- `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spFiniteConstructibleTor` and
  `spFiniteConstructibleTorCategory`, using the recorded constructibility and Tor
  predicates from the item's original statement dependencies.
- Mathlib's `AlgebraicGeometry.SmoothOfRelativeDimension` and standard field,
  ring, scheme-over-base, finite-type, proper and open-immersion predicates.
- `Sheaf.AlgebraicGeometry.AffineSpaceTopTrace`: `affineTraceLeft`,
  `affineTraceRight`, `affineTraceAdjunction`, and the affine-line factors.
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`:
  `etaleAmbientLeftComparison`; the upstream module
  `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection` supplies
  `derivedEtaleLowerShriekUpperStarAdjunction` with coefficient category
  `ModuleCat A` and the explicit étaleness proof.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`:
  `EtaleCompactSupportNormalization`, whose graph and derived normalization
  equations fix the compact-support-to-sum comparison.
- `Sheaf.Paper.ExceptionalCoefficientComparison`: `ExceptionalCoefficients.tensorIso`;
  `Sheaf.Paper.PurEtaleScalarMateProjection`: `scalarPullbackIso`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicDerivedEquivalence` and
  `sfIntrinsicDerivedDirectImageComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange`:
  `openSquarePullbackModel`; `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`:
  `sfDerivedComparisonPullbackIso`.
- `Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction`:
  `fixedCompactSupportComparisonIso`; `Sheaf.Paper.WitnessCompatibility`:
  `pbcComparisonReduction` and `pbcFixedScalarExtension`, only inside the canonical
  fixed-coefficient realization coordinates.
- `Scheme.finiteEtaleTateLine`, `finiteEtaleTateOneGenerator` and
  `Etale.ordinaryFiniteLine` give the actual roots-of-unity Tate line.
- `Sheaf.Paper.SfCompactSupportRestrictionOfScalars`: `sfRealizationRestriction`,
  reusing its sectionwise normalized square before exact derived descent.
- The upstream proper/open composition and common-refinement isomorphisms,
  `Adjunction.rightAdjointUniq`, `mateEquiv`, exact derived descent, and the
  canonical derived scalar adjunction supply the categorical constructions.

`Sheaf.Paper.FiniteLocalizingExceptionalPreservation` is a proof import for the
source's preservation step, not a claimed direct construction of an ambient
pro-etale adjoint. The main proof docstring reproduces all thirteen source steps,
including finite-Tor site transport, the Kummer splitting calculation, nonflat
coefficient change, coordinate induction, open-restriction cancellation, and
isomorphism detection on a smooth chart cover. The statement dependencies cite the canonical interfaces actually used in the statement.
This repair adds definition ownership records for three published constructions and the
four missing recorded dependencies identified by the maintainer; details are below.

Edge cases checked by reading the definitions and types: empty schemes; zero
coefficient rings; n = 0 common annihilator (only zero coefficient rings); arbitrary
nonflat coefficient maps; identity coefficient maps; d = 0 (literal identity affine
adjunction and reassociation); identity/open charts; and unbounded ambient objects
excluded from K by the Dctf domain. No equality of derived morphisms is inferred
merely by checking geometric stalks. The finite scalar-unit and root-generator
normalizations fix maps before exact descent or K-flat localization.

Searches: the retained `searches.jsonl` and node `mathlib_searches` contain the
LeanFinder, Loogle, LeanSearch and Mathlib grep searches. The additional Mathlib
grep `extraordinary|exceptional.*pullback|shriek` in AlgebraicGeometry returned zero
hits. Searches in upstream WeilConjectures and side Sheaf sources found the generic
adjunction, scalar, tensor and trace interfaces listed above, but no declaration
of this whole exceptional coefficient comparison. DAG/interface searches also
checked the normalized tower and chart dependencies. Three definition ownership nodes are introduced, all with existing:true and no duplicate
Lean module. No statement correction or statement dispute is introduced.

## Second reading by NW

The dispatcher forbids starting another agent and explicitly requests the remaining
self-check. I reread the node, its thirteen proof steps, the returned objections,
and the repaired signature and constructions. The old arbitrary b, missing smooth
dimension, D-plus domain, lifted main coefficient rings, ambient adjunction
assumptions, missing chart clause and placeholder dependency claims are all removed.
The chart map is now fixed by actual sum/evaluation and affine trace counits, and
the coefficient side is fixed on root generators and derived representatives.
The two displayed chart paths have the same source and target after the normalized
origin comparison. The source statement and proof are unchanged. I compared the saved node with the current shared node: its statement and all thirteen
proof steps agree; the only source-node change is the added list of already landed
statement interfaces. I also compared the repaired module with returned-source.txt,
which retains the rejected head. This retry moved the leftover diagnostic module from
lean/ to scratchpad/, so it cannot be packaged as an unowned delivery module. The
small-site witness is now a public instance, rather than file-local state, at exactly
universe u+1. Generated structure helper proofs are disabled, as in the existing
constructible exceptional-adjunction interface, to avoid unnecessary elaboration.
The prescribed full-file compiler passes cleanly (sandbox 21.8 s; delivery
module 26.1 s, exit 0). Diagnostic prefix checks only located elaboration costs
and are not delivered. The required `deliver2.py --no-push` run passed
preflight and compilation (dry-run commit 77ff38221d).

The retry also found and reused `sfRealizationRestriction` instead of restating its
underived normalization theorem. The Tate scalar map is now directly the adjoint
transpose of the root-generator map; its invertibility is a named theorem. Both
ordered-coordinate constructions use `Nat.rec` to avoid auxiliary equations generated
by dependent pattern matching. These are changes to construction and elaboration only.

The coordinate chart uses the common annihilator as the natural number `ℓ^n`,
then casts that number into every coefficient ring and the ring of global sections.
This makes the inputs to the recorded Tate constructions literally the same N.

Current upstream exposes the exact derived sum-extension adjunction with a coefficient
category argument and an explicit étaleness proof. Both chart calls now use
`ModuleCat A` and `inferInstance`; the ordinary derived-pullback comparison then
changes only its right-functor model. The zero-coordinate identity branch names its
implicit object `_K`, so the unused-variable linter does not warn.

The prefix compiler additionally located a missing explicit import: the canonical
`sfDerivedComparisonPullbackIso` is defined in
`Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`. The module now imports
that owner directly instead of relying on an earlier transitive import.

A final elaboration review factors the transported counit formula into
`reductionRealizationCounitEquation`; the record still requires exactly that
equation. `reductionExceptionalComponent` is explicitly the underlying arrow
`(c.app K).hom`, with its actual intrinsic scalar-extension source and target.
These named interfaces prevent repeated unfolding in the chart equation. The
root-generator map also has an explicit sheaf-morphism result type. A diagnostic
prefix through the intrinsic chart construction checks in about 20 seconds; only
the final, complete module check counts as delivery validation.


## Repair of return 4e9e16fdec10

1. Replaced the statement dependencies `lem-amb-etale-adjoint-locality` and
   `thm-sf-ambient-adjoint-class` by definition nodes
   `def-sp-etale-adjoint-chart-comparison` and
   `def-sp-fixed-compact-support-comparison`. The first owns the published
   `etaleAmbientLeftComparison` and degreewise sum/evaluation adjunction; the second owns
   `fixedCompactSupportComparisonIso` in `FiniteComparisonClassAdjunction`. Both theorem
   ids remain in `proof_deps` (the latter is added there as explicitly requested by the
   return), and `SpecifiedExceptionalClassHom` is imported as a proof dependency.
   No theorem from that module is used to construct the statement. The existing genuine
   theorem statement dependencies providing `tensorIso`, `openSquarePullbackModel`, and
   `sfRealizationRestriction` remain: each supplies data by a theorem's `.choose`.
2. Added `def-asd-ordinary-finite-p1-arrows` for `OrdinaryFiniteTwistTransport`,
   `def-asd-ordinary-finite-p1-data` for `OrdinaryFiniteP1Datum`,
   `def-sp-etale-compact-support-normalization` for `EtaleCompactSupportNormalization`,
   `lem-fix-direct-image-scalar-exchange` for `directImageScalarPullbackIso`, and
   `lem-pur-etale-scalar-mate-projection` for the theorem-chosen `scalarPullbackIso`.
   Their owning modules are now explicitly publicly imported. The two scalar comparisons
   are precisely the existing maps in the chart equation and its reassociation.

The saved packet's initial prescribed dry run passed at 04d3977bc7, but the independent
reader's content objections still required these repairs. They change dependency ownership
and imports only. I compared the saved node with the current shared main node: its natural
statement, source, proof, and other non-Lean fields agree, apart from the statement-dependency
additions already present in the saved packet. The two removed theorem statement dependencies
were additions of that packet, not original statement dependencies of current main. The only
additional non-Lean change is the proof-dependency reclassification explicitly requested in
this return. The main `lean.statement` remains verbatim and the theorem body remains `sorry`.

## New nodes

`def-sp-constant-scalar-pullback-comparison` defines the canonical scalar-extension
functor, ordinary uncompleted direct image and scalar/pullback isomorphism for arbitrary
commutative rings and arbitrary scheme morphisms. It cites the actual general ringed
operations, constant-section inverse-image maps, and `def-weil-pbc-four-corners`'s
ringed scalar-extension/reduction-pullback interface. The new record's signature is
verbatim from the published `def directImageScalarPullbackIso`, and its other two
recorded declarations are the existing abbreviations. The source and docstrings use
Stacks 06YY, 07A5/07A6, 03EL and 0D6D. The isomorphism is exactly the fixed inverse mate
from FourCorners, specialized to the natural constant-coefficient square. No theorem
from DirectImageScalarExchange supplies any of these three definitions. The new node
owns those published specializations and creates no second copy. LeanSearch, LeanFinder,
Loogle and Mathlib grep find no exact Mathlib construction. Upstream and Sheaf grep
locate this published source; DAG and blueprint exact-name/concept searches find only
its theorem owner, with no definition node. Exact queries/results are recorded in the
new node's `mathlib_searches`. The new node's statement dependencies have no statement
path back to this item (the FourCorners closure was checked explicitly).


`def-sp-etale-adjoint-chart-comparison` records the already constructed ordinary-etale
sum adjunction and graph-normalized left comparison. Its primary existing declaration is
`AlgebraicGeometry.Etale.etaleAmbientLeftComparison` in
`Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`, with the public derived adjunction
also listed. I read the published source with `scompile.py --source`. The current generic
adjunction owner is
`WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection`; the consumer correctly
uses its coefficient category `ModuleCat A` and explicit etaleness proof. The left comparison
is the inverse normalization at the closure compactification, followed by compatible
composition and common refinement. Its source is the etale-locality blueprint and its
published construction. DAG exact-name and concept searches found no definition node for
this constructed interface. LeanSearch returned only general derived adjunctions;
LeanFinder returned site and condensed definitions; Loogle and Mathlib grep found no match.
The upstream and Sheaf grep found this exact published construction, so it is reused with
`existing:true`, rather than redefined or attached through the locality theorem.

`def-sp-fixed-compact-support-comparison` records exactly
`AlgebraicGeometry.ProEtale.fixedCompactSupportComparisonIso` in
`Sheaf.AlgebraicGeometry.FiniteComparisonClassAdjunction`. Its source is the bounded-below
comparison-class blueprint construction. It is defined for arbitrary schemes and finite
commutative A, without the special finite-field coefficient datum of the theorem. Its
source functor is the bounded-below etale inclusion, then site pullback, then pro-etale
compact support; the target is inclusion, etale compact support, then site pullback. The
actual map commutes open extension with comparison, then uses the inverse specified
proper-direct-image counit mate, with bounded-below compatibility and associators. The
new record copies the complete published signature. Exact-name and concept DAG searches
found theorem/helper references, without a definition node owning this construction.
The LeanSearch/LeanFinder/Loogle/Mathlib grep results above found no Mathlib match; Sheaf
grep located the exact existing definition. It is recorded `existing:true` with no module
copy and without using the special theorem `specifiedExceptionalHomEquiv`.

`def-sp-etale-compact-support-normalization` records exactly the structure
`AlgebraicGeometry.Etale.EtaleCompactSupportNormalization` in
`Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`. Its source is Stacks 03S3/03S5/03S6/0F4L: the sum-extension adjunction,
exactness, canonical base-change comparison, and graph-extension map into direct image.
The simultaneous normalization datum is already published with the separate existence lemma. It defines
simultaneous comparison data and equations, not their existence. Its sole coefficient
hypothesis is `CommRing A`; finiteness belongs to the separate existence theorem. Each
field was checked: `comparison`, `sheafComparison`, `sheaf_normalization`,
`derived_normalization`, `base_change`, the pasted `composition` square, `refinement`
with Noetherian coarser compactification, `identity`, and the unique counit-preserving
`adjunction` comparison. The new natural statement enumerates exactly these fields.
DAG searches found the owner existence lemma but no definition node for its structure.
The graph-normalization LeanSearch returned unrelated counits; Loogle and Mathlib grep
found none. Sheaf grep located the exact existing structure, now reused with `existing:true`.
Every new node contains the actual search queries and result summaries in `mathlib_searches`.

## Second reading of this repair by NW

I reread both numbered return points against the node, complete consumer file, and the
three published owners, and checked each new node's declaration and statement. The
accepted theorem still has exactly the same characteristic, coefficient, geometric,
Dctf, counit, natural-isomorphism and normalized chart clauses. No term in its signature,
chart equation, or definitions changed. The four missing dependency records now name the
actual P1 transport/data and scalar comparisons. The two theorem nodes that only supplied
plain definitions have been reclassified as requested; their replacements name precisely
the constructors used. No theorem-chosen comparison was mistakenly reclassified as plain
definition data. All three new nodes use `existing:true`, their recorded signatures agree
with their source, and no new Lean definition or postponed theorem was created. Normalization
remains universally quantified in the chart clause: neither its existence lemma nor a
chosen arbitrary family is added as a theorem hypothesis. Empty schemes, zero coefficients,
nonflat maps and the identity/dimension-zero cases remain as checked in the earlier reading.
The dispatcher forbids delegation; this is the required author self-check, with the
maintainer's independent content review still required on the delivery.

Validation for this repair: the explicit `scompile.py NW det-sp-reduction-exceptional`
run compiled the newly required proof import (8.1 s), the complete sandbox module
(23.4 s), and its library placement (25.2 s), without errors or non-sorry warnings.
A source-only self-check confirms that every new definition dependency resolves,
none reaches back to this item, all delivered Lean lines have at most 100 characters,
and the accepted theorem signature is exactly its recorded `lean.statement`.
The new-node statements were also reread for composition order: their displayed
comparisons use conventional functional order, matching the Lean functor composites.

The first repaired dry run reported metadata faults on the new definition nodes.
These are repaired: their `blueprint.from.via` is empty because the item itself is
a blueprint node; every definition dependency has its own `[id]` citation; and existing
definition signatures start at the `def` keyword, as the server's source-signature
extractor requires. Its warnings about the theorem-backed comparisons were checked
against the return: the three explicitly accepted theorem-chosen comparisons remain
statement dependencies, as do the two scalar interfaces expressly requested there.
The new nodes' composition expressions and the compactification middle scheme are
explicit, so every displayed map is typed by the introduced objects.

## Repair of return 1f522a9a7776

The returned immutable head accepts the complete statement and constructions, and asks
for one ownership correction (H13/A3). Replaced the added statement dependency
`lem-fix-direct-image-scalar-exchange` by the new definition node
`def-sp-constant-scalar-pullback-comparison`. Its `existing:true` record names exactly
`directImageConstantPush`, `directImageScalarPullbackIso`, and
`directImageScalarExtension` in `Sheaf.SecSmoothPurity.DirectImageScalarExchange`.
The exchange theorem is not used to construct or state the item. The module remains
publicly imported for its three actual plain constructions. Removed the unused private
import of `SpecifiedExceptionalClassHom`, as the minor review observation requests.
No declaration signature, docstring, definition body or theorem statement changed.

The saved packet's earlier request to add a proof dependency was not in the accepted
returned head: the delivery wrapper kept current-main proof metadata. This repair
rebases that untouched metadata to current main and removes the unused proof import;
it introduces no proof-dependency change and requires no launcher-tool change.
The source statement and all thirteen proof steps still agree with current main.
The prior three definition ownership nodes are retained unchanged. Genuine theorem
statement dependencies for `tensorIso`, `openSquarePullbackModel`,
`sfRealizationRestriction`, and `scalarPullbackIso` are retained, as the return confirms.

## Second reading of return 1f522a9a7776 by NW

The dispatcher prohibits delegation; this is the author's requested self-check.
I reread the latest return, the complete saved node and consumer, the new node and the
three published definitions including their full signatures and docstrings. The new
node quantifies arbitrary `CommRing A`, `CommRing B`, `φ : A →+* B` and `f : T ⟶ V`
at the actual universe u. The source and target of its isomorphism agree with the Lean
composite order: `S_V ⋙ f_B*` to `f_A* ⋙ S_T` denotes mathematically
`f_B* S_V ≅ S_T f_A*`. Its direct image uses exactly the constant-section identification,
and its scalar map is the actual map induced by φ. Empty schemes, zero rings, identity
maps and nonflat coefficient maps remain admitted; no Finite or properness instance is
required by these three declarations. The theorem still has the accepted smooth
relative dimension d, common compactification, intrinsic Dctf inputs and scalar extension,
actual b, unique natural c satisfying the counit equation, component isomorphisms,
and the normalized chart equation. Its signature remains verbatim in `lean.statement`.
The only Lean edit is deletion of the unused private import. No data, theorem proof,
source statement or dependency node was changed.

Validation of the latest repair: the prescribed explicit `scompile.py NW det-sp-reduction-exceptional` run completed with exit 0, no errors and no non-sorry
warnings: sandbox placement 20.6 s and library placement 23.6 s. All delivered Lean
lines are at most 100 characters. The main node differs from current main only in
`lean` and added statement interfaces; its source statement, proof and proof dependencies
are unchanged. All four existing-definition signature records occur verbatim in their
published source modules, and every new-node citation is listed in its `stmt_deps`.

The fresh latest-repair dry run passed server preflight and all compile/check files:
`OK (dry run): commit e7cd041e15 passes the preflight and compiles; nothing pushed`.
It staged all four definition-node records, including the new constant-scalar/pullback
owner, the main node, the unchanged declarations with the unused import removed, and
this report. No metadata field was discarded by the wrapper in this fresh run.


## Repair of return 249843638e94

The initial saved-packet dry run passed at `0bcd3ffe43`, including preflight and
per-file compilation. The independent return identifies a further route-lock defect:
the source place of `def-sp-etale-compact-support-normalization` cited a prohibited
reference. Replaced that source place with the precise Stacks references and their
roles, and corrected the corresponding source paragraph above. No source route is
changed: the record still uses the same canonical sum-extension and graph maps.

I opened `literature/stacks-project/etale-cohomology.tex` at all four cited labels.
Tag 03S3 defines the module-sheaf sum-extension/inverse-image adjunction and gives
the presheaf sum model. Tag 03S5 gives its stalk formula and exactness. Tag 03S6
specifies the base-change identification by adjunction. Tag 0F4L constructs the
map into direct image by extending each summand off its open-and-closed graph.
The new node assembles normalization data for these maps; it does not claim that
these tags prove existence of the entire simultaneous family. That theorem remains
separate. The ordinary derived unit and counit-preserving uniqueness specify the
derived and adjunction fields of the datum, just as in the recorded structure.

## Second reading of return 249843638e94 by NW

The dispatcher prohibits delegation; this is the required author self-check.
I reread the normalization structure, its source labels, the new node and the main
theorem. All structure fields still have their recorded counterparts: comparison,
sheaf comparison, graph equation, homotopy representative equation, base change,
pasting, proper refinement, identity and the unique counit-preserving right-adjoint
isomorphism. The coefficient universe remains u+1, schemes remain universe u, and
no finite-ring hypothesis or existence assertion is added to the datum.
The main theorem retains its smooth dimension, intrinsic Dctf inputs, actual b,
unique natural c, counit equation, invertibility and chart normalization clauses.
All five recorded signatures occur verbatim in their source files; the delivered
Lean file has no line longer than 100 characters. The main node differs from current
shared main only in `lean` and the retained added statement interfaces. This repair
changes only the new normalization node's source place and this report.

The explicit post-repair `scompile.py` check passed with exit 0 and no compiler
messages: sandbox 20.9 s, library placement 20.1 s.

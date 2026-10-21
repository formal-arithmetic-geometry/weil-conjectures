## Worker report

The module `Sheaf.Paper.StrictQuotientExchangeUnitEquation`, using the four
definition modules listed below, states
`SheafOfModules.StrictQuotientExchange.strictQuotientExchangeUnitEquation`, with
its proof `sorry`. Its helper definitions specify the strict augmented coefficient
diagrams, their derived tensor reduction, canonical projection arrows, evaluated
and quotient-ring comparisons, and the derived-limit/coaugmentation composite.

The metatheoretic def-weil-size-convention is rendered by explicit universes `u w`,
small site categories in `RingedTensorCorner.{u,w}`, and the `HasDerivedCategory.{w}`
fields/binders. There is no extra size equality between the site universe and the
derived Hom universe.

The module categories are `CategoryTheory.ringedSiteModules` from
`Sheaf.CategoryTheory.RingedSiteModules`, transparently used through the existing
`RingedTensorCorner.mateModules` from `Sheaf.Paper.ProjectionMateExact`.
The derived categories are Mathlib `DerivedCategory`, with the existing chosen
`HasDerivedCategory` structures. `RingedTensorEdge` supplies geometric inverse image,
the algebraic lift, extension of scalars, its module adjunction, its total left
derived comparison, and the derived adjunction. The explicit four named `IsIso ringMap` hypotheses
`hf`, `hg`, `hh`, `he` and four finite-limit/finite-colimit-preservation pairs express the stated
isomorphic coefficients and exact inverse images.

`RingedTensorSquare` (Sheaf.Paper.RingedTensorSquarePresentation) specifies the
ring-compatible commutative square. Its `modules` field fixes the chain square,
and `s.exchange` from Sheaf.Paper.RingedExchangeTensorCoherence is the ambient
Mathlib `CategoryTheory.mateEquiv` mate. `towerSquare` localizes this same square
on strict diagrams, and `towerMate` uses `mateEquiv` with the normalized derived
tower adjunctions; the theorem equates `conjugate` with this actual mate.

The inverse sequence is the functor `q.atS.Q : ℕᵒᵖ ⥤ CochainComplex S.mateModules ℤ`,
Mathlib's inverse-system encoding `Functor.ofOpSequence` with positive levels
reindexed by n+1. `q.atS.z` is the strict augmentation from the constant unit complex.
The other corners' sequences and augmentations are related by `PullReduction`'s
coefficient isomorphisms, their augmentation equations, and `CoefficientSquareData.square`,
which retains all transition maps and the specified square before localization.
`hperfect` quantifies over each level separately using
`SheafOfModules.IsPerfectOnRingedSiteOfUniverses` from
Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses. Its covering-sieve
definition allows locally bounded complexes of finite-free retracts and does not
require uniform bounds or globally free terms. `HasPerfectLevels` explicitly uses
the canonical small-site abelian sheafification on the site and its over-sites;
these constructions discharge infrastructure instances and add no hypothesis.

`ReductionData.functor`, `epsilon`, `derived` and `computes` specify the total left
derived functor of ordinary whole-sequence tensor `total`. Its augmentation is
normalized on flat-term K-flat representatives by the actual strict chain formula
`1 ⊗ z`. `ConstantLimitData.normalized` identifies the constant-tower isomorphism with
the ordinary constant/limit adjunction unit and the chosen total-derived-limit
comparison. Consequently `kappa` is exactly augmentation followed by total derived
inverse limit. These helpers have real data definitions and no postponed proofs.

The existing `StrictProjectionLimit` and `StrictProjectionDirectImage` records
from Sheaf.Paper.RingedStrictTowerProjectionMorphism supply the actual total
right-derived limit/direct image, their K-injective computation properties, the
whole-diagram evaluation comparison, and the ordinary-limit/direct-image
comparison. Their `roos` field uses the recorded `IsDerivedLimitTriangle` from
WeilConjectures.CategoryTheory.Triangulated.DerivedLimit. The normalized `a` field
is the comparison c used by `limitComparison`, with the indicated e reassociation.
`TowerAdjunctionData.normalized` specifies the ordinary adjunction transpose before
localization, using these same derived direct-image units. The evaluation helpers
use CategoryTheory.towerDerivedEvaluationInterchange from
Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization and localization's
fully faithful comparison; they are not unrelated isomorphisms at each level.

The displayed B and D are `upper` and `lower`. H is `firstProjection`, the inverse
f-pullback/reduction comparison followed by f-pullback of g's projection mate.
H' is `secondProjection`, h's projection mate followed by the inverse
e-pullback/reduction comparison. `projection` is the adjunction transpose of the
canonical pullback comparison followed by the derived counit. Both isomorphism
claims are in the first conclusion of the theorem. The remaining clauses use
that proved-as-a-conclusion isomorphism to write the inverse in `conjugate`.

`conjugate` is v = H⁻¹ followed by reduction of b and H'; `gamma` is the prescribed
Rlim(H), Rlim(v), c⁻¹ composite. The per-K conjunction gives whole-tower mate
equality, the evaluated mate equation under `evaluatedSource` and
`evaluatedTarget`, `QuotientEquation`, and the exact coaugmentation equation.
The last quantified equation states naturality in K for every derived morphism.

For quotient coefficients, `QuotientAtData.surjective` is local surjectivity of the
ring-sheaf map, and `coefficient` identifies the given coefficient complex with
the restricted quotient unit in degree zero. `forgetQuotient` is Mathlib's exact
`SheafOfModules.restrictScalars` localized on derived categories.
`QuotientComparisons` retains the indicated inverse-image/direct-image comparisons,
the ordinary counit equations, and the ring-compatible square. `QuotientEquation`
equates the restricted quotient mate with the evaluated v under those comparisons
for every quotient-module input representing the evaluated reduction.

No node statement has been corrected. Five new definition nodes record the
normalized presentations and canonical constructions needed by this item. All postponed mathematics is the single named theorem with the complete
seven-step natural-language proof.


The item gains the already-landed statement dependencies
`def-weil-pbc-ringed-tensor-square-presentation`,
`def-sbc-strict-projection-tower-data`, and
`def-weil-pbc-strict-perfect-coefficient-package`, whose declarations are reused.
The five new definition nodes are described below. No dependency record or
mathematical statement is corrected.

Edge cases checked: K = 0; zero coefficients; zero augmentation; the coefficient
unit in degree zero; identity and non-Cartesian squares; noninvertible ambient
mates; level-dependent and locally varying perfect bounds; finite-free rank zero;
quotient maps that are only locally surjective rather than surjective on global
sections. No completeness or reflector assumption on K or C is introduced.

Searches for an exact existing declaration (retained searches.jsonl):

- msearch.py leanfinder: "For a strict augmented tower of perfect coefficient
  complexes the projection formula exchange is the square adjunction mate and
  commutes with the coaugmentation after derived inverse limit". Eight generic
  Dold-Kan comparison hits; none states this result.
- msearch.py loogle: "CategoryTheory.mateEquiv, CategoryTheory.Adjunction".
  Twelve hits, including mateEquiv and its unit/counit formulas. The existing
  mate construction is reused. None is the augmented perfect-tower statement.
- msearch.py grep, CategoryTheory: "projectionFormula|coaugmentation|augmentedTower".
  No hits.
- rg over project Sheaf and WeilConjectures for strict augmented exchanges and
  projection-formula names: the finite-free strict-tower theorem supplies the
  models used here but restricts the coefficients to globally finite-free terms.
  It does not state this arbitrary locally perfect-coefficient square theorem.
- rg for this item's id and the proposed declaration in Sheaf and
  WeilConjectures: no existing declaration.

Validation: all five delivery modules compile cleanly with scompile.py against
current server sources, both under the sandbox names and their library module
names. The main theorem module compiles in 6.6 seconds; the definition modules
compile in 14.9, 9.1, 2.2 and 3.5 seconds. The delivery dry run passed the
maintainer preflight and per-file compiles (commit 84d9772a9e1). Earlier
import-artifact failures and discarded diagnostics remain only in scratchpad/.


Representation details: the generic data records retain every concrete
normalization. Named predicates for the representative, counit and square equations
keep their large types from being copied into every projection term. CoefficientAtData
and CoefficientSquareData group the seventeen coefficient fields, with direct
inherited projections. These implementation choices change no mathematical
hypothesis or conclusion. The existing Lean compatibility option
backward.proofsInPublic retains the representative proof terms in public definitions.
The constant/limit adjunction gives the additive limit functor via Mathlib's
Adjunction.right_adjoint_additive inside the definition.

## New nodes

`def-sbc-strict-augmented-coefficient-presentation` defines the normalized strict
augmented tensor reductions and their ring-compatible coefficient square. Its
module is `Sheaf.Paper.StrictAugmentedCoefficientPresentation`; `Coefficients` is
the main declaration and the reduction, augmentation and adjunction helpers are
listed in its Lean record. The source is the Stacks 0944/0A07 construction used by
the agent-supplied strict-diagram refinement.

`def-sbc-strict-coefficient-exchange-arrows` defines B, D, H, H', v, c, gamma and
the canonical evaluation comparisons in
`Sheaf.Paper.StrictCoefficientExchangeArrows`. It uses the preceding normalized
presentation and the existing strict direct-image/limit interface; the main
declaration is `gamma`. No mate equality is assumed.

`def-sbc-quotient-exchange-scalar-comparisons` defines the quotient specialization
and its scalar comparison equation in
`Sheaf.Paper.QuotientExchangeScalarComparisons`, with main declaration
`QuotientEquation`. It retains the same input identification on both sides and
normalizes the scalar comparisons by counit and square equations.

For all four notions, the additional LeanSearch query was “canonical strict
augmented coefficient reduction on derived categories of inverse sequences and
quotient scalar restriction comparisons”: eight general derived-category or
derivation hits, no exact match. Loogle on the expected derived-functor/mate/scalar
names found no combined interface; the earlier qualified mate/adjunction search
found the generic Mathlib operations used. Mathlib grep for the presentation and
comparison names found none. `blueprint_refs.py search` found no strict augmented
reduction or quotient exchange node. The project/DAG search found only unrelated
filtered quotient comparisons and special finite coefficient-change results.
The common-quotient pullback comparison assumes flat changes and specified ideal
sheaves; the coefficient scalar adjunction treats quotient transition maps; the
quotient-tower evaluation complex treats constant rings. None gives these
normalized general ringed-square presentations. The raw search records are in
each new node's `mathlib_searches`.

`def-sbc-quotient-coefficient-presentation` defines the quotient ring, local
surjectivity, derived tensor model, exact scalar restriction, and degree-zero unit
identification, independently of a square. Its module is
`Sheaf.Paper.QuotientCoefficientPresentation`, main declaration `QuotientAt`.
The actual functor `forgetQuotient` uses Mathlib's exact-functor localization with
the supplied canonical module-category and exactness instances made explicit.
The same quotient-scalar searches above apply: the existing constant-ring quotient
tower and quotient-transition adjunction interfaces do not give this general
ringed-site coefficient presentation. The source is the quotient specialization
of Stacks 0E48 and the strict augmented refinement.

The theorem's clause names expose the same equations without repeatedly expanding
their types in the final signature: `HasPerfectLevels` is the pointwise perfectness
hypothesis; `ProjectionIsomorphisms` gives both invertibility conclusions;
`IsTowerMate` is equality with the actual strict tower mate; `IsEvaluatedMate`
is the evaluated tensor mate equation; `HasCoaugmentationEquation` is the displayed
kappa/gamma equation; and `IsNaturalGamma` is naturality for every input morphism.
`QuotientEquationAt` expresses the quotient comparison using typed input and
output objects; `QuotientEquation` substitutes the canonical evaluated input,
conjugate, and source/target isomorphisms at each level. Every map in this
specialization is the original canonical construction. These are definition
helpers of the same node, with no additional hypothesis or conclusion.

`FullEquation` names the conjunction of exactly these conclusions. Naming the
conjunction avoids the excessive elaboration of a `sorry` proof against the
expanded dependent conjunction; its definition contains all the same equations.



`def-sbc-strict-projection-tower-data` records the normalized strict tower limit
and direct-image presentation and its tensor/unit helpers, already defined in
`Sheaf.Paper.RingedStrictTowerProjectionMorphism`. The source is Stacks 0A07 and
0943, with the strict-limit normalization from 0940/0941. LeanSearch for normalized
strict derived-limit/direct-image data found eight ordinary module-limit hits;
Loogle did not know the project-specific names, and Mathlib grep found none.
DAG and project grep found the unchanged existing module recorded under its
theorem, but no definition owner. The blueprint search found only an unrelated
compact-support exchange node. Raw search results are in the new node. Reuse
of the existing declarations introduces neither a copy nor a new Lean module.

## Returned delivery repair

F1 (returned immutable head 9e7a2d8e17ee): added
`def-sbc-strict-projection-tower-data`, an `existing: true` definition owner of
`StrictProjectionLimit`, `StrictProjectionDirectImage`, their abstract records,
`projectionTowers`, `projectionPost`, `projectionTotal`, `projectionRightUnitor`,
`projectionUnit`, `projectionUnitComplex`, the termwise direct image and its
counit normalization. Every declaration is reused from the unchanged module
`Sheaf.Paper.RingedStrictTowerProjectionMorphism`. The item and both strict
presentation/arrow definition nodes cite this owner instead of the projection
theorem. The theorem remains in the item's `proof_deps`. This is the exact
dependency-ownership repair requested by the maintainer; it changes no
mathematical statement, hypothesis, conclusion or Lean construction. The new
node's statement lists the localization, K-injective, evaluation, Roos, ordinary
limit-post, derived-composite and counit normalizations of the existing records.

F2: the delivery includes
`dag/nodes/sec-smooth-base-change/def-sbc-quotient-coefficient-presentation.json`,
owning `QuotientAt` and every helper of the delivered
`Sheaf.Paper.QuotientCoefficientPresentation` module. Its downstream consumer
`def-sbc-quotient-exchange-scalar-comparisons` cites this exact node.

Ownership self-check: read the existing definitions and their complete fields
in RingedStrictTowerProjectionMorphism.lean, and the retained quotient node and
module. These are definition data, not choices from the projection theorem.
The original theorem signature and seven-step proof docstring are retained.
The independent mathematical review in the return accepted all of its clauses.

Validation of the retained packet on this repair run: the prescribed initial
`deliver2.py --no-push` passed server compilation of all five unchanged modules
and preflight (35bcbc2555d). The local overlay timed out under load; the wrapper
confirmed successful compilation against current server sources. The repaired
packet is validated again below before delivery. The ownership self-check found
six node records, five modules, one named theorem with `sorry`, no definition
sorries and no lines longer than 100 characters.

Compile-time repair after the repaired packet's first server confirmation timed
out: named the existing strict coefficient square predicate
`coefficientSquareNormalized`, rather than copying its large dependent equation
into every use of `Coefficients`. Its body is verbatim the original equation,
with all four corners and pullback comparisons explicitly bound; unfolding it
recovers the original data type. It belongs to the augmented-presentation node
and is listed in that node's `lean.declarations`. No equation or hypothesis is
added. The item also explicitly imports the projection theorem's module as the
proof dependency required by F1.

After that representation repair, direct `scompile.py` compilation of all five
modules passed with no errors or warnings: library module times were 7.6 s
(quotient presentation), 37.0 s (augmented presentation), 21.1 s (exchange
arrows), 12.4 s (quotient comparisons), and 18.8 s (theorem). All five sandbox
compiles also passed, with the slowest taking 43.7 s under the unchanged 60 s
limit. The named coefficient-square predicate is definitionally the exact old
equation; the theorem signature still matches its retained node verbatim.

## Delivery tool failure

The final repaired packet passed all per-file compiles, including the twelve
existing-declaration probes, but `deliver2.py --no-push` failed server preflight.
The exact decisive diagnostic was:

> (b) statement correction: the item changed in proof_deps without a statement
> correction (proof and proof_deps change only as far as a correction of the
> statement forces it)

It also consequently requested a non-empty `## Statement corrected` section.
There is no mathematical statement correction: F1 explicitly requires replacing
the theorem in the three statement-dependency lists with its definition owner,
with the theorem kept in the item's `proof_deps`. The theorem was absent from
`proof_deps` on the base, so fulfilling that numbered return requires this
addition. The launcher wrapper expressly supports a maintainer-requested
proof-dependency-only repair, but the server's node-fields preflight rejects it
without an actual statement change. Creating a spurious statement correction,
dropping the required theorem dependency, or patching a launcher/server tool
would violate the brief. No push was attempted after the failed dry run.

The repaired sandbox retains both requested fixes, the exact original theorem
statement, the compile-time representation repair, and all clean compile
results, ready for delivery once the gate accepts the authorized proof-only
dependency repair.

## Retained-packet retry verification

The prescribed initial `deliver2.py Q58
lem-sbc-strict-quotient-exchange-unit-equation --no-push` was rerun on the
retained packet. It fetched the current base, staged all six node records and
five modules, and again failed server preflight before compilation with the
same two diagnostics: proof_deps changed without a statement correction, and
the resulting corrected-item classification requires a Statement corrected
report section. Nothing was pushed.

Read-only comparison against the shared current node confirms that its
mathematical statement is identical to this packet's. No new statement_change
record exists in the packet. The only proof_deps addition is
lem-weil-pbc-ringed-strict-tower-projection-morphism, precisely the theorem F1
requires retaining as a proof dependency. The item and both strict definition
nodes cite def-sbc-strict-projection-tower-data for the plain definitions;
def-sbc-quotient-coefficient-presentation.json is included for F2.

The launcher wrapper deliver2.py lines 133–140 expressly permits additive
proof-dependency-only repairs requested by a maintainer. Server-side
tools/node_fields.py correction_fields classifies a proof_deps difference as
a correction, and check_statement_change lines 85–93 rejects it when the
statement is unchanged. This is a reproducible mismatch between the authorized
wrapper behavior and server preflight. A report heading alone cannot repair
the decisive field rejection. No mathematical correction is justified by the
return, so none was invented. No launcher or repository tool was modified and
no dependency required by F1 was dropped. The complete repaired packet and
prior clean scompile.py results remain retained for the next attempt.


## Retained-packet retry, 2026-10-21 08:03 UTC

Ran the prescribed initial `deliver2.py Q58
lem-sbc-strict-quotient-exchange-unit-equation --no-push` against the saved packet.
The wrapper fetched its current base and staged all six node records and five
Lean modules. Server preflight again rejected the required additive proof
dependency, before its per-file compilation stage:

> (b) statement correction: the item changed in proof_deps without a statement
> correction (proof and proof_deps change only as far as a correction of the
> statement forces it)

It also requested a non-empty `## Statement corrected` report section as a
consequence of that classification. No mathematical statement correction is
justified: the retained statement equals the current read-clone statement, and
the only proof-dependency addition is
`lem-weil-pbc-ringed-strict-tower-projection-morphism`, explicitly required by F1.
No proof dependencies were removed. Rechecked that the item and both strict
definition nodes cite `def-sbc-strict-projection-tower-data` instead of the
theorem in `stmt_deps`, and that F2's quotient-presentation node is present.

The launcher wrapper's dependency-only repair support remains inconsistent
with the server preflight. This is an actual reproducible tool refusal, not
a missing mathematical interface. No launcher or repository tool was modified,
no spurious statement correction was introduced, and nothing was pushed.
The complete repaired packet and its prior clean compiles remain retained.

## Retained-packet retry, 2026-10-21 08:05 UTC

The required initial `deliver2.py Q58
lem-sbc-strict-quotient-exchange-unit-equation --no-push` again staged the saved
six node records and five modules against the wrapper's fetched base. Server
preflight rejected the packet before compilation with the unchanged diagnostic:

> (b) statement correction: the item changed in proof_deps without a statement
> correction (proof and proof_deps change only as far as a correction of the
> statement forces it)

It also requested `## Statement corrected` because it classified this dependency
repair as a statement correction. Read-only verification against the current
shared node confirms identical mathematical statements, no removed proof
dependencies, and exactly the F1-required projection theorem added to proof_deps.
F1's definition owner is cited from the item and both strict definition nodes;
none of those three cites the theorem in stmt_deps. F2's quotient-presentation
node record and its module are present. The wrapper's lines 133–140 authorize
additive maintainer-requested proof-dependency repairs, while server
`tools/node_fields.py` still rejects them through `correction_fields` and
`check_statement_change`. No legitimate packet-only repair addresses this tool
conflict. The retained fixes and prior clean compiles are unchanged; no tool
was modified, no artificial statement correction was made, and nothing pushed.


## Retained-packet retry, 2026-10-21 08:07 UTC

Ran the prescribed initial dry run on the retained packet and confirmed its
result with another `deliver2.py Q58
lem-sbc-strict-quotient-exchange-unit-equation --no-push`. The fresh wrapper
completed its six-file compile check (the five delivery modules and the
existing-declaration probe), staged all six node records and five modules, and
reached server preflight. Preflight again rejected the packet with two reasons:

> (b) statement correction: the item changed in proof_deps without a statement
> correction (proof and proof_deps change only as far as a correction of the
> statement forces it)

> (e) the item's statement is corrected but the report has no non-empty section
> '## Statement corrected'

Read-only verification against the current shared node confirms the statement
is identical, no proof dependency is removed, and the sole proof dependency
added is `lem-weil-pbc-ringed-strict-tower-projection-morphism`, as F1 requires.
The item and both strict definition nodes cite
`def-sbc-strict-projection-tower-data` for the existing plain definitions, and
F2's quotient-presentation node record owns its delivered module and helpers.
Read the full existing strict-limit and direct-image records and the tensor/unit
helpers to confirm the ownership repair. No Lean or node change is necessary
for either numbered point. The wrapper supports additive proof-dependency
repairs, but server preflight still classifies them as statement corrections.
A fabricated mathematical correction, omission of F1's required dependency, or
modification of the tools would not be an authorized repair. No tools were
modified and no push was attempted; the complete repaired packet is retained.


## Retained-packet retry, 2026-10-21 08:09 UTC

Ran the prescribed initial `deliver2.py Q58
lem-sbc-strict-quotient-exchange-unit-equation --no-push` on the retained packet.
The wrapper completed its six-file server check, staged all six node records
and five modules, then failed server preflight with the same two diagnostics:

> (b) statement correction: the item changed in proof_deps without a statement
> correction (proof and proof_deps change only as far as a correction of the
> statement forces it)

> (e) the item's statement is corrected but the report has no non-empty section
> '## Statement corrected'

Read-only comparison with the current shared node confirms the mathematical
statement and proof are unchanged. The sole proof_deps addition is
`lem-weil-pbc-ringed-strict-tower-projection-morphism`, required by return F1.
The item and both strict definition nodes cite the new existing-definition owner
`def-sbc-strict-projection-tower-data`; neither strict definition node nor the
item cites the theorem in stmt_deps. F2's quotient-presentation node record and
module are included. Both requested repairs remain saved.

Read-only inspection confirms deliver2.py expressly permits additive proof
repairs requested by a maintainer, whereas server tools/node_fields.py rejects
proof_deps changes when the statement is unchanged. No legitimate packet-only
repair resolves this conflict: removing the dependency violates F1, and a
fabricated statement correction misrepresents the unchanged statement. No tool
was modified and nothing was pushed.

## Retained-packet retry, 2026-10-21 08:11 UTC

The prescribed initial deliver2.py --no-push checked all six Lean files
(the five modules and existing-declaration probe), staged the full repaired
packet against fetched base 6f40cd176, and failed server preflight:

> (b) statement correction: the item changed in proof_deps without a statement
> correction (proof and proof_deps change only as far as a correction of the
> statement forces it)

It also requested a Statement corrected report section. Read-only comparison
with the shared node confirms unchanged statement and proof and exactly one
added proof dependency: lem-weil-pbc-ringed-strict-tower-projection-morphism,
required by F1. F1's existing-definition owner is cited by the item and both
strict definition nodes; F2's quotient-presentation node and module are present.
The wrapper explicitly permits this additive maintainer-requested proof repair,
but server preflight rejects it. This is a tool refusal; no authorized
packet-only repair resolves it without violating F1 or inventing a statement
correction. No tool was changed and nothing was pushed. Both repairs remain
saved in the sandbox.


## Retained-packet retry, 2026-10-21 08:14 UTC

Ran the prescribed initial `deliver2.py Q58
lem-sbc-strict-quotient-exchange-unit-equation --no-push` on the saved packet.
The wrapper checked six Lean files, fetched the base, staged all six node
records and five modules, and failed server preflight with:

> (b) statement correction: the item changed in proof_deps without a statement
> correction (proof and proof_deps change only as far as a correction of the
> statement forces it)

It also requested a non-empty `## Statement corrected` report section.
Read-only comparison against the shared node confirms the mathematical statement,
proof and statement_change are unchanged; the only proof_deps addition is
`lem-weil-pbc-ringed-strict-tower-projection-morphism`, explicitly required by F1,
and no proof dependency is removed. The item and both strict definition nodes
cite `def-sbc-strict-projection-tower-data` instead of the theorem. F2's
quotient-presentation node record and module remain included.

Read-only inspection of deliver2.py confirms its explicit support for additive
maintainer-requested proof-dependency repairs. tools/node_fields.py still
classifies every proof_deps change as a statement correction and rejects it
when the statement is unchanged. The fresh server diagnostic confirms the same
conflict. Neither inventing a statement correction nor removing F1's required
proof dependency is an authorized packet repair. No tools or shared files were
changed, and nothing was pushed. Both requested fixes remain saved.


## Retained-packet retry, 2026-10-21 08:18 UTC

Ran the prescribed initial deliver2.py --no-push on the retained packet. The
wrapper checked all six Lean files, staged all six node records and five
modules, and server preflight again rejected the F1-required proof_deps
addition: "the item changed in proof_deps without a statement correction".
It also required a Statement corrected report section as a consequence.

Read-only comparison against the current shared node confirms unchanged
statement and proof, no removed proof dependency, and only the required
lem-weil-pbc-ringed-strict-tower-projection-morphism added to proof_deps.
The item and both strict definition nodes cite the existing-definition owner
def-sbc-strict-projection-tower-data instead of the theorem. F2's quotient
presentation node record and module remain present.

Read-only inspection reconfirms that deliver2.py explicitly accepts additive
maintainer-requested proof dependency repairs, whereas tools/node_fields.py
rejects that same change without a mathematical statement correction. There
is no authorized packet-only repair: omitting the dependency violates F1,
and no mathematical correction justifies changing the accepted statement.
No tools or shared files were modified and nothing was pushed. Both requested
repairs remain saved in the sandbox.


## Retained-packet retry, 2026-10-21 08:27 UTC

The prescribed initial deliver2.py --no-push checked six Lean files and staged
all six node records and five modules. Server preflight again rejected the
F1-required additive proof dependency: "the item changed in proof_deps without
a statement correction". It also requested a Statement corrected report
section because of that classification. Nothing was pushed.

Read-only comparison with the shared current node confirms identical statement
and proof, no removed proof dependency, and exactly the projection theorem
added to proof_deps. The item and both strict definition nodes cite
def-sbc-strict-projection-tower-data instead of that theorem in stmt_deps.
The existing-definition owner records all twelve required declarations. F2's
quotient-presentation node record includes QuotientAt and its helpers and is
staged alongside its module. Both requested repairs remain present.

Read-only inspection of deliver2.py lines 133–140 confirms authorization for
additive maintainer-requested proof-dependency repairs. tools/node_fields.py
correction_fields and check_statement_change still classify and reject the
same change without a mathematical statement correction. No valid packet-only
repair resolves this conflict; no statement correction was invented, no
required dependency dropped, and no tool or shared file modified.


## Retained-packet retry, 2026-10-21 08:33 UTC

The prescribed initial `deliver2.py Q58 lem-sbc-strict-quotient-exchange-unit-equation
--no-push` checked six Lean files, staged all six node records and five
modules, and failed server preflight with the decisive diagnostic:

> (b) statement correction: the item changed in proof_deps without a statement
> correction (proof and proof_deps change only as far as a correction of the
> statement forces it)

It also requested a Statement corrected report section. Rechecked the saved
packet against the shared read-clone node: statement and proof are unchanged;
no proof dependency was removed, and the sole addition is
`lem-weil-pbc-ringed-strict-tower-projection-morphism`, explicitly required by F1.
The item and both strict definition nodes cite `def-sbc-strict-projection-tower-data`
instead of the theorem in stmt_deps; that node reuses the existing definitions.
F2's quotient-presentation node record, its module and its downstream citation
are present. Both numbered repairs remain saved.

Read-only inspection reconfirmed the tool mismatch: deliver2.py explicitly
permits additive maintainer-requested proof dependency repairs, whereas
tools/node_fields.py classifies the same addition as a statement correction
and rejects it when the mathematical statement is unchanged. No authorized
packet-only repair addresses this refusal. No artificial statement correction
was introduced, no required dependency omitted, no tool modified and no push
attempted.


## Retained-packet retry, 2026-10-21 08:36 UTC

The prescribed initial deliver2.py --no-push checked six Lean files and
staged the five modules and six node records against base 4cc3646fc. Server
preflight again rejected the packet: "the item changed in proof_deps without
a statement correction"; it also requested a Statement corrected report
section. No push occurred.

Self-check confirms both numbered repairs are retained: the item and both
strict definition nodes cite def-sbc-strict-projection-tower-data rather than
the projection theorem, and the quotient-presentation node owns QuotientAt
and its delivered module. Statement and proof equal the current read clone;
the only added proof dependency is the theorem F1 explicitly requires.
Read-only tool inspection confirms deliver2.py permits this additive repair
but tools/node_fields.py rejects it without a mathematical statement change.
No truthful packet-only correction addresses this tool refusal. No tool or
shared file was modified, no required dependency omitted, and no artificial
statement correction introduced. Both requested fixes remain saved.


## Final retained-packet self-check, 2026-10-21 08:40 UTC

The prescribed initial `deliver2.py --no-push` now passes preflight and all
per-file compiles (dry-run commit 04bab6598dd). This successful result
supersedes the tool-blocker status in the earlier retry log above.

F1: the item and both strict definition nodes cite
`def-sbc-strict-projection-tower-data` instead of the projection theorem.
Its existing:true record owns the twelve existing tower, limit, direct-image,
tensor and unit declarations in the unchanged published module. The theorem
remains in the item's proof_deps. The current main branch already includes
that proof dependency and cites it in proof step 5; the sandbox proof field
has been refreshed verbatim from current main, without changing its statement.

F2: `def-sbc-quotient-coefficient-presentation.json` is included and owns
`QuotientAt`, its data and helpers, and the delivered
`Sheaf.Paper.QuotientCoefficientPresentation` module. The scalar-comparison
node cites it. The theorem signature and all five Lean modules are retained
unchanged from the repaired packet. No new mathematical statement correction
is needed.

## Second reading by Q58

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

The module `Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange`, with its comparison-data
module `Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons`, states the three
clauses of `det-sp-tower-exceptional-bc`. Its only postponed proof is
`tower_exceptional_base_change`; all helper definitions have actual data. The
accepted stage-1 split, statement and proof are unchanged. The obsolete Q107 route
note concerns stage 1 and a missing retained sandbox; the current item is the
reviewed 2026-10-22 split, and this delivery follows the current stage-2 brief.

### Hypotheses and objects

* The common context binds `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`,
  `[Algebra (Padic l) E]` and `[FiniteDimensional (Padic l) E]`. The theorem binds
  `k : FiniteFieldDatum` and `_hne : l ≠ k.p`. Thus the base field is the fixed
  algebraic closure of a finite field, and the coefficient extension is finite.
  `SpTowerShriek.R l E n` is the existing positive-level coefficient ring: Lean
  index `n` denotes exponent `n+1`, so exponent zero is never introduced.
* `X Y X' Y' : Over (Spec (CommRingCat.of k.k))`, together with separated,
  locally finite-type and quasi-compact structural maps, render separated
  finite-type k-schemes. The explicit assumptions on X' are the consequences of
  the Cartesian square; requiring these standard structures does not remove
  any Cartesian square in the statement.
* `f v u' f'` are morphisms in that Over category. `sq : IsPullback ...` is the
  Cartesian square, including its commutativity and universal property.
  `d : ℕ` and `[SmoothOfRelativeDimension d f.left]` render smooth pure relative
  dimension d. Separatedness follows from the separated k-schemes.
  `c : Compactification f.left` is the fixed compactification; every occurrence
  for f' is `c.ofIsPullback sq`. No smoothness, flatness, or properness of v is
  requested.
* `b : SpTowerShriek.Base`, `o : SpTowerShriek.Operations`, and
  `q : SpTowerCalculus.Coordinates` are the dependency's section-normalized
  realizations of the prescribed coefficient categories and operations.
  `x : SpTowerShriek.OpenExchange` fixes the extension-by-zero exchange by its
  defining ordinary mate. These are presentations of the operations in the
  statement, not arbitrary functors or arbitrary natural transformations.
* `SpTowerCalculus.C` is the existing ordinary derived strict-tower category
  restricted by uniformly bounded constructible finite Tor amplitude. No
  normalized-input restriction is imposed on clauses (1) and (2).

### Clauses

1. The output `a : SpTowerMate.Data ... sq c` supplies the existing ctf
   restrictions of the operations and the two tower adjunctions.
   `hb : IsIso (SpTowerMate.beta ... a x)` asserts invertibility of the actual
   compactification exchange. This beta is extension-by-zero exchange followed
   by proper base change, transported through the published equivalences.
   It is not an arbitrary isomorphism between the two functors.
2. `SpTowerMate.mate ... a x hb` is defined in the dependency as the adjoint
   transpose of inverse beta followed by the pulled-back counit. `IsIso` of this
   natural transformation gives the exceptional base-change natural
   isomorphism. `SpTowerMate.Laws ...` records the explicit unit/counit transpose
   formula, finite evaluations, source and target coefficient comparisons,
   mixed-base-change identity and the reduction square including the input
   transition. In particular its `evaluation` is the finite counit transpose,
   not a chosen finite isomorphism. The output `hfinite` is the invertibility
   witness needed to define those finite inverse-exchange mates, not a new
   assumption. The final universally quantified normalization assertion says
   that both `U(a.right K)` and `a.right'(V K)` are normalized when K is.
3. The integral branch is gated by `Module.finrank (Padic l) E = 1`. This is the
   invariant presentation of E=Ql: the base algebra is then an isomorphism,
   including any copy of Ql in the coefficient universe. Four residue-field
   invertibility instances are universally quantified inside this conclusion;
   they are derivable from the finite-field datum and ell != p. They do not
   become additional hypotheses on the geometric square.

   The output `IntegralData` supplies the completed integral operations and
   their specified identifications. `IntegralCoordinates` uses the published
   completed reduction, normalized reduction/total-limit adjunction, its unit,
   fully faithful constructible restriction, and the cofinal comparison with
   the uniformizer towers. `IntegralData` supplies quasi-compactness of f and
   f' as output fields, hence does not assume it independently.

   `SupportModel` is precisely the dependency's `Reconstruction` package, with
   f=j≫p transported through `c.comm`. In particular the support reduction
   comparison is fixed by the ordinary quotient generators, derived
   composition units, and the reconstruction counit. Its `leftComparison` is
   required by `support_normalized`, using HEq solely for the proof-dependent
   restriction certificates. Completed pullback is the published
   `constructibleIntegralPullback`, never ordinary discrete-ring pullback.
   `PullModel` fixes its cofinal comparison as the ordinary inverse-image mate
   of the identity on direct-image sections. `pullReduction` composes that
   derived mate with the published K-flat/Roos-normalized integral pullback
   model and the actual reconstruction counit. `pull_normalized` pins both
   pullback comparisons to this entire-tower morphism.

   The integral right adjoints in `IntegralData` have adjunctions with the
   actual completed compact-support functors. `rightLimit`, `right_reduction`
   and `counit` identify them with H counit-preservingly. This specifies the
   conventional exceptional adjoint up to its unique adjunction-preserving
   isomorphism, rather than requiring equality of choices of right adjoints.
   `source` and `target` are the resulting whole-tower identifications a_K,b_K.

   `exchangeReduction` is the actual conjugation of tower beta by these fixed
   support and completed-pullback comparisons. `IntegralConclusion` asserts
   existence of integral beta, equality of its reduction to this map, and its
   uniqueness. `reconstructed` is the inverse on Hom sets of fully faithful
   reduction applied to a_K, the actual tower mate, and b_K inverse. No lift
   from a family of finite evaluations is chosen. `IsLimitRealization` is the
   exact total-limit formula in adjunction form: T followed by the target unit
   equals the adjoint of the conjugated tower map. Since the target unit is
   invertible, this is equivalent to T=unit;Rlim(map);inverse(unit).
   Finally `integralTranspose` is the f' integral adjunction applied to inverse
   beta followed by the pulled-back counit, and its HEq with `reconstructed`
   gives exactly the final transpose identification. HEq here has the same
   endpoints and does not assert a weaker relation. `IsIso reconstructed`
   asserts the required isomorphism in the integral constructible category.

### Dependency declarations

The dependency source signatures and docstrings were read in the read-only
project. The modules/declarations used are:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the existing coefficient rings.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `ProEtale.CondensedRing.compactificationOverField` and the Over setting.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `SmoothOfRelativeDimension`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: its stability and dimension-zero API.
* `WeilConjectures.Compactification.BaseChange`: `Compactification.ofIsPullback`.
* `Sheaf.Paper.SmoothPurityCoefficientTowers`: `spCoefficientTowers` and ell rings;
  `Sheaf.Paper.SmoothPurityNormalizedTowers`: `spConstructibleTorTowerCategory`,
  `IsSpNormalizedTower`, and the existing full subcategories.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `Scheme.proEtaleConstantRingDerivedPullback`;
  `Sheaf.AlgebraicGeometry.ProEtaleConstantExact`:
  `ProEtale.finiteCoefficientModulePullback_exact`. The actual levelwise pullback
  is carried by `SpTowerShriek.Geometry` and its ordinary/derived adjunction.
* `Sheaf.Paper.SmoothPurityTowerShriekLevels`: `SpTowerShriek.Base`, `Operations`,
  `OpenExchange`, `R`, `pull`; `Sheaf.Paper.SmoothPurityTowerGluing`:
  `SpTowerGluing.support`, `Levels`; `SpTowerCalculus.Coordinates`, `C`, `F`,
  `realization`, `inclusion` from its published coefficient-calculus imports.
* `Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction`: `SpTowerMate.Data`,
  `U`, `V`, `beta`, `mate`, `finiteExchange`, `Laws`, and the theorem
  `tower_mate_evaluation_reduction` (proof prerequisite).
* `Sheaf.Paper.SmoothExceptionalBaseChangeStatement`:
  `ProEtale.smoothExceptionalBaseChangeStatement` (finite invertibility);
  `Sheaf.SecSmoothPurity.MixedBaseChange`: `ProEtale.mixedBaseChange` (in Laws);
  `Sheaf.Paper.SmoothPurityTowerGamma`: `SpTowerGamma.tower_gamma` (proof).
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `WeilConjectures.integralConstantToCompletionOfUniverses`;
  `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`, its category;
  `Sheaf.Paper.IntegralDerivedOperationsOnSlices`: integral completed operations;
  `Sheaf.Paper.DerivedPullbackTensorHom`: `constructibleIntegralPullback` and
  `pullbackTensorIntegralPullbackModel`.
* `Sheaf.Paper.SmoothPurityNormalizedEquivalence`: `SpNormalizedEquivalence`;
  `Sheaf.Paper.IntegralAdjunctionBijection`: `SpIntegralAdjunction.Realization`,
  `integral_adjunction_bijection`; its public
  `Sheaf.Paper.IntegralReconstructionComparisonData`: `Reconstruction`,
  `support`, `reduce`, `limit`. `SpTwistedPullback.CofinalModel`,
  `CofinalReduction`, and `IntegralStrictReductionModel` are reused from its
  twisted-pullback imports, including their ordinary normalizations.
* `Sheaf.Paper.IntegralDirectImageTower`:
  `IntegralDirectImageTower.integral_direct_image_tower`; the support model uses
  the explicit canonical scalar/limit comparison interface reexported by the
  reconstruction package, rather than a fresh unspecified isomorphism.

The recorded module for `prop-coef-integral-exceptional-adjoint` is stale:
`IntegralCoefficients.lean` explicitly points to
`WeilConjectures.SixFunctors.Etale.Derived.IntegralExceptionalAdjoint` for
`AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint`;
`boundedConstructibleIntegral_rightDerivedUpperShriek` is in `LocalizationIntegral`.
Their full signatures/docstrings were read, including the completed-pullback and
Tor-bound clauses. The current statement specifies the adjoint by its adjunction
and the counit-preserving H comparison, as the DAG itself prescribes. It does
not create a second definition of an integral exceptional functor.

The two proof-only prerequisite nodes
`lem-sp-ctf-tower-pullback-reconstruction` and
`lem-sp-integral-exceptional-mate-transport` have no recorded Lean declaration in
the current read source. They are named in the proof docstring; the item itself
supplies its comparison data as conclusion. They are not imported under invented
module names or used to choose unspecified data.

### Edge cases

Checked against the node and the actual construction: d=0 (etale case), empty
schemes, zero input, identity square, n=m reduction, the first positive exponent
n+1=1, ramified E (cofinal ell-power/uniformizer-power comparisons retained), and
arbitrary nonflat v. The quotient reduction need not be flat; all coefficient
changes are derived and the reduction equation includes the input transition.
Unnormalized towers remain in the theorem's domain. No finite-evaluation-only
uniqueness is used for the integral map. All universes and variables are bound
explicitly; the integral coefficient category is the completed pro-etale one.

### Searches

`msearch.py NH det-sp-tower-exceptional-bc leanfinder` with query
“Exceptional inverse image base change for smooth morphisms on strict coefficient
towers and integral completed sheaves” returned eight geometric smooth base-change
hits (including `isSmooth_isStableUnderBaseChange` and
`isSmoothOfRelativeDimension_isStableUnderBaseChange`); none states this theorem.
Loogle `CategoryTheory.Adjunction, CategoryTheory.NatTrans` returned zero hits.
Mathlib grep `exceptional.*[Bb]ase[Cc]hange|tower_mate` in AlgebraicGeometry returned
zero hits. Project `rg` for exceptional base change and this node id found the
finite statement and the tower-mate evaluation dependency, not the present
invertibility and integral transpose conclusion. `dag/lean_names_upstream.json`
was searched for the source names. Existing frameworks and canonical comparison
interfaces were reused, rather than new independent notions. Search receipts are
retained in the sandbox's `searches.jsonl`.

No statement correction or additional postponed theorem is introduced.
The integral-adjoint dependency has a lean-only existing-declaration record repair.
No unresolved mathematical dispute was found. Compilation uses only scompile.py;
no live source, Git state or global build was modified directly.

## Delivery review

The dispatcher brief assigns a single worker and explicitly forbids starting
other agents; independent maintainer review reads this delivery. The mapping
above is this worker's source-to-signature audit, not a fabricated second reader.
The dry run and delivery wrapper provide the required independent mechanical
checks.

## Dependency modules

`prop-coef-integral-exceptional-adjoint`: no new module is written. Under §1(B),
its stale IntegralCoefficients record is repaired to the published existing theorem
`AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint` in
`WeilConjectures.SixFunctors.Etale.Derived.IntegralExceptionalAdjoint`. The original
module itself documents this move. Its full four-clause signature and docstring
were read, and the server's current source was checked with scompile --source.
The other old recorded name lives in LocalizationIntegral; the repaired record
uses the one theorem that already bundles the exceptional-adjoint conclusion.
The wrapper separately compiles an existing-declaration #check probe.

## New nodes

`def-sp-tower-mate-data` binds the 21 landed SpTowerMate helper definitions with
`existing: true`. Its detailed ownership, source and search audit appears in the
repair section below. It introduces no new Lean declaration or theorem.

`def-sp-exceptional-bc-integral-comparisons` defines the simultaneous integral
comparison datum used in clause (3), with its own module
`Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons`. It reuses the existing
CofinalReduction and Reconstruction records and pins the square's comparisons
to their canonical section/generator and unit/counit normalizations. It asserts
no exceptional-base-change existence or invertibility theorem. The source is
paragraph (3) of the current blueprint proof. The combined module elaborated
without errors but took 70 s locally and 90 s in server confirmation, above the
60 s per-file limit; the comparison definitions were therefore separated into
this definition node after first improving transparency and naming costly terms.
LeanSearch and LeanFinder queries “Canonical integral compact support and
completed pullback tower comparison data for a Cartesian square” each returned
eight unrelated geometric pullback hits. Mathlib grep IntegralData|PullModel|
CofinalReduction returned zero. Project grep found the reused CofinalReduction
and unrelated scalar/tensor records; no matching square-specific datum exists.
blueprint_refs search returned zero matching blueprint nodes. The new node
carries the search receipts and is added to the item's statement dependencies.
The complete hypothesis/clause mapping above also describes each field of this
new definition. No data is sorry and no new theorem is hidden in the definition.

### Validation

The split modules passed the server's per-file 60-second checks: comparison data
18.6 s and the theorem module 55.0 s. The comparison snapshot emitted one
long-line docstring warning, fixed before the delivery dry run. The delivery
wrapper recompiles both actual final modules and probes the rebound existing
integral-adjoint declaration. No limits or transparency safeguards were disabled.

The first dry run exposed timing variability in the theorem module (75 s versus
55 s in the preceding server check). The source, target and transported exchange
helpers were given explicit compact endpoint types, and IntegralConclusion was
marked irreducible to prevent its large formula from unfolding in the theorem.
The comparison-data module's long docstring line was fixed. These changes preserve
all maps and equations.

The final explicit-endpoint revision compiles without warnings on the server:
ExceptionalBaseChangeIntegralComparisons 19.7 s; SmoothPurityTowerExceptionalBaseChange
52.7 s, each under the unchanged 60 s limit.

`def-sp-exceptional-bc-integral-maps` separates the actual reconstruction maps
from the theorem after repeated wall-clock variability (53 to 65 seconds) in
the theorem file. Its module is `Sheaf.Paper.ExceptionalBaseChangeIntegralMaps`.
It defines a_K, b_K, the transported compact-support exchange, inverse-on-Hom
exceptional reconstruction and integral transpose, exactly as described in the
clause mapping above. The theorem module owns the total-limit identity and
integral conclusion predicates.
It asserts no theorem. It reuses fully faithful reduction and the actual tower
mate. The same LeanSearch/LeanFinder and Mathlib/project searches for canonical
integral comparison data found no existing construction; existing CofinalReduction
and Reconstruction alone do not define these square-specific composites.
Its source is paragraph (3) of the blueprint proof. The item's statement gains
this definition dependency; its mathematical statement is unchanged.

A timing check isolated 63 seconds in the maps module; the final two assertion
predicates were moved to the theorem module to distribute elaboration without
changing any signature or construction. The final dry run compiles all three
files and the existing-declaration probe.

## Repair of returned head 4e17d3107f23

The independent return H2/H12 is repaired without changing any Lean source,
mathematical statement, hypothesis, conclusion, or canonical map. The retained
sandbox is the returned packet; comparison with the read-only current main found
that its three Lean modules and two integral definition nodes have not landed.
The item still differs from main only in its Lean record and added statement
dependencies. The delivery wrapper constructs the repaired commit on current main.

1. Added `def-sp-tower-mate-data` with `existing: true`, binding
   `SpTowerMate.Data`, `U`, `V`, `beta`, `mate`, `finiteExchange`, `Laws` and all
   other helper definitions in the landed Q15 module
   `Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction`. Its 21 declarations
   exclude the theorem. The source signatures and full docstrings were read.
   Data records restriction certificates, adjunctions and finite comparisons;
   beta is the actual restricted exchange and mate its inverse/counit transpose.
   Laws only defines the evaluation and reduction predicate; the new node does
   not assert any equation or invertibility. Its statement dependencies are
   definition nodes, including the existing calculus and gluing interfaces.
2. Added this definition node to the statement dependencies of the item and
   `def-sp-exceptional-bc-integral-comparisons`, accounting for their uses of the
   Q15 definitions, including Data/U/V and the tower beta/mate/Laws predicates.
3. Replaced `lem-sp-tower-mate-evaluation-reduction` by the definition node in
   `def-sp-exceptional-bc-integral-maps`' statement and statement dependencies.
   The theorem remains in the item's original proof dependencies; it is no
   longer routed through the new integral-maps definition.

The existing integral-adjoint record repair is retained from the returned packet;
the review correctly notes that the Lean statement does not use that theorem.
The independent reviewer explicitly accepted the mathematical clause mapping,
canonical-map normalizations, edge cases and docstrings; those remain unchanged.

### New definition binding and searches

`def-sp-tower-mate-data` gives a definition-node owner to exactly the landed
SpTowerMate constructions, with no new module, copy, proof or data choice. Source:
current blueprint tower-base-change proof paragraphs (1)--(2). LeanSearch and
LeanFinder query “Strict coefficient tower compact support base change data and
exceptional counit mate” each returned eight generic adjunction/sheaf/scalar
results, including mateEquiv_counit and ordinary sheaf pushforward counits.
Mathlib grep `SpTowerMate|finiteExchange|tower.*mate` in AlgebraicGeometry returned
zero hits. Project/DAG grep found the exact definitions only in the Q15 module
and its theorem-node record, with no definition-node owner. blueprint_refs search
“tower mate” returned zero blueprint nodes. These receipts are recorded in the
new node. The full natural-language definition accounts for every Data field,
all 21 helper declarations, and every Laws clause; it asserts no theorem.

All three delivered Lean modules will be recompiled by the required server
wrapper, together with #check probes for the existing declaration bindings.
The dry run and final delivery are repeated for this repaired packet.


### Repair validation and upstream import-order repair

The three unchanged delivery modules compiled cleanly against the server:
IntegralComparisons 14.4 s, IntegralMaps 33.8 s, and the item 26.9 s.
The subsequent dry run rebuilt newer upstream dependencies and exposed an existing
import-order fault: TensorAdjunctionReductionSquares uses completionMap_isIso,
which was declared only in GeneratorReductionStatement, its own importer.
The live server sources were read with scompile --source. The existing lemma,
including its complete proof and unchanged signature, is moved into
Sheaf.SixFunctors.ShortWordCompletionTransport. Both original modules import it;
GeneratorReductionStatement no longer redeclares it. This is an import-order
refactor of existing proved declarations, with no new sorry, axiom, mathematical
statement, data or DAG node. These three consumer/prerequisite modules are included
and compiled in the delivery to repair the failure revealed by the required dry run.


The six-module server compile passed cleanly, including the factored proof (2.9 s),
TensorAdjunctionReductionSquares (26.4 s), GeneratorReductionStatement (17.5 s)
and the original three modules (14.4/33.8/26.9 s). The second dry run reported a
private-helper name collision between the two existing consumer modules;
GeneratorReductionStatement's helper and its three internal uses were renamed
from inverseOrZero_eq_inv to generator_inverseOrZero_eq_inv. Its type and proof
are unchanged. The checks are repeated after this name-only repair.


## Repair of returned head 6d490a1f28db

The sole return concerns the duplicate completionMap_isIso declaration introduced
by the previous consumer refactor. This repair removes
Sheaf.SixFunctors.ShortWordCompletionTransport entirely from the packet. It also
removes the packet's replacements for GeneratorReductionStatement and
TensorAdjunctionReductionSquares, including the previous private-helper rename.
No declaration is renamed or reproved to avoid the collision.

Comparison with the retained returned packet and current main, confirmed by
scompile --source for both upstream modules, shows that main now has the correct
acyclic import order: TensorAdjunctionReductionSquares publicly imports
GeneratorReductionStatement, which declares the existing
WeilConjectures.GeneratorReduction.completionMap_isIso. The latter no longer
imports TensorAdjunctionReductionSquares. The exact signature, docstring and
proof of the existing declaration were read. The original item modules already
reach these published modules through their integral reconstruction imports;
there is no need for a new direct import or copied theorem.

This section supersedes the preceding consumer import-order refactor and helper
rename: neither is in this repaired delivery. Only the original three item and
integral-definition modules remain. Their Lean text and all mathematical node
statements are unchanged; the accepted definition-node dependency repair is
retained. Compilation, dry-run preflight and delivery are rerun against current
main after removing the duplicate and both obsolete consumer overrides.


The repaired three-module packet compiled cleanly against the current server
library: IntegralComparisons 20.2 s, IntegralMaps 48.2 s, and the item 58.6 s.
All are within the unchanged per-file limit. No consumer override or new
completion-transport declaration was submitted in this compile.

## Second reading by NH

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

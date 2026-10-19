## Worker report

The delivery states `WeilConjectures.eCoefficientSmoothBaseChange` in
`Sheaf.Paper.ECoefficientSmoothBaseChange`. Its statement is the unchanged target
node, including the ambient complete rational category, independence of the specified
lattice presentation, and constructible landing through the specified endpoint
identifications. Nothing is proved at stage 2: the named theorem proofs are `sorry`.
Definitions retain actual categorical data, or select data uniquely fixed by the
specified tensor, section, derived-counit, or completion-unit normalization.

### Hypotheses and conclusions of the item

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Finite E/Qell: `(E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]`.
- A and the chosen uniformizer are precisely
  `Padic.coefficientExtensionIntegers l E` and
  `Padic.coefficientExtensionUniformizer l E`. `pbcOECoefficients` uses the
  principal ideal of that uniformizer, with named proofs of Noetherianity,
  torsion, perfectness, and finiteness of the positive quotients.
- The schemes and arrows are the explicit section variables `X,S,T,Y,f,g,h,e`.
  `sq : ChosenCartesianSquare h e f g` retains both commutativity and the
  chosen projection-compatible identification with the fiber product.
- Smooth f is `[Smooth f]`; g quasi-compact and quasi-separated is
  `[QuasiCompact g] [QuasiSeparated g]`.
- All four schemes are noetherian by four separate `IsNoetherian` instances.
- Finite dimensions are only `_hX` and `_hT`, each a natural upper bound for
  `topologicalKrullDim`. No dimension bound is imposed on S or Y.
- Invertibility of ell on S is `_hl : IsUnit (l : Γ(S, ⊤))`.
- `PbcComplete` is the full subcategory selected by the recorded intrinsic
  Koszul completion unit over `CompletedAdicModules`; it contains no
  constructibility or boundedness condition. `PbcRationalComplete` is its raw
  `ScalarLocalization` at the chosen uniformizer.
- The integral constructible category is exactly the predicate of Q03's
  `IsPbcBoundedConstructibleComplete`, with its actual normalized reductions,
  common local tower models, and compatible retained étale origins.
  `PbcRationalConstructible` is its raw scalar localization, with unchanged
  objects and scalar-localized Hom modules. The canonical away-localized ring
  is identified with E by the recorded uniformizer-localization dependency.
  No Karoubi envelope is taken.
- `sbcPull` restricts Q03's actual `completedPullbackFunctor`; `sbcPush`
  restricts the recorded K-injective derived module direct image along the
  canonical completed coefficient map. Their constant-section linearity is
  stated explicitly. `sbcRationalLeft` and `sbcRationalRight` scalar-localize
  the two integral composites; their pure tensor formulas are the successive
  rational operations in the display.
- `sbcExchangeApp` is the explicit unit/comparison/counit mate. Its adjunction
  is uniquely normalized by the ordinary unit and the actual completion unit;
  its square comparison is uniquely normalized by ordinary tensor composition
  and those completion units. `sbcRationalExchange` is exactly tensor-with-one
  on these components, using `ScalarLocalization.betweenNat`.
- `K : PbcRationalConstructible l E T`, and `L : SbcIntegralLattice ... K`
  retain the integral complex and the specified isomorphism
  `L.presentation : Q L.integral ≅ K`.
- `_hL : SbcFiniteLevelAdmissible ... L` means that every completed-coefficient
  derived quotient reduction is isomorphic to the canonical inverse image of
  a bounded constructible étale complex. It chooses no further witnesses.
- The first conclusion is `IsIso` of the rational exchange at the canonical
  ambient inclusion of K, with output X.
- The second conclusion identifies `sbcTransportedExchange ... L`, explicitly
  `F(iota.inv) ≫ alpha_L ≫ G(iota.hom)`, with the exchange at K.
- The third conclusion quantifies over every other admissible lattice and
  presentation and says the two transported morphisms are equal.
- `SbcSquareConstructiblyAdmissible` requires the finite-level condition and
  one interval `[a,b]` for all n and all four actual outputs: Rg, Lf Rg, Le,
  and Rh Le. Each cohomology sheaf uses the recorded intrinsic constructibility
  predicate, transported by canonical coefficient realizations. Vanishing is
  `IsZero` of `DerivedCategory.homologyFunctor` outside the same interval.
  No common stratification is added to this condition.
- The final implication gives `SbcConstructibleExchangeRepresentation`: two
  integral constructible X endpoints, integral ambient endpoint identifications,
  a rational constructible isomorphism, and the equality identifying its image
  with the ambient exchange after the specified presentation maps. This renders
  “an isomorphism in Dbc(X,E)” without inferring integral constructibility of
  an arbitrary rationally isomorphic representative.

### Dependency declarations used

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`; the recorded
  `BaseChangeInverseImageIso` specializes this same square's inverse-image
  composition. The pro-étale square comparison uses the recorded canonical
  ringed pullback composition, rather than reusing an étale module operation
  on a different site.
- Mathlib `AlgebraicGeometry.Smooth`, `QuasiCompact`, `QuasiSeparated`,
  `IsNoetherian`, `topologicalKrullDim`, `DerivedCategory.homologyFunctor`,
  `ObjectProperty.FullSubcategory`, and `CategoryTheory.IsIso`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the recorded ring,
  chosen uniformizer and finite quotient declarations in the `Padic` namespace.
- `Sheaf.Paper.CompletedAdicCoefficientDatum`: `AdicCoefficientDatum`,
  `completedAdicCommRing`, `CompletedAdicModules`,
  `completedAdicQuotientReduction`, and the universal scalar-change interface.
- `Sheaf.Paper.CompletedAdicIntrinsicCompletion`:
  `IsCompletedAdicDerivedComplete`, the residue-normalized scalar map and the
  intrinsic completion unit.
- `Sheaf.Paper.CompletedPullback`: the exact Q03 delivered completed coefficient
  map, universal K-flat ordinary/tower pullbacks, derived inverse limit,
  `completedPullbackFunctor`, and `completedPullbackComparison`.
- `Sheaf.Paper.WeilPbcBoundedConstructibleTower` and
  `Sheaf.Paper.EtaleOriginReduction`: the exact Q03 delivered normalized
  coefficient reductions, local uniform models and retained étale-origin data.
- `Sheaf.Paper.WeilPbcBoundedConstructibleComplete`:
  `pbcOECoefficients`, `PbcCompatibleEtaleWitness`,
  `IsPbcBoundedConstructibleComplete`, and `pbcBoundedConstructibleComplete`.
- `Sheaf.CategoryTheory.ScalarLocalization`:
  `CategoryTheory.ScalarLocalization`, its canonical tensor composition,
  linear structure and `localization` functor. The new `between` interface
  generalizes its endofunctor-only map to different corners of the square,
  using `LinearMap.baseChange` on Hom modules.
- `Sheaf.AlgebraicGeometry.ProEtaleOperations` and
  `ProEtaleOperationsCanonicalAdjunction`: actual module inverse image,
  tensor extension, derived direct image, and tensor-normalized adjunctions.
- `Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange`: the ordinary
  coefficient-compatible square comparison with its K-flat normalization.
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`: canonical
  restriction/pullback coefficient comparison fixed by identity on sections.
- `Sheaf.Paper.BoundedConstructibleTower`:
  `AlgebraicGeometry.Scheme.pbcDerivedScalarAdjunction`, supplying the
  canonical scalar-extension/restriction adjunction for the finite-reduction
  mate construction. It does not replace Q03's integral category.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`: the canonical
  finite and profinite inverse-image coefficient identifications.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `finiteCoefficientDerivedComparison` and `finiteCoefficientRealization`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`:
  `finiteCoefficientIntrinsicRealization`, allowing use of the recorded
  constant-ring intrinsic constructibility predicate with no universe collapse.
- `Sheaf.Paper.ProEtaleConstructibleSheaf`:
  `AlgebraicGeometry.Scheme.IsConstructibleProEtaleModuleSheaf`.

### Edge cases

The empty scheme is allowed: the finite dimension hypotheses are upper bounds by
natural numbers and include Krull dimension minus infinity. No nonemptiness or
positive dimension is assumed. The input can be zero and all cohomology windows
can contain only zero cohomology. Every reduction index n starts at the positive
exponent n+1; no quotient at exponent zero is substituted. Equal quotient indices
and the quotient cocycle are retained by the Q03 normalized tower interface.
The prime can be 2. The theorem imposes no finite dimension on S or Y and no
properness on g. Constructible landing is conditional, so arbitrary nonconstructible
direct-image outputs are permitted in the first conclusion. The independence clause
allows different integral lattices that become isomorphic only after inverting the
uniformizer; it does not require an integral isomorphism. The two rational categories
use raw localization throughout, so there is no hidden idempotent-pair hypothesis.

### Searches

The required `msearch.py` calls are retained verbatim in sandbox `searches.jsonl`.
LeanFinder query “Smooth base change for rational l-adic complete complexes and
independence of admissible lattice” returned ordinary adic algebra-completion and
BDeRhamPlus results, with no matching theorem. Loogle
`CategoryTheory.ScalarLocalization, CategoryTheory.IsIso` returned no match
(ScalarLocalization is a side-project declaration). Mathlib grep
`smooth.*base.?change|base.?change.*smooth` under AlgebraicGeometry returned
smoothness stability/normalization results, not rational completed exchange.
Repository `rg` searches for the target id and for completed/rational exchange and
admissible-lattice declarations found no exact existing target. The upstream finite
coefficient SmoothBaseChange module does not state rational complete base change.
The upstream rational complete category uses constant coefficients and a Verdier
quotient, so it is not reused as the node's raw scalar localization.

Current server source was checked using `scompile.py --source`; the delivered Q03
branches were also read before implementing missing dependencies. They supply exact
usable completed pullback and bounded constructible definitions, copied without
mathematical changes. Q28's adic-smooth-base-change branch is a stage-1 split, not a
Lean declaration. The final finite-reduction compatibility theorem states the equality
between the specified integral mate after actual quotient reduction and the ordinary
finite mate, through canonical pullback and direct-image reduction comparisons.

No change is made to the target's statement. No new statement dispute is raised.

## Dependency modules

The originally recorded completed-adic intrinsic interface has a different ambient
coefficient presentation. Its lean-only record is repaired to the already landed
Q39 `IsCompletedAdicDerivedComplete`, exactly on `CompletedAdicModules`, as used by
Q03's delivered definitions. No new definition of derived completeness is introduced.

The previously unstated completed pullback, bounded constructible complete category,
and supporting normalized tower/origin interfaces are supplied by the exact delivered
Q03 modules. Their node copies change only `lean`. This retains the original small
site and its equivalent small presentation, without imposing coefficient/site-universe
equalities. All copied modules are included in the per-file compile.

The rational-category, admissible-lattice, and completed-operations dependency nodes
had no usable recorded declaration. They are stated in this delivery, with lean-only
node records and all auxiliary declarations listed. General-purpose abbreviations
are specialized to the exact geometric domain by `pbcRationalCategory` and
`SbcAdmissibleLatticeDatum`; the main theorem imposes all the source hypotheses.

### Dependency node inventory

- `def-weil-pbc-intrinsic-completion`: the old record takes
  `ProEtaleAdicCoefficientDatum` with a different coefficient presentation. The
  existing `IsCompletedAdicDerivedComplete` on `CompletedAdicModules` is the same
  Koszul mapping-fibre/unit predicate for the datum used here; its record is repaired.
- `def-weil-pbc-completed-pullback`: no recorded declaration was available.
  `CompletedPullback` supplies the finite-projection structure map, levelwise K-flat
  tower pullback, derived inverse limit, and its strict-unit-induced comparison.
- `def-weil-pbc-bounded-constructible-tower`: the old record uses coefficients in
  `Type (u+1)` rather than the recorded datum in `Type u`. The delivered module
  transports the actual small site to its equivalent small presentation and retains
  quotient-linear levels, cocycles, common stratification, covers and local models.
- `def-weil-pbc-etale-origin-witness`: the old interface has a different derived
  coefficient presentation. `EtaleOriginReduction` retains the actual bounded-below
  origin and comparison isomorphism after the same canonical site transport.
- `def-weil-pbc-bounded-constructible-complete`: previously unstated.
  `WeilPbcBoundedConstructibleComplete` defines the full subcategory by intrinsic
  completeness, uniform canonical-reduction tower models, and compatible origins.
- `def-weil-pbc-rational-category`: previously unstated. `PbcRationalCategory`
  defines raw scalar localization of that integral category, with its ambient
  complete analogue and canonical inclusion; it adds no Karoubi completion.
- `lem-sbc-completed-operations-linear-natural-exchange`: previously unstated.
  `SbcCompletedOperations` restricts the actual completed operations, gives their
  sectionwise scalar linearity and normalized adjunction/composition interfaces,
  defines the unit-square-counit exchange, and states its finite-reduction equality.
- `sbc-def-admissible-lattices`: previously unstated. `SbcAdmissibleLattices`
  retains an integral lattice and specified rational presentation, defines each
  finite etale-essential-image predicate, and the one common interval condition
  for precisely the four stated ordinary finite-coefficient systems.

## New nodes

None. Every needed notion already has a DAG owner; its missing interface is supplied
under that existing node. All helpers belong to their owning definition or theorem
module and retain source/blueprint documentation.

### Verification and continuation audit

The continuation re-read the item, all statement-dependency records and their
available declarations, plus the supplied dependency modules. It removed the
`letI` binder from the scalar-action characterization by making its `SMul` instance
explicit, added documentation to exported instances, and added available proof-only
imports to the main module. These edits preserve the mathematical statement.

The repeated LeanFinder query for rational ell-adic complete base change returned
8 unrelated algebraic/p-adic results. Loogle `CategoryTheory.IsIso,
AlgebraicGeometry.Smooth` returned only normalization under smooth base change.
Mathlib grep returned 7 normalization and stability-under-base-change hits. Searches
of `WeilConjectures` and `lean/Sheaf` for the target id and rational exchange names
found no existing target declaration. `scompile.py --source
Sheaf.Paper.CompletedPullback` still reports that the module is unpublished, so the
already delivered Q03 construction is included as authorized rather than assumed.
The local blueprint source file is absent; `dag/units/sk-rem-rest.json` and the
item's full retained statement/proof supply its blueprint context and proof route.

Proof-only dependencies without a recorded Lean module are not imported. Available
proof modules are included directly or transitively (including the delivered tower
repair in place of its old record). No import cycle is introduced.

The first server-confirmed compile reached `SbcCompletedOperations` after compiling
all preceding delivery dependencies cleanly. It exposed a zero-morphism instance
search failure at the ordinary-derived comparison, and two implicitly used
naturality binders. The repair exports zero-morphism preservation directly from
the existing additive instance and names those binders `_K` and `_K'`; it adds no
hypothesis and changes no map. Local overlay cache failures are handled only by the
prescribed wrapper's server confirmation; no compiler limits or tools are modified.

The comparison now passes both zero-morphism-preservation instances explicitly to
`NatIso.mapHomologicalComplex`. Its full Mathlib signature was checked through
`scompile.py` in sandbox scratch work. This avoids synthesis of the deeply nested
coefficient functor while leaving the exact normalized comparison unchanged.

### Earlier preflight tool fault

All eight delivered Lean modules and the existing-declaration probe compile cleanly
through the prescribed wrapper's server confirmation (the explicit-instance dry run).
Preflight then incorrectly rejects the supplied prerequisites
`def-weil-pbc-bounded-constructible-complete`,
`def-weil-pbc-bounded-constructible-tower`, and
`def-weil-pbc-etale-origin-witness` as outside the prerequisite closure. The first
two are direct entries of this item's unchanged `proof_deps`; the third is a
prerequisite of the complete-category node. A full traversal of the read-only DAG
contains 10,930 nodes and all three prerequisites. The validator's `_dep_closure`
in `tools/stage2_delivery.py` instead stops at `while todo and len(seen) < 3000`;
its depth-first traversal can stop before visiting even all direct roots.

The stray parsed declaration `AlgebraicGeometry.Scheme.without` was removed from
the completed-pullback record. The named dependency inventory was moved into the
required `## Dependency modules` section. The absent second reading is expected
at the worker's dry run. The false closure rejection requires a tool repair;
no statement or dependency has been changed to work around the validator.

The metadata-only retry was started after those record/report repairs, then stopped
while queued in the shared compiler: the preceding dry run already compiled every
Lean file cleanly and demonstrated the validator's incorrect closure rejection.
Resolving that refusal requires the maintainer to repair the traversal; this worker
has not modified tools, mathematical statements, or dependencies to evade it.

### Retry audit, 2026-10-16

Re-read the stage-2 contract, item statement and proof, dependency records, and the
supplied lattice, rational-category, completed-operations, constructible-category,
and etale-origin interfaces. The item and all eight dependency node copies still
differ from the shared DAG only in `lean`. The canonical maps, raw localization,
finite-level essential-image condition, common four-system window, and endpoint
representation remain unchanged. All definitions retain actual data; postponed
proofs remain named, documented theorems in their owning node modules.

The repeated LeanFinder search for smooth base change of rational l-adic complete
complexes returned eight unrelated adic-completion/BDeRham results. Repository
searches for the target id and rational-exchange declarations returned no existing
matching declaration. `scompile.py --source Sheaf.Paper.CompletedPullback` again
reported that the source is unavailable, so its delivered construction remains
included. A fresh complete traversal of the current DAG contains 10,942 prerequisites
and includes every supplied dependency. The read-only local validator still caps its
traversal at 3,000; its arbitrary root order can omit direct prerequisites. No tools,
statements, or dependency lists have been modified to evade that check.

The prescribed `deliver2.py ... --no-push` retry compiles all eight delivery modules
and the existing-declaration probe before invoking current server preflight. Shared
overlay compilation serializes users of ConstantCompletionEquivalence, so time
spent acquiring that module's lock is separate from each file's 60-second Lean limit.

### Fresh dry-run result

The retry completed every local preliminary, sandbox and library file check cleanly,
including all eight delivery modules and the existing-declaration probe. It reached
current server preflight without any compiler error or non-sorry warning.

Server preflight failed with five reasons. Two are the same incorrect prerequisite
closure refusal: `def-weil-pbc-bounded-constructible-complete` (a direct proof
prerequisite) and `def-weil-pbc-etale-origin-witness` (its prerequisite). Both are in
the fresh full closure audited above. Two module-ownership refusals, for
`WeilPbcBoundedConstructibleComplete.lean` and `EtaleOriginReduction.lean`, are
consequences of those nodes being excluded from the validator's accepted dependency
set; each module is in fact its supplied node's `lean.file`. The fifth reason is
the expected absent `## Earlier second reading (a previous round; superseded)`; the independent second worker must
supply it, and the worker must not invent that reading.

This is a reproduced validator failure after the earlier metadata repairs, not a
Lean failure. Its 3,000-node cutoff cannot validate this 10,942-node prerequisite
closure reliably. The repository tools are read-only and the project contract
forbids working around a tool's wrong refusal. No files were pushed. The completed
sandbox is retained for tool repair and the subsequent independent reading.


### Third continuation audit, 2026-10-16

The fresh worker rechecked the target statement, hypotheses and four conclusions,
its direct dependency records and the supplied completed-operations, lattice,
rational-category, constructible-category and origin interfaces. All nine node
copies differ from the current read-only shared DAG only in `lean`. Each delivered
signature is verbatim in its owning file, all eight files set `autoImplicit false`,
and every line satisfies the 100-character limit. No Lean or node change was needed.

Repeated searches are retained in `searches.jsonl`: LeanFinder for smooth base change
of rational l-adic completed constructible complexes returned eight unrelated adic
completion results; Loogle `CategoryTheory.IsIso, AlgebraicGeometry.Smooth` returned
only the normalization pullback theorem; Mathlib grep for smooth/base-change phrases
returned seven normalization and stability hits. Repository searches of the upstream
and side Lean sources found no declaration of this target or its rational exchange.
The current-source wrapper still reports `Sheaf.Paper.CompletedPullback` unavailable,
so the supplied Q03 dependency construction is retained.

A fresh complete traversal contains 10,953 prerequisites (10,954 nodes including
the item). The complete-category and tower nodes are direct proof prerequisites;
the origin-witness node is a direct prerequisite of the complete-category node.
The precise paths and UTC timestamp are saved in sandbox scratch work. The local
read-only validator still uses `while todo and len(seen) < 3000`; its cutoff can
exclude these authorized dependencies. The required fresh dry run was started to
check the current server tools. No validator, dependency list, statement, or review
section has been changed to bypass a refusal.


### Third dry-run result

The prescribed fresh `deliver2.py Q05 sbc-thm-e-coefficient-smooth-base-change
--no-push` completed successfully. Local checking encountered a missing cached
`SequentialDerivedInverseLimit.olean`; the wrapper's automatic server confirmation
then compiled the delivery cleanly. Current server preflight accepted the supplied
prerequisites and every owning module. It printed:

> OK (dry run): commit 1663a4f3c6 compiles and passes the preflight except for the
> second reading, which the second reader writes; nothing pushed.

Thus the previously reported preflight refusal is not a blocker for this dry run.
The independent second reading remains for the next worker; none has been fabricated.
No Lean statements, node statements, dependencies, or tools were changed during this
continuation. No delivery was pushed.

## Second reading by Q05

This is an independent reading of the current DAG statement, its nine proof steps,
the source passages, and the actual dependency signatures. The older inventories and
dry runs above describe the first worker's sandbox. The final inventory supersedes
them: only `ECoefficientSmoothBaseChange.lean` and `SbcCompletedOperations.lean`, owned
by the item and `lem-sbc-completed-operations-linear-natural-exchange`, respectively,
are delivered. No new definition node is introduced. No natural-language node or unit
statement is changed in this reading.

### Source and dependency audit

I read the master source at
`literature/blueprint/master/blueprint/sec-smooth-base-change/sk-rem-rest/` for
`sbc-thm-e-coefficient-smooth-base-change.md` and `sbc-def-admissible-lattices.md`.
The read-only local literature mirror is `/home/ubuntu/work-bp/sheaf/literature`.
I also read the finite-coefficient/adic context in the alternative smooth-base-change
sketch and Stacks `proetale.tex`, Tags 099M/099N, 09BT and 09C1, and
`algebraization.tex`, Tag 099K. The global conditions in these passages are not a
license to add geometric hypotheses at S or Y: finite dimensionality is required
here at X and T, where the constructible categories are used. The coefficient ring
is the completed ring sheaf, with the abstract coefficient ring acting by constants.
It is not the constant sheaf of the abstract valuation ring.

The original source's final printed S is a type error: both composites end on X.
The DAG already carries the stage-1 correction to X and its explicit raw-localization
convention. I checked that corrected statement against the source before checking
Lean. This reading makes no further statement correction. I reopened both current
citers: `sbc-thm-overline-mathbf-q-ell-coefficient-smooth-base-ch` and
`fix-lem-exchanges`. Both have `holds: true` for this statement: the former now uses
X and explicitly includes the raw exchange into its Karoubi ambient category; the
latter relabels X_sbc=Y' and retains the lattice and conditional constructibility
hypotheses. The old false verdict in the historical split report described the
then-uncorrected Qbar citer, not the current citer. No change to a target unit occurs.

I opened the actual signatures and constructions for the coefficient datum,
coefficient extension/uniformizer, intrinsic completion, bounded constructible
complete objects, bounded towers, raw scalar localization, rational category,
admissible lattices, completed pullback, ordinary ringed operations, finite
coefficient inverse image, and the exchange/adjunction interfaces. During this
reading Q06's rational/lattice/constructible interfaces and Q31's completed-pullback
and intrinsic-presentation interfaces appeared in the shared DAG. I read their
modules in full and reused those landed interfaces. In particular:

* `PbcIsIntrinsicallyComplete`, `PbcIsBoundedConstructibleComplete`,
  `PbcBoundedConstructibleComplete`, `PbcRationalCategory`, `IntegralLattice` and
  both lattice predicates are the published declarations, not private substitutes.
* `PbcIntegralRing` is the published ULift presentation of the valuation ring;
  `pbcUniformizer` and `pbcIntegralDatum` use its recorded fixed uniformizer.
  The Hom actions are the published constant-section actions. No scalar action is
  chosen independently and no extra universe equality is assumed.
* `sbcCompletedPullbackFunctor` merely packages the maps of Q31's actual composite
  `completedReductionTower ⋙ completedTowerPullback ⋙ completedTowerRlim`.
  Its object is Q31's `completedPullbackObject`. Its comparison uses Q31's
  `completedPullbackComparison` with the fixed K-flat universal counits and units.
* The full integral inclusion uses the completeness conjunct of membership. It
  neither changes the ambient coefficient sheaf nor invents constructibility.
* The finite coefficient maps are the landed constant-section comparisons. The
  completed map is their actual limit map. The ordinary scalar extension is the
  existing `completedAdicChange`, whose sheafified tensor formulas fix objects/maps.

### Object, hypothesis and conclusion checklist

For each item below I compared the node, source convention and Lean type, rather
than identifying declarations only by their names.

| Node item | Lean rendering and verdict |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]`; exact. |
| Finite field extension E/Q_l | `E : Type u`, `Field E`, `Algebra ℚ_[l] E`, `FiniteDimensional ℚ_[l] E`; exact. No algebraic-closure or extra topological structure on E is assumed. |
| A=O_E and fixed uniformizer | Published `PbcIntegralRing l E`, `pbcUniformizer l E`, `pbcIntegralDatum l E`; these are the same valuation ring and recorded fixed uniformizer, with only a universe lift. Exact dependency convention. |
| Four schemes and cartesian square | `{X S T Y : Scheme.{u}}`, `f : X ⟶ S`, `g : T ⟶ S`, `h : Y ⟶ X`, `e : Y ⟶ T`, `sq : ChosenCartesianSquare h e f g`; checked the chosen-square signature. Exact arrows and Cartesian condition. |
| f smooth | `[Smooth f]`; exact. |
| g qcqs | `[QuasiCompact g] [QuasiSeparated g]`; exact. No properness, separatedness or finite-type hypothesis on g. |
| All four Noetherian | Four `IsNoetherian` instances, one per corner; exact. |
| X,T finite dimensional | `_hX`, `_hT : ∃ d : ℕ, topologicalKrullDim ... ≤ (d : WithBot ℕ∞)`; exact. No corresponding S/Y hypothesis. |
| ell invertible on S | `_hl : IsUnit (l : Γ(S, ⊤))`; exact. `sbcPrimeUnitOnSource l g _hl` derives the stalk condition needed by the published lattice type; it is not an additional hypothesis. Global invertibility and invertibility as a section of the structure sheaf have the usual stalk-local equivalence. |
| Complete ambient A categories | `PbcComplete` is the full subcategory for the published intrinsic predicate on `PbcCompletedDerived ... (pbcIntegralDatum l E)`; exact, without boundedness or constructibility. |
| Rational ambient categories | `PbcRationalComplete` uses `ScalarLocalization` at the same uniformizer; exact raw localization. No Karoubi envelope. |
| Constructible rational input | `K : PbcRationalConstructible l E T`, an alias of the landed raw `PbcRationalCategory`; exact. X uses the same category in the conditional conclusion. |
| Lattice with specified presentation | `L : IntegralLattice l E T _hT (...) K`, whose fields are `integral` and `rationalization`; exact integral object and rational isomorphism, in that order. |
| Every finite reduction has bounded constructible etale origin | `_hL : L.IsFiniteLevelEtaleAdmissible ...`; I read `IntegralLattice.reduction` and the predicate. It uses derived extension from the completed sheaf and a Prop existential for every n. Witnesses are not retained as extra lattice data. Exact. |
| Rational operations | `sbcRationalLeft`, `sbcRationalRight` localize `sbcPush g ⋙ sbcPull f` and `sbcPull e ⋙ sbcPush h`; exact ambient functors. Neither assumes arbitrary direct images are constructible. |
| The specified exchange | `sbcExchangeApp` is the unit--theta--counit composite, `sbcExchange` its natural transformation and `sbcRationalExchange` its scalar localization; exact map, not an unspecified isomorphism of endpoints. |
| Ambient invertibility | First conjunct `IsIso ((sbcRationalExchange ...).app ((pbcRationalInclusion ...).obj K))`; exact in the rational complete category on X. |
| Specified-presentation formula | Second conjunct equates `sbcTransportedExchange ... L` with the canonical component at K. The definition applies F to the inverse presentation, then the lattice component, then G to the presentation; exact conjugation order. |
| Independence | Third conjunct quantifies over every other `IntegralLattice ... K`, and then its finite-level admissibility, and equates the two transports. It varies both the integral lattice and its presentation. Exact. |
| Square admissibility | The fourth conjunct's antecedent is the landed `L.IsSquareConstructiblyAdmissible ... sq`. It includes finite admissibility and one existential interval a≤b for all n and all four finite systems. Intrinsic constructibility, not common strata, is required. Exact. |
| Conditional constructible landing | `SbcConstructibleExchangeRepresentation ... L` gives integral constructible endpoint models J,J' on X, their actual endpoint isomorphisms, a rational constructible isomorphism beta, and the commuting equation identifying its ambient image with the named component at K. This is exactly proof step 9's stated interpretation. It does not claim integral constructibility for an arbitrary rationally isomorphic representative. |

All theorem variables and universes are explicitly declared (`autoImplicit false`).
The source's positive quotient index is n+1 in Lean, not n. The only geometric
instances on the final theorem are those listed above. The helper for linearity,
adjunctions and strict completion has no smoothness, properness, Noetherian,
finite-dimensional or constructibility assumption on the square.

### Edge cases

* n=0 means A/(varpi), so the residue-field level is included. All positive powers
  are present; there is no missing first quotient and no illicit level A/(1).
* The zero input and zero lattice are allowed. `IsIso` applies to the actual zero
  exchange, not to a nonzero-morphism predicate. No nonemptiness of schemes or
  supports is imposed. The published strata formulation permits an empty domain.
* Empty schemes satisfy the stalk condition vacuously. Global unit pullback still
  works in the zero section ring. An empty scheme's bottom Krull dimension admits
  the natural-number upper bound in the theorem.
* Characteristic ell at a nonempty S is excluded exactly by the source's invertible
  ell hypothesis. No characteristic-zero condition is imposed on the schemes;
  other characteristics are included. The field extension is characteristic zero
  because its algebra is over Q_l.
* The index system is the fixed nonempty natural-number quotient system of the
  source, so there is no additional arbitrary index-set nonemptiness hypothesis.
  The one interval in square admissibility precedes the universal n and the four
  cohomology conditions. No bound on denominators or common stratum is introduced.
* The small pro-etale site keeps its object universe u+1 and morphism universe u.
  The landed coefficient lift is used throughout; no equality of those universes,
  finite coefficient type of the wrong size, or restriction to small scheme types
  is added to solve elaboration.

### Independent searches

I ran the prescribed search wrapper with this sandbox as `WEIL_SANDBOX` (the
machine-readable results are in `searches.jsonl`): LeanFinder for invertibility of
smooth exchange of completed rational coefficient sheaves via a finite etale lattice
returned eight unrelated etale/adic-completion entries; Loogle
`AlgebraicGeometry.Smooth, CategoryTheory.IsIso` returned only a normalization
pullback result; grep for smooth with exchange/base-change returned seven results
about smoothness stability or normalization. A further LeanSearch request failed
with its service's Internal Server Error; no successful search is inferred from it.

Independently, I used `rg` on Mathlib, upstream `WeilConjectures` and the shared
`lean/Sheaf` tree, including searches with different vocabulary: raw localization,
rational exchange, coefficient inversion, lattice presentation, tensor/base change,
and completed smooth exchange. I opened the pro-etale finite smooth-base-change
module and the rational projection-formula category. The former is finite level;
the latter uses a different Verdier-quotient rational category. Neither is the
present raw rational completed theorem. Searches and actual signatures did identify
the newly landed Q06 and Q31 definitions, which are now reused. The generic
`ScalarLocalization.between`/`betweenNat` helper was absent and is supplied here
with its tensor formulas and named functor-law/naturality theorems. I also opened
`Sheaf.CategoryTheory.ScalarLocalization`: its existing `map` handles only
endofunctors C→C, whereas pullback and direct image require different source and
target categories. That special case is retained rather than mistaken for the
missing cross-category construction.

### Mismatches repaired

1. The first worker supplied private competing constructible/rational/lattice/tower
   modules. Those interfaces are now landed from Q06. I dropped the five obsolete
   modules and their node copies, replaced imports with the landed modules, and
   changed the theorem to the published `IntegralLattice` and its exact predicates.
2. The original completed-pullback delivery and intrinsic-completion record would
   replace Q31's newly landed records. I dropped them too and used Q31's actual
   tower pullback, reduction unit, comparison and derived limit. Thus six old
   dependency modules and seven old dependency records are removed, leaving the two owning modules only.
   An interim coefficient transport tested during this reading is also removed:
   the final interfaces all use the same published coefficient presentation.
3. The original linear-operations theorem stated only finite-component agreement.
   Its docstring claimed strict inverse-limit agreement without putting it in a
   Lean conclusion. I added `sbcOrdinaryExchangeApp`, the explicit strict reduction
   map `sbcStrictExchange`, the actual reduction/limit completion and its unit,
   unit-normalized unique endpoint comparisons, and
   `sbcCompletedExchange_strictLimit`. This is an equality of the named maps after
   the actual derived-limit functor; it is not inferred from equality of finite
   reductions. The source/target comparison docstrings give the K-flat, perfect
   projection-formula, strict transition and reflector arguments from proof steps
   8-11 of the owning node. Together with the existing finite-component theorem,
   the helper now states every clause of its node.
4. I expanded the main proof docstring's coefficient check: injectivity of positive
   uniformizer powers gives the perfect two-term resolutions, and the residue
   characteristic plus successive ideal quotients gives ell-power cardinality.
   Invertibility of those orders on all corners follows from the stated ell-unit
   hypothesis. The rest of the nine-step proof, including the coherent origins and
   conditional constructible endpoint descent, remains in the statement docstring.
5. I refreshed `lean.statement` from each exact signature and `lean.declarations`
   from every public declaration of its owning module. The main natural-language
   statement and both dependency lists are unchanged. Every postponed proof is a
   named theorem with source, blueprint owner and complete proof docstring. Data
   definitions are actual composites, tensor maps or full-subcategory operations;
   the only choices of new comparison data are uniquely normalized by their unit
   equations. There is no hollow definition or arbitrary Nonempty choice.

The final compilation and delivery checks are recorded below after running the
prescribed wrappers. Earlier first-worker validator failures are historical and
are not asserted as a current blocker.

### Final validation

The final prescribed `scompile.py Q05 sbc-thm-e-coefficient-smooth-base-change`
invocation checked both final sibling modules separately under sandbox and library
names and exited 0, with no errors or warnings. The earlier long-line warning was
removed and this final run checked the shortened text. Every theorem body is
`by sorry`; no mathematical theorem was proved during this statement delivery.
The current two node copies differ from the shared DAG only in `lean`. Their
`lean.statement` fields equal the parsed signatures verbatim, all 83 declarations
are recorded in their owning module records, and every declaration has a source and
blueprint docstring. Both modules have no line over 100 characters.

The prescribed `deliver2.py Q05 sbc-thm-e-coefficient-smooth-base-change --no-push`
completed with exit 0 and printed:

> OK (dry run): commit 5b12bc252e passes the preflight and compiles; nothing pushed

It staged exactly the two owning node records, the two Lean modules and this report.
There was no ownership, dependency, statement or second-reading rejection. The final
push uses the same statements and declarations; the only subsequent Lean edit
clarified the rational-inclusion docstring (it is now the full inclusion of the same
published coefficient presentation).


### Maintainer immutable-delivery correction

The maintainer review of 9b278db75bfed992e18c97fa730983e82d7f3a72 found
one redundant specialization (H4): `sbcFiniteCoefficientMap_isIso` was already
provided by `completedFiniteCoefficientMap_isIso` in Q31's
`Sheaf.Paper.CompletedTowerPullback`. The replacement completed-operations module
removes that duplicate postponed theorem and uses the existing theorem directly
inside `sbcFiniteCoefficientIso`. The owning node's declaration inventory is updated
from 75 to 74 declarations (82 across the delivery). All mathematical statements,
canonical maps and normalization equations are unchanged. The independent maintainer
review and reproducibility evidence are recorded in the accompanying review.md.

The maintainer reproduced compilation with `scompile.py Q05
sbc-thm-e-coefficient-smooth-base-change`, first on both immutable modules and
then on the replacement operations module together with the unchanged main module.
Both invocations exited 0 without errors or warnings, checking each module separately
under sandbox and library names through the local side overlay. The replacement
also passes the read-only stage2_delivery text/record checks. The merge tool's
record refit drops exactly the removed helper from lean.declarations.

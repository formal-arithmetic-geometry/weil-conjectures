## Worker report

The delivery states `AlgebraicGeometry.ProEtale.RationalP1.rationalP1_triangle` in
`Sheaf.Paper.RationalP1Triangle`. It repairs the withdrawn unit/counit dependency
and its six canonical-construction interfaces under section 1(B). The DAG's
mathematical statements are unchanged. All theorem proofs are `sorry`; all
definition data are explicit constructions or choices uniquely determined by
fixed-map normalization. No arbitrary adjunction or transformation replaces the
geometric unit/counit.

The current main-20261015 triangle and unit/counit blueprint statements, their
DAG proofs, the Brown right-adjoint declaration, and the resolved stage-1 repair
note were read. The former NY delivery report and rollback return were read.
The source reader confirms that the retained unit/counit record points to an
unavailable module. The present repair supplies that actual missing interface,
instead of treating the retained record as a usable import.

Hypothesis and clause correspondence:

| Source | Lean |
| --- | --- |
| Prime ell | `l : ℕ`, `[Fact l.Prime]` |
| Field k of characteristic prime p > 0 | `k : Type u`, `[Field k]`, `p : ℕ`, `[Fact p.Prime]`, `[CharP k p]` |
| p differs from ell | `hpl : p ≠ l` |
| Separated finite-type k-scheme Y | `[Y.Over (Spec (.of k))]`, `[LocallyOfFiniteType ...]`, `[QuasiCompact ...]`, `[IsSeparated ...]` |
| Finite E/Q_ell inside Qbar, or Qbar | `c : Option (PadicAlgCl.FiniteIntermediateField l)`; `some E` and `none` |
| Continuous E coefficients and finite-subextension-valued Qbar coefficients | `coefficient l c`, using exactly the two published ring objects |
| Ordinary unbounded module-object derived categories | `DerivedCategory (DiagonalCoefficients.Modules ... X)` |
| Loc(Dbc), with finite constant models | `rationalLocalizingCategory`, the full subcategory of `CategoryTheory.localizingClosure (constantModelBoundedConstructible ... X)` |
| P, W and the two projections | `ProjectiveLine Y`, `diagonalSurface Y`, `firstProjection Y`, `secondProjection Y` |
| Fixed diagonal class and traces | `D`, `_hcompletion`, `_hsystem`, `δ`, `_hδ` and `_reference : Reference l Y δ family` tie `family` to the whole-system diagonal limit and the three unit/Chern traces; `diagram l c Y family` selects its exact rational or closure diagram |
| Rq_* | `push l c k p hpl Y`, restriction of `moduleObjectDerivedPushforward` |
| q^*(1)[2] | `exceptional l c k p hpl Y`, pullback followed by tensor with the published positive Tate line and shift positive two |
| eta and epsilon from preceding node | `(unitCounit ... family).1` and `.2`, uniquely fixed by `UnitCounitNormalized` to the actual ambient formulas |
| First displayed left side | `push.map (eta.app M) ≫ epsilon.app (push.obj M)`, followed by `.hom` to the ambient full-subcategory Hom |
| First displayed right side | ambient direct image of `diagonalIntegralAction ... 0 M.obj` |
| Second displayed left side | `eta.app (exceptional.obj K) ≫ exceptional.map (epsilon.app K)`, followed by `.hom` |
| Second displayed right side | `diagonalIntegralAction ... 1 (exceptional.obj K).obj` |
| Trace composed with direct image of delta | `diagonalIntegral`, using `d.support₁.hom ≫ d.R₁.R.map d.delta ≫ d.trace₁` or its second-projection counterpart |
| Canonical coefficient source identification | exactly the diagram's `NormalizedSource.hom`, fixed by the ordinary section composition and derived unit |
| Identity tensor the integral | `diagonalIntegralAction`, conjugating tensor-left action by the single/unit comparison and the right unitor |
| Both right sides are identities | third and fourth conjuncts, respectively, with the same M and K quantifiers |
| The prescribed unit/counit give the adjunction | fifth conjunct: existence of `adj : push ⊣ exceptional` and equalities `adj.unit = ... .1`, `adj.counit = ... .2` |
| q! isomorphic to q^*(1)[2], with q! from Brown existence | final conjunct applies to every `G` with the adjunction of the exact `localizingLowerShriek` for the chosen `BoundaryCompactification`; equivalences `eP`, `eY` identify Loc(Dctf) with Loc(Dbc) and retain ambient inclusions; the conclusion is a natural isomorphism `G ⋙ eP.functor ≅ eY.functor ⋙ exceptional` |

The final universal formulation covers the right adjoint supplied by
`exists_localizingExceptionalAdjoint`; it does not assume that this adjoint is
already adjoint to Rq_* or assume the projective-line adjunction. Its isomorphism
follows from properness and compactification coherence, as in proof step 7.
The equivalences between the rational localizing categories are required to
commute with their actual ambient inclusions, so no category is substituted.
The fixed coefficient family is the preceding diagonal-tower data, including
integration equations. The required `Reference` is supplied by
`diagonalTower_coefficients`, and `diagonalTower_coefficients_baseChange` supplies
the trace base-change compatibility used in proof steps 2 and 3.

Dependency declarations used:

- `Sheaf.Paper.RationalP1UnitCounit`: `RationalP1.unitCounit`, `push`,
  `exceptional`, `UnitCounitNormalized`, preservation/invertibility and exactness
  assertions, all restored in this packet.
- `Sheaf.Paper.LocalizingExceptionalAdjoint`:
  `CondensedRing.exists_localizingExceptionalAdjoint`, `localizingLowerShriek`.
- `Sheaf.Paper.LocalizingClosure`:
  `CategoryTheory.localizingClosure`, `localizingClosureProEtale`.
- `Sheaf.Targets.AffineSpaceRationalLine`:
  `CondensedRing.rationalLocalizingCategory`, `rationalLocalizingInclusion`,
  `rationalTwistFunctor`. Only those existing definitions are used; the affine
  adjunction theorem is not used.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `constantModelBoundedConstructible`.
- `Sheaf.Paper.DiagonalCoefficientCategory` and `DiagonalCoefficientDiagrams`:
  `Modules`, `unit`, `source`, `Diagram`, `Family`, `NormalizedSource.hom`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull` and upstream
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`:
  actual derived functors and their original adjunction.
- `Sheaf.Paper.ProEtaleProjectionExchangeMaps`: `CondensedRing.traceProjection`;
  `RationalLocalizingProjectionFormula`: `moduleObjectProjectionMate`.
- `Sheaf.Paper.CondensedAmbientExchange`: `condensedAmbientExchange`.
- Upstream `UpperStarCoherence`, `DerivedCategory.FlatModel`, and
  `DerivedCategory.Monoidal.Shift`: canonical section, coefficient-unit and
  signed tensor-shift comparisons.
- `Sheaf.Paper.CartesianCoefficients`: `cartesianCoefficients`, the fixed
  root/scalar/coprojection-normalized `CartesianAdicComparison`.
- `Sheaf.Paper.ProEtaleTateTwistsOfUniverses`: public `spRationalTwist`,
  `spQbarTwist`, `SpInternalCartesian`.
- Upstream projective-space and coefficient-ring modules supply the unchanged
  relative projective line, pulled-back rings, and finite-subextension closure.

The main module imports recorded proof dependencies for the seven-step proof.
The tensor bundle contains precisely the existing native K-flat monoidal and
shift structures. Fixed-map heterogeneous equality realizes published maps in
this shared interface; each chosen value has a uniquely determining formula.
It never replaces a canonical comparison by a bare Nonempty isomorphism.

Edge cases: empty and disconnected Y; nonproper and nonsmooth Y; zero M and K;
objects unbounded in either direction inside the localizing closure; every
finite coefficient extension and the finite-subextension-valued closure;
positive characteristic distinct from ell, including ell = 2; positive Tate
twist and positive shift two. The only shift interchange has sign
(-1)^(2r) = 1. All geometry stays in arbitrary universe u; the small site has
objects u+1 and morphisms u, abelian values u+1, and natural-transformation
families have universe u+2. No equality of site universes is imposed. The
pullback comparison obtains residue-field invertibility from the structural
maps over k, with no new target hypothesis.

Searches: `msearch.py` LeanFinder query “Triangle identities for the diagonal
unit and trace counit of the rational projective line” returned eight generic
rigid/adjunction triangle results, including `Adjunction.left_triangle_components`
and `right_triangle_components`; none fixes this geometric pair or computes
the displayed kernel integrals. Loogle `CategoryTheory.Adjunction,
CategoryTheory.NatTrans` returned zero hits. Mathlib AlgebraicGeometry grep
`triangle.*identit|projective.*adjunction` returned only the GammaSpec adjunction
docstring. Fresh project-source rg for RationalP1, UnitCounitType and this
item id finds no existing implementation, only the downstream affine-line proof
docstring. The sandbox search log retains earlier LeanSearch and broader
source/Mathlib search results. The six helper notions already have DAG nodes,
so they are repaired rather than introduced again.

No statement correction and no STATEMENT-DISPUTED finding. No repository or
launcher-script edits, direct Git mutations, or global builds were performed.
Compilation uses only the prescribed scompile wrapper. Validation status is
recorded below after final checks.

## Dependency modules

`det-prop-p1-adjunction-rational-unit-counit`:
`RationalP1UnitCounit` restores the actual full-subcategory restrictions and
uniquely normalized natural transformations, their invertibility on Loc(Dbc),
and exactness/shift compatibility. The old binding's source was withdrawn.
The unit inserts the canonical section, diagonal tensor inverse and class,
then inverses of the fixed projection and exchange; the counit is the inverse
projection followed by identity tensor trace and the coefficient unitor.

`def-sfb-projective-diagonal-pullback`:
`ProjectiveDiagonalPullback` restores actual projections, canonical derived
section pullback comparison, native tensor bundle and coefficient-unit
identification. Its data use the same upstream constructions. A named unique
realization theorem fixes the coefficient-unit isomorphism to the published one.

`def-sfb-projective-diagonal-composition`:
`ProjectiveDiagonalComposition` restores the right-adjoint conjugate section
isomorphism, supported degree-zero unit comparison from exact closed direct
image, and the same published left projection map in the shared interface.

`def-sfb-internal-diagonal-tensor-comparison`:
`RationalP1DiagonalTensor` restores the forward canonical projection composite,
its invertibility and inverse, and its naturality square for every unbounded
ambient derived internal module. The canonical self-product square is literal.

`def-sfb-rational-tate-pullback-comparison`:
`RationalTatePullback` restores coefficient selection, the exact existing Tate
lines, unique linear lift of the normalized abelian adjunct, its derived
single/shift comparison, and the projective second-projection specialization.

`def-sfb-tate-twisted-projection-comparison`:
`TateTwistedProjection` restores tensor then shift two, the native tensor-shift
comparison and canonical projection mate, followed by identity tensor the exact
supplied line comparison. Uniqueness fixes all maps, including Koszul signs.

`def-sfb-projective-ambient-unit-counit-composites`:
`RationalP1AmbientComposites` restores the full class/section/projection/exchange
unit paste and the projection/trace counit paste. Component-normalization
predicates name these entire formulas before restriction; only IsIso witnesses
are existential, so no undetermined morphism is introduced.

Each dependency changes only its lean record, with a note explaining the
withdrawn source and the restoration. The item adds these already-recorded
helper nodes as statement dependencies. No new definition node is needed.

## Second reading by Q07

The dispatch explicitly prohibits subagents and assigns independent review to
the maintainer. This is a second self-reading, not a claimed independent review.
I checked both component orders, both normalized integrals and their identity
clauses, the prescribed unit/counit equalities, the rational coefficient branches,
and the Brown category transport against the node and current blueprint. The
shared bundle/unique-normalization interfaces retain the same canonical maps.
No mathematical statement was changed. The H3 repair below supersedes the
previous self-check of the unrestricted-family signature.

## Repair of returned head 56a38d534481 (H3)

The required initial dry run of the saved packet passed at `b5416aa7c9b`, but
that mechanical check did not address H3. Re-read the return, the blueprint
triangle and unit/counit source, `Diagram`, `Family`, `Reference`,
`CompletedTraceCompatibility`, `DiagonalTrace.Result`, `IsDiagonalLimit`, and
both theorems of `DiagonalTowerCoefficients` before editing. The return is
correct: integration alone places no condition on the q trace. Replacing all
q traces by zero preserved the old hypotheses while making the counit zero.

The repaired signature now binds exactly the input of
`diagonalTower_coefficients`: the completed derived reduction `D`,
`_hcompletion : DiagonalCompletionSpec ... D`,
`_hsystem : DiagonalCycleSystemSpec ... hY D`, the completed arrow `δ`,
`_hδ : DiagonalTrace.IsDiagonalLimit ... D δ`, and finally
`_reference : Reference l Y δ family`. These are the preceding construction's
presentation data, not a hypothesis asserting either triangle or an adjunction.
`Reference.delta` fixes the initial class to the realized whole-system limit;
`Reference.q_trace`, `p₁_trace`, `p₂_trace` fix all three traces to
`DiagonalTrace.Result` traces with the specified projective-line models.
`Result.construction` fixes a trace to the unit/Chern splitting and its
constant-summand projection. The family then carries these maps through the
specified coefficient extensions. Consequently the zero-q-trace modification
no longer satisfies the hypotheses on a nonempty base.

`diagonalTower_coefficients` supplies a family with this reference for every
completed limit in the standing setting. Its second theorem,
`diagonalTower_coefficients_baseChange`, applies to referenced families at Y
and any separated finite-type Y'. In particular, use Y' = ProjectiveLine Y and
g = q; the resulting `FamilyPullback` gives the canonical base-changed traces
needed in both kernel computations. Thus base-change compatibility follows
from the pinned construction, rather than being assumed for arbitrary maps.
The proof docstring now explains this relationship. All six conclusions,
composition orders, source normalizations, and the Brown comparison are
unchanged.

The node now cites `det-prop-diagonal-tower-coefficients` and
`det-prop-diagonal-tower-trace` in `stmt_deps`, and their imports are public.
No TeX statement correction is needed: the node already specifies the
preceding canonical morphisms, whereas the old Lean signature failed to fix
them. The seven dependency modules and their node records remain unchanged.

### Standing instances and presentation data

The additional binders repeat the published coefficient theorem's interface,
without imposing a new geometric condition:

- `IsNoetherian Y`, `IsNoetherian (ProjectiveLine Y)`, and
  `IsNoetherian (diagonalSurface Y)`: finite-type schemes over a field are
  Noetherian; a relative projective line and its self-product remain finite
  type over that field. This includes empty and disconnected bases.
- `hY : IsUnit (l : Γ(Y, ⊤))`: the image of ell in k is nonzero since p and
  ell are distinct primes, hence is a unit. The structural ring map from k
  to global sections preserves it and its inverse, including the zero ring
  of sections of the empty scheme.
- The three `DiagonalTraceLocalizations` instances choose derived localizations
  of abelian sheaves, coefficient-module sheaves, their strict towers, and
  completed-coefficient modules, and the Ext size for the strict systems.
  They are localization/size presentations, not exactness, cohomological
  dimension, or boundedness assumptions on Y. These sheaf and system
  categories have the usual small-Hom derived presentations (using their
  injective resolutions); the chosen universe is u+1. The completed category
  here is modules over the completed coefficient sheaf, not an assumed
  Grothendieck category of derived-complete objects. The theorem is universal
  in these choices, using exactly the instances of the preceding construction.
- `D`, completion/system specifications and `IsDiagonalLimit` identify the
  specific finite Cartier system and its completed limit. `Reference` records
  its normalized realization, and the preceding existence theorem supplies it.
  These binders spell out the phrase “morphisms of the diagonal tower” in the
  source, without restricting which M or K the conclusions cover.

Additional dependency declarations read and used: module
`Sheaf.Paper.DiagonalTowerCoefficients`,
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalTower_coefficients`
and `diagonalTower_coefficients_baseChange`; module
`Sheaf.Paper.DiagonalCoefficientReference`, `Reference`; module
`Sheaf.Paper.DiagonalTowerTraceLimit`, `DiagonalTrace.IsDiagonalLimit`;
module `Sheaf.Paper.DiagonalTowerTrace`, `diagonalTower_trace`.
The latter modules are exposed through the two added direct dependencies.

### Second self-reading after H3

Rechecked the new binders against both coefficient-theorem signatures and the
unit/counit source: none asks for the desired adjunction. The reference pins
the completed q trace as well as both projection traces, and Family transports
them to every finite E and Qbar stage. Both zero objects and the empty base
remain included; zero q trace is excluded only where it contradicts the fixed
canonical trace. Every previous clause correspondence still applies, with the
fixed-data row above replacing the defective arbitrary-family row. No new
notion or duplicate definition is introduced. Dispatch prohibits subagents;
this is self-review and the maintainer supplies independent review.

### Repair validation

All eight packet modules were checked with the prescribed `scompile.py`, exit
0 and no diagnostic warnings or errors (`scratch/h3-compile.log`). The node's
recorded theorem signature was regenerated verbatim from the repaired source.
Final dry-run and push results are recorded below.

The repaired dry run passed: `OK (dry run): commit 2dadec36752 passes the preflight and compiles; nothing pushed`. Final self-check confirmed the theorem signature is verbatim, every Lean file disables auto-implicit variables and respects 100 columns, all seven dependency records change only `lean`, and the item changes only `lean` and added `stmt_deps`. The H3 repair changes the actual theorem binders and is not an unchanged re-push.

## Repair of returned head 69f9586112a0 (H2)

The required initial dry run of the retained packet passed at `61d4d24beb0`.
That validated compilation and shape, but the retained packet still had the H2
fault described in the return. This repair changes the dependency records and
imports; it is not an unchanged rebase or re-push. The accepted H3 signature,
both helper definitions, theorem proof docstring, seven dependency modules,
and every mathematical statement of an existing node are retained.

The earlier H3 report's instruction to add the two theorem nodes to statement
dependencies is superseded by this return and this repair:

- Removed `det-prop-diagonal-tower-coefficients` and
  `det-prop-diagonal-tower-trace` from the packet's added `stmt_deps`.
  Both remain unchanged in `proof_deps`: their conclusions are used by the
  proof, not by the signature. The current main item has neither in its
  `stmt_deps`; thus this repair removes no dependency from the current base.
- Added the published definition nodes
  `def-sfb-diagonal-coefficient-reference`,
  `def-sfb-diagonal-trace-limit-characterization`, and
  `def-sfb-diagonal-trace-models`. Their declarations are respectively
  `AlgebraicGeometry.ProEtale.DiagonalCoefficients.Reference`,
  `AlgebraicGeometry.ProEtale.DiagonalTrace.IsDiagonalLimit`, and
  `AlgebraicGeometry.ProEtale.DiagonalTraceLocalizations`. Read their full
  source declarations and docstrings, and their node statements/records.
- Added the three definition ownership nodes listed below. They use
  `existing: true` and list exactly the eight existing plain declarations
  needed here; no theorem conclusion is recorded as a definition. No source
  module is copied or redefined.
- Public imports now explicitly give the definition modules. The coefficient
  theorem module is a private proof import. `DiagonalTowerTrace` stays public
  because it defines `NormalizedSource` and its actual associated morphism,
  which the diagram/support interfaces use. Its theorem is not a statement
  dependency.

The ownership correspondence for the unchanged signature and helper terms is:

| Signature or helper term | Definition owner |
| --- | --- |
| `D : DiagonalDerivedReduction ...` | `def-sfb-diagonal-system-interface` |
| `diagonalScalarExtension ...` | `def-sfb-diagonal-system-interface` |
| `_hcompletion : DiagonalCompletionSpec ...` | `def-sfb-diagonal-system-interface` |
| `_hsystem : DiagonalCycleSystemSpec ...` | `def-sfb-diagonal-system-interface` |
| `diagonalCompletedDomain ...` | `def-sfb-diagonal-completed-endpoints` |
| `diagonalCompletedCodomain ...` | `def-sfb-diagonal-completed-endpoints` |
| `support₁.hom`, `support₂.hom` through `NormalizedSource` | `def-sfb-diagonal-normalized-source` |
| `_reference : Reference ...` | `def-sfb-diagonal-coefficient-reference` |
| `_hδ : DiagonalTrace.IsDiagonalLimit ...` | `def-sfb-diagonal-trace-limit-characterization` |
| All three `DiagonalTraceLocalizations` instances | `def-sfb-diagonal-trace-models` |

The latest main node and all saved dependency node records were compared by
reading JSON. The item still changes only `lean` and added `stmt_deps` relative
to main, and each of the seven restored dependency records still changes only
`lean`. The wrapper refreshes/rebases its delivery worktree on current main.
There is no statement correction and no change to `proof` or `proof_deps`.

## New nodes

`def-sfb-diagonal-system-interface` owns exactly
`AlgebraicGeometry.ProEtale.DiagonalDerivedReduction`,
`diagonalScalarExtension`, `DiagonalCompletionSpec`, and
`DiagonalCycleSystemSpec`, all in `Sheaf.Paper.DiagonalTowerSystem`.
Its statement spells out ordinary quotient/transition normalization, the
pointwise universal left-derived counit and exactness; sheafified constant
scalar extension; both total derived limits and the completion unit's universal
property; and the single whole-system positive Cartier class with its source,
root and every finite-level normalization. It defines the predicates without
asserting them. Source: diagonal-tower-system clauses 2--4 and the corresponding
full existing source declarations. The generic reduction has unrestricted
category universes, the specialization uses the existing small pro-etale site,
and the first index is exponent one, not exponent zero. Empty schemes and
unbounded complexes are included.

`def-sfb-diagonal-completed-endpoints` owns exactly
`AlgebraicGeometry.ProEtale.diagonalCompletedDomain` and
`diagonalCompletedCodomain`, in `Sheaf.Paper.DiagonalTowerLimit`.
They are the actual supported completed coefficient in degree zero and the
published completed Tate line shifted by positive two, respectively. The
supported module's coefficient action is restriction along the finite-projection
limit map, then the actual ringed direct image. Source: diagonal-tower-limit
clauses 1 and 3. No existence, arrow, completeness theorem or arbitrary endpoint
is substituted. The localization universe is the declaration's arbitrary `w`;
no field or nonemptiness assumption is added. This includes the empty base.

`def-sfb-diagonal-normalized-source` owns exactly
`AlgebraicGeometry.ProEtale.DiagonalTrace.NormalizedSource` and
`NormalizedSource.hom`, in `Sheaf.Paper.DiagonalTowerTrace`.
The structure's four fields are the proof of `P`, the ordinary isomorphism,
its supplied normalization predicate, and invertibility of the universal
single-object comparison. Its associated map is exactly the single functor
applied to the ordinary isomorphism, followed by that comparison. Source:
diagonal-trace proof part (2), the supported-source comparison in the displayed
integration map. The general statement keeps the existing common object,
morphism and derived-localization universes. Zero source objects and arbitrary
normalization predicates remain included; the node asserts no existence.

These are ownership nodes for existing declarations, explicitly requested by
H2, rather than duplicate definitions. Each has its existing primary signature
verbatim and the full exact declaration list. No other declaration in those
three theorem modules is claimed by these records. The existing three reference,
limit-characterization and model nodes are cited directly without being edited.

Fresh searches, shared by the three ownership nodes and logged in
`searches.jsonl`: `msearch.py` LeanSearch and LeanFinder with the query
“Simultaneous derived reduction of a strict coefficient tower, completed
diagonal endpoints, and adjunction normalized supported source” each returned
eight generic results, none of these definitions; the exact names are retained
in each new node's `mathlib_searches`. `msearch.py grep` with the eight-name
regular expression returned zero Mathlib hits. Actual `rg` on both project roots
found no upstream matches and located the existing definitions and their
consumers in `Sheaf`; they are reused. DAG search found their listings in the
three theorem records and references by the existing trace/reference nodes,
but no definition node owning these eight declarations. `blueprint_refs.py
search` for “diagonal derived reduction” and “normalized source” both returned
zero blueprint matches. The ancestor tool identified this item itself as the
blueprint ancestor. No new Lean module is needed for an existing declaration.

### Second self-reading after H2

The dispatcher forbids subagents; this is self-review, with independent review
reserved for the maintainer. Re-read the returned H2 entry against the complete
source bodies of the eight definitions and the three existing definition-node
interfaces. Every requested owner now appears in the item's `stmt_deps` and
maps to the terms in the table. The two theorem nodes appear only among proof
dependencies. Comparing the repaired main module with the saved source from
before this repair gives identical text from the module docstring to the end;
only imports changed. Thus both displayed computations, both identity clauses,
the prescribed unit/counit adjunction, Brown comparison, all H3 binders and
universes, and the signature recorded in `lean.statement` are unchanged.

The first H2 dry run identified the blueprint-origin path convention for a
blueprint item (`via: []`) and individually bracketed citations required by
preflight. Both were corrected in the new node records before rerunning.
All eight packet modules compiled with exit 0 and no warnings or errors
(`scratch/h2-compile.log`). The item signature is byte-for-byte equal to its
`lean.statement`; every new node citation list equals its `stmt_deps`.

Final H2 dry run: `OK (dry run): commit 361c865c6c2 passes the preflight and
compiles; nothing pushed`. Final self-check passed: all base dependencies are
preserved, the two theorem nodes remain only in `proof_deps`, all three new
existing-definition ownership nodes are cited, their bracketed citations match
their dependency lists, and the mathematical statement and proof route are
unchanged. The wrapper's preliminary existing-declaration check also compiled.

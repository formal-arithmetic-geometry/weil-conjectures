## Worker report

The module `Sheaf.AlgebraicGeometry.LocnoethLCICurveAdjunctionGluing` states
`AlgebraicGeometry.exists_locnoethLCICurveAdjunctionGluing`, with one `sorry` and
the eight-step natural-language proof in its docstring. It reuses the owning
adjunction and fundamental-class interfaces. Two helper definitions retain the
polynomial chart and its normalized Ext comparisons; neither contains postponed
data or a new mathematical construction.

Hypotheses, individually:

- Schemes and structure morphism: `{X S : Scheme.{u}} (p : X ⟶ S)`.
- Locally Noetherian base: `[IsLocallyNoetherian S]`, with no quasi-compactness
  requirement on S and no global `[IsNoetherian S]` assumption.
- Flatness: `[Flat p]`.
- Finite presentation: `[LocallyOfFinitePresentation p] [QuasiCompact p]
  [QuasiSeparated p]`, exactly the three properties spelled out in the node.
- Nonempty fibres pure of dimension one: `hpure : ∀ s : S,
  (flatLCIGeometricFibre p s).IsPureDimension 1`. The recorded fibre is literally
  the pullback along Spec of the algebraic closure of the residue field. The
  pure-dimension predicate quantifies over irreducible components; empty fibres
  have no components. Thus this imposes no surjectivity or nonemptiness condition.
- Regular affine curve coverage: `hcharts : ∀ x, ∃ A :
  NodalCanonicalPresentation p, x ∈ A.U.1`. The existing presentation structure
  retains both affine opens, their inclusion over p, c+1 variables, c ordered
  regular equations, the actual coefficient map, surjectivity, and kernel equality.

Conclusion clauses, individually:

- The adjunction lines K_V, their determinant comparisons, and the glued line K:
  `∃ F : FlatLCIAdjunctionSystem p 1, F.IsNormalized ∧ ...`. Its identity member
  `F.line (FlatLCIBaseChange.identity p)` is K on X; base-open members give K_V.
  `F.invertible` is invertibility of every member. `F.localIso` identifies each
  actual conormal determinant with the restriction of that same line.
- Specified transitions: `F.IsNormalized` asserts the exact-cone determinant
  formula for refinements and the normalized tensor formula for pullbacks. These
  are equations on actual exterior sections, not free isomorphisms.
- Identity and triple cocycle: `F.identity` and `F.composition` are the exact
  identity and iterated-base-change equalities, with the recorded section-normalized
  tensor pullback comparisons. Affine refinements of base overlaps are particular
  members and maps of this system. Their comparisons cancel to give t_ij and
  t_jk t_ij = t_ik. Arbitrary intersections are allowed; no assertion that an
  intersection is affine occurs anywhere.
- Fundamental maps: `α : ∀ B, B.p'.relativeDifferentials ⟶ F.line B` and
  `F.IsCurveFundamentalClass α`. Its first clause gives local restrictions of
  the global α and the cofactor and scalar Jacobian formulas in every presentation,
  not just the selected cover. The sign is the existing
  `flatLCICurveFundamentalSign c`; in the repaired kernel-first convention it is
  +1, since the negative conormal inclusion and rank signs cancel. The last
  clause gives the comparison square on actual differential generators.
- Nodal dualizing datum: the explicit existential `D : NodalDualizingDatum p
  (F.line (FlatLCIBaseChange.identity p))`, with `D.fundamental = α ...`, includes
  invertibility, the same morphism, chart coverage, the polynomial Jacobian formula
  for every chart and its actual sheaf Ext isomorphism. This is datum terminology,
  not a nodal-singularity hypothesis.
- Retained Ext comparisons: `F.HasNormalizedCurveExtComparisons` uses the existing
  `PolynomialDualityChartAtlas` on the shifted single complex of **F.line B**.
  Its restriction equation is the independent comparison from evaluation, and
  `LciKoszulDuality.IsNormalizedAtlas` imposes the specified affine and localized
  presentation comparisons. For every affine ambient lci presentation C there is
  a chart T with `T.chart = C.polynomialChart` and `T.c = C.c`, and the local map
  `e` is `HEq` to **F.localIso B U C**. No different polynomial presentation or
  independently rescaled line trivialization is substituted. The comparison ρ
  satisfies `T.IsNormalized`, the existing signed contraction formula on every
  quotient-augmented Koszul roof, and the displayed shifted equation connects
  that same ρ to the atlas via the actual local line map. Its homology in degree c
  supplies the Ext comparisons. Thus restriction and change-of-presentation keep
  those specified comparisons. Arbitrary base change preserves this normalization:
  the defining roof formula, coefficient maps, evaluation and ordered signs are
  unchanged by scalar extension. All members of F satisfy this same condition.
- Derived and Ext identifications: `C.HasExtIdentification ∧ C.HasDualityModel`
  for all base changes and presentations. The latter is the derived isomorphism,
  so the conclusion does not replace a derived statement by homology alone.
- Relative smooth locus: `IsIso ((tensorPullback U.ι).map (α B))` on every smooth
  open U, so α itself is the canonical identification. The recorded
  `IsCurveFundamentalClass` also characterizes this locus on stalks.
- Every base change, including non-Noetherian bases: `B : FlatLCIBaseChange p`
  has no Noetherian assumption on B.S'. The final clause covers B.X' by the
  existing `FlatLCIPresentation` notion, which only asks regularity at primes
  containing the immersion ideal. This does not demand global regularity of the
  coefficient-extended equations away from the closed subscheme. `F.baseChange`,
  `F.identity`, `F.composition` and the generator equation of the fundamental
  predicate give the requested restriction, iterated-base-change, and isomorphic
  family compatibilities for these very comparisons.
- There are no properness, separatedness of p, nodal-singularity, connectedness,
  or affine-intersection hypotheses. Quasi-separatedness is exactly the stipulated
  finite-presentation hypothesis.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` / `QuasiCompact`:
  `LocallyOfFiniteType` / `QuasiCompact` (only quasi-compactness is needed here).
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `QuasiSeparated`.
- `Sheaf.AlgebraicGeometry.NodalDualizingDatum`: `NodalCanonicalPresentation`,
  its ambient, immersion, Jacobian and Ext constructions, `NodalDualizingDatum`.
- `Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction`:
  `FlatLCIPresentation`, its line, conormal and differential modules;
  `FlatLCIBaseChange`, `.identity`; `FlatLCIAdjunctionSystem`, `.IsNormalized`;
  `flatLCIGeometricFibre`, `HasExtIdentification`, `HasDualityModel`.
  The full `exists_flatLCICanonicalAdjunction` statement and its docstring were read.
- `Sheaf.AlgebraicGeometry.LCICurveFundamentalClass`:
  `flatLCICurveFundamentalSign`, `IsCurveCofactorMap`, `IsCurveJacobianMap`,
  `IsCurveFundamentalClass`; read the full `existsUnique_lciCurveFundamentalClass`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `Scheme.Modules.IsInvertible` (inside the existing system and datum).
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, `.D`, and the
  universal derivation equivalence, through
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials` and its derivation.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  the existing `Scheme.Modules.tensorPullback`, section normalization, identity
  and composition comparisons, already publicly imported by the adjunction module.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  literally used by the existing `flatLCIGeometricFibre`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- `Sheaf.TraceFormula.LciKoszulDualityData`: `Chart`, `.IsNormalized`,
  `.unshiftedModel`, `.unshiftedTarget`; and its actual augmentation and pairing.
- `Sheaf.TraceFormula.LciKoszulDualityDeterminantComparison`: `.openTensorIso`,
  `.Chart.ImageExact`, `.Chart.shifted`, `.IsNormalizedAtlas`.
- `Sheaf.AlgebraicGeometry.PolynomialDualityRestrictionAtlas`:
  `PolynomialDualityChartAtlas`, imported publicly through the preceding modules.

The statement now cites the landed definition owners
`def-trf-lci-koszul-duality-data`, `def-sfb-flat-lci-base-change`,
`def-sfb-flat-lci-adjunction-system` and `def-sfb-lci-curve-fundamental-class`,
and the two definition-only attachments described under New nodes below.
The newly added theorem dependency
`lem-trf-lci-koszul-duality-determinant-comparison` has been removed from
`stmt_deps`; it remains in `proof_deps`. No theorem conclusion is chosen to
construct the data in the statement. The two inherited adjunction/fundamental-class
theorem edges remain byte-for-byte as on the base: the unchanged-item field rule
allows adding definition owners but forbids deleting inherited dependencies.
Both now have their separately cited definition owners. This implements the
recommended ownership repair without inventing a mathematical statement change.
`polynomialChart` only forgets fields of an existing chart, and
`HasNormalizedCurveExtComparisons` packages this item's own Ext-comparison clause.
Every helper carries this item's source/blueprint docstring and is listed in
`lean.declarations`.

Proof imports include the landed determinant-normalization and module-sheaf
gluing nodes. The presentation-base-change node has no Lean statement in the
read clone; its already landed relative-equations base-change ingredient is imported.
The Mathlib base-change and affine-Noetherian proof dependencies are already
available through the statement modules. No live source was modified.

Sources opened locally: duality.tex, labels `lemma-lci-shriek` (4692),
`lemma-base-change-relative-dualizing` (7254), `lemma-determinant` (7510),
`lemma-fundamental-class-lci` (7557), including their proofs. The last source
has a Noetherian/proper-smooth-factorization setting; this node explicitly uses
the recorded nonproper adjunction/fundamental-class versions and affine descent,
not an assertion that Tag 0E9Z verbatim has the gluing statement.

Edge cases checked: empty source and empty geometric fibres (all point/component
conditions vacuous); c=0 (one coordinate, empty regular sequence, sign +1,
Ext degree zero); zero localized chart omitted from covering; nonseparated base
with nonaffine intersections (the restriction system has no affine-intersection
condition); nonseparated source; disconnected bases; arbitrary characteristic;
nonflat and non-Noetherian base changes (no new regularity-away-from-source
assumption). Universes are bound explicitly. The Ext normalization uses actual
standard derived categories at u+1 locally inside a definition, not an extra
hypothesis or an arbitrary `Nonempty` witness. Explicit derived universes were
needed to avoid Lean selecting its smaller hom-universe instance for exact
restriction; the corrected file compiles at the intended standard universe.

Searches made on 2026-10-24 using the prescribed msearch.py (raw output is in
the sandbox's searches.jsonl):

- LeanFinder: "The normalized adjunction line and Jacobian fundamental class of a
  flat lci curve glue over locally Noetherian base opens and commute with arbitrary
  base change". Eight normalization-scheme hits; none is an adjunction line or
  fundamental-class descent theorem.
- LeanSearch: "A normalized adjunction line and fundamental class of a flat local
  complete intersection curve glue over a locally Noetherian base". Eight hits
  about normalization schemes and relative scheme gluing; no matching theorem.
- Loogle: `"KaehlerDifferential", "ExteriorPower"`: zero hits.
- Mathlib grep: `dualizing|fundamentalClass|fundamental_class`, AlgebraicGeometry:
  zero hits. `polynomialChart|HasNormalizedCurveExtComparisons|locnoethLCICurveAdjunction`:
  zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `IsCurveFundamentalClass`, and locally-Noetherian-adjunction names: only the
  existing Noetherian fundamental-class predicate/theorem and the proper nodal
  relative-dualizing-system consumer. The latter imposes properness and nodal
  fibres and is not this theorem. No item-id occurrence in WeilConjectures.
- Read the existing Koszul-duality data and comparison modules and the cotangent
  determinant normalization module; these supply the normalization interfaces
  reused here. No duplicate construction is written.

Validation: scompile.py compiled both sandbox and final module paths cleanly,
with no warnings or errors after the explicit derived-universe repair. The theorem
alone has `sorry`; definitions have concrete data. No statement correction or
statement dispute was necessary.

## Second reading by Q81

I reopened the node and module for a separate clause-by-clause self-reading;
the dispatcher explicitly prohibited starting other agents, so this is not
represented as an independent worker review. The maintainer's independent review
reads the delivery. The rereading found that existence of individual Ext
isomorphisms would omit the specified-comparison restriction clause. I added
the shared polynomial-chart atlas, its independent evaluation restriction and
normalized affine-refinement conditions, and the equation tying its normalized
Koszul ρ to the same `F.localIso`. I also added explicit coverage by locally
regular lci presentations after arbitrary base change. Each hypothesis and
conclusion is matched above, including the global datum using exactly α, the
smooth-locus map, nonaffine overlaps and non-Noetherian changes of base. The
only additional geometric consequence in the interface is the already-recorded
local derived duality model, which specifies the Ext comparison rather than
introducing a new geometric hypothesis. Neither the main node statement nor any
dependency's definitions were changed.

## Return repair

The return on immutable head `1c542c4ab079` identified one required H2 defect:
the newly added theorem statement dependency owned only definitions used here.
The saved packet's initial dry run passed (commit `e84abdc2c89`), confirming
that this was a review defect rather than a compilation defect. This repair
adds a definition owner for precisely the six requested comparison declarations
and replaces that added theorem edge. The accepted Lean module is unchanged.
The theorem remains a proof dependency, as requested.

The recommended three landed definition owners have also been cited. The two
inherited theorem statement edges were retained because brief-stage2 section 5
and the unchanged-item preflight permit dependency additions only; their text is
still cited in the mathematical node. The source statement and proof have not
changed. Separately, the local duality predicates have their own definition node,
and the local-duality definition node now also lists the existing geometric-fibre
convenience declaration. The generic geometric-fibre node retains its original
Mathlib record unchanged.

The advisory about `openTensorIso` was checked against the current upstream
`WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`, lines 48 onward.
Its `exists_tensorPullbackAdjunction` now includes the actual sectionwise unit
formula, sending m to 1 tensor m. Thus the selected adjunction in the existing
`openTensorIso` is already section-normalized, just as
`tensorPullbackSectionAdjunction` is. Both use the identical tensor functor and
direct image; uniqueness of the normalized unit identifies their adjunctions.
No arbitrary adjunction is assumed by the newly attached node, and no upstream
or shared module was edited.

The self-check reopened every new node against the existing declaration bodies.
`ImageExact` has both finite-limit and finite-colimit preservation; `modelShift`
uses the right-derived shift comparison; `targetShift` uses n-c=d and the exact
single-functor comparison; `shifted` is their composite with rho[n].
`IsNormalizedAtlas` quantifies over every affine pair and requires both affine
and principal-open compatibility of the same presentation system. The local
model predicates quantify over every derived-category instance at u+1 and
intertwine every endomorphism of the closed source's unit module, with the
contravariant action on the first Hom/Ext argument. The fibre definition is the
literal pullback along Spec of the algebraic closure of the residue field.
Rank zero, empty fibres and affine charts, h=0/h=1, arbitrary bases and all the
original edge cases remain included. New definitions contain no data or proofs;
the new records attach already-landed concrete definitions.

## New nodes

`def-sfb-lci-koszul-shifted-comparison` attaches `existing: true` to
`Sheaf.TraceFormula.LciKoszulDualityDeterminantComparison`, listing exactly
`AlgebraicGeometry.LciKoszulDuality.openTensorIso`, `Chart.ImageExact`,
`Chart.modelShift`, `Chart.targetShift`, `Chart.shifted` and `IsNormalizedAtlas`
in that namespace. It defines the ordinary open restriction comparison, exact
image data, shifted comparison and independently normalized atlas predicate.
Sources: Stacks 0BQZ/0BV2/0BZI/0BZJ, read in duality.tex at 3544 and 4419 and
in dualizing.tex at 4319 and 4365. LeanSearch returned generic shift and
closed-immersion facts; LeanFinder returned cotangent/polynomial differential
facts; Mathlib grep returned no exact name. Source/DAG grep found the six
existing definitions only under the comparison theorem, with no definition
owner. `blueprint_refs.py search 'Koszul duality'` found no blueprint node.
The new record owns existing declarations; it supplies no second construction.

`def-sfb-lci-local-duality-models` attaches `existing: true` to
`Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction`, listing
`AlgebraicGeometry.FlatLCIPresentation.HasDualityModel`,
`AlgebraicGeometry.FlatLCIPresentation.HasExtIdentification` and
`AlgebraicGeometry.flatLCIScalarAction` and
`AlgebraicGeometry.flatLCIGeometricFibre`. It records the ambient shifted derived
Hom model and its ordinary Ext counterpart with their actual closed-source
scalar action, as properties of a supplied presentation, together with the
existing convenience construction for the geometric fibre over the chosen
algebraic closure of a residue field. That construction is the literal Mathlib
pullback of `def-weil-geometric-fibre`. Sources: Stacks 0B6V/0BQZ and 01JO. LeanSearch returned ordinary residue-field fibre facts; LeanFinder
returned smoothness and cotangent-module facts; Mathlib grep returned no match.
Project grep found only these existing predicate definitions, and DAG grep
found no definition owner. The existing adjunction-system node owns the
presentation and its determinant line, not these separate duality predicates.
All raw search summaries are preserved verbatim in each new node's
`mathlib_searches`; source and DAG searches are recorded there too.

Repair validation: the prescribed scompile.py compiled the unchanged module both
as its sandbox probe and as its final library module, with no messages, warnings
or errors (7.1 s and 4.8 s). A separate JSON self-check confirmed that the item
changes only lean/stmt_deps, the geometric-fibre dependency is byte-identical to the shared base,
each new node cites exactly its declared dependencies, and each lean.statement
is verbatim in its recorded source module.

## H13 return repair (357840c4974d)

The previous delivery needlessly rebound the still-usable generic
`def-weil-geometric-fibre` record. I restored that sandbox JSON byte-for-byte
from the shared sheaf-dag copy, including its original Mathlib pullback record.
It is no longer a dependency repair in this packet.

I followed option (a) of the return: `def-sfb-lci-local-duality-models` now lists
`AlgebraicGeometry.flatLCIGeometricFibre` among its existing declarations, adds
a TeX sentence giving the exact algebraic-closure residue-field pullback, and
cites `def-weil-geometric-fibre` in its statement and `stmt_deps`. The source
record includes Stacks 01JO. The body at FlatLCICanonicalAdjunction.lean:525
was reopened and matches this sentence literally; there are no flatness, lci,
Noetherian or nonempty-fibre assumptions on this convenience construction.
The prior search results already cover this declaration and remain preserved.

The advisory is implemented by adding
`def-trf-polynomial-duality-restriction-atlas` directly to the item's
`stmt_deps`, for the `PolynomialDualityChartAtlas` used in
`HasNormalizedCurveExtComparisons`. Its recorded definition and module were
reopened. It was already publicly imported through the comparison module.

Self-reading confirmed that the six shifted-comparison declarations and the
three local-duality declarations accepted by the review are unchanged. Only
the added convenience-declaration ownership and direct atlas citation differ.
The accepted Lean module and its signature are unchanged, so all hypotheses,
conclusions, universe parameters and edge cases described above are retained.
No mathematical statement correction, new construction or additional sorry
was introduced. The maintainer supplies the independent review; no other agent
was started.

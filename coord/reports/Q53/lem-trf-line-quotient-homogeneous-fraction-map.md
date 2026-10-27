## Worker report

The module `Sheaf.TraceFormula.LineQuotientHomogeneousFractionMap` states
`AlgebraicGeometry.Scheme.Modules.line_quotient_homogeneous_fraction_map`.
Its sole postponed proof is the whole proof of that named theorem. All helper definitions
have real data; coefficients use `Function.invFun` on multiplication by a specified frame
power, which is a uniquely invertible function when the predicates use it. No algebra,
module, morphism, or graded component is chosen from an unproved existence statement.

Source read: `literature/stacks-project/constructions.tex`, section-projective-bundle
(01OA), its paragraph beginning “Let f : T → S ... be a surjection”, and
lemma-invertible-map-into-relative-proj (01O9), including its preceding generation-open
construction and characterizations (2) and (3). The seven-step proof docstring follows
all seven steps of the assigned node, with their named supporting lemmas.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| S and T schemes, arbitrary h:T→S | `{S T : Scheme.{u}} (h : T ⟶ S)` |
| E arbitrary quasi-coherent, with no finite-type/local-free assumption | `(E : S.Modules) [E.IsQuasicoherent]`; no other condition on E |
| A is the canonical symmetric graded algebra, P its relative Proj | `SymmetricAlgebraSheaf.gradedAlgebraData E`, `.relProj`, `.relProjHom` |
| L invertible | `(L : T.Modules) [L.IsInvertible]` |
| q a surjective sheaf map from the tensor pullback | `(q : (tensorPullback h).obj E ⟶ L) [Epi q]`; Epi is sheaf surjectivity, not surjectivity on all open sections |
| unique graded algebra extension ψ | `∃ ψ : RelativeGradedLineMap ...`, `ExtendsLineQuotient`, followed by `∀ ψ', ... → ψ' = ψ` |
| degree one exactly q | `ExtendsLineQuotient`: on every affine base section m, the right unitor identifies ψ₁(ι(m)) with `q (tensorPullbackSection h E ... m)` |
| structural unit in degree zero, scalar linearity, products and restriction | existing `RelativeGradedLineMap.one`, `.smul`, `.mul`, `.restriction`; the degree-zero scalar map follows from `.one` and `.smul` |
| tensor powers | existing `Scheme.Modules.tensorPow` and `.tensorPowAddIso`, with their existing sheaf tensor structure |
| every affine U, affine W⊆h⁻¹U and frame l | `HasQuotientFractionCharts` quantifies `U : S.affineOpens`, `W : T.affineOpens`, `hWU`, `l`, and `IsFreeGenerator l` |
| q(m⊗1)=b_m l | `quotientGeneratorCoefficient` is the inverse of b↦b•l applied to q on the actual normalized tensor-pullback section; the imported affine comparison identifies this section with m⊗1 |
| b(a) is the coefficient in the dth frame power | `quotientFramePower` recursively tensors l, starting with the structural unit; `quotientCoefficient` uses its inverse scalar function; the first chart conjunct explicitly asserts its coefficient equation |
| degree-one coefficients agree with b_m | the second chart conjunct identifies `quotientCoefficient ... 1 (quotientSymmetricGenerator ... m)` with `quotientGeneratorCoefficient ... m` |
| W_m=D(b_m) cover W, without finite generation | the indexed supremum of `T.basicOpen (quotientGeneratorCoefficient ... m)` equals `W.1`; the index is every section m of E(U) |
| well-defined R-algebra homomorphism ρ_m | `IsQuotientFractionChart` takes a bundled `→+*` out of `HomogeneousLocalization.Away`, requires all fraction values, and requires its action on `quotientFractionScalar`; this last equation is exactly R-algebra linearity along h.appLE |
| a/e^d ↦ b(a)/b_m^d, including d=0 | `degreeOneQuotientFraction ... d a` maps to the literal `Localization.mk` with numerator `quotientCoefficient ... d a` and denominator `b_m ^ d` |
| spectrum map lands in D₊(e) and defines the local restriction of F | `quotientFractionSource W b_m ≫ F = Spec.map ρ ≫ Proj.awayι ... ≫ A.relProjι U`; the middle arrow is the canonical standard-chart open immersion |
| agreement on all overlaps, also across base affines | each local morphism equals the restriction of the same F by the preceding equation, so their pullbacks to every overlap coincide |
| f/e maps to b_n/b_m | specialize the fraction equation to d=1 and `a=quotientSymmetricGenerator E U n`; the degree-one coefficient equation gives b_n |
| this ratio is a unit on the double open | the last conjunct of `IsQuotientFractionChart` asserts `IsUnit` after `awayToAwayRight` into `B[1/(b_m*b_n)]` |
| changing l to u l multiplies degree-d coefficients by u⁻ᵈ | the units-v conjunct states precisely `quotientCoefficient (v • l) d a = (↑(v⁻¹))^d * quotientCoefficient l d a` |
| every ρ_m is unchanged under frame change | `QuotientFrameIndependent` compares any two chart maps after arbitrary common scalar-preserving maps from their localization targets, hence in particular after the canonical localization isomorphism |
| affine source and base restriction compatibility | the final two conjuncts of `HasQuotientFractionCharts` give source restriction of coefficients and compatibility with `gradedAlgebraData.res`; the fraction formulas determine the corresponding restricted ρ on every homogeneous fraction |
| an S-morphism F | the first chart conjunct is `F ≫ A.relProjHom = h` |
| uniqueness and independence of all choices | F satisfies all charts for all choices; `∀ F', HasQuotientFractionCharts ... F' → F' = F` requires no canonical-map hypothesis on the competitor |
| U(ψ)=T | `ψ.GeneratesEverywhere`, the existing pointwise positive-degree generation predicate |
| F equals the canonical r of the recorded general Proj-map theorem | `ψ.IsCanonicalMap F`, the existing scheme specialization of its chart characterization; with generation everywhere this characterizes r on all of T |

Dependencies and interfaces used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`; read the full structures
  and their docstrings in the pinned source.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: imported the node's current module;
  the quasi-coherent clause uses its imported Mathlib `SheafOfModules.IsQuasicoherent`.
  Its extra `IsQuasiCoherentFiniteType` is deliberately not imposed: the assigned
  statement only asks for quasi-coherence, not the finite-type part of that record.
- `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`:
  `SymmetricAlgebraSheaf.gradedAlgebraData` and `sectionGradedAlgebra`; read all
  associated restriction and degreewise base-change declarations and docstrings.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Basic` and `.GradedAlgebraData`:
  `Scheme.GradedAlgebraData`, its grading/ring/algebra instances, `.relProj`,
  `.relProjHom`, `.relProjι`, and affine restriction isomorphisms.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `IsInvertible`, `tensorPow`, `tensorPowAddIso`; read their full signatures.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `tensorPullbackSection`, the section-normalized adjunction, and the existing
  `tensorPullback` functor. No arbitrary pullback comparison or map is introduced.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: imported the current
  tensor dependency record; the scheme tensor and its section operation are the existing
  `Scheme.Modules.tmulSection` and monoidal structure, not a second tensor construction.
- `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`:
  `HomogeneousLocalization.Away`, `.Away.mk`, `.fromZeroRingHom`; these include zero
  and nilpotent denominators. Read the constructors and `.Away.mk_surjective`.
- `Sheaf.TraceFormula.SpaceLineModuleProjMap` and `.SpaceLineModuleProjInput`:
  read `space_line_module_proj_map`, `GradedLineMap`, `.generationSet`,
  `.IsGenerationOpen`, `.IsCanonicalMap`, and `trivializedPower` in full.
- `Sheaf.TraceFormula.GradedImmersionAmpleCriterion`: reuse the already landed
  `RelativeGradedLineMap`, `.GeneratesEverywhere`, `.IsCanonicalMap` and `.evaluate`.
  The new definition node `def-trf-relative-graded-line-map` owns these declarations
  with `existing: true`. The item cites that definition node; no ampleness theorem,
  quasi-compactness or immersion hypothesis is used. Read its node
  and module; traversing its stmt/proof dependency closure found 259 nodes and did
  not find the assigned item, so this addition creates no cycle.
- Proof imports: `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections`
  (`exists_tensorPullback_affine_sections`) and `.RelativeProj.Universal`
  (chart uniqueness/cover independence). The symmetric universal property and grading
  are already publicly imported. The atlas and scheme-morphism-gluing proof nodes have
  no recorded Lean module in this checkout, so no speculative import was added for them.

Edge cases checked before writing: T empty and W empty; all-zero or nilpotent b_m give
empty generator charts with zero localization rings; d=0 gives denominator 1; m=0 is
allowed; E=0 can have a line quotient only on the empty source; arbitrary infinite
modules index an unrestricted supremum; no affine intersections or separatedness are
assumed. Over a field E=k² with quotient coefficients (a,b), the fractions give the
usual [a:b], and rescaling the frame cancels in all coordinate ratios. All schemes and
module sections are in the same explicit universe u as the dependency interfaces;
there are no independent small test universes or auto-bound variables.

Searches performed:

- `msearch.py ... leanfinder`: “A surjective line bundle quotient of a pullback defines
  a unique relative Proj morphism with homogeneous fraction charts”. Eight hits,
  including `Proj.fromOfGlobalSections`, `toSpecZero`, `awayι_toSpecZero` and chart
  pullback lemmas. None states the relative quasi-coherent quotient assertion.
- `msearch.py ... loogle`: `AlgebraicGeometry.Proj.fromOfGlobalSections`. Six hits:
  the absolute construction and its scalar, preimage and restriction lemmas. They do
  not include the graded extension from q or the full relative statement.
- `msearch.py ... grep`: `fromOfGlobalSections|line.*quotient|quotient.*line` in
  `AlgebraicGeometry`. Seven hits, principally absolute Proj plus unrelated elliptic
  curve coordinate quotient results.
- `msearch.py ... leansearch`: “Surjective invertible quotient defines a relative
  Proj morphism and a map on homogeneous localizations”. Eight hits, including
  `basicOpenToSpec`, `basicOpenIsoSpec`, `toBasicOpenOfGlobalSections` and
  `HomogeneousLocalization.mk_surjective`. These are reusable local ingredients,
  not the assigned assertion.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for homogeneous fractions and
  line quotient/Proj interfaces found the canonical symmetric algebra, space-level
  graded maps, the existing `RelativeGradedLineMap` specialization and section-ring
  coefficient theorems. Exact-item-id search in both roots found no implementation.
- `tools/blueprint_refs.py search 'graded line'` returned no blueprint nodes;
  `rg` of DAG records found the interface only as auxiliaries of the ampleness-criterion node.
  The repair adds the definition node below to own the existing scheme interface.
  The remaining helpers belong to this node's explicit fraction-chart specification.

No statement correction or disputed statement. The item JSON changes only lean and
adds `def-trf-relative-graded-line-map` to stmt_deps. No upstream source or shared file was
edited and no git command was run directly. Every compile uses the prescribed
scompile.py wrapper. The final module compiles in both sandbox and actual module mode
within 60 seconds, with no errors or non-sorry warnings.

## Worker self-check

I reread the node and the complete module after compilation. This is the worker's own
second pass; the dispatch explicitly forbids another agent, and the maintainer supplies
independent review. The first draft only asserted existence/uniqueness of a canonical
morphism: this omitted the node's explicit local conclusions. I added the cover,
coefficient, ring-homomorphism, scalar, spectrum, overlap-unit, frame and restriction
predicates, and checked every clause in the table above. I also replaced nested ∃!
assertions whose predicates included all auxiliary properties with explicit uniqueness
among every extension of q and every morphism satisfying the formulas; competitors
need not separately assume generation or canonicality. Degree-one membership is typed
in the actual bundled grading, not an untransported private grading. Checking d=0,
empty charts and arbitrary qcoherent E found no missing assumption or false edge case.


## New nodes

`def-trf-relative-graded-line-map` owns the landed structure
`AlgebraicGeometry.Scheme.Modules.RelativeGradedLineMap` and its `evaluate`,
`GeneratesEverywhere`, and `IsCanonicalMap` definitions in
`Sheaf.TraceFormula.GradedImmersionAmpleCriterion`, with `existing: true`.
No additional Lean module or duplicate definition is introduced. The source is
Stacks Constructions 01O9, the input and generation open before
`lemma-invertible-map-into-relative-proj`, and characterization (3), read in full.
The additive components, scalar law, degree-zero unit, product law, and restriction
law are the fields `component`, `smul`, `one`, `mul`, `restriction`.
Evaluation is canonical tensor pullback through `boundaryPullbackPowIso`.
Generation is the explicit nonzero residue condition in `GeneratesEverywhere`.
The canonical-map predicate is the over-base equality and all trivializing open
chart equations with `Proj.fromOfGlobalSections`, precisely `IsCanonicalMap`.
These definitions accept an arbitrary module; the generation interpretation uses
invertible L. No existence theorem, ampleness, immersion, or quasi-compactness
hypothesis is introduced.

Repair searches: `msearch.py` LeanSearch “Graded algebra map into tensor powers of a
line bundle generation locus canonical relative Proj morphism” returned eight
tensor/graded-algebra hits; LeanFinder “Relative graded line map affine components
tensor powers generation everywhere canonical map relative Proj” returned eight
absolute Proj/chart hits; grep `RelativeGradedLineMap|GradedLineMap|fromOfGlobalSections`
in AlgebraicGeometry returned five absolute Proj hits. I read
`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean` around 443: this is an
absolute chart ingredient. Local `rg` of both source roots found the existing four
scheme declarations only; DAG search found no definition node owning them. The
similar `def-trf-space-line-module-proj-input` instead owns cartesian algebraic-space
test data. `blueprint_refs.py search 'relative graded line map'` returned zero
matches and `ancestor` returned `lem-trf-local-term-locality`. Actual queries are
in `searches.jsonl`, with their results in the new node's `mathlib_searches`.

## Repair of return H2/H12

Returned head: 66d14ec28b8b. Comparing the retained packet with the live node found
only `lean` and the added theorem dependency different. The initial packet dry run
passed (e4669d936ef), but its mechanical pass did not resolve the ownership defect.
The item now adds only `def-trf-relative-graded-line-map` to the live dependencies.
The added `lem-trf-graded-immersion-ample-criterion` edge is removed. Its conclusion
is not needed. The Lean module and mathematical statement are retained unchanged,
as the return approved their clause-by-clause content. No dependency module is
required: the return explicitly permits an existing:true record on landed definitions.

## Second reading by Q53

This is the dispatch-authorized worker self-check, not an independent review.
I read the new node against all four declarations at lines 44--110: each component
law, actual pullback evaluation, stalk maximal-ideal test, and every trivializing
chart binder is represented. The item's hypotheses and clauses remain those in
the table: arbitrary quasi-coherent E, Epi q, unique extension, degree-one and unit
normalization, all generator charts and d=0 fractions, scalar and spectrum clauses,
overlap units, frame change, restrictions, uniqueness among chart-satisfying maps,
generation, and canonical identification. This repair changes the DAG owner only.
Empty schemes, zero/nilpotent denominators, degree zero, arbitrary positive degrees,
arbitrary degree-zero algebra, and infinite E remain allowed. No new sorry is added.

Repair validation: scompile.py passed in sandbox (18.8 s) and library (21.1 s) mode,
with no errors or warnings. Exact stored signatures, permitted item fields, all new-node
citations, line width and the sole main-theorem sorry were checked. The new node
dependency closure does not reach this item, so the added edge creates no cycle.

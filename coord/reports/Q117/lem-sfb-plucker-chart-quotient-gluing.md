## Worker report

This repaired delivery states `AlgebraicGeometry.Plucker.chart_quotient_gluing` in
`Sheaf.AlgebraicGeometry.PluckerChartQuotientGluing`, with proof `sorry`. It imports
Q118's landed `Sheaf.AlgebraicGeometry.PluckerDeterminantLocusCharts` and uses those
exact coordinate objects. It adds only the sheaf restriction/pivot helpers and the
previously reviewed quotient/frame predicates. All definitions have actual data.
The new definition node `def-sfb-plucker-determinant-coordinates` records the existing
coordinate declarations with `existing: true`; no coordinate code is added.
There are no dependency repair modules.

Hypothesis-by-hypothesis and clause-by-clause correspondence (the paper's rank is
Lean's `r + 1`, so write r_paper = r_Lean + 1):

- `N r : ℕ` and `_hrN : r + 1 < N` encode exactly the integers 0 < r_paper < N.
  `PluckerDeterminantLocus.Index N r` is the cardinality-(r+1) finset subtype;
  `columns I` is its increasing enumeration. `Fin N` relabels 1,...,N by 0,...,N-1.
- `PolynomialRing N r` is exactly `MvPolynomial (Index N r) ℤ`. There is no ULift
  of the variable type and no second polynomial ring in this delivery.
  `orderedCoordinate` is the signed ordered coordinate: the incidence determinant
  vanishes on repeats and gives the sorting sign on a permutation of I.
- `replacementMatrix`, `relation` and `relationsIdeal` are the displayed C, F and
  plain ideal span, with exponent r_Lean = r_paper-1. `CoordinateRing` is B/H.
  `quotientGrade N r d` is exactly the image of the homogeneous degree-d polynomial
  submodule; the imported `quotientGradedRing` is the grading on these fixed pieces.
  Its decomposition is uniquely determined by the direct-sum inclusion/sum map.
- The fixed integer scheme is literally `Proj (quotientGrade N r)` in universe 0.
  Every chart is literally `Proj.basicOpen (quotientGrade N r)
  (Ideal.Quotient.mk (relationsIdeal N r) (MvPolynomial.X I))`.
  Every matrix entry is Q118's `normalizedMatrix I a j` sent to sections by
  `Proj.awayToSection`. Its numerator is the signed single-column replacement and
  its denominator is p_I. `matrixOn` only restricts these entries to a subopen.
  The first conjunct asserts that the pivot columns are the identity on every
  subopen of U_I, including U_I itself.
- `pivot I K W hI` is the ordered K-column submatrix D_IK. The second conjunct
  states that its determinant is a unit, equals the restriction of
  `Proj.awayToSection ... (fraction I (columns K))`, and that
  M_K = D_IK⁻¹ * M_I on each W lying in both charts. The displayed section is the
  exact p_K/p_I fraction from Q118, not an independent ratio construction.
- The third conjunct is g_IL = g_KL * g_IK on every subopen of a triple overlap,
  and g_II = 1, with g_IK defined by the inverse pivot matrix. The unit determinant
  assertion in the preceding conjunct makes this inverse an actual matrix inverse.
- The fourth conjunct supplies an actual `Q : (Proj (quotientGrade N r)).Modules`,
  an actual quotient `q`, `Epi q` and `Q.IsFiniteLocallyFreeOfRank (r+1)`.
  Its actual frames identify each restriction with the free sheaf of rank r+1.
  `quotientMatrix ... = (normalizedMatrix I).map (Proj.awayToSection ...)` gives
  the specified local quotient matrices. `NormalizedFrame` states that the pivot
  inclusion followed by q in that frame is the identity, giving the right inverse.
  `frameChange ... = (pivot I K W hI)⁻¹` pins the actual transitions to g_IK.
  The free-sheaf labels here use `ULift.{0}`, matching this fixed scheme's universe.
- The final conjunct retains every `T : Scheme.{u}`, actual module Q and quotient q,
  with exactly `Epi q` and finite local freeness of rank r+1 as hypotheses.
  `QuotientCharts` supplies opens U_I whose underlying sets equal `pivotLocus q I`,
  defined as the locus where the pivot map is an isomorphism at the stalk. For maps
  between finite free modules of the same rank this is exactly the frame locus.
  `⨆ I, U I = ⊤` asserts covering. The normalized frame exists and is unique among
  all normalized frames. Inverting the pivot map is the unique such normalization,
  so this is exactly uniqueness of the normalized quotient matrix. Both its
  inverse-K-column matrix formula and the actual frame change are stated on overlaps.
- For every `T' : Scheme.{u}` and every `f : T' ⟶ T`, `PullbackCharts` is applied
  to the explicit `Sigma.desc` map on pulled-back standard generators. Its i-th
  component is `homOfGlobalSection` of q(e_i) sent through the section-normalized
  `tensorPullbackSectionAdjunction` unit. This is the canonical tensor pullback
  quotient, with its free source identified on generators; no arbitrary comparison
  is assumed. `PullbackCharts` states that this quotient remains epi and rank r+1,
  supplies normalized frames on f⁻¹(U_I), identifies these exact opens with the
  pulled-back pivot loci, and equates their matrices with entrywise `f.app (U I)`
  applied to the original matrix. Thus identity maps and every arbitrary f remain.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.PluckerDeterminantLocusCharts`:
  `AlgebraicGeometry.PluckerDeterminantLocus.Index`, `columns`, `PolynomialRing`,
  `orderedCoordinate`, `replacementMatrix`, `relation`, `relationsIdeal`,
  `CoordinateRing`, `quotientGrade`, `quotientGradedRing`, `fraction`,
  `normalizedMatrix`; its `closedImmersion_and_charts` supplies proof step 1 on
  exactly the same objects. Its source was also read from the live server with
  `scompile.py --source Sheaf.AlgebraicGeometry.PluckerDeterminantLocusCharts`.
- Mathlib `MvPolynomial`, `Matrix.det`, `Ideal.Quotient.mkₐ`, `AlgebraicGeometry.Proj`,
  `Proj.basicOpen`, `Proj.awayToSection` and `Scheme` are the recorded definitions
  for the polynomial, determinant, quotient, Proj and scheme nodes. These are reused,
  including the actual quotient grading and standard-open section map.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules` is
  the transparent abbreviation of `SheafOfModules`; `X.Modules` is precisely this
  category for the Zariski structure-ring sheaf.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank` is the recorded locally free predicate.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback` and `tensorPullbackSectionAdjunction`, whose unit
  is normalized on actual sections, give exactly the recorded pullback interface.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`: `freeMatrix`,
  `restrictFreeIso`, `restrictCompIso`; `SheafOfModules.freeMap` gives pivot inclusion.
  `WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator` supplies the
  existing `homOfGlobalSection`. `RingedSpace.moduleStalkFunctor` is reused from
  `WeilConjectures.Algebra.Homology.ModuleStalkFunctor` for the intrinsic frame locus.

The plain proof imports retain the adjugate, residue-field/basic-open, local-unit,
sheaf-gluing, finite-free stalk, stalk-exactness and left-inverse-minors interfaces.
Q118's now-landed module also supplies the determinant-chart proof dependency, whose
objects are used publicly in this statement. The downstream abstract Grassmannian
module is not imported: its proof depends on this result. The canonical pullback map
is written inline using existing primitives instead of duplicating its definition.

Edge cases checked: Lean r=0 means paper rank 1, and includes its zero determinant
relations and ordinary projective charts. Rank N-1 remains. N=0, paper rank 0 and
rank N are excluded exactly by 0<r_paper<N. Repeated tuples give zero, permuted tuples
give the sorting sign. Empty schemes/opens, the zero section ring, nonaffine T,
zero divisors and nonunit nonpivot minors are permitted. No field, reducedness,
sectionwise surjectivity or cancellation hypothesis appears. Arbitrary-T and
pullback clauses retain universe u, while the fixed integer construction uses its
landed universe-0 definitions.

Searches retained from the saved packet: LeanFinder for normalized quotient-pivot
gluing found generic Grassmannian, Proj-overlap and representability-gluing APIs;
Loogle `"Grassmannian", "chart"` had zero hits; msearch grep
`Plucker|plucker|pivot|Grassmann` in Mathlib/AlgebraicGeometry had zero hits. These
found no existing version of this theorem. Repair searches rerun the latter two
queries, both with zero hits, and LeanFinder for normalized quotient pivot matrices
on Plucker charts and canonical base change. Project rg for Plucker/plucker now finds
Q118's landed coordinate module, so it is reused. Project rg for `matrixOn`, `pivot`,
`QuotientCharts` found no existing sheaf-gluing construction under these names.
The earlier proposed coordinate-data module was removed when Q118 landed. The new
definition node requested by this return records Q118's declarations without adding code.

## Repair of return L H2

Return L names immutable head `f01d2b7ea32e`. Its one defect is the addition of
`lem-sfb-plucker-determinant-locus-charts` to `stmt_deps` although the statement uses
only that module's definitions. The initial saved-packet dry run passed mechanically
(commit `14bec8f79d1`); that did not discharge this mathematical metadata review.

Added `def-sfb-plucker-determinant-coordinates` as requested and replaced the theorem
id in the item's `stmt_deps` with this definition id. The determinant-chart theorem
remains in the unchanged `proof_deps` for proof step 1. Compared with the current live
read clone, the item changes only `lean` and `stmt_deps`; its statement, proof, proof
dependencies and all other fields are unchanged. The prescribed delivery wrapper
rebases the packet on current main. No direct Git command or shared-tree edit was used.

The Lean module is byte-identical to the saved returned module, SHA256
`cc3d5c8d1bb4aaf102734451125f32e0321cae91a4535351bda393e11a97a460`.
It retains its existing public import: the coordinate definitions are used publicly,
and the assertion theorem is a proof dependency in the same module. No added sorry,
extra theorem, duplicate definition, or change of mathematical statement is needed.

## New nodes

`def-sfb-plucker-determinant-coordinates` is a definition node with `existing: true`
on `Sheaf.AlgebraicGeometry.PluckerDeterminantLocusCharts`, whose full source and
coordinate docstrings were read. Its primary declaration is
`AlgebraicGeometry.PluckerDeterminantLocus.normalizedMatrix`. Its declarations list
also records `Index`, `PolynomialRing`, `columns`, `orderedCoordinate`,
`replacementMatrix`, `relation`, `relationsIdeal`, `CoordinateRing`, `quotientGrade`,
`polynomialGradedRing`, `quotientGradedRing` and `fraction`, all in that namespace.
It deliberately excludes the assertion `closedImmersion_and_charts`.

The definition introduces N and r as natural numbers and k=r+1. Its k-subsets with
increasing enumeration are exactly `Index N r` and `columns`. Its B is
`PolynomialRing N r`; the incidence-determinant sum for p_t is exactly
`orderedCoordinate t`. The updated tuple is `Function.update (columns I) a j`, so
its C, F, H and A are exactly `replacementMatrix`, `relation`, `relationsIdeal` and
`CoordinateRing`. Its A_d is the explicit image submodule `quotientGrade N r d`.
`polynomialGradedRing` and `quotientGradedRing` supply precisely the grading on these
fixed components. The helper `quotientGrade_exists` postpones only the unique grading
proof; it does not choose an unspecified ring or components. Finally its p_t/p_I and
replacement-entry matrix are exactly `fraction I t` and `normalizedMatrix I`.
All thirteen named declarations were read in the landed source; none is copied.

Sources read: `literature/stacks-project/constructions.tex`, Tag 089T,
`lemma-gkn-representable`, especially increasing pivot subsets and the normalized
quotient charts, and Tag 01M4, `lemma-standard-open`, for homogeneous fractions.
The homogeneous determinant presentation is explicitly the agent completion already
used in the setup of the landed determinant-chart node, rather than an assertion that
089T prints these equations. The four definition dependencies are exactly
`def-weil-pbc-mv-polynomial-ring`, `def-weil-pbc-matrix-determinant`,
`def-weil-pbc-algebra-hom-quotient`, and
`def-nagata-homogeneous-localization-degree-zero`; their records and Mathlib
construction signatures were read.

Fresh logged searches, copied verbatim from `searches.jsonl` into the new node:
LeanSearch, "Plucker determinant coordinates quotient graded ring normalized matrix
homogeneous localization" (eight generic homogeneous-localization hits);
LeanFinder, "Polynomial ring on Plucker minor coordinates modulo determinant
relations with degree zero localized normalized matrix entries" (eight generic
Jacobian/presentation hits); msearch grep, `Plucker|plucker|normalizedMatrix|relationsIdeal`
in Mathlib `AlgebraicGeometry` (zero hits). Direct rg of `lean/WeilConjectures` with
that expression found no hits. Direct rg of `lean/Sheaf` found Q118's existing
coordinate module, which is reused. Direct rg of DAG definition ids found no Plucker
coordinate definition; the nearby Plucker nodes are assertions, including the owner
of the existing code. `tools/blueprint_refs.py search Plucker` returned zero blueprint
nodes, and `ancestor lem-sfb-plucker-chart-quotient-gluing` returned None; accordingly
`blueprint.from.node` is null and via prepends the item to its inherited chain.

Definition edge cases: k=1 (Lean r=0) gives the ordinary projective coordinates and
zero determinant relations; ordered repeated tuples give zero and permutations carry
their sorting signs. The data remain defined when k>N (the index type is empty),
when N=0, on zero rings, and for nilpotent or zero denominators in the homogeneous
localization. No theorem about affine charts, an identity pivot, invertible minors,
or gluing is added to this definition. The item itself continues to assume k<N.

## Second reading by Q117

Author's separate self-check, with both JSON files and the unchanged Lean file open;
the dispatcher prohibits subagents, and the maintainer supplies independent review.
The reviewed five-conjunct statement still has exactly the bound r+1<N, identity
pivot columns, the unit determinant p_K/p_I and left inverse-pivot multiplication,
cocycle order g_IL=g_KL*g_IK, actual glued quotient with epi/rank/normalized frames,
and arbitrary Scheme.{u} quotient and canonical Sigma.desc pullback clauses.
The eight-step natural-language proof and its single sorry are unchanged.

For the new node I checked each displayed formula against its existing declaration,
including the determinant-incidence sign, exponent r=k-1, plain generated ideal,
image grading, and fraction numerator and denominator. The new node is solely a
record of the data; the determinant-chart assertion remains only in proof_deps.
The item's non-lean field delta is exactly addition of this definition to the live
base stmt_deps. The Lean signature in the item record remains verbatim, and the new
existing record's signature is verbatim from Q118's source. No disputed statement or
statement correction is present. This repairs the sole numbered point H2 of return L.

## Validation

The saved packet's initial prescribed deliver2.py --no-push passed, but the required
H2 dependency repair was then applied before delivery. The repaired packet contains
one unchanged Lean module, the item node, one new existing-definition node, and this
report. Final server compile and preflight results follow below.

Final prescribed scompile.py: sandbox and library passes succeeded (28.1 s and
29.2 s), with no errors or warnings in the output. Source self-check confirmed the
unchanged Lean SHA256, both verbatim signatures, exactly the intended dependency
separation, the new node fields and citations, and indent-1 Unicode JSON layout.

The first repaired dry run found two metadata-format issues: for an existing
declaration the signature starts at `def` (excluding the `noncomputable` modifier),
and the current new-node schema requires `import_flags`. The record now uses the
source signature from `def normalizedMatrix` to `:=`, and the node carries
`import_flags: []`. These are metadata-only changes.

Final repaired deliver2.py --no-push: OK, commit `b464c60b16e` passes
the server preflight and compilation. All H2 changes were present in that packet.

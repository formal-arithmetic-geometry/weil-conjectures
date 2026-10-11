## Worker report

The module `Sheaf.CategoryTheory.HypercohomologyFirstPage` states
`CategoryTheory.Functor.exists_hypercohomology_firstPage`. Its sole theorem proof is
`sorry`; no definition, instance or proof is introduced. The server compiled it cleanly
in 6.3 seconds, with no warning. All universes and variables are explicitly bound.

Hypothesis-by-hypothesis and clause-by-clause:

- The functor v of def-sp-truncation-couple is `F : A ⥤ B`, with both categories
  explicitly `Abelian` and `IsGrothendieckAbelian` at their hom universes. Additivity
  is `[F.Additive]`; left exactness is `[PreservesFiniteLimits F]`, exactly the
  Mathlib record of def-sp-left-exact-additive. No additional cohomology bound a is
  assumed: the original says “v as in” that node, not its auxiliary truncation input.
- The bounded-below K is `K : CochainComplex.Plus A`. The Stacks-indexed resolution
  is `I : HomologicalComplex₂ A (up ℤ) (up ℕ)`, with ONE bicomplex augmentation `a`
  from `single₀` applied to every term of K. The resolution degree is natural and
  then extended by zero; the complex degree is integer, with arbitrary lower bound
  `hbelow`, not normalized to zero.
- The rows A^{bullet,s} resolving K^s are Stacks columns `I.X s`:
  `hterms` gives injectivity of every term, and `hrows` gives `QuasiIso (a.f s)`.
  These are precisely the fields of Mathlib `InjectiveResolution`.
- Being Cartan--Eilenberg also includes the cycles, boundaries and cohomology
  resolutions: `hinjective` gives their termwise injectivity and `hquasi` the three
  quasi-isomorphisms induced by the SAME augmentation. These are the five properties
  of `exists_cartanEilenberg_resolution`; `hbelow` replaces its normalized zero bound.
  The corrected column-cohomology assertion is the cohomology part of these fields.
- `CartanEilenbergPresentation.mappedFunctor F` applies F, extends the natural
  resolution degree by zero to ℤ, and `flip` puts the resolution degree first.
  Mathlib's `.total (up ℤ)` is then exactly the blueprint total with its stated signs.
  Grothendieck coproducts provide `HasTotal`; no extra existence hypothesis is added.
- The existential `L` is a filtration by SUBCOMPLEXES of that total. The first
  conclusion fixes every degreewise step to the recorded `.secondFiltration n`.
  Its finite image-sum formula remains valid for this half-plane bicomplex:
  resolution degree n-s >= 0 forces s <= n, while s below the lower bound vanishes.
- `E : CohomologicalSpectralSequence B 0` is the cohomological spectral sequence.
  `e₀`, the page-zero differential equation and the `complexCycles/complexBoundaries`
  quotient clause render the associated filtered-complex spectral sequence in the
  form of `filteredComplex_associated_spectralSequence`. They specify which
  filtration yields the sequence rather than postulate an unrelated E1 page.
- The node lists (resolution degree r, complex/filtration degree s). Mathlib lists
  (filtration degree s, complementary degree r), so `e₁ r s` is exactly
  `(E.page 1).X (s,r) ≅ (F.rightDerived r).obj (K.obj.X s)`, for every natural r and
  integer s. The `q < 0` clause states the zero extension of R^rF to negative r.
- The d1 equation uses `(E.page 1).d (s,r) (s+1,r)` and `(F.rightDerived r).map
  (K.obj.d s (s+1))`, so it renders the differential induced by K. The isomorphisms
  e₁ are the signed row identifications: Stacks 0130 has (-1)^r in d1 for the second
  filtration; multiplying at (s,r) by (-1)^(rs) cancels it. This is a normalization
  of the identifications, not a different total complex or a different filtration.
- For EVERY `ρ : KInjectiveResolutionChoice K.obj`, `c n` identifies total cohomology
  with the RECORDED `F.rightDerivedCohomologyWithResolution K ρ n`. `H n` is its
  finite decreasing filtration, fixed to the image of H^n(L.step p) transported
  through c. The last clause identifies every sufficiently late page term with
  `(H n).gradedPiece p` in total degree n = p+(n-p). This is the bounded convergence
  case of def-sp-convergence: finite filtrations are separated, exhaustive and
  inverse-limit complete; the cycle/boundary towers stabilize here. The arbitrary
  lower bound excludes no negative-degree cases.
- Independence of resolution is expressed by quantifying over every I and every ρ:
  every Cartan--Eilenberg total computes the same derived cohomology, up to the
  cohomology comparison isomorphisms. No independence of the E1 spectral sequence
  itself or of its entire filtration from all choices is asserted by the node.

Dependency declarations read and reused:

- `Sheaf.CategoryTheory.TruncationCouple`, `CategoryTheory.truncationCouple`: its
  signature and docstring give the Grothendieck/left-exact/additive setting; no
  truncation construction is duplicated or needed as an argument here.
- `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`, `InjectiveResolution`
  (fields at lines 43–55), and `Mathlib.CategoryTheory.Preadditive.Injective.Basic`,
  `Injective` (line 32): used literally in the resolution hypotheses.
- `Mathlib.CategoryTheory.Abelian.RightDerived`, `Functor.rightDerived` and
  `InjectiveResolution.isoRightDerivedObj` (lines 110–120): R^rF on objects and its
  resolution computation. AdditiveFunctor line 42 and Preserves/Finite line 44
  supply the other clauses of def-sp-left-exact-additive.
- `Sheaf.CategoryTheory.KInjectiveBridge`, `KInjectiveResolutionChoice`,
  `Functor.rightDerivedComplexWithResolution`, `rightDerivedCohomologyWithResolution`:
  full signatures and docstrings read; the last is the abutment in the statement.
- `Sheaf.CategoryTheory.KInjectiveComputes`, `Functor.kInjective_computes`: full
  signature/docstring read; its comparison and bounded-below injective clauses
  provide the resolution-independent comparison described in the proof docstring.
- `Sheaf.CategoryTheory.DoubleComplexTotal`, `HomologicalComplex₂.secondFiltration`,
  and Mathlib `HomologicalComplex₂.total`, `.flip`: reused without a private total
  or filtration definition, including the finite-image-sum formula.
- `Sheaf.CategoryTheory.ExactCoupleConvergence`, `BigradedExactCouple.ConvergesTo`,
  `AbutsTo`, `WeaklyConvergesTo`, `IsInverseLimit`: read; the finite-filtration
  specialization is rendered by image filtration and stable-page graded isomorphisms.
  This theorem does not construct a separate exact couple argument or a new notion
  of convergence.
- Additional already-landed nodes: `lem-sp-cartan-eilenberg-exists` in
  `Sheaf.CategoryTheory.CartanEilenbergExists`, with its five shared-augmentation
  conditions; `def-sp-cartan-eilenberg-presentation` in
  `Sheaf.CategoryTheory.CartanEilenbergPresentation`, whose generalized
  `mappedFunctor` is used directly (no object presentation is assumed); and
  `lem-sp-filtered-complex-associated-spectral-sequence-construction` in
  `Sheaf.CategoryTheory.FilteredComplexSpectralSequence`, whose page-zero and
  cycle/boundary statement fixes the associated sequence. These three landed nodes
  were added to stmt_deps; no new or dependency module was needed.

Edge cases checked: zero K and zero bicomplex; K supported in a negative degree
(e.g. -3), where hbelow and the interval filtration still apply; r=0, including
its actual d_K map; r=1, where the unnormalized d1 really has a minus sign;
s outside the support, where both first-page sides vanish; total degrees below
hbelow, where the diagonal is zero; p>n, where the filtration sum is empty.
Arbitrary object and hom universes remain explicit; there is no independent
small test-index universe or characteristic hypothesis.

Searches actually run:

- msearch.py leanfinder: “hypercohomology spectral sequence Cartan Eilenberg resolution
  first page derived functors”: 8 hits (HomComplex.leftHomologyData', representation
  resolution Ext isomorphisms, InjectiveResolution.ofCocomplex_d_0_1, groupCohomologyIso,
  ProjectiveResolution.fromLeftDerivedZero', InjectiveResolution.toRightDerivedZero');
  none states this spectral sequence.
- msearch.py loogle: “CohomologicalSpectralSequence, InjectiveResolution.isoRightDerivedObj”:
  0 hits, unknown identifier CohomologicalSpectralSequence (service result, not a
  claim that the identifier is absent from the pinned source).
- msearch.py grep: “hypercohom|Cartan.?Eilenberg|secondFiltration” in Algebra/Homology:
  0 hits. Direct rg of WeilConjectures found the Grothendieck E2 spectral sequence,
  whose source/signature was read: it concerns a pair of functors and an object,
  not an arbitrary complex, its E1 page or its specified second filtration.
- Direct rg of project lean/Sheaf found CartanEilenbergProperties, presentation,
  filtered-complex spectral sequence and comparison modules; all relevant
  signatures/docstrings were read and existing notions reused. No exact theorem.
- Direct rg for “thm-sp-if-e1” in WeilConjectures and dag/lean_names_upstream.json:
  no matches. Direct rg for “exists_hypercohomology_firstPage” in Mathlib,
  WeilConjectures and lean/Sheaf: no matches before writing.

## Statement corrected

Only the column-cohomology wording and the normalization implicit in d1 were
clarified. Source read online: https://stacks.math.columbia.edu/tag/015H (condition 6)
and https://stacks.math.columbia.edu/tag/0130 (second-filtration first-page differential).
The local literature copy is absent on this machine. The old statement is reproduced
verbatim below and in statement_change.old_statement. A noninjective X in degree zero
shows why a cohomology RESOLUTION cannot be replaced by the object X in each column.
Tag 0130's sign is real for r=1; the stated (-1)^(rs) normalization removes it without
changing any page term or the abutment. The proof paragraph now records this calculation.
No unit statement changes: dag/units/sk-prop-av-pqf-finite.json has the geometric
“proper and quasi-finite implies finite” proposition, not this auxiliary theorem.

Old statement:

Let $v$ be as in [def-sp-truncation-couple] and let $A^{\bullet,\bullet}$ be
a Cartan--Eilenberg resolution of a bounded-below complex $K^\bullet$: the
row $A^{\bullet,s}$ is an injective resolution
[def-sp-injective-resolutions] of $K^s$, and the column cohomologies are the
$\mathcal H^s(K^\bullet)$. Then the filtration of the total complex by the
*second* degree gives the spectral sequence

$$
 E_1^{r,s}=R^rv(K^s)\Longrightarrow
 \mathcal H^{r+s}(RvK^\bullet),
$$

$d_1:E_1^{r,s}\to E_1^{r,s+1}$, induced by the differential of $K^\bullet$,
and the abutment is the cohomology of the derived functor of $K^\bullet$,
independent of the resolution.

All nodes whose stmt_deps or proof_deps name this item were found by a full DAG scan
(the textual rg hits that only mention it in notes were excluded). No citer was edited.

- lem-pc-grothendieck-edge-cocycle: holds=true. Its edge comparison uses degree-zero resolution cohomology, where the sign normalization is 1; the E1 collapse argument is unchanged.
- lem-pc-grothendieck-ss-double-complex-model: holds=true. The actual Cartan--Eilenberg conditions and R^rG(F(I^s)) page remain; the only surviving r=0 row has sign normalization 1.
- lemma-weil-pbc-leray-acyclicity: holds=true. Uses the total K-injective resolution and resolution-independent derived cohomology; neither changes.
- lem-finrepair-finite-surjection-cancellation: holds=true. Uses constructibility through the spectral-sequence route; its terms, abutment and finite filtration remain unchanged.
- thm-fin-projective-line-constructible: holds=true. Uses E1 terms and convergence to prove constructibility; its swapped labelling is only an index convention and remains usable.
- lem-weil-pbc-hypercohomology-e1-pullback-functorial: holds=true. The same (-1)^(rs) factor in source and target cancels in the naturality square, so E1 pullback maps retain their stated form.
- lem-weil-pbc-etale-cohomology-limit-complex-systems: holds=true. Uses the terms, natural E1 maps and finite abutment filtration; the common sign normalization leaves each comparison unchanged.

## Second reading by G1

Independent reading of the corrected node first, then the 109-line module and
its dependency declarations. Verdict: the statement renders the corrected node;
no Lean or node repair was needed. I left both unchanged and added this audit.

Source check before the Lean check: read Stacks Tags
[015H](https://stacks.math.columbia.edu/tag/015H) and
[0130](https://stacks.math.columbia.edu/tag/0130), then fetched and read their
actual `derived.tex` and `homology.tex` source into the item's scratchpad.
In `derived.tex`, `definition-cartan-eilenberg` lists the arbitrary horizontal
lower bound, zero negative resolution degrees, and the term, cycle, image and
cohomology resolutions. Condition (6) is a resolution of H^s(K), not H^s(K)
itself in every resolution degree. In `homology.tex`, `lemma-ss-double-complex`
item (4) gives the second-filtration differential sign. With blueprint indices
(resolution r, complex s), changing the identification by (-1)^(rs) changes the
d1 conjugation by (-1)^r and removes that sign. This also works for negative s.
Read `lemma-two-ss-complex-functor` in `derived.tex`: its first filtration uses
Stacks' opposite order of the two degrees and gives the same E1 terms, derived
abutment, and finite filtrations. Thus the corrections follow the source and do
not make the statement easier. The source assumes abelian categories here;
the stronger Grothendieck setting is already required by this node's explicit
reference to def-sp-truncation-couple, rather than added by the worker.

The node's objects, hypotheses and conclusions, matched individually:

1. Source and target Grothendieck abelian categories: `{A : Type uA}` with
   `Category.{vA}`, `Abelian`, `IsGrothendieckAbelian.{vA}`, and the separate
   corresponding B binders. Read the signature and definitions in
   `TruncationCouple.lean`; these are precisely its functor's categories. PASS.
2. Left exact additive v: `(F : A ⥤ B)`, `[F.Additive]`,
   `[PreservesFiniteLimits F]`. Read the defining Mathlib classes and the
   recorded right-derived-functor declaration. Preservation of finite limits
   expresses left exactness in the abelian setting. The truncation node's
   extra input a concerns its own K, not v, and is not needed here. PASS.
3. Bounded-below K: `(K : CochainComplex.Plus A)`; no zero lower-bound
   normalization. PASS.
4. Cartan--Eilenberg double complex and its common augmentation: integer
   complex degree and natural resolution degree in `I`, together with the
   bicomplex map `a` from termwise `single₀`. Read the full signatures and
   docstrings of `exists_cartanEilenberg_resolution` and
   `CartanEilenbergPresentation.mappedFunctor`; the latter works on any I
   and does not require an object presentation. PASS.
5. Uniform lower bound and nonnegative resolution degree: `hbelow` gives
   an arbitrary integer b for all columns; the natural inner index and
   `mappedFunctor`'s extension by zero give zero negative resolution degrees.
   These are conditions (1) and (2) of 015H. PASS.
6. Each blueprint row resolves K^s: `hterms s r` is injectivity of every
   inner term, and `hrows s` is the augmentation quasi-isomorphism. Read
   `InjectiveResolution` in Mathlib: these are exactly its substantive fields;
   homology exists automatically in an abelian category. PASS.
7. Cycle, boundary and cohomology resolutions: `hinjective` supplies all
   three termwise injectivity conditions; `hquasi` supplies their induced
   augmentation quasi-isomorphisms, using this same a. `image (I.d (s-1) s)`
   represents B^s, equivalently the source's images with the index shifted.
   Read the corresponding dependency module; no private notion or stronger
   Cartan--Eilenberg hypothesis occurs. PASS.
8. Total of v(A), filtration by second degree: the flipped
   `mappedFunctor F` total has blueprint resolution degree first. The first
   conclusion fixes `L.complexStep p n` to its `secondFiltration n` step p.
   Read `DoubleComplexTotal.lean`: this is the image sum over p <= s <= n.
   Even with negative complex degrees this is precisely the desired sum,
   since resolution degree n-s is nonnegative. L is a filtration by actual
   subcomplexes, not just unrelated subobjects in each degree. PASS.
9. The spectral sequence of that filtration: `CohomologicalSpectralSequence B 0`
   has bidegree (t,1-t) on page t; read Mathlib's structure and its successor
   homology isomorphisms. `e₀`, its differential equation, and the page-t
   cycle/boundary quotients are the clauses of the recorded
   `filteredComplex_associated_spectralSequence`, which I read in full.
   The cycle and boundary definitions were also read. These clauses express
   the existing associated-sequence interface; no second definition is made.
   PASS.
10. E1^{r,s}=R^r v(K^s): `e₁ r s` identifies page-one `(s,(r:ℤ))` with
    `(F.rightDerived r).obj (K.obj.X s)`. Read `Functor.rightDerived` and
    `InjectiveResolution.isoRightDerivedObj` in Mathlib. The swap is the
    Mathlib filtration-first indexing convention, not a changed page. The
    separate q<0 vanishing clause covers negative resolution degrees. PASS.
11. d1 induced by d_K: the fourth conjunct intertwines page-one
    `(s,r) -> (s+1,r)` with `(F.rightDerived r).map (K.obj.d s (s+1))` using
    the existential signed e₁. The node asks for identifications under which
    this differential is unsigned; the sign choice is explained above and
    in the theorem's proof docstring. PASS.
12. Abutment H^{r+s}(RvK): for every `ρ : KInjectiveResolutionChoice K.obj`,
    `c n` identifies total homology with the dependency-recorded
    `rightDerivedCohomologyWithResolution K ρ n`. Read that definition, the
    structure of ρ, and `kInjective_computes`, including its comparison
    uniqueness and bounded-below injective clauses. This is the same derived
    cohomology object, for all integer total degrees. PASS.
13. Convergence and its filtration: H n is finite; its steps are exactly
    images of H^n(L.step p) in total cohomology transported through c n.
    Every sufficiently late page `(p,n-p)` is isomorphic to its graded piece.
    Read `DecreasingFiltration.IsFinite`, `gradedPiece`, and the convergence
    predicates in `ExactCoupleConvergence.lean`. Degreewise boundedness of L
    in n-1,n,n+1 stabilizes the cycle and boundary subobjects, and finite H
    is exhaustive, separated and inverse-limit complete. Thus this is the
    bounded convergence assertion in the node, not merely an unfiltered
    identification of total cohomology. PASS.
14. Independence of resolution: I and a are arbitrary universally quantified
    input data satisfying the CE conditions; the conclusion quantifies over
    every ρ. Hence every such CE total computes the same derived cohomology
    object. The node does not assert that all filtration choices or complete
    spectral sequences are independent of the resolution. PASS.

Edge cases: zero K and zero I are allowed, with all injectivity and quasi-iso
conditions meaningful. A complex supported in degree -3 is allowed by Plus
and the arbitrary hbelow bound; for total degree n the diagonal is confined
to b <= s <= n. Below b the total vanishes, and for p>n the image sum is empty.
r=0 uses the actual rightDerived zero map; for r=1 the sign normalization is
essential. Negative r is represented by the explicit vanishing clause. No
field, ring or characteristic is fixed. Empty schemes, if instantiated via
sheaf categories, introduce no extra restriction; there is no external index
set or finite nonempty-index assumption. All four object/hom universes are
explicit and independent; countable diagonal sums are supplied by the target
Grothendieck structure at its hom universe, as in the existing dependency.

Independent duplicate searches, with different queries from the first worker:

- `msearch.py leansearch`: "spectral sequence of a bounded below complex for
  an additive left exact functor with E1 derived functors of its terms".
  Service returned Internal Server Error; recorded as unavailable, no absence
  verdict inferred from this service.
- `msearch.py leanfinder`: "second filtration bicomplex injective resolutions
  converges derived functor complex". Eight hits, all injective-resolution
  maps/comparison identities, including `toRightDerivedZero'` and `descFSucc`;
  none states the hypercohomology E1 theorem.
- `msearch.py grep`: `hypercohomology|firstPage|cartanEilenberg|secondFiltration`.
  Five hits in Mathlib's `SpectralObject/FirstPage.lean`, describing generic
  first-page computation, not the CE resolution theorem.
- Direct rg of all project `lean/Sheaf` and source `WeilConjectures` for
  `hypercohomology|hypercohom|firstPage|secondFiltration|cartanEilenberg`:
  found CE helpers, filtration constructions, unrelated perfect-complex
  vanishing, and mentions of sheaf hypercohomology. Read the potential
  `cartanEilenberg_leftExact_cohomology` declaration: it compares cohomology
  under F for a single complex with injective cycles and boundaries, and
  does not state the E1 sequence. Read upstream
  `CategoryTheory/SpectralSequence/Grothendieck.lean` and its construction:
  its two-functor/object E2 sequence is not the arbitrary-complex E1 theorem.
  Direct search of `dag/lean_names_upstream.json`, source and project for
  this item id and its theorem name found no existing realization.

Correction citers: independently scanned all DAG files by membership in
stmt_deps/proof_deps and found exactly the seven recorded citers. Opened and
read in full the statements and proofs of
`lem-pc-grothendieck-edge-cocycle` and
`lem-weil-pbc-hypercohomology-e1-pullback-functorial`. Their holds=true verdicts
are correct: the first uses the r=0 comparison, unchanged by (-1)^(rs); in the
second the same sign factor occurs on source and target at each bidegree and
cancels in its naturality square. The resolutions and derived abutment used
by both remain the ones in Stacks. Read the unit's own proper/quasi-finite
statement: this auxiliary correction does not alter it. No citer was edited.

No new definition node or dependency module is included or needed. All
imports are used, there are no definitions or instances in this delivery,
and the sole theorem proof remains `sorry`. Module/declaration docstrings
name the source and blueprint id and carry the node's two-step proof,
including the bounded filtration, augmentation/cone argument and canonical
resolution comparison. Every variable and universe was checked by eye;
there is no file-local notation or auto-implicit free identifier. The stored
lean.statement is verbatim identical to the theorem signature, and no Lean
line exceeds 100 characters.

Validation: independently ran `scompile.py G1 thm-sp-if-e1` on the module;
server compilation succeeded in 9.0 seconds, exit 0, with no warnings.

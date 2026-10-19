## Worker report

Q75 states `lem-a1-constructible-degree-zero-proper-support` in
`Sheaf.Paper.ConstructibleDegreeZeroProperSupport`. All postponed assertions are
named theorems with `sorry` and source/proof docstrings. The definitions have actual
data. The comparison packages collect the natural transformations and the equations
specifying them on the existing completed integral models; they are conclusions,
not assumptions on X or G. No statement correction is made.

Hypotheses and clauses, read against the node:

- The finite field and its algebraic closure are `D : FiniteFieldDatum.{u}`;
  `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p` express the coefficient prime.
  `Ω : Type v`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`,
  `[IsAlgClosure ℚ_[l] Ω]` retain an independent coefficient universe.
- The scheme is `X : Scheme.{u}` with `[X.Over (Spec (.of D.k))]` and
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` on its structure map.
  Finite type is local finite type plus quasi-compactness. Smoothness, a Weil
  structure, connectedness and properness of X are absent from the general theorem.
- A degree-zero constructible object is `G : sfCommonStageHeart l X Ω`.
  Its underlying object `G.obj` belongs to the recorded
  `generalAlgebraicallyClosedConstructibleCategory`, rather than a replacement
  category of discrete non-torsion étale sheaves.
- `a1ConstructibleUnit` uses `pullbackTensorCommonUnit`, with residue inverses
  derived by `constructiblePullbackResidueUnits`. `A1ConstructibleSections` is
  literally the ambient Hom from this unit. The heart is full, so these are the
  heart Hom groups; no Frobenius-equivariance condition is added.
- `ordinaryValue` and `compactValue` identify the natural cohomology functors with
  the specified `adicOrdinaryCohomology ... 0` and `adicCompactCohomology ... 0`.
  The `ModuleCat.uliftFunctor` only aligns carriers with the completed-module
  universe. A second `uliftFunctor` aligns Type-valued cohomology with the Hom
  universe; all occurrences are entered/exited by `ULift.up` or the displayed iso.
- The actual compact arrow is built in
  `a1ConstructibleCompletedOpenComparison`: the mate, under pullback/direct-image
  adjunction, of the inverse extension-by-zero unit. Composition of direct images
  is the conjugate of the recorded pullback composition. Whiskering with the
  proper direct image gives `a1ConstructibleCompletedComparison`.
  `a1ConstructibleModelComparison` applies actual point sections, H⁰ and scalar
  extension. `comparisonIntegral` requires the natural compact arrow to be exactly
  this arrow on every finite coefficient field and every integral morphism.
- `ordinary`, `compact` are functors, `comparison` is a natural transformation,
  and `sections` is a natural isomorphism on the full constructible heart.
  Thus their composite is natural in G, including common-stage arrows.
  `a1ConstructibleCompactSection` gives the resulting map on the actual specified
  H_c⁰ carrier, through `compactValue` and the harmless carrier lift.
- `injective` is `Function.Injective` on every heart object. The section map is
  its composite with isomorphisms, hence is injective. `comparison.app` is a
  ModuleCat morphism and is linear. The `linear` field states that the ordinary
  Hom identification sends zero and `a • s + t` to zero and the corresponding
  linear combination after every normalized actual adic geometric fibre. The
  recorded exact conservative fibre family detects these Hom equalities; this
  is the same expression of Hom-linearity as in the lisse dependency.
- `support` quantifies over every compact class and produces
  `Z : TopologicalSpace.Closeds X`. It uses the recorded
  `IsClosedSubsetProperOver (X ↘ Spec (.of D.k)) Z`, including its reduced-induced
  scheme structure. Its second conjunct is equality to the zero morphism after
  actual pullback to the complement open. No claim that X is proper is used.
- For every `U : X.Opens`, `a1ConstructibleRestriction` is the recorded
  `commonStageDerivedPullback`; `a1ConstructibleRestrictionUnit` chooses the unique
  unit iso satisfying the recorded tensor-unit equations. Ordinary section
  restriction is its inverse followed by the pullback of the section morphism.
  No arbitrary unit iso is chosen. `openOrdinaryIntegral` and
  `openRestrictionIntegral` identify ordinary cohomology on U and its restriction
  with completed pullback/direct-image and its actual adjunction-unit map.
  `restrictionSections` is the explicit commuting equation with ordinary
  restriction on every open, including the empty and whole opens.
- `a1ConstructibleDegreeZeroProperSupport_lisse` separately states the
  normalization on the exact domain of the recorded lisse H⁰ theorem: a smooth
  finite-field model, its geometric fibre, a Weil object with its lisse lattice,
  and coefficients of that theorem's universe. Its existential
  `A1ConstructibleLisseCompatibility` realizes the entire lisse category in the
  constructible heart, on all integral models and their arrows. Its `sections`
  equation says the ordinary section is the unit-preserving realization of the
  old ordinary lisse section; `comparison` is the compact-arrow square.
  `realizes` is the recorded inverse-limit realization predicate.
  The old theorem's H⁰ and H_c⁰ module comparisons for For(F) are included.
  Combining this equation with `restrictionSections` gives the lisse-restriction
  clause wherever the cited lisse theorem is defined. Its smooth/Weil hypotheses
  occur only in this specialization and do not restrict the general theorem.

A compactification c is a presentation parameter already required by the recorded
`adicCompactCohomology`. It is not an added properness assumption on X. The main
proof docstring explains Nagata existence and the argument for every such c.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and its k, p.
- Scheme conventions: Mathlib's `Scheme.Over`, structure morphism notation,
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`; this convention node needs
  no private definition or replacement Lean record.
- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty`,
  `sfCommonStageHeart`, with its full-subcategory inclusion.
- `Sheaf.Paper.CommonStageCompactWeilCohomology`: `adicOrdinaryCohomology`,
  `adicCompactCohomology`, and the recorded underlying cohomology definitions.
- `WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase`:
  `AlgebraicGeometry.Scheme.IsClosedSubsetProperOver`. Its current live source
  was read with `scompile.py --source`, since it is not in the older source tree.
- `Sheaf.Paper.DegreeZeroCompactSupportSections`: `A1DegreeZeroLisse`,
  `a1DegreeZeroUnit`, `A1DegreeZeroRealizes`, `a1DegreeZeroIntegralModel`,
  `a1DegreeZeroLisseInclusion`, `A1DegreeZeroNaturalComparison`, and
  `a1DegreeZeroCompactSupportSections_natural`.
- `Sheaf.Paper.ConstructiblePullbackTExact`: `constructiblePullbackResidueUnits`,
  and the recorded exact common-stage pullback interface.
- `Sheaf.Paper.DerivedPullbackTensorIso`: `pullbackTensorCommonUnit`,
  `canonicalCommonStagePullbackTensor_unit`, `derivedPullbackTensorIso`.
- `Sheaf.Paper.AdicHeartIntrinsicFibres`: `SfAdicCommonFiberSpec`,
  `sfAdicCoefficientEmbedding` and the normalized exact conservative fibres.
- Existing completed operations are `PurCompactSupport.completed`, `pull`, `push`,
  `openExtension`, `image`, `openDerivedAdjunction`, `geometricPullComposition`,
  `completedPull_comp`, and `proEtaleRingDerivedAdjunction`.
- Proof imports retain the stated Nagata, boundary compactification and
  proper-closed-subset properties modules. The still-unstated proof dependencies
  are named in the full proof docstrings; no private copy of them is introduced.

The statement dependencies now cite the existing definitions through
`def-a1-constructible-pullback-residue-units`,
`def-a1-common-stage-coefficient-unit`, and
`def-a1-intrinsic-adic-fibre-specification`, together with
`def-weil-derived-pullback-tensor-hom` for `commonStageDerivedPullback`.
The enclosing pullback/tensor/fibre theorem nodes are not statement prerequisites;
`lem-per-adic-heart-pullback-fibres` remains in the unchanged proof dependencies.

Edge cases checked before drafting and again against the signatures:

- X empty, G zero, and the zero compact class: the section is zero, with empty
  proper closed support; no nonempty or connected hypothesis is present.
- X proper: Z can be the entire underlying closed subset; the statement does not
  require support strictly smaller than X.
- A skyscraper sheaf on an affine scheme has point support proper over k.
  A general extension by zero is allowed; G is not assumed lisse.
- Opens U empty and U = top are included, as are all non-affine opens.
  Their finite type follows from X being Noetherian, not an added hypothesis.
  Restricting the constant compact section on proper P¹ to A¹ gives an ordinary
  section, not a compact section on A¹. Accordingly `openRestriction` is ordinary
  cohomology restriction; no false compact-to-compact restriction is asserted.
- Compactifications need not be dense; the open-extension unit construction only
  needs an open immersion. The proof does not use density.
- The coefficient prime can be 2, and u and v are unrelated in the general result.
  No equality of coefficient/site universes or arbitrary inverse is assumed.

Searches for an existing statement or needed canonical maps:

- `msearch.py ... leanfinder "Degree zero compactly supported constructible adic
  cohomology injects into global sections with proper support"`: 8 hits, including
  structure-sheaf restriction and scheme image injectivity, no adic statement.
- `msearch.py ... loogle "CategoryTheory.Sheaf, AlgebraicGeometry.Scheme"`: 12
  site-equivalence and structure-sheaf hits, no match.
- `msearch.py ... grep "compactlySupported|compactSupport|sectionsWithSupport"
  AlgebraicGeometry`: no Mathlib hits. The raw responses are retained in the
  sandbox search log; no new definition node is needed for an already-owned map.
- `rg` in the upstream WeilConjectures tree and side `lean/Sheaf` found the
  recorded lisse statement and completed compact-support framework, but no
  constructible-heart version of this result. Searching the item ID upstream
  found no declaration. New declaration names `a1Constructible` and
  `A1Constructible` have no collision in upstream, Mathlib, the side library or
  `dag/lean_names_upstream.json`.
- Read the actual source of Milne Definition 18.1 and Proposition 18.3(b) and
  BS Proposition 6.8.14 and Remark 6.8.15 from the local PDFs, as well as the full
  dependency signatures and their docstrings. The finite-torsion statement is
  not silently identified with its adic extension.

No mathematical statement dispute was found. The helper definitions
are canonical maps and comparison data belonging to this node's own statement;
the three new definition ownership nodes reuse existing published declarations.
The current live sequence-site dependency is used directly.

## Second reading by Q75

The dispatcher expressly forbids starting another agent. This section records a
second pass by the same worker, not an independent-worker review; the maintainer's
independent delivery review remains required. I reopened the node and compared
its clauses with the module and the explicit fields listed above.

The second pass found and repaired these issues: the first draft did not expose
an explicit ordinary cohomology restriction square, so it now has the actual
completed adjunction-unit restriction and `restrictionSections` for every open.
The lisse clause initially existed only in prose; it now has its own realization,
ordinary-section and compact-comparison equations. Open restrictions initially
lacked the derived quasi-compactness instance; the current definitions derive
Noetherianness and compose the open immersion with the original structure map.
The cohomology carriers and Hom carriers live in different universes; explicit
ModuleCat and Type lifts now preserve the independent coefficient universe.

The general theorem retains exactly the finite-field, coefficient and separated
finite-type hypotheses. G is the recorded common-stage heart object. The natural
map is tied to the completed open-adjunction mate on all integral models,
injectivity and fibre-linearity are explicit, support uses the existing proper
closed-subset predicate and an actual zero restriction morphism, and the open
and lisse equations are present. No target statement, definition of cohomology,
or existing dependency interface was changed.


## Repair self-check (2026-10-18)

Read the saved report and the complete statement module, compared the
node with the current shared base without Git commands, and reread the heart,
cohomology, coefficient-unit, open-unit specification and lisse-normalization
interfaces. The item's natural-language statement and proof are unchanged.
Its recorded Lean signature matches the file verbatim; auto implicits are
disabled, lines are at most 100 columns, and the five `sorry` occurrences are
exactly the bodies of the five named theorems listed in `lean.declarations`.
The return contains a handoff status rather than numbered mathematical defects.
The first dry run rebuilt the saved sequence-site override and then timed out in
transitive imports (DerivedPullbackTensorHom locally and
CoefDerivedSystemEvaluationCalculus on the server). Comparing the saved override
with the current shared base and `scompile.py --source
Sheaf.Paper.CoefficientRingedSequenceSite` showed that the live source now handles
the generic successor-universe sheafification instance directly. The saved
sequence-site replacement is superseded and has been removed from this packet;
the item imports the current recorded dependency without changing it. This
avoids rebuilding its transitive dependants against a needless override. The empty
scheme, zero sheaf/class, proper scheme, empty/whole opens and independent
coefficient universe cases remain covered by the saved signatures. No new
mathematical discrepancy was found on this same-worker rereading.


## New nodes

`def-a1-constructible-pullback-residue-units` records the existing abbreviation
`WeilConjectures.constructiblePullbackResidueUnits` in
`Sheaf.Paper.ConstructiblePullbackTExact`. Its finite-field and finite-type hypotheses
are the displayed D, l, hl and Y binders. Its result is exactly the family of
`Invertible (l : Y.residueField y)` structures extracted from
`constructibleTruncations_exists`; the latter is cited directly. It does not require
or assert the conclusion of `constructible_pullback_t_exact`. Source: BS 6.8.15 and
the finite-field convention. This is an existing-definition record, with no new Lean.

`def-a1-common-stage-coefficient-unit` records the existing
`WeilConjectures.pullbackTensorCommonUnit` and its integral/rational units, unit
reductions, normalized left/right unitors and their unique-lift assertions,
scalar-unit comparison, stage comparison and three unit-condition predicates in
`Sheaf.Paper.DerivedPullbackTensorIso`. The full signatures and normalization
conditions were reread. The common unit is the actual pair at the least coefficient
field, whose integral representative is the derived limit of the coherent ring
unit. The predicate `canonicalCommonStagePullbackTensor_unit` is an `ExistsUnique`
proposition imposing both displayed unitor equations, rather than the theorem
asserting this proposition for every map. The helper assertions determining the
unitors remain owned through `lean.declarations`, as do the unit constructibility
and reduction-counit helpers. Source: BS 6.8.14--15 and the module's Stacks
03EL/07A4/0941 references. No arbitrary unit, unitor or comparison is introduced.

`def-a1-intrinsic-adic-fibre-specification` records the existing
`WeilConjectures.SfAdicCommonFiberSpec`, `sfAdicCoefficientEmbedding`,
`sfAdicIntegralFiber`, `sfAdicRationalFiber_existsUnique` and
`sfAdicRationalFiber` in `Sheaf.Paper.AdicHeartIntrinsicFibres`. The predicate
quantifies over every finite coefficient field and asks for natural isomorphisms
with the actual completed-section rational fibre followed by scalar extension.
The embedding is literally subfield inclusion composed with `Shrink.algEquiv`.
The rational fibre is the uniquely normalized descent of the integral functor,
not a choice of an unrelated fibre. Existence/exactness/conservativity of a
common-stage fibre remains theorem content and is not asserted by this definition.
Source: BS 6.8.4 and 6.8.14. No new Lean module is delivered.

For all three nodes, the raw fresh LeanSearch, LeanFinder and Mathlib grep results
are copied into `mathlib_searches`, alongside the local upstream/project/DAG search.
LeanSearch returned ordinary rational completions and monoid normalization;
LeanFinder returned BDeRhamPlus and ordinary adic tensor-completion comparisons;
Mathlib grep returned zero hits. Upstream grep returned no declaration. Project
and DAG grep found these three existing modules and their theorem records, but no
independent definition owner. `blueprint_refs.py search "coefficient unit"` found
19 general unit/duality references, none owning these normalized interfaces. Hence
all three nodes have `existing: true`; nothing is duplicated or redefined.

## Repair of L H2 at 777f546ea33b

The saved packet's first required dry run passed (commit 4bc446d16d, not pushed).
That mechanical pass did not discharge the maintainer's H2 return. I removed the
three theorem nodes from the delivered statement prerequisites and replaced them
with the three definition nodes above. I also added the already published
`def-weil-derived-pullback-tensor-hom`, which directly owns the used
`commonStageDerivedPullback`. All original base statement dependencies are retained,
and all proof steps and proof dependencies are unchanged. The fibre theorem stays
in proof dependencies. No mathematical statement correction is needed.

A further same-worker reading checked the changed records against the full source
signatures and docstrings. The new nodes include the local helper declarations
on which the consumed definitions rely, especially the normalized unitor lifts
and rational fibre descent. They neither assert the three overarching theorem
conclusions nor depend on them. The item's Lean module is byte-identical to the
saved packet that passed its initial dry run; all hypotheses, clauses and edge
cases matched above therefore persist. The dispatcher prohibits other agents,
so this is a self-check for the maintainer's independent review, not a claim of
an independent second worker.

Final repair checks: all declaration lists resolve in their recorded published
module; each primary signature matches the source; statement citations agree with
the new-node dependencies. No dependency cycle reaches a delivered node. The
inherited DAG contains an unrelated missing node reference, so the final server
preflight remains authoritative for its baseline. The unchanged Lean file has
SHA256 `0fc71f20b1e509c6e6d6a79016b3954dfe708703f1cc9693ef12dbec31b0cda8`. The required scompile.py run compiled the
sandbox in 30.3 s and the library form in 26.1 s, without diagnostics.

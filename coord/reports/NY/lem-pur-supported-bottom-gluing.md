## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.SupportedBottomGluing`; principal declaration:
`AlgebraicGeometry.supported_bottom_gluing`. This is a stage-2 statement: the only postponed
proof in the module is this named theorem. Definitions have actual data, and the two
restriction-additivity instances have their reflexive sectionwise fields. No declaration
is selected from the theorem's existential conclusion. The witness structures package the
specified canonical comparisons and their representative normalizations; they are conclusions,
not additional assumptions.

The source is the supplied node's complete thirteen-step proof, Stacks derived.tex,
`lemma-grothendieck-spectral-sequence` (015N), and the sheaf support construction in
etale-cohomology.tex, `section-cohomology-support` and
`lemma-sections-with-support-acyclic` (09XP/09XQ). The bottom-edge statement in 015N gives
`E₂^{p,q}=R^p G(H^q(RF(X)))` with a convergent finite filtration; this is exactly the
vanishing-below-d argument needed here. The comparison follows the coefficient, unit and
kernel normalizations already recorded in the dependencies, rather than an unspecified
isomorphism between the resulting groups.

Hypotheses and clauses, matched individually:

- The finite field, its fixed algebraic closure, ell distinct from the characteristic,
  finite coefficient extension, uniformizer quotient and positive coefficient level are
  the existing `P : WeilConjectures.PurityFiniteSetting`. `bottomCoefficient P` is literally
  `Scheme.finiteTateCoefficient P.coefficients.l P.extension (P.level - 1)`. That existing
  declaration indexes its quotient by one less than the positive level. Since
  `P.level_pos : 1 ≤ P.level`, the quotient exponent is precisely P.level. No ramification
  divisibility hypothesis is introduced.
- `X.Over (Spec (CommRingCat.of P.field.k))`, `LocallyOfFiniteType` and `QuasiCompact` of the structure map, and
  `IsSeparated` of that map render the separated finite-type k-scheme hypothesis.
- `i : Z ⟶ X` with `IsClosedImmersion i` is the specified closed support.
  The support on U is exactly `pullback.snd i U.hom`.
- `a : ℤ` includes all signed twists. `r : ℕ` and the displayed `hA` specify any positive
  power `ell^(r+1)` annihilating the coefficient quotient. This is the chosen annihilating
  power from the statement, not a divisibility requirement on the coefficient level.
- `bottomEtaleTwist` aliases the recorded `Scheme.finiteEtaleTateSheaf`, with exactly this
  coefficient ring, annihilating exponent and integer a. `bottomProLine` aliases the
  recorded signed `finiteCoefficientTwist`, transported by the existing
  `finiteTateConstantRestriction` to ordinary fixed-ring modules. It does not introduce
  another line or replace a negative twist by an arbitrary sheaf.
- `bottomForgetEt` and `bottomForgetPro` retain the underlying abelian sheaves.
  `SupportedBottomModel.I` and `.J` are injective resolutions in precisely those abelian
  sheaf categories, not module resolutions whose injectivity is asserted after forgetting.
- `SupportedBottomModel.etaleComplex` is `P_Z(I)` with the existing
  `Etale.supportedKernel i.openComplement.ι`. Its homology is H^q of the right-derived
  sheaf kernel C. Using the explicit representing complex is the representing-complex
  clause of `def-weil-derived-cohomology-sheaves`; the node's Mathlib match applies here.
  The added statement dependency `lem-pur-etale-supported-kernel-adjunction` records the
  existing declaration used for P_Z. Its module is reused, not repaired or duplicated.
- `d : ℕ` is d≥0. `∀ q : ℕ, q < d → IsZero (M.etaleComplex.homology q)` is precisely
  vanishing below d: this is a nonnegative injective-resolution complex, so its extension
  to integer degrees has zero terms and zero cohomology at all negative degrees.
- `SupportedBottomEdge.edge` is an isomorphism of presheaves from objectwise supported
  cohomology to the underlying presheaf of the single sheaf H^d(C). Its `.cycles_inclusion`
  fixes the cycle comparison by its monic inclusion. `.edge_cocycles` fixes the edge by
  the actual quotient of cycles in the sheaf-support complex. Thus an arbitrary automorphism
  of the cohomology group cannot be substituted for the edge.
- The actual small-site groups on U are exposed by `SupportedBottomModel.etaleTateEdgeAt`
  and `.proTateEdgeAt`, using `SupportedLocalResolution.groupIso` and the corresponding
  local resolutions. Their domains are the right-derived section-kernel functors on U's
  own small etale/pro-etale sites. Their domains literally use A_U(a). `bottomLocalCoefficientEt` and
  `bottomLocalCoefficientPro` transport the restricted coefficient on X to this exact
  coefficient, using the root/evaluation-normalized pullback data stored in Theta; no
  choice from the postponed theorem is made. The intermediate `etaleEdgeAt`/`proEdgeAt`
  use restricted coefficients and the same normalized local resolutions.
  The fields `.restriction` and `.augmentation` make each local resolution a restriction
  of the global one. `.kernel_sections` fixes each comparison by the actual kernel
  inclusion and the literal final-object evaluation. All etale U are quantified; no
  quasi-compactness, finite type or separatedness restriction is imposed on U.
- Further etale restriction is retained by `bottomComplexPresheaf`, which is the functor
  taking the homology of each evaluated support complex, and by `.edge`, a natural
  isomorphism of these presheaves. The local group identifications come from these
  normalized common resolutions, independently of the edge. Consequently naturality
  uses the actual restriction maps on kernel cocycles, not maps defined using the edge.
- `SignedFiniteTateComparison.theta` supplies theta on every k-scheme T, at every integer
  a and every admissible annihilating power. `.positive` uses exactly the existing
  `IsFiniteTateSiteComparison` root-projection characterization. `.evaluation_sections`
  fixes the pro-etale evaluation on actual internal-Hom sections; `.negative` states that
  theta preserves evaluation. These determine the negative comparisons by evaluation
  duality. The data-valued `.pullback` field supplies the etale and pro-etale coefficient pullbacks,
  normalizes their nonnegative powers with the existing predicates and their negative
  powers by evaluation, and states the square with the existing
  `comparisonUpperStarCompUpperStarIso`. Thus the signed comparison is canonical and
  pullback-compatible, not just a bare existence of isomorphisms.
- The supported comparison is `SupportedBottomModel.comparison`. Its construction is the
  inverse of the explicit support-complex isomorphism `.supportComplexIso`.
  `.unit_normalization` fixes the resolution augmentation to the comparison adjunction
  unit followed by theta; `.kernel_normalization` fixes the support identity by the
  kernel inclusion. These are the resolution normalizations of the specified composite
  RΓ_Z(unit), b and theta: b is the kernel identity on injective/K-injective representatives
  in `derivedSupportDirectImageComparison`. The inverse of that comparison, followed by
  the etale edge, is the actual definition of `.proEdge` and `.proEdgeAt`. The target is
  literally the same `(M.etaleComplex.homology d)` sheaf sections.
- Unique gluing is `SupportedBottomEdge.gluing` and the final
  `Presheaf.IsSheaf X.smallEtaleTopology (bottomProComplexPresheaf M.proComplex d)`.
  These are sheaf conditions on the original presheaves of supported groups, before
  sheafification. They state existence and uniqueness for every etale covering, including
  Zariski coverings. The entire edge/gluing conclusion is conditional on the bottom-degree
  vanishing; nothing asserts gluing in higher degrees without that hypothesis.

Dependency declarations read and used:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and its actual
  coefficient data. Its narrower `twistEtale` is not used, because it requires the
  ramification-index divisibility hypothesis absent from this node.
- `Sheaf.AlgebraicGeometry.SupportCohomology`: `Etale.supportCohomology`,
  `Sheaf.supportedSectionsFunctor`, and both `supportRestrictionArrow` declarations.
- `Sheaf.Paper.PbcQbarStandardCohomology`: read its recorded Qbar-specific primary
  declaration; for the ordinary abelian sheaves here the same node's general Mathlib
  match `DerivedCategory.homologyFunctor` is used through its representing-complex
  homology description. No Qbar hypothesis is added.
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`: `Scheme.etaleFiniteTwistPullback`
  and its publicly imported `finiteEtaleTateSheaf` construction.
- `Sheaf.Paper.PbcCoefficientTwists`: read the recorded primary rational/Qbar declaration;
  its public `CoefficientTwistsDetailed` supplies the finite signed
  `WeilConjectures.finiteCoefficientTwist` actually needed at these coefficients.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`: `Scheme.proEtaleSiteComparison` and
  the public fixed-coefficient `ProEtale.comparisonAdjunction`/inverse/direct images.
- `Sheaf.Paper.FiniteTateSiteDescent`: `Scheme.finite_tate_site_descent`,
  `finiteTateConstantRestriction`, and all three normalization predicates used above.
- `Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison`:
  `ProEtale.DerivedSupportDirectImageComparison`, including its kernel and unit
  normalizations; these identify the concrete support-complex comparison with b.
- `Sheaf.AlgebraicGeometry.EtaleSupportedKernelAdjunction`: `Etale.supportedKernel`.
  All stated proof dependencies are imported as non-public proof imports when not
  already public statement imports, retaining all thirteen steps of the proof route.

Edge cases checked before writing: d=0 makes the vanishing hypothesis vacuous and leaves
ordinary supported sections; no positive-degree assumption is hidden. Empty X, empty U,
empty support and full support use the same kernels and permit zero groups. Negative a
uses the actual internal dual, including a=-1. Positive coefficient level need not be
ramification-divisible. Arbitrarily large or non-quasi-compact etale U are included.
Sheaf gluing includes empty covers and arbitrary covering families. The scheme universe
is u and the abelian sheaf/group universe is u+1 throughout, matching the small sites;
no equality of site object and morphism universes is imposed.

Searches for an existing statement (no exact match):

- `msearch.py ... leanfinder "lowest nonzero local cohomology supported cohomology sections edge isomorphism etale gluing"`:
  eight hits, on algebraic local cohomology and ideal-sheaf geometry, none this statement.
- `msearch.py ... loogle "Functor.rightDerived, Presheaf.IsSheaf"`:
  zero hits; service reports the first identifier unknown. The existing APIs were then
  read directly in Mathlib's RightDerived and HomologicalComplex sources.
- `msearch.py ... grep "supportedKernel|supportCohomology|localCohomology" CategoryTheory`:
  zero Mathlib hits for this scheme-site statement.
- `rg` in the upstream `WeilConjectures` and project `lean/Sheaf`, for the item id,
  `supported_bottom`, `supportedBottom`, and bottom-edge patterns: no existing theorem;
  results include the general spectral-sequence and cocycle-edge APIs and unrelated
  supported-perfect-map gluing. Direct reading found and reused the support kernel,
  finite-Tate and direct-image comparison dependencies rather than restating them.

No statement correction, dependency-module repair or new DAG node is needed. No
STATEMENT-DISPUTED issue was found. The declaration auxiliaries belong to this node's
explicitly introduced support and comparison constructions and all carry its source tag.

## Second reading by NY

Independent maintainer second reading of immutable delivery
`7ca0b1ba2ee2c46edbc2f35e896ca9ffb2ac18c0`, performed by Codex on
2026-10-18. This replaces the author's explicit no-second-reading placeholder.
I read the snapshot node, all thirteen proof steps, all nine statement-dependency
nodes and their records, the delivered module in full, and the dependency declarations
and source places identified below. The worker report above is preserved.

Hypothesis and conclusion audit:

- The finite-field and coefficient datum is the existing `PurityFiniteSetting`, with
  its finite subextension and positive `level`. `bottomCoefficient` uses the published
  quotient at `(level - 1) + 1`, which equals `level` by `level_pos`. There is no
  ramification-index divisibility condition. The finite coefficient level zero is
  excluded by the node itself; it is not a missing case of this theorem.
- `X.Over`, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` state exactly
  separated finite type over the fixed field. `i` and `IsClosedImmersion i` specify
  the support, and `pullback.snd i U.hom` specifies its base change. No hypotheses
  on finite type, quasi-compactness, separatedness or nonemptiness of U were added.
- `a : ℤ` includes negative twists. The chosen positive annihilating power is
  `ell^(r+1)` with `hA`; this is not a restriction on the quotient level.
  `bottomEtaleTwist` and `bottomProLine` reuse the existing signed finite sheaves.
  Scalar restriction and forgetting retain the ordinary underlying abelian sheaves.
- `I` and `J` in `SupportedBottomModel` are resolutions in abelian sheaves.
  `etaleComplex` is the actual sheaf-support kernel applied termwise to I.
  Its homology represents the node's cohomology sheaf by the general recorded
  `DerivedCategory.homologyFunctor` / `homologyFunctorFactors` interface; the
  Qbar-specific primary declaration is not incorrectly specialized to finite A.
- `d : ℕ` is d >= 0. The vanishing assumption on natural degrees below d is
  equivalent to the stated integer-degree assumption because this injective
  resolution and its support complex are concentrated in nonnegative degrees.
- `SupportedBottomEdge.edge` is a natural isomorphism from presheaf homology of
  evaluated support complexes to the underlying presheaf of the homology sheaf.
  `cycles_inclusion` fixes the cycle comparison by a monomorphism, and
  `edge_cocycles` fixes the edge by the sheaf quotient of cycles. Thus the edge is
  canonical, with further etale restriction retained, rather than an arbitrary iso.
- `SupportedLocalResolution.restriction`, `augmentation`, and `kernel_sections`
  fix the local model by the actual augmentation and section-kernel inclusion.
  `groupIso` uses the standard injective-resolution formula for right derived
  functors. `etaleTateEdgeAt` and `proTateEdgeAt` have the prescribed A_U(a)
  coefficients, transported by the normalized coefficient pullbacks. They expose
  the actual supported groups on U's own small sites.
- `SignedFiniteTateComparison.theta` covers every k-scheme and integer twist.
  `positive` uses the existing root-projection normalization. `evaluation_sections`
  is the actual internal-dual evaluation, and `negative` forces its preservation.
  Since the positive line is locally free of rank one, this determines the negative
  comparison uniquely. The `pullback` field gives root/evaluation-normalized
  pullback isomorphisms and their square with the recorded site comparison.
- `bottomCoefficientUnit` is the genuine adjunction unit followed by theta.
  `unit_normalization` fixes the resolution augmentation, and
  `kernel_normalization` fixes the sheaf-kernel comparison by its inclusion.
  Consequently `supportComplexIso` computes the specified direct-image comparison;
  its inverse defines `comparison`. `proEdge` composes its inverse with the etale
  edge, giving sections of exactly the same sheaf. The existence of the model is a
  conclusion, not an assumption; no data is chosen from the postponed theorem.
- `SupportedBottomEdge.gluing` and the theorem's pro-etale `Presheaf.IsSheaf`
  concern the original cohomology presheaves, before sheafification. They give
  existence and uniqueness for all etale covers, and hence all Zariski covers.
  No assertion in higher degrees without the vanishing assumption is made.

Source and dependency checks: Stacks `derived.tex:7293-7362` supplies the acyclicity
hypothesis and finite-filtration Grothendieck spectral sequence (015N).
`etale-cohomology.tex:13966-14065` supplies the support kernel and injectivity on the
closed part (09XP/09XQ); exact closed pushforward gives the required acyclicity on X.
`proetale.tex:3738` and `:3950-4006` give the genuine small-site comparison and the
bounded-below adjunction-unit comparison, without restrictions on U. Read
`EtaleSupportedKernelAdjunction`, `SupportCohomology`, `PurityFiniteSetting`,
`EtaleFiniteTwistPullback`, `FiniteTateSiteDescent`,
`DerivedSupportDirectImageComparison`, `ProEtaleSiteComparison`,
`CoefficientTwistsDetailed`, `PbcCoefficientTwists`, and `PbcQbarStandardCohomology`.
The finite signed interfaces remain publicly available through the latter modules.
The direct-image comparison's kernel normalization agrees with the model here.
Also inspected the side-tree comparison functors, localization restriction, the
lowest-row edge statement and Grothendieck cocycle-edge statement.

Edge cases: d=0 (vacuous vanishing), a=0 and a=-1 and arbitrary negative a,
positive levels not divisible by the ramification index, empty X/U/support, full
support, zero groups, arbitrary non-quasi-compact etale objects, and empty/arbitrary
covering families. Scheme universe u and coefficient/group universe u+1 match the
small sites; object and morphism universes are not silently equated. All variables
are bound, with autoImplicit disabled.

Independent searches used `rg` for supported kernels, supported-bottom names,
local cohomology/gluing and hypercohomology in Mathlib, upstream WeilConjectures,
and the group's side tree. Mathlib's algebraic `localCohomology` is an ideal/Ext
construction, not this theorem. Existing kernel, coefficient, derived homology,
comparison and edge constructions are reused. No duplicate statement was found.
The worker's LeanFinder, Loogle and grep searches were also inspected.

Landing gates: the module and all auxiliary docstrings carry source and blueprint
references, and the main docstring follows all thirteen proof steps. Definitions
contain real data; the only postponed proof is the principal theorem's `sorry`.
Other proof terms are structural functor/instance laws and definitional transports.
The recorded `lean.statement` equals the signature verbatim; all recorded
auxiliary declarations are present; no line exceeds 100 characters. The delivery
changes only the report, the item module and the item node; the node changes only
`lean` and addition of the already recorded supported-kernel dependency to
`stmt_deps`. There is no statement correction, new node or dependency repair.
No cited statement/proof dependency occurs on the current route-pivot dropped list;
no enhanced, dg, Quillen, coherent-section or operadic machinery is reintroduced.
No item-specific route-pivot repair note exists at the inspected shared ref.

Finding H11: the delivered second-reading section expressly said no independent
reading had occurred. This complete replacement report supplies the actual reading.
No mathematical or Lean correction was necessary.

Independent compiler reproduction used the prescribed command on the immutable file:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NY lem-pur-supported-bottom-gluing
snapshot/lean/Sheaf/AlgebraicGeometry/SupportedBottomGluing.lean`.
It returned exit code 0, with no errors or warnings, for both sandbox
`Sheaf/Stage2/Sandbox0.lean` (18.9 s) and library-path
`Sheaf/AlgebraicGeometry/SupportedBottomGluing.lean` (65.0 s as printed by the wrapper).
The currently installed wrapper performs server-side overlay and confirmation;
no separate ssh command, global build, live Lean write, delivery or Git mutation
was run. The immutable snapshot and project clone were not edited.

## Validation

The final module passed `scompile.py NY lem-pur-supported-bottom-gluing` in both
the sandbox check and the library-path confirmation, with no errors or warnings.
The wrapper enforced its normal per-file limit; no global build was run.
The declaration list and verbatim theorem signature were synchronized with the node;
the module has no lines exceeding 100 characters and exactly one named theorem proof hole.
The delivery wrapper independently reruns the server preflight and per-file compilation.

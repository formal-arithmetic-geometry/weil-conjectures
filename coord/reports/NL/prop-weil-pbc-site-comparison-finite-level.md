## Worker report

The module states all three clauses of prop-weil-pbc-site-comparison-finite-level,
with one sorry theorem, AlgebraicGeometry.ProEtale.siteComparison_finiteLevel.
No definitions, dependency repairs, new nodes or statement corrections are needed.

Hypothesis and clause correspondence:
- The arbitrary base scheme is `(T : Scheme.{u})`; no affine, qcqs or proper restriction.
- The finite discrete coefficient ring is `(Λ : Type (u + 1)) [Ring Λ] [Finite Λ]`.
  Discreteness here means ordinary fixed-ring module coefficients, with no topology.
- Exactness of ν* is the first two conjuncts, `PreservesFiniteLimits` and
  `PreservesFiniteColimits` of `comparisonUpperStar (ModuleCat.{u + 1} Λ) T`.
  For this additive functor between abelian categories this is equivalent to exactness.
- Every etale Λ-module sheaf is `∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  The unit is exactly `(T.proEtaleSiteComparisonModules Λ).unit.app F`, not an
  arbitrary isomorphism. `IsIso` states invertibility of that map.
- Every injective etale module sheaf is the quantified `I` with `(_ : Injective I)`.
- The positive degrees are `(q : ℕ), 0 < q →`; the conclusion is `IsZero` of
  `((comparisonLowerStar ... T).rightDerived q).obj ((comparisonUpperStar ... T).obj I)`.
  Degree zero is deliberately excluded from the vanishing clause.

Statement dependency: Sheaf.AlgebraicGeometry.ProEtaleSiteComparison,
AlgebraicGeometry.Scheme.proEtaleSiteComparisonModules, read in full, is the canonical
upstream comparisonAdjunction specialized to module sheaves. Its functors are
AlgebraicGeometry.ProEtale.comparisonUpperStar and comparisonLowerStar, defined in
WeilConjectures.SixFunctors.ProEtale.Comparison.Defs by Kan extension/sheafification
and restriction. The module imports the recorded dependency rather than copying it.
Mathlib.CategoryTheory.Abelian.RightDerived supplies Functor.rightDerived.
WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf supplies the sheaf
Grothendieck structure needed to form these derived functors.

Recorded proof dependencies imported: ind-etale basis via
WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine; affine etale equivalence
via Sheaf.AlgebraicGeometry.FullAffineEtaleTopos; etale restriction injectives via
WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap; ring-sheaf Grothendieck theorem
via WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian; enough injectives
via Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives.
RingedSiteModules is already publicly imported by the statement dependency.
The comparison sections, comparison pullback, comparison injective acyclicity and
proetale restriction injectives nodes have no recorded statements in this snapshot;
they are proof prerequisites only and add no assumptions to the signature.

Edge cases: the empty scheme is admitted; the zero coefficient ring is admitted;
zero sheaves and injective zero sheaves are included; q=0 is excluded, q=1 included.
Coefficients and module values use the same u+1 convention as the dependency, and
the small sites retain their original object and morphism universes. A finite ring
in a smaller universe can be lifted to this fixed site universe. No finiteness on
sheaf sections is imposed. No node fault or STATEMENT-DISPUTED was found.

Searches (2026-10-15):
- msearch.py leanfinder "etale proetale comparison inverse image exact fully faithful
  unit higher direct image injective acyclic": eight hits, etale site/forgetful
  definitions and an unrelated condensed equivalence; no complete proposition.
- msearch.py loogle "CategoryTheory.Functor.rightAcyclic,
  CategoryTheory.Functor.PreservesHomology": zero hits, unknown rightAcyclic.
- msearch.py grep "comparisonUpperStar|comparisonAdjunction": ten hits, all ordinary
  monadic comparison adjunctions; none for proetale comparison.
- rg of the upstream WeilConjectures source and the side framework found
  preservesFiniteLimits_comparisonUpperStar, preservesHomology_comparisonUpperStar,
  isIso_comparisonAdjunction_unit, and rightAcyclic_comparisonUpperStar_obj_of_injective.
  Their full signatures/docstrings were read. These separately state general-coefficient
  clauses, not the complete finite-ring proposition using the recorded module adjunction.
- rg of the item id upstream found the acyclicity theorem docstring, explicitly
  identifying that theorem as only the acyclicity clause.
- rg of lean/Sheaf for comparison names found the recorded ProEtaleSiteComparison
  definition, and no complete finite-level proposition.

The proof docstring follows the four DAG proof steps, including affine localization,
the unit representative, injective restriction, and sheafification of section cohomology.


## Second reading by NL

Read the node, its blueprint source (order 1285), the complete recorded statement
 dependency module ProEtaleSiteComparison, and upstream Comparison.Defs. Also read
Stacks proetale.tex, section-comparison opening, lemma-describe-pullback-from-etale,
and lemma-relative-comparison with its proof. The source assumes an arbitrary scheme;
there is no separatedness, Noetherian, qcqs, affine or proper hypothesis to inherit.
The node specializes the comparison to finite discrete coefficient rings.

Object/hypothesis/conclusion checklist:
- Base scheme T: `(T : Scheme.{u})`; arbitrary, as required. Pass.
- Finite discrete coefficient ring Lambda: `(Λ : Type (u + 1)) [Ring Λ] [Finite Λ]`.
  ModuleCat is ordinary fixed-ring modules, so no topology or continuity condition
  is silently added; Ring also admits noncommutative and zero rings. Pass.
- The canonical comparison morphism: `comparisonUpperStar` and `comparisonLowerStar`
  are precisely the functors in `Scheme.proEtaleSiteComparisonModules`, whose body
  is the upstream `comparisonAdjunction`. Read their definitions: restriction for
  direct image, left Kan extension followed by sheafification for inverse image.
  No substitute map or noncanonical adjunction is used. Pass.
- Exactness of inverse image: the two conjuncts `PreservesFiniteLimits` and
  `PreservesFiniteColimits`. For this additive functor of abelian module-sheaf
  categories they express exactness, without an extra hypothesis. Pass.
- Every etale module sheaf F: the full quantified `Sheaf T.smallEtaleTopology
  (ModuleCat.{u + 1} Λ)`; there is no constructibility or finite-sections assumption.
  `IsIso ((T.proEtaleSiteComparisonModules Λ).unit.app F)` asserts invertibility
  of the specified unit, rather than existence of an arbitrary isomorphism. Pass.
- Every injective etale module sheaf I: the same sheaf category, quantified I and
  `(_ : Injective I)`. The right derived functor is that of comparison direct image,
  evaluated on comparison inverse image of this very I. Pass.
- All positive degrees: `(q : ℕ), 0 < q → IsZero (...)`. This asserts the zero
  higher-direct-image sheaf in every positive integer degree, exactly as the node.
  It adds no degree-zero vanishing or boundedness assertion. Pass.

Edge cases: the empty scheme, zero ring, zero sheaf and injective zero sheaf are
all admitted. Degree zero is excluded from the vanishing clause and degree one
is included. No index set is introduced. There is no characteristic restriction.
The explicit universe u binds every site/scheme occurrence; coefficients and module
values use u+1, the dependency's established common larger universe. Finite rings
can be transported to this universe, so this excludes no finite coefficient ring.
The site object/morphism universes are inherited unchanged, without an equality
assumption. All variables and universes are explicitly bound.

Independent searches:
- msearch leanfinder: "pro-etale to etale module sheaves exact inverse image
  adjunction unit injective higher direct images"; eight hits concerning etale
  morphisms/forgetful functors, no complete statement match.
- msearch loogle: `"rightDerived", "Injective"`; twelve generic derived-functor
  hits. These do not assert acyclicity of comparison pullbacks.
- msearch grep: `siteComparison_finiteLevel|comparison.*[Ee]xact|[Aa]cyclic.*comparison`;
  one unrelated Mathlib homology-comparison hit.
- Direct rg of Mathlib Sites/Proetale, upstream WeilConjectures, the exact side
  framework and lean/Sheaf: found the separate exactness instances in Comparison.Defs,
  `isIso_comparisonAdjunction_unit` in Comparison.FullyFaithful, and
  `rightAcyclic_comparisonUpperStar_obj_of_injective` in Comparison.LowerStarAcyclic.
  Opened the signatures and docstrings: each is one constituent, with general
  Grothendieck coefficients, and none is the full finite-ring conjunction.
  The acyclicity docstring explicitly identifies itself as only that clause of this
  node. FiniteCoefficient/UpperLowerStar/Defs concerns scheme pullback, not this
  comparison proposition. No duplicate complete statement or new notion was found.

No mathematical mismatch found; no Lean or node correction was needed. There are
no new nodes, dependency modules or statement_change records to review. The existing
module's four-step proof docstring matches the DAG's affine localization, unit
representative calculation, injective restriction/vanishing and sheafification
argument. Its sole theorem remains sorry; there are no definitions, hollow data,
private copies, local notation, proved helpers or extra axioms. The recorded
lean.statement was checked verbatim against the file signature. Only this independent
reading section was added. Compilation and dry-run results are recorded below.

Validation: scompile.py compiled the delivered module cleanly (exit 0, no warnings);
local overlay library check completed in 1.8 seconds.

## Worker report

Item: lem-sp-tower-adjoint-compositor-realization.
Module: Sheaf.Paper.TowerAdjointCompositorRealization.
Main declaration: AlgebraicGeometry.ProEtale.TowerAdjointCompositor.towerAdjointCompositorRealization.

This states the actual tower isomorphisms, not isomorphisms of diagrams of derived
objects. The only postponed theorem is the main declaration, with proof `by sorry`.
Every other declaration is a record, predicate, abbreviation, or explicit construction
from existing data. No coefficient object, scalar extension, constructibility predicate,
derived category, or compact-support functor is redefined.

The additional stmt_dep def-sp-coefficient-tower-shriek-interfaces is the landed
definition node owning the plain SpTowerCalculus interfaces in
Sheaf.Paper.CoefficientTowerShriekInterfaces. It is publicly reexported by tower
gluing. Calculus is the supplied `cal` hypothesis; it is not a choice from the
coefficient-tower shriek-calculus theorem, and that theorem's module is not imported.
This replaces the incorrect theorem dependency from returned head 2a24658e6959,
as explicitly requested by the maintainer's H2 correction. No original base stmt_dep
is removed; the natural-language statement, proof and Lean module are unchanged.
There are no new DAG nodes or dependency repairs.

Hypotheses and setup, clause by clause:

* Distinct primes p and ell: `[Fact p.Prime]`, `[Fact l.Prime]`, `_hpl : p ≠ l`.
  Primality implies positive characteristic. The field is `k : Type u`, `[Field k]`,
  `[CharP k p]`; there is no algebraic-closure or perfection hypothesis.
* X,Y,Z are `Scheme.{u}`, with their `Over (Spec (.of k))` instances. Separatedness,
  local finite type and quasi-compactness of each structure map express separated
  finite type over k. Morphisms f,g are over that base, with nonnegative pure
  relative dimensions `d e : ℕ` and `[SmoothOfRelativeDimension d f]`, respectively
  e,g. The displayed separated/local-finite-type/quasi-compact instances on f,g
  are consequences of this setting and are retained for the existing interfaces.
* The finite extension is `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
  `[FiniteDimensional (Padic l) E]`. `SpTowerShriek.R l E n` is precisely the
  quotient of the recorded integer ring by `spEllIdeal l E ^ (n+1)`. The n+1
  convention includes every positive exponent, and permits ramified extensions.
* `SpTowerShriek.Base`, `Operations`, and `SpTowerCalculus.Coordinates` are the
  section-normalized actual tower operations of the recorded dependencies. The
  `q.abelian T` localization is the ordinary derived category of the original
  strict semilinear tower category. No completion, diagram-category localization,
  or assumption of evaluation faithfulness is substituted.
* `SpTowerCalculus.C l E b q T` is the recorded full, unnormalized uniform ctf
  category. Its predicate has independent common cohomological and Tor intervals;
  no common stratification, equality of those intervals, or normalization is added.
  Finite evaluation is `SpTowerGluing.level`, landing in the recorded full finite
  ctf category. Constructibility and finite Tor amplitude are inherited predicates.
* cf,cg,ch are fixed compactifications of f,g,f≫g and do not depend on n. `Pair`
  packages exactly the restricted compact-support functor, its given right adjoint,
  and adjunction with `SpTowerGluing.Levels`. The latter retains finite adjunctions,
  realization, both unit/counit evaluation equations, scalar closure, invertibility
  of coefficient mates and the actual right-adjoint reduction equation. These are
  the adjunctions and evaluations that the node says to use from tower gluing.
* `z`, `hP`, `cal` are the existing tower-calculus presentation of the chosen
  operations; they are not arbitrary left or right functors. Its composition is
  a map in the ordinary tower derived category. The theorem chooses restricted
  alpha and explicitly identifies its underlying arrow with that composition.
* `A n : FiniteAdjointCompositorDatum ...` supplies the finite proper/open
  normalized alpha at every level. Its normalization field transports the etale
  compositor through the specified site comparisons. Its extra finite adjunction
  fields do not replace the finite adjunctions in `Pair.levels`; `finiteTheta`
  uses precisely the latter, and the alpha from A.
* `FiniteIdentities` states exactly the two assumed finite coefficient identities.
  Its left field uses the canonical `reductionDirectImageComparison` b for f,g,gf.
  Its right field uses the canonical counit transpose `coefficient` c and the
  finite counit-normalized `finiteTheta`. All scalar extensions are the recorded
  derived functors along `SpTowerCalculus.quotient l E h`; no flatness or finite
  projective-dimension hypothesis is imposed.

Conclusions, clause by clause:

* `∃ alpha : left Pf ⋙ left Pg ≅ left Ph` is the requested left natural
  isomorphism on actual tower categories. `Laws.proper_open` identifies the
  underlying derived-tower arrow with `cal.composition.composition`, so alpha
  cannot be replaced by a family of finite isomorphisms.
* `∃ theta : Ph.right ≅ Pg.right ⋙ Pf.right` is the requested right natural
  isomorphism. Lean writes functor composition in application order: Pg.right
  followed by Pf.right means Hf Hg, as in the source.
* `Laws.counit` states L(theta(K)) followed by the composite counit equals
  alpha(Hgf K) followed by epsilon_gf(K). `Laws.unique` characterizes theta by
  exactly that equation among natural isomorphisms. `Laws.composite_counit`
  writes the composite counit as Fg(epsilon_f(Hg K)) followed by epsilon_g.
* `Laws.left_evaluation` equates the evaluation of alpha with finite alpha after
  the specified two left evaluation comparisons. `Laws.right_evaluation` equates
  evaluation of theta with `finiteTheta` after the specified right comparisons.
  The latter is constructed using `Adjunction.rightAdjointUniq` after transport
  along finite alpha, so it is precisely the finite counit-normalized comparison.
  Both unit and counit compatibilities are retained by the input Levels records.
* Uniform ctf preservation by all six functors is expressed by their actual source
  and target categories (`Pair.closed` for the left restriction and the type of
  `Pair.right` for the right). `Laws.normalized_f`, `_g`, `_gf` assert that each
  pair also preserves `IsSpNormalizedTower`, for every object in that uniform
  category. This supplies exactly the six restrictions to normalized full
  subcategories; no reconstruction of tower morphisms is involved.
* `Laws.reductions_f`, `_g`, `_gf`, each of type `Reductions`, spell out both
  image reduction equations for every m≤n. The left field is b_h(C_n) followed
  by F_h,m(r^C), conjugated by support evaluation. The right field is c_h(C_n)
  followed by H_h,m(r^C), conjugated by right evaluation. `coefficient` is the
  existing `SpTowerGluing.coefficientMate` with its specified inverse b and
  adjunction transpose; it is not an unconstrained natural transformation.
* `Laws.left_square` and `right_square` quantify over all m≤n and all objects
  before normalization. They use actual derived evaluations of alpha/theta and
  the existing canonical reductions. Inserting the preceding evaluation equations
  gives precisely the finite-compositor reduction squares in the node's proof,
  with no cancellation using faithfulness of evaluation.

Dependency declarations read and used:

* WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible:
  `CondensedRing.compactificationOverField`, the standing over-field compactification.
* Mathlib.AlgebraicGeometry.Morphisms.Smooth: `Smooth`, `SmoothOfRelativeDimension`.
* Sheaf.AlgebraicGeometry.ProEtaleFiniteModules: `FiniteCoefficientModules`, ordinary
  module categories and their coefficient realization.
* Sheaf.Paper.ProEtaleFixedModuleConstructible:
  `Scheme.IsConstructibleProEtaleFixedModuleSheaf`; the intrinsic module form used
  by the recorded ctf tower predicates is retained unchanged.
* Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations:
  `Scheme.HasFixedCoefficientProEtaleTorAmplitude`, its universal degree-zero test.
* Sheaf.Paper.FiniteLocalizingExceptionalPreservation:
  `CondensedRing.localizingExceptionalAdjoint_preserves_finiteConstructible`, the
  restricted finite adjunction used by the finite comparison dependencies.
* Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  `Padic.finite_coefficientExtensionRing`, with the integer-ring construction
  inherited by `SpTowerShriek.R` and the existing ell-power finite instance.
* Sheaf.Paper.SmoothPurityCoefficientTowers: `spCoefficientTowers`, `spEllIdeal`.
* Sheaf.Paper.SmoothPurityNormalizedTowers: `spConstructibleTorTowers`,
  `spFiniteConstructibleTorCategory`, `spDerivedCoefficientEvaluation`,
  `IsSpNormalizedTower`, `spNormalizedConstructibleTorTowerCategory`.
* Sheaf.Paper.SmoothPurityTowerShriekLevels: `SpTowerShriek.Base`, `Operations`,
  `R`, `F`, `tower_shriek_levels`; these fix the real system operations.
* Sheaf.Paper.SmoothPurityTowerGluing: `SpTowerGluing.support`, `level`, `Levels`,
  `coefficientMate`, `tower_gluing`; their complete interfaces were read.
* Sheaf.SecSmoothPurity.ReductionDirectImage: `reductionDirectImage_isIso` and
  the canonical comparison `reductionDirectImageComparison`.
* Sheaf.SecSmoothPurity.ReductionExceptional: `reductionExceptional_isIso`,
  canonical counit-mate realization inherited by `coefficientMate`.
* Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons:
  `Etale.unboundedEtaleLowerShriekCompIso`, normalized finite composition.
* Sheaf.Paper.FiniteCompactSiteCoherence: `finiteCompactSiteCoherence`, and
  `coherenceEtaleCompositor` used by the finite normalized datum.
* Sheaf.Paper.FiniteAdjointCompositorTransposes: `FiniteAdjointCompositorDatum`,
  `finiteAdjointCompositorTransposes`; finite alpha and its specified coefficient laws.
* Sheaf.Paper.CoefficientTowerShriekInterfaces: `SpTowerCalculus.Coordinates`,
  `FiniteCoordinates`, `Preservation`, `C`, `F`, `Calculus`, `quotient`, `reduction`;
  their landed owning definition node def-sp-coefficient-tower-shriek-interfaces is
  the single added stmt_dep. It is publicly reexported by tower gluing.
* Mathlib.CategoryTheory.Adjunction.Basic and Unique: `Adjunction.comp`,
  `Adjunction.ofNatIsoLeft`, `Adjunction.rightAdjointUniq`; no private mate formula.

The modules of all recorded proof dependencies are imported without `public` unless
also needed for the statement. Mathlib-only dependencies arrive through these public
interfaces. No omitted import is needed to avoid a cycle in this delivery.

Edge cases checked before writing:

* n=0 means the valid exponent 1, never the zero coefficient stage; every positive
  exponent occurs. m=n is included literally in every reduction and normalization
  quantifier; the scalar-coordinate unitors cover that case.
* d=0 or e=0, identity morphisms, empty schemes and zero towers are permitted.
  No Nonempty scheme, nonzero coefficient, strict inequality m<n, or connectedness
  binder excludes these cases. Finite rings include the zero ring in the interfaces.
* Uniform cohomological and Tor bounds may differ. Normalization is tested only in
  the preservation conclusions; inputs to comparisons and squares need not be normalized.
* Scalar extensions along quotient maps are allowed to be nonflat and to have infinite
  projective dimension. The prescribed finite ctf scalar closure comes from Levels.
* Both the pro-etale object universe u+1 and morphism universe u are retained by
  the dependencies. The existing universe-u E,k and Scheme interfaces are reused;
  no extra equality of site object and morphism universes is imposed.

Searches for reuse:

* msearch.py leanfinder, query "Actual derived coefficient tower compact support
  composition and exceptional adjoint compositor compatible with finite evaluation
  and derived reduction": eight results including Adjunction.derivedε_fac_app and
  generic derived-adjunction lemmas; no theorem about these strict varying coefficients.
* msearch.py leansearch, query "Composition of adjunctions on derived coefficient
  towers with finite evaluation and reduction maps": Adjunction.comp, derived,
  Equivalence.trans_toAdjunction, leftAdjointCompNatTrans; generic APIs only.
* msearch.py loogle, query "CategoryTheory.Adjunction.comp,
  CategoryTheory.Adjunction.rightAdjointUniq": no hits for the comma query; separate
  local source search confirms both APIs in Mathlib. A further exact-name Loogle
  query for rightAdjointUniq returned 12 hits, including the exact API and its
  counit normalization lemmas.
* msearch.py grep, query `tower.*[Cc]ompositor|[Cc]ompositor.*tower`, subdirectory
  CategoryTheory: zero hits.
* rg in lean/WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `tower.*[Aa]djoint.*[Cc]ompositor|[Cc]ompositor.*[Rr]ealization|towerAdjointCompositorRealization`:
  no matching statement. Other completed-shriek and trace-stalk realization modules
  concern different coefficients and operations. Exact node-id search in
  lean/WeilConjectures returned no hit.
* Read the actual interfaces in CoefficientTowerShriekInterfaces, tower shriek,
  tower gluing and finite adjoint compositors rather than duplicating their notions.

Validation: scompile.py compiled the module against the live published server library
in 14.7 seconds (preceded by a 22.9-second sandbox setup); no errors or warnings.
The delivered theorem has one sorry, as required by stage 2. All variables and universes
are explicitly bound, autoImplicit and relaxedAutoImplicit are disabled, and no line
exceeds 100 characters. The current blueprint proof (1)--(3) was opened and checked. The deliver2.py
dry run passed the server preflight and compilation (commit 24483b99fb0).
No STATEMENT-DISPUTED issue or source-based statement correction was found.

## Repair of returned head 2a24658e6959

H2: replaced only the added theorem dependency lem-sp-coefficient-tower-shriek-calculus
with the landed definition node def-sp-coefficient-tower-shriek-interfaces. The current
main node has the original sixteen statement dependencies and no Lean record; this
repair retains all sixteen and adds the correct owning definition node. Updated the
lean.note and the report to distinguish plain interface definitions from their theorem.
The Lean file was retained byte-for-byte, with SHA-256
b66e78de26310aeb2603009ba298d9dd09d7926f097f2ea3c19f4744f2bf0ed4.

Repair validation: scompile.py accepted the unchanged module with no errors or
non-sorry warnings. deliver2.py --no-push passed server preflight and compilation
on the refreshed main base (dry-run commit bb3fb2102ce). The node delta against main
contains only lean and stmt_deps; all sixteen original dependencies remain, with
def-sp-coefficient-tower-shriek-interfaces as the sole added dependency. The recorded
signature was checked verbatim against the unchanged Lean file.

## Second reading by O3

Independent review is the maintainer L's review of immutable head 2a24658e6959,
recorded in coord/returns/O3.md (2026-10-25 06:53 UTC), rather than a second worker
started by O3. L found H2 in the ownership of the added dependency. The correction
above addresses that defect without changing the reviewed Lean statement.

L explicitly checked the distinct-prime and arbitrary-field setting, separated finite
type schemes and smooth relative dimensions d,e; alpha pinned by proper_open to
cal.composition; the uniqueness imposed by Evaluation.comparison.normalization;
A n alpha pinned via coherenceEtaleCompositor; theta's counit and uniqueness;
finiteTheta via rightAdjointUniq; the b_h and c_h Reductions; PreservesNormalized
for all six functors; and both squares for all m≤n, including m=n. L also checked
d=e=0, empty schemes, the verbatim statement record, and the single sorry, and
reported the mathematics otherwise OK. The present revision changes the metadata
identified by that review and retains exactly the Lean text it checked. This report
attributes those checks to L and does not claim another independent O3 worker.

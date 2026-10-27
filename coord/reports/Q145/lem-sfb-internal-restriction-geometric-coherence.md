## Worker report

The module `Sheaf.CategoryTheory.InternalRestrictionGeometricCoherence` states
`lem-sfb-internal-restriction-geometric-coherence` in several declarations, all listed
in `lean.declarations`. Every theorem ends with `by sorry`. No theorem is proved,
no definition selects data from a sorried existence assertion, and the item's
statement, proof, proof dependencies and source are unchanged.

Source read: the complete item and its ten proof steps, and the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3). The paragraph supplies the six-functor context; the categorical
infrastructure is the explicitly agent-written material retained in this node,
not a claim that the blueprint itself already contains these formulas. Also read
all five original statement dependencies, their full Lean records and declaration
source/docstrings, and the existing action-site framework.

Hypotheses and clauses:

- The fixed universe is `universe u`; the site is `{C : Type u}` with
  `[SmallCategory C] [HasFiniteLimits C]`, `J : Precoverage C`, and
  `hJ : J.IsSiteForCoverings`. The underlying topos is
  `Sheaf J.toGrothendieck (Type u)`. This uses the recorded presieve-site convention;
  there is no independent small universe excluding some group or coefficient values.
- A group sheaf is `K : Cᵒᵖ ⥤ GrpCat.{u}` and
  `hK : Presheaf.IsSheaf J.toGrothendieck (K ⋙ forget GrpCat.{u})`;
  likewise L and H. The existing `groupSheaf J K hK` and `SetActions J K hK`
  use Mathlib `Mod` in the cartesian monoidal category of set sheaves.
  Their new definition-node owner is `def-sfb-internal-set-actions`.
  Their structure is a natural internal left action satisfying the unit and
  associativity diagrams, and their maps are exactly equivariant sheaf maps.
- A group-sheaf map is `θ : L ⟶ K`. `restrictionGroupMap_isMonHom` records
  preservation of unit and multiplication for its existing underlying sheaf map.
  `restrictSetActions` is Mathlib `Mod.comap` of that map. It constructs the new
  action by actual precomposition, keeping the section sets and maps.
- `trivialSetActions` uses existing `Mod.trivialAction` and keeps every sheaf map.
  The named theorem `trivialSetActions_map` supplies only the equivariance proof.
  Both definitions contain actual data, not choices from mere existence.
- `internalRestriction_finiteLimits` states creation for each finite category D
  using `Nonempty (CreatesLimitsOfShape D (Mod.forget ...))`, and finite-limit
  preservation for restriction and inflation. This covers the empty diagram
  (terminal object), products and parallel-pair equalizers. The docstring spells
  out the tuple construction, coordinatewise action and uniqueness, so the action
  on these particular limits is specified by their projections, not arbitrary.
- `internalRestriction_identities` states equality after the forgetful functor,
  the section formula `l • x = θ(l) • x`, identity restriction, composition for
  `ψ : H ⟶ L` with composite `ψ ≫ θ`, and restriction of trivial inflation.
  These are literal functor equalities, not unspecified natural isomorphisms.
- `internalRestriction_terminal` gives an equivalence between modules over the
  terminal internal group (the monoidal unit) and ordinary sheaves, whose forward
  functor is exactly `Mod.forget`. Its inverse followed by `Mod.comap` of
  `CartesianMonoidalCategory.toUnit (groupSheaf J K hK)` is trivial inflation.
- `internalRestriction_fixedAdjoint` gives F, its natural inclusion i into the
  underlying sheaf functor, and `trivialSetActions J hK ⊣ F`. The components of i
  are injective. Their ranges are exactly the sections x fixed after every
  `f : U ⟶ V` in Cᵒᵖ by every `k : K.obj V`. Thus the test is over every further
  restriction, not just K(U). Its counit has underlying map `i.app X`.
  This existential is a universal-property specification of the actual fixed
  subobject, not a definition choosing an unknown sheaf.
- `internalRestriction_presentedIdentities` repeats the literal inverse-image
  equalities in the existing action-site model, uniformly for the set and ring
  coefficient categories. The site model is the existing labeled category and
  label-1 generated topology, not a new definition of internal actions.
- `RestrictionRingedRealization` is a record of the specified conclusion:
  an existing `RingedToposMorphism`, its inverse image equal to the prescribed
  precomposition, its direct image equal to a supplied G, the same adjunction
  (including its unit and counit), and identity structural ring map.
  `internalRestriction_ringed` gives this for q_theta and p_K, for each supplied
  right adjoint. It does not assume or conclude existence of right adjoints for
  every arbitrary restriction. Small-site presentation is the one used in the
  proof by `lem-sfb-internal-action-sheaf-equivalence`.
- `internalRestriction_baseCoherence` gives the actual mate equation for p_K,
  q_theta and q_psi: conjugating the total inverse-image equality equals
  whiskering the first mate then composing the second. It also states the identity
  mate equation. The equalities e_theta and e_psi are quantified proofs of the
  equalities already supplied by `internalRestriction_presentedIdentities`;
  they impose no additional mathematical hypothesis.
  `internalRestriction_comparisonCoherence` states the transitivity, identity and
  invertibility equations for the same normalized comparisons between identified
  restriction inverse images. Thus different parenthesizations give the same
  comparisons, and Mathlib `conjugateIsoEquiv` supplies the isomorphism direction.
- Coefficients are arbitrary `R R' : Sheaf J.toGrothendieck CommRingCat.{u}` and
  `φ : R ⟶ R'`. `internalRestriction_coefficients` supplies `CoefficientChange`
  on the base and action site, with the direction (E,R') to (E,R), identity
  inverse image and structural map phi built into that existing record.
  It states the component formula phi_U and the commuting restriction square,
  with the literal inverse-image equality used as `eqToIso`. The structural
  composites are therefore the same phi_U. Inflation is the displayed p_K
  precomposition, so its coefficient map is exactly its functorial image of phi.
- `RestrictionScalarSquare` records the actual comparison on extension-of-scalars
  module pullbacks, its naturality, and its pure-tensor formula. It uses the
  existing `PrecompositionPullback` section identifications and the existing
  `SheafOfModules.changeOfRings` and `changeOfRingsHom`; no different module
  category or different tensor is introduced. The pure tensor is the existing
  `SheafOfModules.scalarExtensionConstraintTmul`, the image of r' tensor m under
  the module-sheafification unit. `internalRestriction_scalarSquares` supplies
  these normalized comparisons for both inflation and restriction, for any
  specified normalized module pullbacks. The formula is literally r' tensor m
  sent to r' tensor m, after their specified section identifications. There is
  no flatness hypothesis on phi.

Dependency declarations used:

- `def-weil-size-convention`: the explicit universe binders, as its convention
  record requests (there is no object-valued declaration).
- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`, together with Mathlib `Sheaf`.
- `Sheaf.CategoryTheory.RingedToposMorphism`:
  `CategoryTheory.RingedToposMorphism`, including its induced module direct image.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules` = existing `SheafOfModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and its public
  imports: the existing sheafified section tensor and its monoidal structure.
- `def-sfb-internal-action-site-basic`, module
  `Sheaf.CategoryTheory.InternalActionSiteBasic`: `Object.mk`, `topology`,
  `projection`, `coefficientSheaf`, `baseRing`.
- `def-sfb-internal-set-actions`, module
  `Sheaf.CategoryTheory.ActionToposGeometricRestriction`: its existing
  construction declarations `groupSheaf`, `groupMonoid`, `SetActions`, `setAction`,
  `restrictionSite`, `precomposition`, `restriction`, `inflation`, `baseRing`,
  `coefficientSheaf`, `pulledCoefficient`, `PrecompositionPullback`, and
  `CoefficientChange`. The theorem `geometricRestriction` and its existence
  conclusion are never used. The new existing:true definition node owns this
  vocabulary, including `actionPrecomposition_isSheaf`, `moduleSets` and
  `ModulePullback`, without depending on the parent theorem.
- `Mathlib.CategoryTheory.Monoidal.Mod` and `.Cartesian.Mod`: `Mod.comap`,
  `Mod.forget`, `Mod.trivialAction` and `ModObj.trivialAction`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `conjugateEquiv` for the actual
  right-adjoint comparisons; `Adjunction.comp` for composite adjunctions.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionConstraintCoherence`:
  `SheafOfModules.scalarExtensionConstraintTmul`, which avoids another definition
  of the same standard pure-tensor image. The new existing:true definition node
  `def-sfb-scalar-extension-constraint-data` owns it together with
  `ScalarExtensionConstraintModules` and `scalarExtensionConstraintPureTensor`.
  The theorem node `lem-pd-sheaf-scalar-extension-constraint-coherence` is removed
  from stmt_deps as requested by the return; no theorem conclusion is used.
- Proof import `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`:
  `SheafOfModules.module_pullback_pushforward_adjunction`, the recorded general
  ringed-topos module-adjunction interface. Other recorded proof inputs either
  are Mathlib declarations made available through these imports or have no
  recorded Lean module yet. No missing theorem is replaced by an assumed fact.

Import-cycle note for maintenance: do not add a reverse proof import from
`ActionToposGeometricRestriction` to this module while the shared construction
vocabulary lives there. Stage 2 section 3(7) explicitly omits proof imports that
would close such a cycle. This module does not use the parent's theorem.

Edge cases checked by reading the actual formulas before writing: the empty finite
diagram gives the singleton/terminal sheaf; equalizers have the restricted action;
K=1 and theta=id recover the ordinary/identity actions; arbitrary noncommutative
section groups are allowed; theta followed by psi uses `ψ ≫ θ` in the correct
order. Empty covering families are not ruled out. The fixed-subsheaf condition
continues to test all further objects even if there are few sections on U. Zero
rings, zero modules and nonflat phi remain allowed. All section sets, groups,
rings and sheafified module values have the same chosen universe u, exactly the
node's V-small convention.

Searches actually made:

- msearch LeanFinder: "Restriction of internal group sheaf actions preserves finite
  limits and commutes with trivial inflation and coefficient ring maps"; eight
  generic module-sheaf/scalar-restriction hits, no complete internal-group theorem.
- msearch Loogle: "CategoryTheory.Mod, CategoryTheory.Limits.CreatesLimitsOfShape";
  unavailable identifier `CategoryTheory.Limits.CreatesLimitsOfShape` in the service,
  zero hits. This is a query failure, not evidence of absence.
- msearch grep: `Mod.*(restrict|trivial)|def (restrict|trivial)|CreatesFiniteLimits`
  under CategoryTheory; 25 hits, including Mathlib Mod.comap/scalarRestriction and
  Mod.trivialAction, all reused rather than copied.
- msearch LeanSearch: "Restriction of internal group actions preserves finite limits
  and trivial action"; eight hits, mainly `Action.*` for an external monoid.
  Those do not state the node for an internal group sheaf.
- rg in both lean/WeilConjectures and lean/Sheaf for InternalAction/internalAction,
  internal restriction, fixedSheaf, Mod.comap, restriction identities and the
  proposed new names. Found and read InternalActionSiteBasic,
  InternalActionSitePresentation and ActionToposGeometricRestriction. No complete
  existing declaration states the present node: the parent record omits finite-limit
  creation, the fixed-subsheaf adjoint, explicit coherence equations, and the final
  coefficient-extension pure-tensor square. Its existing definitions are reused.
- grep/rg for the exact item id in lean/WeilConjectures: no hits.
- rg for scalar-extension pure-tensor helpers found and read
  ScalarExtensionConstraintCoherence, ScalarExtensionRingIso and
  InternalScalarExtensionSectionTest. Selected the exact standard changeOfRings
  helper, not the different universe-transport or internal-module tensor helpers.

No STATEMENT-DISPUTED issue or statement correction is needed. The returned
ownership faults are repaired by the two existing:true definition nodes below
and the basic action-site citation. Helpers in this module are representations of this node's own
comparisons and concrete action restriction, not independently postulated notions.
All compiles used the prescribed scompile.py wrapper against the published server
build. The complete final file compiled in sandbox and library modes with no errors
or warnings before delivery preflight.

## New nodes

`def-sfb-internal-set-actions` records the existing general internal group-sheaf
action category and section action, label-changing functor, sheaf precomposition,
restriction and inflation, underlying module sets, and the normalized module
pullback, pulled coefficient, precomposition-pullback and coefficient-change
records. Its source is the paragraph-(3) agent-written categorical infrastructure,
as realized in `ActionToposGeometricRestriction.lean`; it asserts no existence of
`GeometricRestriction`. `lean.declarations` names the exact existing declarations
and the precomposition sheaf-condition typing lemma. LeanSearch for "Internal
group sheaf actions and restriction functors on a small site" and LeanFinder for
"Category of internal group sheaf actions and label changing restriction and trivial
inflation" returned generic external `Action.res`/`ContAction.res` results, not
this interface. msearch grep `SetActions|PrecompositionPullback|CoefficientChange|groupSheaf`
in Mathlib CategoryTheory returned no hits. Project rg found the exact existing
module and no corresponding WeilConjectures interface. DAG grep and
`blueprint_refs.py search 'internal group action'` found no general definition
owner; the existing profinite-action coefficient node specializes a different
site and refers back to the theorem. Thus this is a new DAG owner with
`existing: true`, with no copied or rewritten Lean definitions. Its statement
dependencies include the basic action-site, site/size, ringed-morphism, module
and tensor nodes used to type these records. `groupSheaf`, `groupMonoid` and
`SetActions` give the actual internal action; `setAction` evaluates its morphism;
`restrictionSite`, `precomposition`, `restriction` and `inflation` give the actual
sectionwise functors; each remaining record has its literal equalities and
normalizations exactly as described in the node. Neither finite-limit creation
nor existence of adjoints is folded into the new definition.

`def-sfb-scalar-extension-constraint-data` records exactly the existing
`SheafOfModules.ScalarExtensionConstraintModules`,
`SheafOfModules.scalarExtensionConstraintPureTensor`, and
`SheafOfModules.scalarExtensionConstraintTmul` from
`ScalarExtensionConstraintCoherence.lean`, with `existing: true`. Its source is
Stacks 03CY/03DD/03EK, module sheafification and tensor/change of rings. The module
category is the existing `ringedSiteModules`; the tensor image is the
sheafification unit followed by `tensorObjIsoSheafification.inv`; the scalar
extension image is the sheafification unit applied to `s tensor h` in
`changeOfRingsPresheaf`. Object and morphism universes remain independent, with
`EssentiallySmall.{w} C` and the recorded `HasSheafCompose` hypothesis. LeanSearch
for "Image of pure tensor under sheafification unit for scalar extension of
sheaves of modules" found ordinary extend-scalars units and sheafification;
LeanFinder for "Pure tensor in sheafification of sectionwise change of rings for
module sheaves" found sheafification scalar-action ingredients. msearch grep
`scalarExtensionConstraint|changeOfRingsPresheaf|tensorObjIsoSheafification` in
Mathlib Algebra/Category/ModuleCat returned no hits. Project rg found the exact
helpers, and DAG grep plus `blueprint_refs.py search 'scalar extension constraint'`
found only the theorem owner, no definition node. All three search-service
records and the project/DAG results are in the new node. Zero rings/modules and
nonflat coefficient maps remain permitted; no coherence theorem is needed to
define these section images.

## Returned delivery repair

The return reviewed immutable head `364e2fece838`. For its first H2 point,
replaced `lem-pd-sheaf-scalar-extension-constraint-coherence` in stmt_deps with
`def-sfb-scalar-extension-constraint-data`, an existing:true definition node
owning all three requested declarations. For its H2/H12 point, added
`def-sfb-internal-set-actions`, an existing:true node on the plain definitions
and structures of `ActionToposGeometricRestriction`, and cited it together with
the landed `def-sfb-internal-action-site-basic`. The new nodes have no dependency
on `lem-sfb-action-topos-geometric-restriction`, so its proof-dependency on this
item cannot close a cycle. The Lean file is byte-identical to the returned
version; the mathematical statement, proof and proof dependencies are unchanged.
The source signatures in both new lean records were extracted verbatim before
`:=`. Their records omit `file` because the declarations already exist.

## Second reading by Q145

This is a second pass by the dispatcher worker; the independent review is the
maintainer's delivery review, as requested in this assignment. No other agent was
started. Reopened the original node and final module, checked every mapping above,
and checked all retained hypotheses. In particular, site hypotheses are retained
with `include hJ`, and group-sheaf hypotheses on presentation-based statements are
retained with `include hK hL` (and hH for two successive restrictions), even when
those hypotheses are absent from the displayed functor types.

The first reading found that bare existence of geometric isomorphisms would miss
the requested normalizations. The final file instead specifies the supplied
adjunction, identity structural map, the transitive/whiskered mate equations and
pure-tensor formulas. A subsequent search found an existing pure-tensor helper;
the duplicate provisional helper was removed and the existing declaration used.
The terminal group is the terminal internal monoid with its forced trivial action,
not an arbitrary external group. The fixed-adjoint counit is the actual inclusion.
There are no let-bound hypotheses, file-local instances/notations, auto-implicit
variables, or proof bodies other than sorry.

Repair second reading: reopened both existing source modules and both new nodes.
Checked every listed name, the two verbatim primary signatures, the label-change
and sheafification-unit formulas, and every normalized-data clause. The basic
site definitions are now directly cited. Removed the theorem ownership edge;
no new edge goes back through the parent theorem. No change to the accepted
clause-by-clause Lean rendering was necessary. The new nodes reuse the existing
constructions and introduce no additional mathematical assumptions on the item.

Repair validation (2026-10-24): scompile.py compiled the final unchanged Lean file
cleanly in sandbox mode (5.4 s) and library mode (5.2 s). The repaired packet
passed deliver2.py --no-push: `OK (dry run)` at `56d1aab9f12`, including preflight
and compilation. A read-only traversal of both statement and proof dependencies
found no path back to this item from any of its eight statement dependencies
(122 nodes reachable from the new general-action owner and 119 from the new
scalar-extension owner). No live repository files were edited directly.

## Worker report

The module `Sheaf.CategoryTheory.InternalSectionScalarAdjunction` states
`CategoryTheory.InternalAbelianSheafModule.internal_section_scalar_adjunction`.
Its conclusion is the existence proposition `InternalSectionScalarAdjunction J a`:
it states every clause of this node, with the actual functors fixed by the dependency
interfaces and their universal properties. It is not a hypothesis asking for arbitrary
comparison data. The theorem has only `sorry`; the section-ring map and internal generator
are real constructions. No statement correction, new node, or dependency-module repair.

Hypotheses and objects, read clause by clause:

- An arbitrary site is `{C : Type c} [Category.{v} C] (J : GrothendieckTopology C)`.
  `[UnivLE.{max c v, u}]` expresses exactly that its objects and arrows fit in the
  coefficient universe. The site object and arrow universes are independent.
- Abelian sheafification and monoidal local equivalences are
  `[HasSheafify J AddCommGrpCat.{u}]` and `[(J.W (A := AddCommGrpCat.{u})).IsMonoidal]`.
  The canonical symmetric sheaf tensor and tensor-colimit instances come from
  `InternalSectionTensorComparison` and `SheafTensorStructure`. No extra closedness,
  Grothendieck, functorial-flat-resolution, or flat-ring-map hypothesis is added.
- `R S : Sheaf J AddCommGrpCat.{u}`, `MonObj R`, `MonObj S`, `IsCommMonObj R`, and
  `IsCommMonObj S` are the two commutative ring objects. Commutativity of S is implicit in
  the node's use of E_S; it is also recorded in the stage-1 review.
  `(a : R ⟶ S) [IsMonHom a]` is the given ring-object morphism.
- `sectionRingSheaf J R` and `sectionModuleEquivalence J R` (and the corresponding S
  terms) are the dependency's exact reconstructed ring sheaf and fixed equivalence.
  `sectionScalarMap J a` applies the monoidal inclusion and commutative-monoid
  functor-category equivalence to a, then the existing `commMonToRing`. Thus it is
  the section map of a, not an arbitrary map between reconstructed rings.
- The chosen ordinary unbounded derived categories are `DerivedCategory` with explicit
  `HasDerivedCategory.{w}` binders for the four module categories. This is the node's
  localization-size choice; there is no boundedness or completion condition.

Conclusions, read clause by clause:

- `restriction` has precisely the functor-order translation of
  E_R Res_a ≅ Res_(a_sec) E_S. Its restriction-sections clause says every component is
  identity on every underlying section, for all modules, site objects and sections.
- `sectionPair` is the already defined `SheafOfModules.ScalarDerivedPair (sectionScalarMap J a)`.
  Its `extension_obj` and `extension_map` fix the sectionwise functor to the recorded
  sheafified `changeOfRings` on objects and maps. Its `ordinaryUnit` fixes 1 tensor m,
  and its universal derived property, `computes`, and `normalization` retain the specified
  unbounded K-flat derived adjunction. This uses the additional already-landed node
  `def-sfb-scalar-hom-comparison-data`; its statement dependency was added under §5.
- `extension` has precisely E_S Ext_a ≅ Ext_(a_sec) E_R, using
  `Mod.extendScalars a`, the actual relative coequalizer extension. The helper
  `internalScalarGenerator` applies the sheaf tensor inclusion and `Mod.extendπ`.
  `extension_generators` sends this s tensor m to the sheafification of the identical
  sectionwise balanced tensor s tensor m. The equality transport is only the existing
  `sectionPair.extension_obj` identification.
- `ordinary_transpose` identifies the *specified* Hom adjunctions, using exactly
  `Mod.extendRestrictAdjunction a` and `sectionPair.ordinaryAdjunction`, not just an
  isomorphism of left adjoints. On identity maps it gives both unit and counit compatibility.
  The section pair fixes the unit m ↦ 1 tensor m; its Hom transpose therefore sends f to
  m ↦ f(1 tensor m), and its inverse sends g to s tensor m ↦ s g(m). In particular its
  counit is s tensor n ↦ sn. The generator equation and transpose equality give the same
  formulas internally. No separate unconstrained adjunction is substituted.
- `internalDerived`, `internalCounit`, `internalUniversal` give the universal left derived
  pair of the *actual* internal coequalizer extension. This is the generic existing
  `Functor.IsLeftDerivedFunctor` predicate on cochain complexes localized at quasi-isos.
  It expresses L(Ext_a) of `sk-def-sfb-derived-extension-of-scalars` without imposing the
  extra ambient functorial-flat-resolution typeclass needed to instantiate its generic
  upstream constructor on an arbitrary site. No second definition of a derived functor
  or K-flatness is made. Universal pairs are unique up to the canonical comparison.
- `internalComputes` gives invertibility of its universal counit on K-flat complexes.
  The K-flat predicate is the dependency's `IsKFlatIndependentCoefficients` on the termwise
  E_R-image, exactly equivalent to internal K-flatness by the recorded
  `internal_section_tensor_comparison`. This is not an extra hypothesis on an input:
  it is the universal K-flat representative clause in the conclusion.
- `internalAdjunction` uses actual termwise `(Mod.comap a).mapDerivedCategory`.
  Its internal-unit clause independently pins the internal derived adjunction:
  its unit followed by derived restriction of `internalCounit` and the canonical
  comap factorization is the localization of the specified ordinary internal chain
  unit, for every internal complex. This supplies the normalization missing in the
  returned head 8c16bc95777c, without any new hypothesis.
  The already recorded exactness instances for `Mod.comap` are used. `derivedRestriction`
  compares this with the section pair's exact derived restriction.
  `derivedRestriction_eq` fixes that isomorphism to localization of `restriction`, using
  the canonical composition and natural-isomorphism localization constructions.
- The derived section functors in `derivedRestriction` and `derivedExtension` are
  `(sectionModuleEquivalence J T).functor.mapDerivedCategory`, for T = R,S. These are
  precisely the termwise localized equivalences; their equivalence instances are supplied
  by `Functor.isEquivalence_mapDerivedCategory`, not arbitrary derived equivalences.
- `derivedExtension_complex` quantifies over every flat-term K-flat internal complex,
  expressed by the existing predicates on its unchanged E_R-image. Its equation identifies
  the two paths from E_S(T QP) to Q(Ext_(a_sec)(E_R P)): the internal universal comparison,
  canonical E_S factorization and localized `extension` on one path; `derivedExtension`,
  canonical E_R factorization and the section pair's universal comparison on the other.
  Thus the comparison on those representatives is exactly the localization of the
  generator-preserving termwise map.
- `derived_transpose` identifies the complete Hom bijections of `internalAdjunction` and
  `sectionPair.adjunction` under the *same* normalized derived comparisons. Substituting
  identities gives the derived unit and counit comparison equations. The independent
  internal-unit clause pins the internal adjunction; the section pair's `normalization`
  specifies its K-flat transpose formulas.
  There is no flatness assumption on a, on S over R, or on scalar restriction.

Dependency declarations used:

- `Sheaf.CategoryTheory.SheafTensorStructure`: `CategoryTheory.sfbSheafTensorStructure`
  (canonical tensor infrastructure), and the canonical sheaf instances it records.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionRingSheaf`,
  `sectionModuleEquivalence`, and `commMonToRing`.
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars` (publicly re-exported
  by its derived module): `CategoryTheory.Mod.extendScalars`, `extendπ`,
  `extendRestrictAdjunction`, and `comap`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, through the existing `scalarRestriction` alias.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  the existing sheafified tensor and its canonical universe-general monoidal instances.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`:
  the exact `Mod.comap` finite-limit/finite-colimit instances. The universal L(Ext_a)
  is expressed using the same generic left-derived-functor universal property rather
  than assuming the additional prerequisites of the generic ambient constructor.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`: `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Algebra.Homology.ScalarInternalHomData`:
  `ScalarDerivedPair`, `scalarModules`, `scalarRestriction`, `scalarDerivedRestriction`,
  and `scalarPairComplexComparison` in namespace `SheafOfModules`.
- `Sheaf.CategoryTheory.InternalSectionTensorComparison` supplies the actual E_R
  additivity, tensor-colimit and smallness infrastructure; its theorem justifies the
  transported K-flat and flat predicates. Its module is already a proof dependency.
- The remaining stated proof dependencies are imported directly: the balanced-bilinear
  universal property, independent-coefficient K-flat resolution, cochain universal
  derived change of rings and normalized derived Hom comparison.

Edge cases checked before drafting: a = identity; R or S the zero ring object;
zero module or zero complex; an empty site; unbounded complexes; a nonflat map such as
Z/4 → F_2. The statement excludes none of these. The nonflat example requires deriving
extension but exact restriction remains termwise. All comparisons are natural in modules
or derived objects, rather than tied to a selected resolution. No statement fault found.

Searches made:

- msearch LeanFinder: “The equivalence from internal module objects in abelian sheaves
  to sectionwise module sheaves identifies extension restriction scalar adjunctions and
  their derived adjunctions”. Eight hits on ordinary ModuleCat scalar adjunctions and
  module sheafification; no comparison of internal and sectionwise derived scalar pairs.
- msearch LeanSearch: “The internal module and sectionwise module sheaf equivalence
  preserves scalar extension restriction units counits and K-flat derived functors”.
  Eight hits on ModuleCat unit/counit, SheafOfModules restriction and module-sheaf
  pushforward sections; none states this comparison.
- msearch Loogle: `SheafOfModules.restrictScalars, CategoryTheory.Mod.extendScalars`.
  Zero hits; the service reports unknown identifier `CategoryTheory.Mod.extendScalars`
  (this name is project-specific). The actual upstream declaration was read directly.
- msearch grep: `internal.*section|section.*scalar` in
  `Algebra/Category/ModuleCat/Sheaf`: zero hits.
- Project rg searches for `sectionModuleEquivalence`, `internal.*section`,
  `scalar.*adjunction`, `derived.*scalar`, `changeOfRings`, and the proposed declaration
  names in both `lean/Sheaf` and `lean/WeilConjectures` found the reused infrastructure
  but no theorem identifying both scalar adjunctions with these normalizations.
- The required search for this exact blueprint id in `lean/WeilConjectures` found no hit.
  `dag/lean_names_upstream.json` searches found no matching recorded scalar-section
  comparison declaration. The proposed full declaration names have no collision in
  Mathlib or either project source tree.

Sources opened: the node and every statement dependency and its recorded declarations;
Stacks sites-modules.tex, section-tensor-product and lemma-sheafification-tensor;
the current blueprint's det-prop-scalar-six-pullback.proof.md (1).

Validation: every Lean file is compiled separately through scompile.py; the delivery's
required server preflight and compilation are run by deliver2.py --no-push before push.

The module's existence proposition only packages this item's conclusion. It introduces
no independent mathematical notion or substitute for a dependency. Every declaration
carries the node's source/blueprint docstring; the theorem docstring contains all six
proof steps, with the unit/counit maps and the derived representative argument.


## Returned-delivery repair, 2026-10-21

Repaired the independent review of immutable head 8c16bc95777c, point H3
(H4 aspect). The saved structure left internalAdjunction constrained only by
derived_transpose, so the statement could choose a conjugate of the sectionwise
adjunction without asserting the specified internal normalization. Added the
internal-unit compatibility clause immediately after the internalAdjunction
witness. For every internal cochain complex P it asserts exactly:

- Start with internalAdjunction.unit at DerivedCategory.Q.obj P.
- Apply derived internal restriction to internalCounit.app P.
- Apply (Mod.comap a).mapDerivedCategoryFactors.hom at the actual termwise
  internal extension of P.
- The result equals DerivedCategory.Q.map of the unit of
  (Mod.extendRestrictAdjunction a).mapHomologicalComplex (.up ℤ) at P.

Both sides run from Q(P) to Q(Res_a(Ext_a(P))). This equation refers only to
internal data and Mathlib's canonical exact-restriction factorization; it does
not use E_R, E_S, sectionPair, derivedExtension or derivedRestriction. It is the
ordinary-unit compatibility defining (Mod.extendRestrictAdjunction a).derivedAdjunction
after transport along rightDerivedComapIsoMapDerivedCategory, with the acceptable
universal internal left-derived pair used in place of a constructor that would
require additional ambient resolution hypotheses. No hypotheses, universes or
node statement changed. On a K-flat P, internalCounit is invertible, so naturality
and the unit equation give the internal derived transpose as internalCounit
followed by Q of the ordinary chain transpose; that transpose is s tensor p mapped
to s g(p). Thus the specified internal adjunction is pinned independently before
derived_transpose compares it to the sectionwise adjunction.

Self-check: read Mathlib.CategoryTheory.Functor.Derived.Adjunction,
Adjunction.derivedη_fac_app (the defining unit compatibility),
Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor,
Functor.mapDerivedCategoryFactors (direction Q DRes to Res_complex Q), and
WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars,
derivedExtendRestrictAdjunction and rightDerivedComapIsoMapDerivedCategory.
The added compatibility clause has the direction and ordinary unit of these constructions.
The identity ring map, zero ring/module/complex and nonflat ring map cases
remain included. The theorem docstring now describes the internal normalization
argument. This is the worker's repair self-check; independent review remains
with the maintainer.

## Second reading by Q26

Worker self-check for the returned repair, with the node, saved module and
current source interfaces open; no second agent was started, as instructed.
The sole returned defect was the free internalAdjunction normalization. The new
internal-unit compatibility clause uses the actual ordinary internal chain adjunction and the
existing internalCounit, and its two paths have identical endpoints
Q(P) and Q(Res_a Ext_a P). It does not reference the sectionwise data, so
derived_transpose now asserts compatibility between independently normalized
adjunctions. The original site/universe, ring commutativity, map, sheafification,
and derived-category hypotheses are retained. restriction_sections,
extension_generators, ordinary_transpose, internalUniversal, internalComputes,
derivedRestriction_eq and derivedExtension_complex retain every quantifier and
normalization previously checked by the independent maintainer. The identity map,
zero ring/module/complex, empty site, unbounded complexes and nonflat-map cases
remain allowed. No statement correction, additional node or dependency repair
was needed. The independent delivery review is supplied by the maintainer.

Compilation adjustment: the fixed 60-second per-file gate rejected the
record packaging. Profiling identified expensive automatically generated record
auxiliaries; even the equivalent PSigma packaging was too close to the limit
under current server load. The final InternalSectionScalarAdjunction is the
direct existence proposition: eight existential data witnesses (sectionPair,
restriction, extension, internalDerived, internalCounit, internalAdjunction,
derivedRestriction and derivedExtension), with each original proof field as
its identical property in a conjunction. The final derived_transpose formula
is the last conjunct. This is exactly the existence asserted by Nonempty of
the former record. The theorem now states this proposition directly, and its
lean.statement record is updated verbatim. No datum, hypothesis, property,
quantifier or comparison formula is dropped or weakened. In particular the
canonical derivedRestriction_eq expression is unchanged. The only additional
mathematical clause is the internal-unit normalization required by the return.
No helper declaration, new node, statement correction, alternate localization
formula, debug option or nonstandard unfolding setting is retained. All data
definitions are real constructions; the proposition uses only standard Exists
and And. The theorem proof remains the sole sorry.

Final validation, 2026-10-21: scompile.py compiled the delivered source cleanly
as sandbox and final library module in 32.0 and 50.2 seconds respectively,
with no warnings. The final self-check found only the authorized lean record
and the previously approved landed stmt_dep addition in the node delta;
lean.statement matches the theorem signature verbatim, every Lean line is at
most 100 characters, the theorem proof is the only sorry, and no probe module
remains. deliver2.py --no-push reported OK for commit c4937a31932: preflight
passes and the module compiles. The saved packet was repaired rather than
merely rebased or re-pushed; all mathematical clauses except the missing
internal-unit compatibility retain their original contents.

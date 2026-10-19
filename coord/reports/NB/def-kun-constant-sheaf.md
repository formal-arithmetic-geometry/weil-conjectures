## Worker report

This item uses existing declarations; no new module or duplicate constant-sheaf or
constant-complex definition is supplied. The primary declaration is
`CategoryTheory.Functor.mapHomologicalComplex`, in the recorded module
`Mathlib.Algebra.Homology.Additive`. Its signature is copied verbatim into
`lean.statement`. Supplementary compatibility declarations are identified below
and in `lean.note`, with their own source modules. The specialization below is the node's
entire construction, rather than a replacement notion.

Clause-by-clause correspondence:

* Scheme T: `T : AlgebraicGeometry.Scheme.{u}`; its small etale site is
  `T.Etale` with `T.smallEtaleTopology`.
* Commutative coefficient ring: `Λ : Type (u + 1)` with `[CommRing Λ]`.
  A coefficient module is `M : ModuleCat.{u + 1} Λ`. These are the shared
  coefficient universes of the project's etale sheaves; there is no finite,
  nonzero, or connectedness hypothesis. Smaller coefficients can be lifted
  to this common coefficient universe, as in the dependency's convention.
* The constant sheaf is
  `(constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M`.
  Reading `CategoryTheory.constantSheaf` in
  `Mathlib.CategoryTheory.Sites.ConstantSheaf` shows its defining expression
  is exactly `Functor.const T.Etaleᵒᵖ ⋙ presheafToSheaf ...`: restrictions
  in the constant presheaf are identities. This is the existing construction
  underlying the dependency `def-constructible-constant`, whose recorded
  `Sheaf.IsConstant` is essential-image membership for this same functor.
* The function description is supplied without restatement by the recorded
  proof dependency `lem-weil-pbc-constant-module-locally-constant`, namely
  `AlgebraicGeometry.Scheme.Etale.locallyConstantModulePresheafFunctor_iso_constantSheaf`
  in `Sheaf.ConstructibleSheaf.ConstantModuleLocallyConstant`. Its full signature
  asserts a natural isomorphism between the presheaf functor of locally
  constant module-valued functions and `constantSheaf ... ⋙ sheafToPresheaf ...`.
  Its real construction uses precomposition for restrictions and linear
  postcomposition for coefficient maps. The full definition and docstring were
  read. This covers functions into the discrete module, not arbitrary functions.
* A complex is `K : CochainComplex (ModuleCat.{u + 1} Λ) ℤ`, with no bound.
  Put `F = constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  Its constant complex is `(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K`.
  Reading the definition shows its objects are `F.obj (K.X i)`, its
  differentials `F.map (K.d i j)`, and its chain maps `F.map (f.f i)`.
* Shift compatibility is the existing natural isomorphism
  `F.mapCochainComplexShiftIso n` for every `n : ℤ`, from
  `shiftFunctor _ n ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ)` to
  `F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ shiftFunctor _ n`.
  `CategoryTheory.Functor.mapHomologicalComplex_commShiftIso_hom_app_f`
  identifies each component in each degree with the identity. The definition
  and full signature were read in `Mathlib.Algebra.Homology.HomotopyCategory.Shift`.
  Thus this is the canonical termwise shift comparison, including negative shifts.
* Quasi-isomorphism compatibility: for arbitrary complexes K and L and a map
  `f : K ⟶ L` with `[QuasiIso f]`, the existing instance
  `HomologicalComplex.quasiIso_map_of_preservesHomology` gives
  `QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)`.
  Its homology-preservation assumption is furnished by the existing exactness
  instances, not added as a hypothesis to this item. `F.Additive` is Mathlib's
  constant-sheaf instance in `Mathlib.CategoryTheory.Sites.Abelian`.
  `CategoryTheory.preservesFiniteLimits_constantSheaf` and
  `CategoryTheory.preservesFiniteColimits_constantSheaf`, read in
  `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`, supply
  the finite-limit and finite-colimit preservation. Their constructions use
  constant presheaves and sheafification, exactly the argument in the node's
  proof. For a derived interpretation, `F.mapDerivedCategoryFactors` identifies
  the termwise complex with the image under the induced derived functor.

Dependency declarations used/read:

* `def-weil-pbc-etale-site`: `AlgebraicGeometry.Scheme.smallEtaleTopology`
  in `Mathlib.AlgebraicGeometry.Sites.Etale`, together with `Scheme.Etale`
  in `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
* `def-constructible-constant`: `CategoryTheory.Sheaf.IsConstant` and
  `CategoryTheory.constantSheaf` in `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
  The former is exactly the predicate for the latter's essential image;
  there is no dependency interface defect requiring a replacement module.
* `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.Q` in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
* The function-model theorem is named above. The sheafification-exactness
  dependency has a usable Mathlib match in
  `Mathlib.CategoryTheory.Sites.Sheafification`; no extra declaration is needed.
  The exact-functor-derived-factorization dependency matches
  `CategoryTheory.Functor.mapDerivedCategoryFactors` and the associated
  shift and triangulated instances in `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.

Edge cases checked: the empty scheme and empty etale objects are covered by
sheafification (the function-model proof explicitly uses the empty covering);
the zero module and zero ring need no exclusion; arbitrary disconnected
schemes use locally constant functions rather than one global constant;
complexes are unbounded and degrees/shifts range over all integers; n = 0
has the same identity-component comparison. No finiteness hypothesis occurs.

Searches for an existing declaration:

* `msearch.py ... leanfinder` with query "The constant sheaf functor of modules
  on the small etale site applied termwise to complexes commutes with shifts
  and preserves quasi-isomorphisms": eight hits, including
  `mapHomologicalComplexUpToQuasiIsoLocalizerMorphism`,
  `mapHomologicalComplexUpToQuasiIso`, and `mapHomologicalComplexUpToQuasiIsoFactors`.
* `msearch.py ... loogle '"constantSheaf", "mapHomologicalComplex"'`:
  zero joint hits. Direct source inspection located the generic constructions.
* `msearch.py ... grep 'constantSheaf|mapHomologicalComplex_commShiftIso_hom_app_f'
  CategoryTheory/Sites`: 21 hits including `constantSheaf` and its additive instance.
* `rg` of the source tree for `def-kun-constant-sheaf`: no node-tagged declaration.
  Searches for constant complexes and constantSheaf/mapHomologicalComplex in
  both the upstream tree and `lean/Sheaf` found existing usages, notably
  `Sheaf.Paper.FiniteFreeEtaleLocalActual`, which uses precisely this termwise
  construction with the same coefficient universe. Upstream `constantComplex`
  usages concern a single coefficient object in the derived category, not a
  competing definition for arbitrary input complexes.
* Direct Mathlib searches located `mapHomologicalComplex` in `Additive.lean`,
  the canonical shift comparison in `HomotopyCategory/Shift.lean`, and
  `quasiIso_map_of_preservesHomology` in `QuasiIso.lean`; the full definitions,
  surrounding hypotheses and docstrings were read.

Validation: the sandbox scratchpad `Check.lean` uses only the prescribed
`scompile.py` wrapper. It checks additivity, finite-limit and finite-colimit
preservation by instance search for the actual etale/module specialization,
then checks quasi-isomorphism preservation and constructs the canonical shift
isomorphism. It also checks the function-model theorem. Scratch examples are
not delivered. The existing-declaration delivery dry run separately checks all
recorded declaration names against the live library.

No new nodes, dependency repairs, statement corrections, or disputed statements.

## Second reading by NB

Independent reading of the node copy, its blueprint source at order 1679,
all three statement-dependency records and their source declarations, and the
existing constructions named in the worker report. No statement correction,
new node or dependency module is present or needed.

The node's objects, hypotheses and clauses, in order:

1. An arbitrary scheme T and its small etale site. Rendered by
   `T : Scheme.{u}`, `T.Etale`, `T.smallEtaleTopology`. I read the dependency's
   `Scheme.Etale` definition (MorphismProperty.Over, with finite limits) and
   `smallEtaleTopology` and its covering-family characterization. Verdict: the
   specified site, with no connectedness, separation or finiteness assumption.
2. A commutative ring Lambda and a Lambda-module M. Rendered by
   `Λ : Type (u + 1)`, `[CommRing Λ]`, `M : ModuleCat.{u + 1} Λ` in the
   recorded specialization. Verdict: arbitrary coefficients under the shared
   etale coefficient size convention. This does not require a field or a
   nonzero ring. The primary generic declaration itself has independent
   category universes, rather than imposing a universe equality.
3. The constant sheaf is sheafification of the identity-restriction constant
   presheaf. Rendered by `(constantSheaf T.smallEtaleTopology
   (ModuleCat.{u + 1} Λ)).obj M`. I read `constantSheaf`'s actual definition
   `Functor.const Cᵒᵖ ⋙ presheafToSheaf J D`, and `Sheaf.IsConstant` in
   the dependency module: essential-image membership for that very functor.
   Verdict: exact construction, with no private substitute for the dependency.
4. The sheaf of locally constant M-valued functions. Rendered by
   `Scheme.Etale.locallyConstantModulePresheafFunctor_iso_constantSheaf`.
   Its statement is a natural isomorphism, under Nonempty, of the presheaf
   functors in M; its underlying presheaf takes U to
   `ModuleCat.of Λ (LocallyConstant U.unop.left M)`, restrictions are
   precomposition and linear coefficient maps act by postcomposition.
   I read the definition, the full theorem and its surrounding hypotheses.
   Verdict: exactly the discrete-coefficient function model; no arbitrary
   functions or global-constant-only restriction.
5. An arbitrary complex of modules and its termwise constant complex.
   Rendered by `K : CochainComplex (ModuleCat.{u + 1} Λ) ℤ` and
   `((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomologicalComplex
   (ComplexShape.up ℤ)).obj K`. The actual `mapHomologicalComplex` definition
   applies F.obj to every term and F.map to differentials and chain-map
   components. Its zero-preservation assumption is inferred for the actual
   constant-sheaf functor. Verdict: exact construction, without boundedness.
6. Compatibility with shifts. Rendered by `F.mapCochainComplexShiftIso n`
   for every integer n. I read its `NatIso.ofComponents` construction from
   degreewise `Iso.refl`, and
   `mapHomologicalComplex_commShiftIso_hom_app_f`: every degree component
   is the identity. Verdict: the canonical comparison with the specified
   signed cochain shift, including all negative shifts and n = 0.
7. Compatibility with quasi-isomorphisms. Rendered by the existing
   `HomologicalComplex.quasiIso_map_of_preservesHomology` instance on arbitrary
   `f : K ⟶ L` with `[QuasiIso f]`. I read its hypotheses and the exactness
   instances `preservesFiniteLimits_constantSheaf` and
   `preservesFiniteColimits_constantSheaf` in ConstantSheafOver, which use
   constant presheaves followed by sheafification. Verdict: the required
   property, with exactness supplied by instances rather than added as a
   hypothesis. The dependency's DerivedCategory is the localization of these
   cochain complexes at quasi-isomorphisms; no bounded replacement is used.

Source cross-check: the blueprint text agrees verbatim with the node's
statement. Stacks sites.tex Example `example-constant-sheaf` assumes only a
site and a set. etale-cohomology.tex Remark
`remark-constant-locally-constant-maps` treats arbitrary abstract groups and
Zariski locally constant maps on the small/big sites; its surrounding text
adds no finiteness assumption to this remark. sites-modules.tex
`lemma-constant-exact` starts with arbitrary abelian groups and uses exact
sheafification; `lemma-sheafification-exact` allows any presheaf of rings.
derived.tex `lemma-right-derived-exact-functor` treats exact functors between
abelian categories and explicitly includes the unbounded derived category.
The node's three proof steps are therefore supported by the cited existing
constructions: constant sheaf/function comparison, additivity and exactness,
then termwise application with quasi-isomorphism and shift compatibility.

Edge cases: empty scheme and empty etale objects remain allowed; the existing
function-model proof explicitly uses the empty covering for local injectivity.
The zero module and zero ring are admitted. Disconnected schemes use locally
constant functions. All integer degrees, unbounded complexes, zero and negative
shifts are covered. There is no finite index-set assumption; empty limits and
colimits are included in the exactness instances. No characteristic condition
is introduced. All scratch variables/universes are explicitly bound under
`autoImplicit false`.

Independent searches: ran msearch Loogle with
`"mapCochainComplexShiftIso"` (three hits, including the comparison and its
component formulas), and LeanFinder with "Prolongation of an additive functor
to cochain complexes commutes with integer translation and sends homology
equivalences to homology equivalences" (eight hits, including the induced
localizer morphism and its shift instance). Independent rg searches for
`constantComplex`, `constantSheaf.*mapHomologicalComplex` and the blueprint id
in upstream WeilConjectures and project Sheaf found the termwise usage in
FiniteFreeEtaleLocalActual and upstream `Etale.constantComplex`; the latter is
the single coefficient-ring object, not a construction on arbitrary complexes.
Direct Mathlib inspection found the generic prolongation, shift and quasi-iso
instances above. Thus existing:true is appropriate and a new module would
duplicate existing constructions.

Mismatch/change verdict: none in the mathematical record. Kept the worker's
node and report intact and appended this independent reading. The primary
lean.statement matches the definition header verbatim through the type before
`where`; all supplemental modules are identified in lean.note. Since there is
no delivered module, new docstrings or postponed proofs are unnecessary; there
is no hollow definition and nothing new is proved. Re-ran the prescribed
scompile.py on scratchpad/Check.lean: local overlay and library checks both
succeeded without warnings, verifying additivity, exactness, arbitrary quasi-iso
preservation and the integer shift comparison for the actual specialization.

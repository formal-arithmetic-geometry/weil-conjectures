## What changed

`Sheaf.AlgebraicGeometry.ProperFlatGlobalSectionsCriterion` now has a complete proof
of its unchanged theorem from one new single-point stalk lemma. Its private
`fiberwise_appTop_isIso_baseChange` is fully proved: the Mathlib fibre pullback square,
flatness of the residue-field map, the flat-base-change pushout on top opens and
`IsPushout.isIso_inr_of_isIso` establish the hypothesis after every base change.
Stalk detection then proves both clauses of the original theorem. Properness, flatness
and local finite presentation of the base-changed projection are supplied explicitly
by their base-change instances.

The new module `Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk` isolates the
local derived argument. Its hypothesis concerns only one residue-field fibre and its
conclusion only one stalk. It does not assert a global or universal isomorphism.
The complete natural-language proof uses a rank-minimal finite free model of the
perfect direct image, represents the derived structure map, and uses its invertible
degree-zero component at the local ring to force the outgoing differential to vanish.
It also spells out the comparison to the specified chosen tensor adjunction unit.
No data is chosen from an unproved existence result in any new definition: no new
definition is introduced.

The original public imports, signature, universe, visibility and statement are unchanged.
The proof-only imports were replaced and its DAG proof updated. The new module publicly
imports the stalk API required by its statement and privately imports its two derived
proof dependencies. No other existing module is adapted, and no change record is needed.

Sources read: Stacks `perfect.tex`, `lemma-proper-flat-h0`, the Tag 0E62 proof;
Mathlib `Morphisms/Flat.lean` lines 222–243 and 457–470; Mathlib `Fiber.lean`'s
`isPullback_fiberToSpecResidueField_of_isPullback`; the source library's
`Modules/FlatPullbackStalk.lean` and `Sites/EtaleTopologicalInvariance/GlobalSections.lean`.
Both delivered modules compile cleanly through the authorized `lcompile.py --all`.

## Proved and sorry left

Closed the original explicit hole in
`AlgebraicGeometry.isIso_structureSheafMap_of_proper_flat_fiberwise`
(node `lem-sc-proper-flat-global-sections-criterion`).
The private helper `fiberwise_appTop_isIso_baseChange` has a complete proof with no holes.

Added exactly one explicit hole:
`AlgebraicGeometry.bijective_structureSheafMap_stalk_of_proper_flat_fiber`
(node `lem-sc-proper-flat-structure-sheaf-stalk`), in the new module
`Sheaf.AlgebraicGeometry.ProperFlatStructureSheafStalk`, with proof exactly `:= by sorry`.
There are no sorries left in the item's module and no other holes added by the delivery.
This is a decomposition, not an axiom-free proof of the geometric criterion: one upper
hole closed and one strictly local lower hole added, giving net zero explicit holes.
The pre-existing derived dependency theorems remain unfinished and are not edited.

Edge cases for the new statement: an empty base has no point to which it applies;
an empty fibre over a point fails its field-to-zero-ring isomorphism hypothesis;
identity morphisms and any field base satisfy the expected conclusion.
Nonreduced and non-Noetherian bases are allowed: the argument uses a perfect finite free
model and invertibility in the local ring, with no reducedness or Noetherian assumption.
No statement about neighbouring fibres is assumed. The negative fibre cohomology
vanishes because this is a derived image of a single sheaf, independently of H^0.
The main proof also handles the empty base and empty base changes by stalk detection.

## No longer needed

Removed direct proof imports:
`Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion` and
`Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`.
The latter remains needed through the new local lemma; it is not globally pruned.
The node `lem-sc-perfect-degree-zero-fibre-criterion` is no longer a proof dependency:
the rank-one argument at a single local ring replaces its global splitting argument.
Its finite free residue model remains needed, so it is not pruned.

The following 20 modules disappear from this item's transitive import closure when
compared against the initial source. This is a local closure calculation; another
route from the targets may still need them. Their matching node records are listed
where present, so the maintainer can compute the actual global pruning:

- `Sheaf.Algebra.Homology.AffinePerfectCutDegreeZero` (nodes: `lem-pc-affine-perfect-cut-degree-zero`)
- `Sheaf.Algebra.Homology.ModuleCohomologyBaseChange` (nodes: `def-pc-module-cohomology-base-change`)
- `Sheaf.Algebra.Homology.RingPseudoCoherentSummand` (nodes: `lem-pc-ring-pseudo-coherent-summand`)
- `Sheaf.AlgebraicGeometry.DegreeZeroFibreSurjective` (nodes: `def-sc-degree-zero-fibre-surjective`)
- `Sheaf.AlgebraicGeometry.FiniteLocallyFreeResidueIso` (nodes: `lem-sc-finite-locally-free-residue-isomorphism`)
- `Sheaf.AlgebraicGeometry.PerfectCutComplexDegreeZero` (nodes: `lem-sc-perfect-cut-complex-degree-zero`)
- `Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion` (nodes: `lem-sc-perfect-degree-zero-fibre-criterion`)
- `Sheaf.AlgebraicGeometry.PerfectSummand` (nodes: `lem-pc-perfect-summand`)
- `Sheaf.AlgebraicGeometry.PseudoCoherentSummand` (nodes: `lem-pc-pseudo-coherent-summand`)
- `Sheaf.Paper.DerivedSplittingUnique` (nodes: `lem-pc-derived-splitting-unique`)
- `Sheaf.RingTheory.FiniteFreeMapResidueLocalization` (nodes: `lem-pc-finite-free-map-residue-localization`)
- `Sheaf.RingTheory.FiniteProjectiveCokernelLocalization` (nodes: `lem-pc-finite-projective-cokernel-localization`)
- `WeilConjectures.Algebra.Homology.Monoidal.Dual` (no matching `lean.module` node record)
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable` (no matching `lean.module` node record)
- `WeilConjectures.CategoryTheory.DerivedCategory.Perfect` (nodes: `def-pc-perfect-ring-complex`)
- `WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat` (no matching `lean.module` node record)
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed` (no matching `lean.module` node record)
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective` (no matching `lean.module` node record)
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence` (no matching `lean.module` node record)
- `WeilConjectures.Mathlib.RingTheory.Flat.Basic` (no matching `lean.module` node record)

## Where the brief, the DAG or earlier work was wrong

The original DAG gave the mathematical derived route but its two declarations do not
by themselves connect the derived unit to the ordinary chosen tensor-pullback unit in
this signature. No existing theorem supplies that comparison together with the local
rank-one argument. The new lemma owns precisely that local work. The original theorem
and source are not disputed; no hypothesis or conclusion is changed.

The universal clause needs only degree-zero flat base change between residue fields,
not a second application of the global perfect-complex criterion after arbitrary
derived pullback. This is proved directly in Lean, rather than left as another hole.
The unit record `sk-prop-av-cube` has empty realized entries, and this below-unit change
keeps the theorem-of-the-cube ancestor's structure-sheaf pushforward argument.

Searches actually run through `msearch.py`: LeanFinder on both the global theorem and
the local stalk criterion, Loogle on `SheafOfModules, IsIso` and `AlgebraicGeometry.Flat`,
and grep for stalk isomorphisms and for proper-flat stalk results. LeanSearch on the
local stalk criterion returned Internal Server Error and is recorded as unavailable.
Blueprint searches for “proper flat” and “structure sheaf” found no duplicate of the
single-point stalk criterion. The source and all existing signatures were read before
introducing the new module.

## New nodes

`lem-sc-proper-flat-structure-sheaf-stalk` in
`dag/nodes/sec-abelian-varieties/lem-sc-proper-flat-structure-sheaf-stalk.json`
states bijectivity at one fixed base stalk from the canonical functions isomorphism on
that one fibre. Its source is the local argument in Tag 0E62, with the Tag 0BCD minimal
free model. Its proof dependencies are `lem-pc-rf-perfect-base-change`,
`lem-sc-perfect-finite-free-residue-model`, and `lem-pc-module-pullback-adjunction`.
It inherits the item's chapter and unit and records the theorem-of-the-cube ancestor.
Its statement has no global or base-change conclusion, so it is a strict part of the
argument. The new node carries actual searches, complete proof steps and its verbatim
Lean signature. No change records or forced adaptations are present.

## Second reading by X3

1. Compared the delivered item module with the repository version. The public theorem
signature, hypotheses, conclusion, universe, and visibility are unchanged; only proof
imports, the private helper, and the proof body changed. The new stalk module and node
are the only additions.

2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds. The
item has no remaining `sorry`; the sole remaining hole is the named split theorem in
the new stalk module. No forbidden declarations or hollow definitions were introduced.

3. Checked the split statement and node against the Lean declaration. It is a strict
single-point reduction, with no universal conclusion or duplicated target statement;
its source, proof description, dependencies, and searches are recorded in the node.
The statement is true in the stated proper, flat, finitely presented setting and has
no added assumptions beyond the fibre hypothesis.

4. Checked pruning and imports. The two former direct proof imports are removed; the
new stalk proof dependency imports the perfect base-change machinery. The updated node
proof and `proof_deps` follow the actual Lean route, and the unit route remains
represented by the target theorem.

5. Checked the universal base-change helper: the residue-field map is flat, the fibre
square is the Mathlib pullback square, and the pushout isomorphism argument is compiled
successfully. No existing declaration signatures or definitions were altered.

Changed after this reading: added this review section only; no Lean or DAG changes.

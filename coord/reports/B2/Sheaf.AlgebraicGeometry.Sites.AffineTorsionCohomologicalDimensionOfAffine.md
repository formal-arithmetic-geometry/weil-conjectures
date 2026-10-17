## What changed

Repaired the return at head 28c84b472 by removing duplicate proved helpers and importing
and using the existing declarations, including private declarations through Lean's
`import all` form already used by PolynomialGenericStrictLocalizationField.

AffineInfinityBoundarySupport now reuses:

- residueFieldHomOfOver_eq, polynomial_residue_trdeg_le and infinity_residue_trdeg
  from AffineLineInfinityStrictLocalModel;
- projectiveLine_polynomial_geometry from AffineLineProjectionStalkBound;
- Etale.strictHenselizationComparison_over and Etale.nonempty_addEquiv_strictLocalization
  from FieldHigherDirectImageStalk.

The same repair is applied throughout the delivery. AffinePolynomialProjectionSupport
reuses its strict-localization comparison from FieldHigherDirectImageStalk and its
point-pullback and affine-line helpers from AffineLineProjectionStalkBound. It reuses the
coordinate isomorphism from AffinePolynomialHigherProjectionSupport. The latter reuses
four existing compactification/Leray helpers from AffineLineProjectionStalkBound.
SupportedTorsionCohomologyBound reuses Etale.dim_finite_union_le from SupportDimension.

The main module combines its two one-way cohomology conversions into the private theorem
subsingleton_etaleCohomology_iff_H. This is an equivalence proved from the existing
nonempty_sheafH_extDerivedIso and used in both directions. Importing the duplicate conversion
from FiniteTypeTorsionCohomologicalDimension would create a cycle, confirmed by
import_direction.py; that later theorem already imports this item.

The retained proof closes the unchanged affine torsion cohomological dimension theorem
by simultaneous dimension induction over all fields, finite normalization, algebraic-closure
descent, polynomial projection, supported cohomology and Leray. Its seven new public
intermediate theorems are fully proved, including the punctured coefficient-field argument.
The unit route, every existing public signature and visibility, and the assigned module's
public imports stay unchanged. No existing module besides the assigned item is adapted.
No change record is needed. The earlier returned G2 helper adaptation remains omitted.

The existing second reading below predates this repair and is retained as historical evidence;
a fresh independent reader must check this repaired version before delivery. No second reading
has been performed by this repair worker.

## Proved and sorry left

One of one original holes is closed:
AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_isAffine
(thm-sc-affine-torsion-cd). Zero holes remain in the assigned module.

All seven new public declarations are proved, with zero holes added:

- subsingleton_H_of_bounded_support (lem-sc-supported-torsion-cohomology-bound);
- subsingleton_H_polynomial_of_lowerDimension (lem-sc-affine-polynomial-induction-step);
- isZero_stalk_polynomialProjection_of_lowerDimension
  (lem-sc-affine-polynomial-projection-support);
- isZero_stalk_polynomialProjection_of_lowerDimension_of_gt_two
  (lem-sc-affine-polynomial-higher-projection-support);
- isZero_rightDerived_projectiveLine_of_killed_by
  (lem-sc-projective-line-bounded-torsion-vanishing);
- isZero_stalk_infinityBoundary_of_lowerDimension
  (lem-sc-affine-infinity-boundary-support);
- hasTorsionCohomologicalDimensionLE_punctured_of_coefficientField
  (lem-sc-punctured-coefficient-field-cohomological-dimension).

All eight delivered Lean modules contain zero sorry tokens. This is a proof from existing
library declarations, not a claim that every imported obligation is already axiom-free.
No axiom, unsafe declaration, opaque declaration, or hollow definition is introduced.

Edge cases retained: the empty scheme including degree zero; polynomial dimensions zero
and one; n=0 at the generic degree-two stalk; empty supported complements; nonclosed base
points; q>d; separably closed geometric fields tested after algebraic closure; and the
punctured dimension-one case.

## No longer needed

The duplicate helpers listed under What changed are removed, rather than renamed or
reproved locally. The old affine-line and infinity modules remain imported for their
existing private proofs; their withdrawn public interfaces are not used. They are therefore
not claimed as globally pruned modules in this repair.

Removed redundant proof imports from AffineInfinityBoundarySupport:
WeilConjectures.PointCount, Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg,
Mathlib.RingTheory.KrullDimension.Polynomial, Mathlib.RingTheory.KrullDimension.Field,
Sheaf.AlgebraicGeometry.ClosedImmersionResidueFieldIso,
WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth,
Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula,
WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived,
WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility,
and WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections.

Removed redundant proof imports from AffinePolynomialProjectionSupport:
Mathlib.AlgebraicGeometry.AffineSpace, Mathlib.Algebra.MvPolynomial.Equiv,
WeilConjectures.AlgebraicGeometry.Curve.TorsionCohomologicalDimension,
Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula,
WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived,
WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility,
and WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections.

The main module no longer directly imports the original wrapper modules
ArbitraryCurveCohomologicalDimension, SeparablyClosedTorsionCohomologicalDimension,
DimensionPreservedFieldExtension, or OneVariableFieldCohomologicalDimension: the existing
source bounds, field-base-change dimension inequality and proved RatFunc bound suffice.
The main node's removed direct dependencies remain exactly those recorded in its sandbox
proof_deps; the new intermediate nodes retain the local-model, stalk, affine-limit,
projective-line, support-union and Leray inputs actually used. No Lean file is withdrawn,
and no whole module is claimed globally unreachable.

The complete list of original direct imports removed from the assigned module is:

- `Sheaf.AlgebraicGeometry.DimensionPreservedFieldExtension`
- `Sheaf.AlgebraicGeometry.Sites.AffineLineProjectionStalkBound`
- `Sheaf.AlgebraicGeometry.Sites.ArbitraryCurveCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Sites.TorsionCohomologicalDimensionAffineLimit`
- `Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModel`
- `Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula`
- `Sheaf.AlgebraicGeometry.SupportDimensionUnion`
- `Sheaf.AlgebraicGeometry.TorsionFilteredUnion`
- `Sheaf.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing`
- `Sheaf.CategoryTheory.GrothendieckSpectralSequence`
- `Sheaf.FieldTheory.OneVariableFieldCohomologicalDimension`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine.GeometricStalk`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`
- `WeilConjectures.SixFunctors.Finite.Exact`
- `WeilConjectures.SixFunctors.Finite.Stalk`

These removals concern direct imports; some remain transitive proof inputs.

The complete list of old direct proof dependencies removed from thm-sc-affine-torsion-cd
is (these can still occur transitively in the new reductions):

- `lemma-weil-pbc-finite-stalk-formula`
- `lemma-weil-pbc-finite-direct-image-exact`
- `lem-sc-arbitrary-curve-cd`
- `lem-sf-separably-closed-torsion-cd`
- `lem-weil-pbc-dimension-preserved-field-extension`
- `def-kun-transcendence-degree`
- `lem-sc-cd-affine-limit`
- `lem-sc-one-variable-field-cd`
- `lem-sc-smooth-strict-local-field-model`
- `lemma-weil-pbc-p1-exchange-geometric-stalk`
- `lem-weil-pbc-p1-field-dimension-one`
- `lem-weil-pbc-direct-image-preserves-injectives`
- `lem-weil-pbc-etale-restriction-injectives`
- `lemma-openclosed-stalk-upperstar`
- `lem-sc-exact-functor-higher-derived-vanishing`
- `prop-weil-pbc-strict-henselization-stalk-formula`
- `def-weil-pbc-etale-cohomology`
- `thm-sp-grothendieck`
- `lem-sc-affine-line-projection-stalk-bound`
- `lem-sc-support-dimension-union`
- `lem-weil-pbc-cohomology-filtered-colimit`
- `lemma-weil-pbc-torsion-filtered-union`

The obsolete top-level tool approval removed is `lemma-weil-pbc-finite-stalk-formula`.

## Where the brief, the DAG or earlier work was wrong

The returned delivery copied private helper proofs already available in the library.
The library's own PolynomialGenericStrictLocalizationField demonstrates the supported
`import all` access pattern; ordinary imports alone would not make these private names
usable. The repair now uses that pattern instead of duplicating facts or changing visibility.

The original affine-line and infinity public interfaces are commented out after an upstream
sync. Their still-active private helper proofs remain usable. The new boundary principal-open
proof supplies the repaired small-colimit evaluation/local-ring transport itself. The main
source affine theorem is a wrapper back to this item and cannot be used without a cycle.

The projection drops the first coordinate to match finSuccEquiv. This changes only the new
helper signatures and leaves the target unchanged. The cycle-free projective-line geometric
stalk comparison and exact coefficient forgetting preserve the unit's proper-base-change route.

## New nodes

The seven retained nodes are unchanged in statement and all their public theorems are proved:
lem-sc-supported-torsion-cohomology-bound (directed support union and finite comparison),
lem-sc-affine-polynomial-induction-step (global Leray diagonal),
lem-sc-affine-polynomial-projection-support (degree two and higher weighted support),
lem-sc-affine-polynomial-higher-projection-support (compactification and mixed-term vanishing),
lem-sc-projective-line-bounded-torsion-vanishing (finite-coefficient geometric-stalk bound),
lem-sc-affine-infinity-boundary-support (punctured strict-local calculation), and
lem-sc-punctured-coefficient-field-cohomological-dimension (explicit RatFunc embedding,
transcendence drop, finite-subalgebra induction and affine-limit passage).

The repair adds no node, statement or hole. The changed proof metadata records reuse of
existing private facts. There is no change record and no forced adaptation.

## Earlier second reading (a previous round; superseded)

1. **Signatures and accidental changes — PASS.** I compared the assigned module with the
shared repository. The target theorem's signature, universes, visibility, and definitions are
unchanged; only its proof imports and proof body changed. The seven additional modules are new
split nodes, and their public theorem statements match the `lean.statement` fields in their DAG
nodes. The previously returned G2 helper is absent from this delivery, so no held module is
adapted and no change record is required.

2. **Proof and axioms — PASS.** `lcompile.py --all` compiles all eight delivered modules with
no errors or warnings, each under the fixed time limit. A source scan finds no `sorry`, `axiom`,
`unsafe`, `opaque`, `implemented_by`, `extern`, or `debug.skipKernelTC`. The delivered proofs
use only the permitted foundational axioms, apart from `sorryAx` that may occur in existing
imported obligations; no new hole is introduced.

3. **Split statements — PASS.** Each of the seven new public theorems is a proper reduction of
the affine theorem: support cohomology, polynomial projection, higher projection, projective
line, infinity boundary, and punctured coefficient field. Each has a source, docstring proof,
and matching DAG node, and none restates the target. The rational-function bound uses the
existing proved source theorem directly. Empty schemes, dimensions zero and one, the generic
degree-two case, and the dimension-one puncture were checked in the corresponding proofs.

4. **Route and pruning — PASS.** The proof keeps the unit route through finite normalization,
simultaneous field induction, polynomial projection and Leray support. The new modules retain
the required lower-dimensional, strict-local, projective-line, and affine-limit inputs. Imports
and direct proof dependencies removed from the main node are listed under “No longer needed”; the
withdrawn G2 helper is not modified.

5. **DAG agreement — PASS.** The assigned node's `proof`, `proof_deps`, and `proof_origin` now
describe the implemented induction route. Every new node records its theorem, module, source,
proof steps, dependencies, and split status. The Lean declarations and DAG signatures agree,
and the unit record is unchanged.

The second reading added this section only; no Lean declaration, statement, definition, or
consumer interface was changed during the review.

## Second reading by B2

1. **Existing interfaces — PASS.** Compared all eight delivered module paths with the shared
repository. Only the assigned module already exists; the other seven are new. The target
theorem signature is byte for byte identical, with the same universe, visibility, quantifiers,
field bound, finite-type assumptions, dimension conversion and empty-scheme clause. Its four
public imports also agree. No existing definition or other held module is changed. The new
public signatures agree with their node records. No change record is required.

2. **Proof and axioms — PASS.** A fresh `lcompile.py --all` compiled all eight modules without
errors or warnings (each in 0.9–1.3 seconds). A fresh scratch `#print axioms` checks all seven
new public theorems and the target: supported cohomology, punctured coefficient fields and
infinity-boundary vanishing use only propext, Classical.choice and Quot.sound. The projective
line, higher projection, projection support, polynomial induction and target also use sorryAx
from existing imported obligations. No delivered module contains a sorry or forbidden trust
mechanism; no definition or arbitrary data choice from an unproved existence is introduced.
The puncture constructs the RatFunc map by localization, rather than postulating a field map.
The coefficient-field witnesses in the boundary argument are eliminated inside a proof.

3. **New reductions — PASS.** Read every proof and docstring against its node. All seven
public intermediate theorems are proved and strictly narrower than the affine theorem. The
all-fields hypothesis in the puncture and polynomial steps is precisely the strong induction
hypothesis supplied by the main module. Checked e=1 (zero-dimensional finite subalgebras),
n=0, the q=2 generic stalk, q>d (all stalks vanish), a=0, an empty supported complement,
nonclosed base points, and the empty scheme at degree zero. N>0 makes each bounded sheaf
torsion; N=1 just gives a zero sheaf. The infinity chart pulls its explicit coordinate back
through the small-colimit comparison; flatness makes that coordinate nonzero. The weighted
cardinal inequality gives exactly the required integer inequality. Independent LeanFinder
search for Artin vanishing by support induction found no matching theorem; Loogle returned
only generic injective-object derived vanishing, already accounted for in the proof. Mathlib
grep and differently worded source searches found no missing shortcut. Checked the prior
return: its six duplicated helpers now come from import all, and the other reused helpers
come from their original modules. The old principal-open and public affine-line interfaces
are commented out upstream, so they cannot replace the repaired arguments here.

4. **Route and pruning — PASS after report repair.** The proof retains simultaneous field
and dimension induction, algebraic-closure descent, finite normalization, the polynomial
projection, compactification in P1, the strict-local puncture, supported cohomology, and the
Leray diagonal. Read dag/units/sk-prop-sf-cbc.json: its realized statement/step lists are empty
and unchanged; no unit route is replaced. Each public import supplies signature material,
and the added helper imports are private proof imports. The original direct imports are
listed above; this reading added the exact removed proof_deps and tool_uses entries. No
whole module is claimed pruned, since old helper modules remain transitively imported.

5. **DAG agreement — PASS after metadata repair.** Read all eight node files. Each proof_deps
is the union of its proof-step uses; the seven new nodes have their source, complete
statement, matching Lean record, three search kinds, creation record and blueprint ancestry.
Existing-node changes are limited to proof/proof_deps/proof_origin and deletion of an obsolete
tool approval. Corrected the supported-cohomology step that still said the reused finite-union
lemma was proved locally. Corrected the main node's dimension step to describe the actual
finite upper-bound argument, which does not use nonemptiness.

This second reading changed only these two proof descriptions and this report (including
the exhaustive pruning inventory). No Lean code, statement, definition, import or hole changed.

## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.FieldExceptionalSystem.field_exceptional_system_comparison`
with an assembly of two geometric subresults and complete categorical proofs. The public
signature and public import remain unchanged. Private helpers construct the restricted support
isomorphism, prove the specified counit transpose's counit, naturality and unit laws,
derive transition naturality by transposing the actual strict transition, prove composition
and identity under the actual scalar associators/unitors, and
use finite invertibility plus the existing conservative evaluations to obtain invertibility
in the normalized full subcategory. The unit and composition calculations specialize the
proved private categorical arguments in ReductionCompatibilities; they are included privately
here because
that module does not export them. Naturality is proved directly with the adjunction Hom
bijection, avoiding elaboration of a concrete mate-equivalence expression.

Also removed four unused private imports from the unclaimed definitions-only module
Sheaf.Paper.FieldExceptionalSystemDomains. Its public imports and declarations remain
verbatim. The edited Domains module compiled without warnings in 9.1 seconds.
The delivery also proposed typed `def` projections in the unclaimed Adjoints module and an
explicit finiteTheta type in the unclaimed FieldPurityTransposeLevelWords, for compile time.
The independent reader withdrew both changes and restored the two published modules verbatim.
The withdrawals are recorded in M9-field-exceptional-adjunction-projection.md and
M9-field-purity-finite-theta-type.md.

Validation (reader, 2026-10-26, re-delivery a81ecce98000): a sandbox rebuild used the delivered
Domains, the new modules and the item, with the published Adjoints and LevelWords and the current
published importers. Every exceptional interface module compiled. The item took 51.8 to 57.1 s and
FieldPurityTransposeLevelWords 57.7 s, at a machine load of about 90. The unchanged published Adjoints
took 59.5 s in the same run, and at lower load the earlier review measured 45.1 s and 35.4 s.
FieldPurityTransposeArrows and the item's direct importers FieldOrientationSystemCoordinates,
FieldOrientationSystemComparison and FieldExtensionTowers also compiled. FieldProjectionOriginWitnesses
(newly proved by C3) stops at 120 s in any sandbox rebuild, including an all-published control. Its
published single-file compile passes in 55 s, so that timeout does not come from this delivery.
`#print axioms field_exceptional_system_comparison` gives propext, sorryAx, Classical.choice
and Quot.sound. sorryAx comes from the two new substeps.

Two new modules state proper geometric substeps with complete source proofs in their
docstrings. FieldExceptionalNormalizedAdjoints states existence of the normalized domains
and adjunctions with the right-adjoint quotient formula. FieldExceptionalFiniteCompatibility
states the evaluated transpose equation, finite invertibility, and agreement of mixed finite
quotient paths. Neither assumes or restates the whole-system comparison theorem. Their
statements quantify over the already supplied Models, support comparison, and where relevant
adjoint data. No object is chosen from an unproved mere existence theorem in a definition.

## Proved and sorry left

One existing hole closed: `AlgebraicGeometry.ProEtale.FieldExceptionalSystem.field_exceptional_system_comparison`
(node `lem-sp-field-exceptional-system-comparison`). No sorry remains in the item module.

Two holes added:

- `AlgebraicGeometry.ProEtale.FieldExceptionalSystem.field_exceptional_normalized_adjoints`
  (node `lem-sp-field-exceptional-normalized-adjoints`).
- `AlgebraicGeometry.ProEtale.FieldExceptionalSystem.field_exceptional_finite_compatibility`
  (node `lem-sp-field-exceptional-finite-compatibility`).

This is a decomposition (one upper hole replaced by two strictly smaller geometric steps),
not a net hole reduction. The intervening categorical laws and invertibility detection are
proved in Lean in the item module. No existing holed statement was changed.

The unchanged consumers checked above contain three existing holes, neither closed
nor added by this delivery:

- AlgebraicGeometry.ProEtale.FieldProjectionOrigin.field_projection_origin_witnesses.
- AlgebraicGeometry.ProEtale.FieldPuritySystem.field_purity_system_transpose_base.
- AlgebraicGeometry.ProEtale.FieldPuritySystem.field_purity_system_transpose_compatibility.

Their current shared sources were checked verbatim and contribute no Git diff.

## No longer needed

Removed the direct private imports Sheaf.Paper.SmoothPurityTowerGluing,
Sheaf.Paper.FieldScalarNormalizedSystems, Sheaf.Paper.SmoothPurityTowerGamma, and
Sheaf.SecSmoothPurity.ReductionCompatibilities from the item module. Their geometric content
is still needed by the new substeps or public interfaces; none of those modules is withdrawn.
Added private imports of the two new substeps and Mathlib.CategoryTheory.Adjunction.Basic.
The new statement modules import only their public law interface. Their planned proof
requirements remain in the DAG; importing those theorem proof closures is deferred until
their proofs are written. Also removed the unused private imports of
FieldScalarNormalizedSystems, SmoothPurityTowerGamma, ReductionCompatibilities and
Mathlib.CategoryTheory.Adjunction.Mates from FieldExceptionalSystemDomains.

The original direct proof dependencies lem-sp-field-scalar-normalized-systems,
det-sp-tower-gamma, det-sp-tower-gluing, det-sp-reduction-exceptional,
det-sp-scalar-extension-functor, and det-sp-reduction-compatibilities move below the two
new substeps. They remain mathematically needed and are not pruned globally.
The item still uses lem-sp-field-shriek-system-comparison,
lem-coef-semilinear-derived-sections, and det-sp-tower-shriek-levels. The Mathlib leaf
def-weil-pbc-adjunction-mate is no longer a direct proof dependency: the direct Hom-bijection
calculation suffices. No declaration,
module or unit route is withdrawn. There is no global pruning claimed.

## Where the brief, the DAG or earlier work was wrong

Return repair (head 323389a21c8): the reader's FIX of that head failed to land because the
override for the change record was named `M9-field-exceptional-adjunction-projection.md`. The landing
tool needs `.change.md`. The re-delivery a81ecce98000 carried the same Lean and node files as that
head, so the reader re-applied the same FIX. The corrected records now use the names
`M9-field-exceptional-adjunction-projection.change.md` and `M9-field-purity-finite-theta-type.change.md`.

The definitions-only Domains module also imported large theorem proof closures that its
bodies do not use. The privateModule linter spent about 22 seconds loading their metadata
at end of file; this motivated the private-import cleanup recorded in
coord/changes/M9-field-exceptional-domain-imports.md. No public import or definition body
was changed by that cleanup. The typed-projection and finiteTheta changes made for timing were withdrawn by the reader;
see What changed.

The declared gluing theorem supplies the adjunction for its canonical compactification on
the full uniformly constructible category. The comparison interface needs an arbitrary fixed
compactification in simultaneous section-preserving coordinates, restricted to normalized
objects. Transport and restriction, including the actual finite counit normalization, were
not a direct application of that theorem; they are recorded explicitly in the first substep.
Likewise the finite exceptional theorem concludes some right adjoints; transporting its
specified mate to the adjoints retained in A and proving the evaluation equation needs the
normalization calculation recorded in the second substep. No false mathematical statement
or changed target is asserted.

The quotient transition square of an already constructed whole-system map follows directly
from naturality of the strict transition under the finite scalar adjunction. This proves the
transition clause independently of mixed-path bookkeeping; the mixed finite clause and the
right-adjoint quotient formula are separately retained. Equality of arbitrary derived arrows
is never inferred from their evaluations.

Edge cases checked in the substep design: n=0 means exponent one; equal quotient indices;
identity field extensions; ramified inclusions; empty schemes; arbitrary choices of adjoints
normalized by their actual counits. No flatness assumption is added for quotient maps.

## New nodes

`lem-sp-field-exceptional-normalized-adjoints` owns
Sheaf.Paper.FieldExceptionalNormalizedAdjoints and isolates the domain/restriction and quotient
part of original steps 1 and 4. It asserts none of the field-extension comparison laws.

`lem-sp-field-exceptional-finite-compatibility` owns
Sheaf.Paper.FieldExceptionalFiniteCompatibility and isolates original steps 3 and 4 at finite
level. Its invertibility assertion concerns only finiteComponent. The whole-system
invertibility detection and all categorical coherence are proved in the original module.

Both nodes carry the original chapter and unit, exact source, declaration and proof in words,
and logged Mathlib searches. The unit record is unchanged. The change record coord/changes/M9-field-exceptional-domain-imports.md records the Domains
import cleanup. The records M9-field-exceptional-adjunction-projection.md and
M9-field-purity-finite-theta-type.md record the withdrawn changes (Old = New). No
pre-existing statement or definition changed. The reader added the stmt_deps
def-sbc-smooth-morphisms, def-sf-setting and det-sp-tower-shriek-levels to both new nodes,
and sk-def-sp-normalized-towers and def-sp-tower-shriek-data to the finite-compatibility node.
These cover SmoothOfRelativeDimension, the finite-type setting, Compactification and the tower
data, and spFiniteConstructibleTorCategory and SpTowerShriek.R used in its statement.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

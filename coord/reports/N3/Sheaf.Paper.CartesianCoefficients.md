## What changed

Completed the cartesianCoefficients assembly from the library's canonical alpha/exactness
instances, cartesianCoefficients_finiteFree, spRoots_cartesian,
spFiniteTwists_cartesian and spTwists_cartesian. The finite-free dependency supplies
its own integral basis, so both finite ranks and isomorphisms are extracted directly.
The underlying inverse-image lift equality is rfl; its canonical natural comparison
with module pullback is retained.

Replaced the unused duplicate CartesianTwistMaps/CartesianTwistNormalization API with
the existing signed coefficient-module comparison records. CartesianTwistAssertions
now packages their finite root-tensor normalization, Kummer compatibility, canonical
integral projections, rational balanced equation, finite-subextension Qbar colimit,
and zero/positive-tensor/negative-evaluation normalization. Finite coefficients retain
Type u and ULift A. The replacement also retains signed derived comparisons and
finite-field inclusion compatibilities. The adic witnesses and their seven compatibility clauses are fields of
CartesianAdicComparison, and CartesianAdicTwistAssertions is its Nonempty proposition.
This avoids expanding a large nested existential during kernel conversion.
No module outside this item references any
changed or removed name (searched lean/ and quarantine/; downstream.py run).

The theorem's written signature and the DAG statement are unchanged. The definition
under its twist predicate changes and requires independent mathematical review; this
is described clause by clause in coord/changes/N3-cartesian-normalized-twist-api.md.
No source-library files or locked Challenge declarations are changed. The three unit
steps (alpha, twists, finite-free extensions) remain realized by their original nodes.

Validation: lcompile.py compiled the final module under normal limits in 17.8 seconds;
import_direction.py confirms that the twist dependency introduces no import cycle.

## Proved and sorry left

Proved AlgebraicGeometry.ProEtale.cartesianCoefficients from the named dependencies.
The module has zero remaining sorry declarations and adds zero holes elsewhere.

The old AlgebraicGeometry.ProEtale.cartesianTwistMaps_existsUnique is removed as part
of pruning the unused duplicate comparison-family construction. It is NOT claimed as
a proved theorem. Of the original two hole declarations, one is proved and one is
pruned. The replacement is the normalized signed-comparison argument already stated
by det-prop-sfb-cartesian-coefficients-twists, not a new assumed lemma. The retained
dependency theorems have their own existing holes, unchanged by this delivery.

## No longer needed

Removed proof imports:
- Sheaf.NumberTheory.Padics.LocalFieldIntegralBasis
- WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
- Sheaf.CategoryTheory.SheafTensor
- Sheaf.CategoryTheory.SheafTensorClosed
- Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
- Sheaf.CategoryTheory.ModuleObjects.LiftExact
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic (redundant)

The node no longer directly uses lem-sfb-local-field-integral-basis: its finite-free
dependency already includes basis existence. Its expanded exactness proof is already
proved by the source instances in ModuleObject.UpperLowerStar.Defs. Hence its direct
uses of def-weil-pbc-proetale-site, lem-weil-pbc-site-sheaves-enough-injectives,
sk-def-sfb-sheaf-tensor, det-def-sfb-sheaf-tensor-closed, lem-sfb-modobj-abelian,
sk-def-sfb-pulled-back-coefficients, lem-weil-pbc-sheaf-algebraic-structures-objects,
det-pe-topos-functoriality-inverse-image, lem-sfb-internal-abelian-finite-limit-creation,
lem-sfb-products-zero-additive, det-prop-sfb-module-pullback-exact-lifted and
lem-sfb-finite-exactness-nat-iso are removed. Some remain needed transitively by other
modules; no claim is made that their modules can be withdrawn globally.
Obsolete tool_uses approvals are withdrawn for lem-pur-ringed-site-grothendieck-abelian,
lem-sfb-modobj-abelian, det-prop-sfb-module-pullback-exact-lifted,
lem-weil-pbc-site-sheaves-enough-injectives and
lem-weil-pbc-sheaf-algebraic-structures-objects. The twist detail approval stays.

Pruned local declarations: cartesianSignedAb, CartesianSignedMaps,
CartesianSignedNormalization, cartesianSectionLine, cartesianSectionRing,
CartesianInternalSignedMaps, CartesianInternalSignedNormalization, CartesianTwistMaps,
cartesianTwistMate, cartesianUnitsBaseChange, cartesianTwistLevelMap,
cartesianFiniteQuotientHom, CartesianTwistNormalization,
cartesianTwistMaps_existsUnique, cartesianTwistMaps.
Their replacements and consumer check are in the change record. No Lean module is
withdrawn, no deleted.txt is supplied, and no DAG node is deleted.

## Where the brief, the DAG or earlier work was wrong

The plan expanded module exactness although the adopted source already proves it
uniformly for every condensed coefficient ring. It also requested an integral basis
separately even though cartesianCoefficients_finiteFree supplies one. The earlier
statement layer duplicated the normalized signed comparison API as a family of
adjoint abelian maps with an additional existence-and-uniqueness obligation. No
consumer used that duplicate API. The current statement uses the prescribed twist
dependency's actual coefficient-module isomorphisms and canonical normalizations.

The old cartesianTwistMaps_existsUnique hole was not proved; the report and delivery
count it as pruning, with an explicit representation-change record. The signed
comparisons are still required and their dependency is retained. Edge cases remain:
empty X/Y, zero finite A, all integer degrees and the finite-subextension Qbar model.
The unneeded expanded exactness imports were removed only after finding the existing
proved source instances. No source declaration is deleted or replaced by sorry.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

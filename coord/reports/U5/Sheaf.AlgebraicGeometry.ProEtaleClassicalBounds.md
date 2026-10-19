## What changed

Replaced the proof of AlgebraicGeometry.ProEtale.classicalUniformBounds by a complete Lean
assembly, without changing any existing declaration signature or definition. Proved private
helpers for the canonical finite dimension bound, finite-type and etale-stage torsion bounds,
comparison for abelian coefficients, absolute affine limits, and base-changed affine limits.
The pullback proof uses Over.liftCone, preservation of limits by Over.pullback, pullback pasting,
and the affine-limit theorem. The finite-type proof uses the existing source theorem with a
less-than-or-equal dimension hypothesis, which includes empty schemes.

Added two proved helper modules: the all-torsion finite-field bound and a general higher-direct-image lemma. All three modules compile together with lcompile.py --all (7.3, 1.2 and 10.1 seconds).
No other existing module was changed; new public statements have no pre-existing consumers.

## Proved and sorry left

Closed the original hole AlgebraicGeometry.ProEtale.classicalUniformBounds
(det-pe-unbounded-classical-bounds). Original module: 1 hole before, 0 after.
Added holes: 0. Total textual holes in the three delivered modules: 0.

Also proved both new public theorems completely:

- AlgebraicGeometry.Scheme.hasTorsionEtaleCohomologicalDimensionLE_one_of_finite
  (lem-sfb-finite-field-all-torsion-cd).
- AlgebraicGeometry.Etale.isZero_higherDirectImage_of_affineEtale_cd
  (lem-sfb-higher-direct-image-affine-etale-bound).

The finite-field proof constructs the finite-stalk filtered colimit from the existing
covering theorem, proves a common prime-power annihilator on each finite primary piece,
verifies the kernel-colimit torsion condition, applies the existing prime-power field
bound, and uses additive primary decomposition and filtered cohomology continuity.
It adds no new unproved intermediate statement. The existing base-field bound remains a
stated dependency with its own sorry; this delivery proves the requested theorem from
existing declarations, as stage 3 requires.

The higher-image proof uses the source affine-object criterion and Ext comparison, then
the exact equivalence between abelian sheaves and ULift Z-module sheaves.

## No longer needed

Removed direct proof imports from the item:
- Sheaf.AlgebraicGeometry.AbelianSheavesGModules
- Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants
- Sheaf.RepresentationTheory.BaseFieldContinuousCochains
- Sheaf.FieldTheory.FiniteFieldAbsoluteGalois
- Sheaf.GroupTheory.CyclicInflation
- Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
- WeilConjectures.Mathlib.Topology.KrullDimension
- Mathlib.AlgebraicGeometry.Morphisms.Etale
- Sheaf.RingTheory.Etale.LocalDimension
- Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension
- WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
- Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
- WeilConjectures.AlgebraicGeometry.HigherDirectImageSheafifiedPresheaf
- Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
- Mathlib.CategoryTheory.Sites.Sheafification
- Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage

The field cochain/Galois/inflation ingredients remain transitively required by the existing
prime-power base-field bound. The higher-direct-image localization ingredients are used
inside its separate proved helper module. These imports are relocated, not globally pruned. The source abelian comparison supplies the needed restriction/cohomology compatibility;
no extra weakly-etale localization or module-coefficient comparison bridge is needed here.
The exact source etale dimension theorem uses discrete fibres and strict specialization chains,
so the ring-localization dimension calculation is not needed for this proof.

Removed parent proof dependencies (some remain transitively required by the helper nodes):
- lem-exc-abelian-sheaves-gmodules
- lem-exc-field-sections-stalk-invariants
- det-base-field-cd-cochains
- det-base-field-cd-galois-group
- det-base-field-cd-inflation
- def-sc-etale-torsion-cd
- def-kun-dimension
- def-weil-finite-type-morphism
- lem-weil-pbc-proper-fp-permanence
- lem-sc-etale-local-dimension
- lem-sc-scheme-stalk-dimension-generalization-chains
- lem-sc-scheme-sober
- lem-weil-proetale-weakly-etale-localization
- def-weil-proetale-inverse-image
- def-pc-fibre-product
- lem-weil-pbc-higher-direct-image-sheafified-presheaf
- lem-weil-pbc-cohomology-over-object-localization
- lem-weil-pbc-etale-site-localization-open
- lem-weil-pbc-etale-inverse-image-restriction
- def-weil-pbc-sheafification

Removed the corresponding obsolete parent tool_uses entries. No entire module is withdrawn;
no claim is made that an import shared by other targets leaves their global closure.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The recorded finite-type theorem requires equality with a
natural dimension, but the source library already proves the stronger useful interface with
an upper bound; it avoids a separate empty-source proof. The recorded comparison theorem is
module-valued, whereas the source library already provides exactly the abelian comparison
vanishing needed here. Its direct proof import is used instead of rebuilding coefficient
transport. The item does not assume that g respects the chosen k-structures; product stages
use their finite-type structure through the target's affine etale stage, while their dimension
is controlled through the etale projection to the source. The unit route is retained.

Edge cases checked: empty source/stage (dimension bot), zero torsion sheaf, unbounded torsion
exponents, integer q (converted to positive natural degree), arbitrary nonseparated finite-type
schemes, and maps not compatible with the given ground-field structures.

## New nodes

lem-sfb-finite-field-all-torsion-cd records only the all-torsion field calculation from
steps 1--3. It is now proved, using the existing prime-power field bound together with
finite-stalk approximation and primary decomposition. Its direct dependencies match this
route rather than restating the cochain argument already delegated to the base-field bound.

Cross-unit tools used here are lem-sc-field-torsion-finite-stalk-subobjects-cover and
lem-sc-generic-finite-primary-decomposition (field statements with no curve hypotheses),
and lem-pbc-u2-sheafH-large-filtered-colimit-derived (continuity on a qcqs scheme, applied
to an affine spectrum). They supply exactly finite torsion approximation, finite primary
splitting, and cohomology continuity; no unit-level geometric route is bypassed. The
original cochain/Galois argument remains inside sk-lem-base-field-cd. No tool_uses approval
was added by this worker.

lem-sfb-higher-direct-image-affine-etale-bound records the general affine-etale local-to-global
step 10, assuming its local absolute bound. It is proved completely using the source-library
affine-object higher-direct-image criterion and integer-module/abelian-sheaf equivalence.
It imposes no finite-type restriction.

No definition or existing statement changed, so no change record is required.
The earlier scratch proof compiled before integration; the final finite-field helper,
higher-image helper and assigned module then all compiled together with no warnings.
The private generic-field annihilator and finite-stalk-colimit proofs are necessary here:
the existing similarly named declarations specialize to curve function fields.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

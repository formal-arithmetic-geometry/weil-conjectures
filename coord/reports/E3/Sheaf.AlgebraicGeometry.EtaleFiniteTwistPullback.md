## What changed

The original statement is unchanged. Its proof chooses the canonical normalized roots
comparison from the proved source library, obtains ordinary signed c and p from a
strictly smaller coherence statement, constructs the required derived natural
isomorphism by functor whiskering, and constructs the exponent-transition roots map
by kernel.lift. Positive exponent transitions recurse by tensorIso; negative ones are
the inverse duals. Their evaluation equation is proved from
id_tensor_pre_app_comp_ev and inverse cancellation.

Three ordinary coefficient lemmas were separated into new modules, each with its
source, proof in words, and DAG node. The common-local-bases lemma is proved completely.
The other two remain as ordinary coefficient obligations. The source roots and fixed-factor derived tensor
comparisons are attached as two existing-declaration nodes so the revised route names
its actual proved inputs. No source declaration is copied or reproved.

Validation: all four final delivery modules compiled together without errors or
warnings. The main item took 21.3 seconds in the first complete check; the complete
local-bases proof took 25.9 seconds. The only direct consumer compiled unchanged
against the smaller import set. The required delivery dry run passed all checks
(review class CODEX). No axiom or data chosen from an unproved mere-existence
theorem is added. All existential witnesses from pending theorems are eliminated inside
the proof of the proposition.

## Proved and sorry left

Closed the original syntactic hole in
AlgebraicGeometry.Scheme.etaleFiniteTwistPullback. This is a decomposition, not a
completed proof without sorry: 0 of the original 1 holes is claimed as fully proved.
The normalized roots comparison, its kernel normalization, the entire derived natural
comparison with its exact component formula, the concrete roots exponent map, and the
extension of degree-one exponent maps to all signed powers are proved in Lean.

The delivery adds these holes, each exactly `:= by sorry`:

- AlgebraicGeometry.Scheme.finiteEtaleTwistExponentLine
  (blueprint: lem-asd-finite-twist-exponent-line)
- AlgebraicGeometry.Scheme.finiteEtaleTwistSignedCoherence
  (blueprint: lem-asd-finite-twist-signed-coherence)

AlgebraicGeometry.Scheme.finiteEtaleTwistCommonLocalBases is proved: construct the
primitive-root etale cover, compare ZMod and integer scalar extension sectionwise,
prove naturality using the integer-module equivalence counit, and trivialize signed
powers by tensor recursion and the internal-Hom comparison. No hole is added there.

The signed-coherence obligation needs descent of the local basis tensor
maps and verification of the thirteen displayed equations. The exponent-line
obligation needs the local cyclic reduction map after coefficient extension; every
higher signed transition and its evaluation law are already proved in the item.

The new obligations are strictly parts of the original argument: none includes the
normalized roots construction, the derived comparison, or the full signed exponent
transition. The item contains no sorry.

## No longer needed

The following original imports are removed from the item:

- Sheaf.Paper.RingedTopoiDerivedTensorPullback
- Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
- Mathlib.Algebra.Homology.BifunctorShift
- Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
- Sheaf.AlgebraicGeometry.Sites.InverseImageRepresentable
- Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale
- Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily
- Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
- Sheaf.CategoryTheory.SiteInverseImageTensor
- Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
- Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction
- WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
- Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
- Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
- Sheaf.Paper.RingedTopoiCanonicalTensorPullback
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
- WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
- WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
- WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
- WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable

The old affine root-algebra/representable-Yoneda route is replaced by the proved
source roots pullback theorem. In particular the item's proof no longer needs
lem-asd-affine-roots-representability,
lem-asd-etale-representable-pullback-normalization,
lem-sbc-root-split-away-cover-etale, or their representable-restriction glue.
The abstract ringed-topos canonical tensor-pullback construction and its universe
variants are replaced by the concrete proved source derived comparison, so
lem-weil-pbc-ringed-topoi-derived-tensor-pullback is no longer a proof dependency.
The algebraic-structure, inverse-image restriction/composition, site inverse-image
tensor and exactness steps are supplied by the proved source API rather than the
corresponding old holed proof imports. The main node's proof_deps follows the actual
new proof. Its old top-level tool_uses approvals are pruned, retaining none.

These are removals from this item's route, not a claim that no other target needs
those modules. The finite cyclic-line input remains relevant to the pending
exponent obligation; the common-local-bases proof uses the existing coefficient definitions and proved
source comparisons, with no dependency on that old line theorem. The unit sk-prop-sf-cbc has no realized own statement or
step bypassed here. Its smooth base-change route is retained.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed and no target or definition changes meaning. The planned
roots representability and general derived-tensor developments duplicated the
concrete proved source APIs needed here. The original finite-line theorem has a
Finite A assumption, while this item intentionally has arbitrary A; the scalar
extension step must therefore actually be supplied, rather than applying that theorem
directly with A. The exponent map on cyclic bases is reduction to the smaller
modulus, not multiplication by mprime/m on the final A coefficient line.

Edge cases checked mathematically: m=1 forces A to be the zero ring and all module
comparisons are between zero coefficient objects; empty schemes and empty covering
members cause no exception; nonreduced schemes are allowed; mprime=m gives the
identity power map; the zero ring and infinite coefficient rings require no
finiteness or flatness assumption. The isIso roots input requires NeZero m, supplied
from hm. The q kernel calculation uses exactly m divides mprime.

## New nodes

lem-asd-source-roots-pullback-invertible-exponent attaches the existing proved source
roots comparison with its kernel normalization. It replaces the old affine route.

lem-asd-source-derived-tensor-fixed-factor attaches the existing source natural
isomorphism with the prescribed canonical components. It records the concrete
etale derived-category encoding used in the signature, rather than a new theorem
about an unrelated abstract ringed-topos model.

lem-asd-finite-twist-common-local-bases proves the single-cover signed basis step.
Its coefficient ring remains arbitrary, exactly as in the item. It no longer depends
on the old finite-coefficient line theorem.

lem-asd-finite-twist-signed-coherence isolates only the ordinary signed c and p and
their thirteen coherence equations, with the source roots map fixed in its degree-one
formula. It asserts neither the derived comparison nor exponent transitions.

lem-asd-finite-twist-exponent-line isolates only the degree-one coefficient map for
a supplied normalized roots power map. The item constructs that roots map and
extends the resulting line comparison to all signed degrees itself.

Import cleanup record: coord/changes/E3-finite-twist-import-pruning.md.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

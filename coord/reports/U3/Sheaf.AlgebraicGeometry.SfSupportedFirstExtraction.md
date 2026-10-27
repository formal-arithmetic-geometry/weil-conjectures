## What changed

The unchanged statement SupportedTrace.firstExtraction is proved by an explicit
coordinate calculation. Its two new private imports provide a native Kunneth
symmetry theorem and proper normalization of a single relative Kunneth route.
The proof compares both supported routes with the independently defined ordinary
Kunneth map, cancels the proper comparisons, and performs the compositor,
ordered-projection, exchange-inverse and symmetry algebra explicitly.

EtaleKunnethTensorSymmetry proves the ordinary Kunneth tensor-symmetry theorem
for general coefficients and arbitrary commutative squares by a common
mixed-counit transpose. EtaleKunnethSymmetricFactorization isolates the generic
ordinary projection/exchange normal form and projection naturality before
coefficient specialization.
ProperRelativeKunnethSupports proves one-route
normalization using the existing native projection and compactification exchange
comparison equations. Its tensor algebra is proved for an abstract bifunctor
before specializing coefficients. ProperKunnethNormalizationAlgebra proves the
remaining diagram calculation for arbitrary functors and morphisms, so the
coefficient specialization applies the six comparison squares once. The inverse
route component is likewise a specialization of a generic four-isomorphism
identity. Local transparency controls prevent the proof
from expanding the compactification and derived-category implementations.
Private congruence code builds equality proofs checked by Lean's kernel from
congruence, proof irrelevance and definitional coefficient-instance equality.
This avoids expanding large derived constructions during normalization.
ProperShriekCompSupports isolates compatibility of the
specific native supported compositor with forget supports. Its statement has no
tensor, coordinate projections, exchange map or Kunneth map.

ProperSupportedKunnethRoute constructs the proper-only route explicitly from the
existing lower-level compositor, projection, exchange and canonical symmetry.
It contains zero holes. Importing the native Kunneth.RelativeMap would close an
import cycle: import_direction.py reports that it already reaches this item.
The proper-only construction avoids that source module and its Kunneth.Defs
import; every original source declaration and public import is preserved.

No existing definition, public import, theorem signature or source-library file
changes. The unit route is preserved.

Validation: all seven modules compile together with no warnings through
`lcompile.py --all`; the assigned module completed in 41.5 seconds. The original
theorem signature and every attached Lean statement were checked verbatim.

## Proved and sorry left

Closed: AlgebraicGeometry.Etale.SupportedTrace.firstExtraction (the item's only
original hole), by a complete proof from the declared dependencies below.

Also proved: AlgebraicGeometry.Etale.kunnethMap_tensorSymmetry,
AlgebraicGeometry.Etale.kunnethMap_symmetricFactorization and
AlgebraicGeometry.Etale.properRelativeKunneth_comp_forgetSupports, including the
mixed-counit, generic proper exchange and ordinary-route calculations.

Added and remaining: AlgebraicGeometry.Etale.properShriekComp_comp_forgetSupports
in Sheaf.AlgebraicGeometry.ProperShriekCompSupports, node
lem-sf-proper-shriek-compositor-supports. Its proof is exactly `by sorry` and its
docstring supplies the compactification/composite-counit argument. There are no
other holes in this packet, and no data definitions depend on arbitrary choices
from unproved existence statements.

Within this packet, one upper hole is closed and one strictly smaller
composition-coherence hole is added: it is a decomposition, with zero net holes
closed in the packet, not a completed proof
from the permitted axioms. In particular it does not move the original
coordinate-interchange statement under another name: the remaining obligation
only compares two compositors and contains none of the tensor calculation.

## No longer needed

No original public import is removed, and no existing module is withdrawn.
The proof no longer needs the planned nodes
lem-sfb-ringed-derived-monoidal-comparisons
(Sheaf.SixFunctors.RingedDerivedMonoidalComparisons) and
lem-sfb-ringed-kunneth-factorizations
(Sheaf.Paper.RingedKunnethFactorizations). Their ringed-module presentation is
replaced by proved native sheaf-valued tensor comparison and Kunneth APIs.
These two modules were not previously imported by the item, so this removes
planned dependency edges rather than claiming two library modules disappear
from all targets. Proper projection and proper support comparisons are still
used by the normalization proof. Proper exchange invertibility is retained
through the explicit proper-supported Kunneth route.

## Where the brief, the DAG or earlier work was wrong

The native RelativeMap cannot be a proof dependency here: it already reaches
SfSupportedFirstExtraction through its imports. All remaining external proof
imports were checked with import_direction.py and do not reach the item.

The previously recorded generic ringed Kunneth statement does not directly use
the native DerivedCategory of sheaves on X.smallEtaleTopology appearing here.
The native source library already proves its projection/exchange Kunneth
factorization, so rebuilding ringed-module transport is unnecessary. The needed
symmetry follows directly from the native definition, not from a specialized
coordinate factorization requiring a pulled-back coefficient.

Edge cases: arbitrary E,K are retained throughout. No trace, line condition,
nonempty scheme, nonzero coefficient ring, boundedness or extra cohomological
dimension assumption is introduced. The ordinary symmetry holds even without
properness or a pullback condition. The remaining compositor equation for
identity maps is the unit/composite-counit identity; zero objects, empty schemes
and the zero ring impose no exceptional case.

## New nodes

def-sf-proper-supported-kunneth-route records the real, proper-only route
construction and its elementary component API in ProperSupportedKunnethRoute.
It depends on no new theorem and contains no holes.

lem-sf-native-kunneth-tensor-symmetry records the proved generic native Kunneth
symmetry in EtaleKunnethTensorSymmetry. Its proof is the mixed-counit calculation
followed by braided tensor comparison and braiding naturality.

lem-sf-proper-relative-kunneth-supports records the proved one-route proper
normalization in ProperRelativeKunnethSupports. It compares one specified route
to the independently defined ordinary Kunneth map, and is applied twice by the
coordinate proof.

lem-sf-proper-shriek-compositor-supports records the sole remaining named theorem
in ProperShriekCompSupports. It is the direct-image-compositor substep of the
normalization, independent of all tensor and coordinate calculations. No change
record is needed: only the assigned module and new modules/nodes change.

lem-sf-native-kunneth-symmetric-factorization records that proved generic ordinary
normal form in EtaleKunnethSymmetricFactorization. It is separated to keep the
generic braiding computation outside the finite-coefficient proof context.

lem-sf-proper-kunneth-normalization-algebra records the proved abstract diagram
calculation in ProperKunnethNormalizationAlgebra. It uses only Mathlib
functoriality, naturality and associativity, has six explicit square hypotheses,
and introduces no additional hole.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

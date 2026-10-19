## What changed

Proved AlgebraicGeometry.Etale.supported_kummer_scalar_source from the existing
AlgebraicGeometry.Etale.geoCartierCoeffExtension theorem, retaining the original
statement, supportedScalarMap definition, public imports and target signatures.
The new proof identifies the normalized coefficient map with coefficientUnitModule
using the constant-sheaf adjunction. An invertible adjunct gives the required
unbounded derived universal property by precomposition and adjunction naturality.
The identity closed immersion gives the constant case; a proved transport lemma
carries its universal property across the supportedConstantUnit isomorphisms.

SupportedKummerScalarSourceData proves exists_supported_constant_scalar_map by
an explicit R-linear presheaf map and sheafifyLift.
SupportedKummerScalarSourceNaturality proves the normalized unit square on
constant-presheaf generators for arbitrary rings and scheme morphisms. The
terminal-generator calculation follows the existing calculation in
WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardFunctoriality.
All added imports in the item are proof-only. The unclaimed
OrdinarySupportedKummerScalar module now names the canonical derived unit map
as exactDerivedScalarUnitMap and packages its universal property in the one-field
Prop structure ExactDerivedScalarUnit. SupportedDerivedScalarUnit specializes
this property to restriction of scalars. The old unbounded test objects,
normalization, and absence of flatness hypotheses are preserved: expanding the
map and reassociating composition gives exactly the old bijectivity formula.
The unclaimed GeoCartierCoeffExtension definition coefficientUnitDerived uses
that named map, with its existing signature and canonical composite unchanged.
Its new public import supplies this construction. The unchanged direct consumer
OrdinarySupportedKummerSystem compiles against the repaired predicate. No other
existing consumer needs adaptation. The original target signatures are unchanged.

The existing node lem-geo-cartier-coeff-extension is used as a generic tool: it
already gives the specified closed-supported comparison for arbitrary finite
coefficient maps, including our lifted ZMod N map. Its own coefficient-adjunction
and stalk proof supplies the original plan's derived calculation. No unit statement
or realized proof step is bypassed; the item's unit has no realized steps attached
to this node. The maintainer should approve this cross-unit tool use on review.

## Proved and sorry left

Closed the one original hole:
AlgebraicGeometry.Etale.supported_kummer_scalar_source
(lem-asd-supported-kummer-scalar-source).

Also proved the two new supporting statements, with no direct sorry:

- AlgebraicGeometry.Etale.exists_supported_constant_scalar_map
  (lem-asd-supported-constant-scalar-map).
- AlgebraicGeometry.Etale.supported_kummer_scalar_source_naturality
  (lem-asd-supported-constant-scalar-naturality).

All private helpers are proved. The delivery adds zero holes and leaves zero
direct holes in the item, the two new helper modules, and the repaired scalar
predicate module. GeoCartierCoeffExtension retains its one pre-existing hole:
AlgebraicGeometry.Etale.geoCartierCoeffExtension
(lem-geo-cartier-coeff-extension). The delivery does not add that hole or change
its theorem statement or proof. This is a proof from existing declarations;
geoCartierCoeffExtension is an existing theorem with sorry, whose proof remains
its own item. No claim is made that the transitive proof is now axiom-free.

The earlier sandbox's two unsubmitted holed modules were superseded and removed
from the delivery: supported_constant_derivedScalarUnit and
closedPushforward_supportedDerivedScalarUnit. Neither was present in the shared
repository; neither is imported by the delivered proof. Their draft files and
nodes are retained only in scratchpad/superseded-splits, outside the delivery.

## No longer needed

Removed direct proof imports from the item:

- Sheaf.Algebra.Homology.KFlat
- Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
- Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
- Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
- WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
- WeilConjectures.SixFunctors.Finite.Stalk
- WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
- WeilConjectures.SixFunctors.Etale.Derived.Tensor
- Mathlib.AlgebraicGeometry.Morphisms.Finite
- Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
- WeilConjectures.SixFunctors.Finite.BaseChange

The original direct proof dependencies are no longer used directly:
def-kun-derived-tensor, def-pc-kflat-complex, def-pur-sheaf-tensor-product,
def-weil-closed-immersion, def-weil-finite-integral-morphism,
def-weil-pbc-direct-image, lem-pod-etale-stalk-tensor-scalar,
lem-pur-derived-change-of-rings, lem-weil-pbc-constant-sheaf-geometric-stalk,
lem-weil-pbc-exact-functor-derived-functor,
lem-weil-pbc-finite-stalk-formula-restriction,
lemma-weil-pbc-geometric-stalk-conservative,
prop-weil-pbc-geometric-stalks-exact and sk-lem-pbc-finite.
The existing coefficient-extension theorem encapsulates the supported derived
calculation. Some listed nodes remain statement dependencies or transitive
imports; no globally unreachable module is claimed.

Withdraw the old direct tool approvals sk-lem-pbc-finite,
lem-weil-pbc-finite-stalk-formula-restriction,
lem-pod-etale-stalk-tensor-scalar,
lem-weil-pbc-exact-functor-derived-functor and
lem-pur-derived-change-of-rings from this node's tool_uses.

The earlier sandbox's draft nodes
lem-asd-supported-constant-derived-scalar-unit and
lem-asd-closed-pushforward-derived-scalar-unit and their modules
SupportedConstantDerivedScalarUnit and ClosedPushforwardDerivedScalarUnit are
not needed and are not submitted. No existing library file is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The initial resumed dry run compiled Data and Naturality but timed out on the
main module. Profiling isolated expensive kernel unfolding of the universal
property and coefficientUnitDerived, including a reflexivity check for the
latter. Caching weak sheafification and the two definition repairs above make
the proof compile. The final clean main compile took 29.7 seconds;
GeoCartierCoeffExtension compiled in 13.2 seconds. The scalar predicate module
also compiled in 34.8 seconds. Diagnostic heartbeat and profiler options are
removed. Earlier compile-service failures are resolved. The completed packet passed the
required delivery dry run, including compilation and preflight; independent
review is required for the two definition repairs and the new nodes.

The retained report described a decomposition with two holes, but the later
retained main module already attempted the shorter existing-comparison route.
This session completes that route and updates the DAG and report accordingly.
The initial dry run rejected the obsolete holes; they are now unnecessary.

An earlier naturality helper based on universal properties alone permitted
independent rescaling of units. For R=S=Z/3 and identity support, id and 2*id
are each universal coefficient maps but do not give the same unit square.
The delivered naturality theorem instead uses the actual generator equations.
The original library statement already required these normalizations.

The finite reverse adjunction needs an etale hypothesis and was not used.
The actual route applies to empty supports, identity immersions, zero rings
(including N=1), nonreduced closed supports and nonflat Z/4 to Z/2. Positivity
of N is used only to obtain the finite lifted source ring.

## New nodes

lem-asd-supported-constant-scalar-map: the proved explicit normalized coefficient
map construction in SupportedKummerScalarSourceData. Its proof defines the map
on sections and extends it through sheafification; no arbitrary witness is
chosen in a definition.

lem-asd-supported-constant-scalar-naturality: the proved normalized unit square
in SupportedKummerScalarSourceNaturality. The generator equation first follows
at the terminal object from adjoint uniqueness, then on every object from
naturality, and finally for sheaves from sheafification's universal property.

The existing definition node def-asd-ordinary-supported-kummer-scalar now lists
the two added construction declarations in its Lean attachment. Its mathematical
statement is unchanged. Definition change records:
coord/changes/M4-supported-derived-scalar-unit-structure.md and
coord/changes/M4-supported-coefficient-derived-unit-map.md. Both include the
old/new definitions and the full downstream user tables; target meaning is
reopened for the independent reader. No held module of another group is edited.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

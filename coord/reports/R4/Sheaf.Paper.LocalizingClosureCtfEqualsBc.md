## What changed

The main theorem is assembled from uniform local-model Tor bounds, finite-strata
devissage and the cohomology-interval theorem. The coefficient disjunctions are
reconciled explicitly, the field interval is enlarged only for the integral-style
clause, and boundedness supplies an ordered interval even for the zero complex.
The object-property equality and the localizing-closure equality are proved by
extensionality and congruence.

The scalar Z/ell² example is proved directly: the annihilator computation, residue
nontriviality, infinite self-Tor, infinite projective dimension, perfectness of the
two-term cone, and nonperfectness of the residue. The finite-ring thickness clause
uses the normalized fixed-module equivalence, a cover-universe comparison, the
constructible Serre class, and the kernel-of-one-minus-idempotent proof for retracts.
The generic bounded-homology argument is proved locally rather than importing the
unrelated coefficient-heart theorem. Existing public imports and all original
public signatures and definitions are unchanged. No source-library module is edited.

Two distinct arguments from the source are stated separately: arbitrary-scheme
finite-constant-local-model Tor bounds, and the constant square-zero residue/truncation
calculation. Their docstrings give complete proofs, including the required comparison
between internal and sectionwise module encodings. These comparisons are not supplied
by simply applying the intrinsic scalar-resolution/tensor lemmas: those lemmas use
different module and derived-tensor encodings. The scalar and finite-ring closure
parts of the parent are real proofs and do not rely on the new examples lemma.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.localizingClosure_ctf_equals_bc` by a complete assembly.
This is a decomposition, not a net hole reduction: one upper hole is closed and two
strictly smaller, independent source arguments are added below it.

Added holes (exactly two, each a public named theorem with proof `by sorry`):

- `AlgebraicGeometry.ProEtale.padic_constant_local_model_tor`, node
  `lem-sfb-padic-constant-local-model-tor`.
- `AlgebraicGeometry.ProEtale.constant_square_zero_tor_example`, node
  `lem-sfb-constant-square-zero-tor-example`.

No hole is left in the item module. All private helpers are proved. In particular,
`scalar_finiteRing_example` and `finite_coefficient_ctf_thick` are proved, as are
`boundedConstructible_torBounds`, the cover/local-model comparison, the bounded
homology thickness argument, and the scalar annihilator/perfectness helpers.
Validation: `lcompile.py --all` compiled all three modules with no errors or
warnings (5.1 s, 3.5 s, and 24.8 s). Main theorem signature is byte-identical to the
original, both new node signatures match their Lean declarations, all node references
resolve, and all Lean lines are at most 100 characters.

The imported stratified-devissage and finite-discrete constructibility comparison
remain existing stated dependencies; their holes are not added by this packet.

## No longer needed

Removed proof imports:

- `Sheaf.Paper.LocalizingClosureExistence`

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`
- `Sheaf.AlgebraicGeometry.ClassicalModuleWeakSerre`
- `Sheaf.AlgebraicGeometry.ConstructiblePartitionLocalClosedStratum`
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`
- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`
- `Sheaf.AlgebraicGeometry.IntegralConstantCompletion`
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheaves`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.AlgebraicGeometry.PullbackConstantModelConstructible`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.FiniteRingConstructibleSheafOrigin`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.RingedProjectionRestriction`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.ConstructibleSheaf.KernelCokernel`
- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`

The former direct route through classical derived weak-Serre objects, classical
pro-etale sheaves, the finite-ring origin theorem and upstream bounded-constructible
triangulation is replaced by the precise normalized finite-discrete encoding and
fixed-module Serre closure. The old open-closed/locality infrastructure is used
through the existing stratified-devissage statement rather than imported in the
parent. Scalar-model resolution and locality are retained below the new local-model
node; periodic tensor remains directly used for the scalar example and below the
constant example. These are parent-edge pruning claims only: no module is withdrawn,
and upstream declarations or other consumers are not removed.

The obsolete top-level tool approvals removed from the parent node are:
- `det-def-localizing-closure-existence`
- `lem-weil-l-adic-extension-integers-dvr`
- `lem-pc-kflat-closure`
- `lem-weil-pbc-site-pullback-abelian-exact`
- `lem-weil-pbc-ringed-projection-mate-exact`
- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-weil-proetale-weakly-etale-localization`
- `lem-weil-pbc-ringed-projection-restriction`
- `lem-sf-constructible-partition-local-closed-stratum`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-proetale-ringed-open-closed`
- `lem-sf-derived-concentrated-single`
- `lem-sf-derived-truncation-triangle`
- `lem-sf-derived-homology-long-exact`
- `lem-weil-pbc-finite-ring-constructible-sheaf-origin`
- `det-pe-classical-derived-weak-serre`
- `sk-thm-pe-classical-sheaves`
- `thm-constructible-serre`
- `prop-weil-pbc-module-bounded-constructible-triangulated`
- `det-prop-integral-criterion-constant-coefficients`
- `sk-prop-sfb-cartesian-coefficients`
- `lem-sfb-pullback-constant-model-constructible`
- `lem-weil-pbc-finite-discrete-condensed-ring-constant`
- `lem-weil-pbc-finite-discrete-scheme-ring-constant`
- `lem-weil-proetale-constructible-exact-closure`
- `lem-weil-proetale-dbc-triangulated`

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is unchanged. Its parent assembly is not an immediate Lean
application: scalar resolutions and the periodic tensor calculation are sectionwise
module theorems, whereas the item uses internal module objects and the normalized
condensed pullback. The remaining statements explicitly isolate those comparisons.
Finite locally constant covers in the fixed-module library use a larger index universe;
the smallification argument is necessary for the recorded local-model definition.
Importing the fixed-module derived-category library also introduces a namespace
collision for Tor amplitude; private proofs use `_root_.DerivedCategory` explicitly.
No statement is disputed or weakened. The unit route is preserved, and the two source
subarguments are genuine proper parts of the original proof.

## New nodes

`lem-sfb-padic-constant-local-model-tor` / `Sheaf.Paper.PadicConstantLocalModelTor`:
the Local models and Locality paragraphs, before constructible-stratum devissage.
The result has no qcqs assumption and applies only to finite constant local models;
it contains no bounded-complex, closure, finite-ring thickness or example conclusion.
Tested zero scalar modules, zero powers, empty schemes/covers, integral torsion,
and the field interval. Finite-subextension-valued Qbar is retained.

`lem-sfb-constant-square-zero-tor-example` / `Sheaf.Paper.ConstantSquareZeroTorExample`:
the constant-sheaf part of the Examples paragraph. It contains no p-adic coefficient
Tor bound, closure identity, finite-ring thickness, or scalar perfectness conclusion.
The coefficient ring is abstract with a specified finite-ring isomorphism; this
keeps expensive coefficient constructions out of repeated instance synthesis, and
the parent applies it to the identity isomorphism. Tested ell=2 and fields of characteristic ell or different characteristic; coefficients
are constant A-modules and the characteristic of k is irrelevant. Spec k is nonempty.
There is no change record because no existing signature or definition is changed.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

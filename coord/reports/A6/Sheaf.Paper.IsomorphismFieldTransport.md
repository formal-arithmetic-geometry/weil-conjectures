## What changed

Replaced the single sorry in WeilConjectures.isomorphismFieldTransport by a
complete assembly proof with its original signature. The proof constructs stalk
and residue units directly from the finite-field datum; proves both integral
scalar laws using integralPullbackComparisonRealization,
pullbackIdentities_scalarExtension, and isomorphismScalarComparisonAgreement;
constructs normalized finite-stage packages, including the opposite family for
inv (inv g) used by the second descent application; then combines rational scalar
compatibility and common-stage descent.

Moved the four existing clause declarations verbatim to
Sheaf.Paper.IsomorphismFieldTransportClauses and publicly reexported them from
the original module. This avoids cyclic imports in the smaller argument
steps. Public names, signatures, bodies, constructors and projections stay
unchanged. No source-library declaration or target changes. The associated change
record audits all 707 downstream modules; no consumer adaptation is needed.

Sheaf.Paper.IsomorphismFieldTransportFiniteStage proves the single-field
construction: normalized integral lambda, inverse-composition counit, raw
localization of counits, both inverse equivalences, and the existing shift and
exactness structures. Its generic tensor-induction helper proves naturality on
all localized arrows. No new arbitrary functor is selected.

Validation: lcompile accepted all five modules' proof bodies. The parent's sole
style warning (one long docstring line) was wrapped before delivery. Profiling is
removed. Static checks confirm the five original declaration signatures are
unchanged, new node signatures match their files, proof_deps equal the proof-step
uses, and the Lean files obey the 100-character line limit. The delivery command
performs the final compile and preflight on the actual packet.

## Proved and sorry left

Original holes closed: one, WeilConjectures.isomorphismFieldTransport. This is a
decomposition, not a completed proof of the original theorem without new holes.
Its finite-field transport and integral scalar compatibility parts have complete
Lean proofs from the existing declared dependencies.

New proved declarations:

- WeilConjectures.isomorphismFieldTransportFiniteStage
  (lem-pod-isomorphism-field-transport-finite-stage).
- WeilConjectures.isomorphismFieldTransportRationalScalar
  (lem-pod-isomorphism-field-transport-rational-scalar): proves localization of the
  integral scalar equation using the prescribed object, tensor, scalar-comparison
  and epsilon formulas. Heterogeneous congruence handles the object identifications;
  localization preserves the two compositions of the integral equation.

New holes added: one, a public theorem in its own new module, with a source,
complete proof in words, and matching node:

- WeilConjectures.isomorphismFieldTransportCommonStage
  (lem-pod-isomorphism-field-transport-common-stage): descent of two given
  normalized finite-stage families already satisfying both rational scalar laws.

There are zero sorries in the original module, the clause module, the finite-stage
module and the rational-scalar module. There are no hollow definitions or axioms.
The package adds one hole and closes one, so its local net is zero; existing
dependency holes remain. The remaining statement is strictly the descent part:
it assumes the finite equivalences and both scalar equations, whereas the parent
constructs these from its original hypotheses.

## No longer needed

No existing module is withdrawn and no unit step is bypassed. The original public
imports remain public through Clauses, so no public dependency is claimed pruned.

Removed direct private imports from the original module:
Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso and
Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor: the normalized raw-stage
comparison already supplies the integral shift/exactness; the two inverse
counits supply equivalences directly. No new derivation of a module equivalence
is needed here.

Sheaf.Paper.SfIntegralConstructibleTriangulated is removed as a redundant private
import: it is already public through SfRationalizationKaroubi and
SfIntegralConstructibleLinear. No new public dependency is introduced.
Sheaf.Paper.IsomorphismPullbackTExactCoefficients and
Sheaf.CategoryTheory.StageSystemFunctorDescent are removed as direct imports of
the original file: the former's raw-stage predecessor is used in the proved
finite-stage construction; both remain in the common-stage lemma's proof plan.
Sheaf.CategoryTheory.SemilinearScalarLocalization moves to the finite-stage
proof, which actually uses its extension and tensor-composition API.

The rational-scalar lemma itself needs no application of
lem-pur-semilinear-scalar-localization: it uses the already published pure-tensor
and scalar comparison formulas and functoriality of localization. That generic
semilinear API is still used by the proved finite-stage construction, so its module
is retained there.

The direct parent proof dependencies are replaced by the three genuine argument
parts and the actual scalar-comparison tools. The former geometric, derived,
triangulated, rationalization and descent dependencies remain needed by the
new nodes or original statement, except that
lem-weil-sheaf-scalar-extension-ring-iso and
lem-sf-exact-functor-derived-triangulated need no separate application in this
argument. This is no claim that those modules leave the targets' import closure.

The following obsolete parent tool_uses approvals are removed (remaining
approvals keep their original order):

- "lem-weil-proetale-isomorphism-inverse-image"
- "lem-weil-sheaf-scalar-extension-ring-iso"
- "lem-weil-isomorphism-derived-pullback"
- "lem-weil-integral-constructible-triangulated"
- "lem-pur-integral-operations-scalar-extension"
- "lem-pod-isomorphism-pullback-texact-coefficients"
- "lem-pur-semilinear-scalar-localization"
- "lem-sbc-coherent-pair-functor-descent"

## Where the brief, the DAG or earlier work was wrong

No disputed mathematical statement was found. The planned fresh termwise-derived
construction is unnecessary: IsomorphismPullbackRawStage already gives the
normalized integral comparison and integral/rational exactness. The inverse
comparison and its precise epsilon formula still require the natural-isomorphism
construction, which is supplied here.

The original statement's four clause declarations share the original module with
the theorem. The required smaller localization/descent modules would otherwise
need to import their own parent; the verbatim clause extraction removes that
cycle without changing the original interface.

The old source path in the parent node belongs to an earlier snapshot. The current
latest blueprint's inverse paragraph is
sec-six-functors/sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md;
the current prop-weil-operations proof is under
sec-poincare-duality/sk-thm-frobenius. These current texts were consulted.
The parent source/statement are preserved; proof_origin and new nodes point to
latest. The common-stage step retains noetherian and finite-dimension assumptions,
which the parent proves from finite type over the field, so the existing descent
and exactness tools apply unchanged.

The first preflight returned four metadata errors: the new nodes' lean.statement
fields omitted the declaration keyword and short name. These fields now use the
actual stage-3 checker's complete signature format. No mathematical statement or
Lean proof changed in this repair.

Edge checks: empty schemes and non-k-linear isomorphisms are allowed throughout;
there is no separatedness assumption. The localization statements concern every
rational object, and tensor induction covers arbitrary localized arrows, including
torsion. Identity coefficient inclusions are included. The common-stage component
is required at the object's own stage, not merely at a larger representative.

## New nodes

- def-pod-isomorphism-field-transport-clauses: owns the four unchanged clause
  declarations extracted to the public interface module; no sorry.
- lem-pod-isomorphism-field-transport-finite-stage: the proved normalized
  single-field package, including localization of both inverse counits.
- lem-pod-isomorphism-field-transport-rational-scalar: proved scalar localization,
  assuming both finite packages and the integral scalar equation.
- lem-pod-isomorphism-field-transport-common-stage: only descent, assuming the
  already constructed finite families and their rational inverse/scalar equations.

Change record: coord/changes/A6-isomorphism-field-transport-clauses.md.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

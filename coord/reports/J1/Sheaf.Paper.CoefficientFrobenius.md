## What changed

Proved the integral ordinary, integral derived, general perfect-derived, and finite-Tor
point assertions in Sheaf.Paper.CoefficientFrobenius. Completed its coefficient_frobenius
proof from ordinary DVR-quotient duality, field perfect-complex duality, and a separate
bounded dualizing-complex theorem. All existing public signatures and public imports
are unchanged. The only new module is
Sheaf.CategoryTheory.DerivedCategory.DualizingComplexBoundedDuality.

The shorter routes use the existing source-library QuotientDuality, perfect-object
biduality, and general finite-Tor perfectness theorems. Private helpers prove exactness
of ordinary duality, degree-zero perfectness over a PID using a finite-free presentation
and its mapping cone, restriction of a bidual equivalence, and the scalar-action
isomorphism of the tensor unit. A named derived braiding and local irreducibility
attributes avoid expensive unfolding of the derived monoidal structures. No definition
has a proof hole, and no arbitrary object is chosen from an unproved existence theorem.

Updated lem-weil-coefficient-frobenius's proof, proof dependencies, and proof origin to
follow this implementation. Removed the unused finite-Tor-node tool approval, retaining
the DVR approval in its original order. The unit record has no realized statement or
steps to bypass; its integral/finite/field distinctions are retained.

## Proved and sorry left

Baseline: five named holes in lem-weil-coefficient-frobenius. Closed all five textual
holes in the item module:

- WeilConjectures.integral_coefficient_ordinary_duality: proved.
- WeilConjectures.integral_coefficient_derived_duality: proved from the already stated
  perfect-cohomology assembly theorem and a constructed PID resolution.
- WeilConjectures.perfect_coefficient_derived_evaluation: proved by identification with
  the source library's canonical perfect-object evaluation.
- WeilConjectures.finiteTor_point_coefficient_evaluation: proved using the source
  library's general finite-Tor perfectness theorem and the preceding evaluation theorem.
- WeilConjectures.coefficient_frobenius: ordinary quotient assertions and both field
  assertions proved; the finite-ring derived assertion is reduced to the separate
  bounded dualizing-complex theorem below. This last assertion is a decomposition,
  not a claim that its remaining proof obligation has been closed.

Added one hole, exactly:
DerivedCategory.dualizingComplex_bounded_duality, node
lem-sf-dualizing-complex-bounded-duality, in its own new module. Its proof is exactly
`by sorry`. It is the bounded clause of Stacks Lemma 0A7C for an arbitrary Noetherian
ring and a dualizing complex, not the coefficient-stage conjunction under a new name.
The coefficient proof supplies its bounded injective model, finite cohomology, and
canonical scalar-action isomorphism in Lean. Its natural comparison specifies the
actual ambient internal-Hom functor.

Thus four original holes are proved and the fifth is decomposed into one genuine
source lemma: five holes closed, one added, net four before the closure ledger's
independent baseline calculation. Other already stated imported proof dependencies
are used as authorized; no claim is made that all their axioms are discharged.
The sandbox compiles in import order through lcompile.py; delivery checks are recorded
by the delivery tool.

## No longer needed

Removed proof-only imports from the original item module:

- Mathlib.Algebra.Module.FinitePresentation: the PID argument constructs a finite-free
  surjection and uses Noetherianity of its kernel directly.
- Mathlib.Algebra.Homology.HomotopyCategory.KInjective: the parent supplies a bounded
  injective model to the separate dualizing-complex theorem.
- Mathlib.Algebra.Homology.HomotopyCategory.KProjective: canonical perfect biduality
  is already proved in the source library.
- Mathlib.Algebra.Homology.ShortComplex.PreservesHomology: no explicit homology-of-dual
  calculation occurs in the parent proof.
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor: restriction uses the existing
  categorical bidual-equivalence construction.
- Mathlib.Topology.Algebra.Valued.LocallyCompact: no topological argument is used.
- Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses: the canonical internal Hom and
  evaluation are already supplied by CoefficientDuality and the source library.
- Sheaf.CategoryTheory.DerivedCategory.FiniteTorAmplitudePerfect: its finite-stage
  finite-free-model equivalence is unnecessary; the general source-library theorem
  DerivedCategory.isPerfect_of_finiteTorAmplitude suffices.

Removed direct proof dependencies from the parent node:
lem-sf-baer-criterion (source QuotientDuality has already proved the relevant instance),
lem-sc-noetherian-finite-module-finite-presentation (direct finite-free surjection),
lem-weil-pbc-bounded-below-injectives-kinjective (moved beneath the separate source
lemma), def-pur-derived-internal-hom (the existing canonical interface suffices),
lem-sp-exact-functor-preserves-homology and lem-sf-exact-functor-derived-triangulated
(no separate complex-level exact-dual construction), def-weil-abstract-derived-category
(no separate localization argument in the parent),
lem-sc-bounded-above-projective-kprojective (already proved perfect-object evaluation),
and lem-trf-finite-tor-amplitude-perfect (general source-library criterion suffices).
The corresponding finite-Tor tool_uses entry was removed. Statement dependencies are
unchanged; this list does not claim that these nodes are unused elsewhere or that
K-injectivity is unnecessary inside the new source lemma.

Retained the Mathlib finite-projective-dual and DVR finite-torsionfree-free leaves,
the DVR and finite-quotient facts, and perfect-cohomology assembly, which are used.
No Lean module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous packet's ordinary integral argument omitted the nonzero hypothesis of
Ideal.irreducible_of_isMaximal_span_singleton. Extracting the nonzero maximal ideal
from the recorded DVR data repairs this. The coefficient ideal is defined as an
ideal power, whereas source QuotientDuality uses the ideal generated by the element
power; Ideal.span_singleton_pow supplies the necessary equality.

The original plan reconstructs several algebraic results already proved in the
source library. Reusing these avoids the finite-presentation proof of finite-ring
reflexivity and the chain-level proof of perfect evaluation. The new Stacks lemma is
needed because the existing coherent-RHom and finite-injective evaluation statements
are formulated for modules on ringed sites, whereas the parent uses ordinary ModuleCat;
there is no ready-made ordinary-module dualizing-complex duality declaration.
Its docstring and node describe the transport and the canonical evaluation argument.

The earlier compile-service nonresponses have ceased: the complete packet has now
compiled successfully. No delivery push was interrupted or repeated. Concrete
unfolding of derived monoidal instances initially exceeded the compiler limit; the
private abstract scalar-unit calculation and named braiding resolve that problem
without changing any definition, increasing the limit, or splitting the item file.

The continued proof attempt established the ordinary-module boundedness calculation
in scratchpad/Bounds.lean: if the injective model lies in [a,b] and the input lies
in [c,d], its internal Hom lies in [a-d,b-c]. It also established the one-point
module equivalence and the sectionwise presheaf tensor comparison in scratch files.
The remaining obligation is transporting coherent finiteness and natural finite-
injective evaluation through the sheafification and derived tensor comparisons.
Those exploratory files are not delivered, and their partial results introduce no
additional public declarations or holes. The existing complete-local coherent-duality
lemma cannot replace this source theorem: it supplies an unspecified dualizing
complex rather than duality into the given Omega.

The consumer scan found 193 transitive importers and zero downstream mentions of
coefficientBraided, which is private. No consumer signature or adaptation is affected.
The continued attempt observed a launcher reference-clock reset: the earlier
preserved start was 1792426373.901991, while the current unchanged .budget records
1792436086.3912191. No budget metadata was edited by this worker. The completed dry
run passed preflight; the server reported that its appended axiom probe timed out
and that the merge will rerun it, while the delivered files compiled successfully.

## New nodes

lem-sf-dualizing-complex-bounded-duality is the bounded clause of Stacks dualizing.tex,
Lemma 0A7C. Its three hypotheses are a bounded injective representative, finite
cohomology, and invertibility of the canonical homothety. The conclusion is the
restricted RHom anti-equivalence with its ambient natural comparison. This is a
separate source result over every commutative Noetherian ring; the coefficient proof
uses only the special case of the unit over its self-injective finite quotient.
The docstring supplies cohomological bounds, the finite-Ext argument (0G4H), canonical
evaluation (0A69), naturality, and construction of the restricted equivalence. Checked
zero-ring and zero-object cases; there is no nontriviality or perfect-input assumption.
Its new module and matching DAG node are included. The local reducibility and irreducibility proof attributes are recorded in
coord/changes/coefficient-frobenius-local-attributes.md; they are proof-local and
leave public interfaces unchanged.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

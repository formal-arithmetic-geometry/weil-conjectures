## What changed

Replaced the sole hole in `AlgebraicGeometry.Scheme.adic_constructible_finite_reductions`
by a complete Lean proof from four strictly smaller source-backed intermediate theorems.
The proof first derives all quotient Tor bounds and the completion bounds, chooses etale
origins independently, and uses a dependent case split to set the zero origin to the given
`C` and its comparison to the given `e`. It then applies normalized quotient transport
to that family, preserving the original residue marking literally.

Moved the existing construction prefix, including all already proved scalar unit,
reassociation and comparison theorems, to `Sheaf.Paper.AdicFiniteReductionData`. The original
module publicly reexports it. This is necessary for the intermediate statements to use
those constructions without a circular import. All old public names, universes, visibility
and attributes are preserved. Four theorem signatures use named normalization predicates definitionally equal to their former inline
formulas. The main theorem signature is verbatim unchanged. Data-body edits supply explicit
finite-limits proof arguments to adicFiniteComparisonData and the two derived-pullback constructions;
proof irrelevance keeps their values definitionally equal. The additive instance proof
directly applies the existing pull_additive theorem. The old public
imports remain available through the new companion. Searches found no external uses of
any moved private helper. No source-library module is edited.

The baseline original file exceeded the 60-second limit before editing. Compilation
optimization keeps the original constructions and uses proved interfaces. Explicit
finite-limits proofs and pull_additive avoid searching through concrete functors. The
native Mathlib abelian instance is used directly; an additional instance alias caused
expensive conversions and was removed. Inside the three derived proofs, the native
abelian record explicitly retains its native preadditive field, as in the adopted
ConstantCompletionEquivalence proof. Transparency checks are explicitly enabled in the construction module. The ordinary
section-module instances and adjunction types are made explicit where conversion had
previously depended on unfolding large constructions.

The derived square reuses resolving_module_square_iso through a proved helper over
abstract ordinary functors, and the flatness tests reuse pull_flat_kFlat and
change_flat_kFlat. Scalar composition is also assembled over abstract ordinary functors;
resolving_comparison_iso and naturality provide the normalized isomorphism. Both uniqueness
arguments use resolving_nat_ext. The unit derives the tensor/restriction adjunction and
transports it along the unique left-derived comparison. A private proved helper performs
that argument over abstract abelian categories before specialization. Another proved
wrapper exposes the unique comparison normalization while keeping its construction folded.
The source's proved change_preserves_kFlat_quasiIso interface supplies preservation of quasi-isomorphisms.
Ordinary adjoint uniqueness and transport of its sectionwise normalization are also
proved over abstract categories before specializing to the scalar square.
Restriction composition reuses resCompIso and its section formula. The two
termwise-comparison wrappers retain
explicit composite functors in their result types, so the cochain-functor construction
may stay locally irreducible. The derived pullback and its comparison project from the same named universal
DerivedPull package, definitionally the original construction. Four normalization
predicates are named definitions;
unfolding them gives the previous inline formulas. The chosen witnesses and their
normalizations remain definitionally equal. All proved helpers stay in the same
construction module. A private structure records a flat-term K-flat representative;
proved APIs supply resolutions, preservation by the two ordinary pullbacks and the
invertible derived computations. Both derived comparison proofs use that
structure, avoiding repeated expansion of the predicates. The scalar-composition normalization proof applies those APIs directly. A proved
generic helper reverses the comparison equation and converts its resolving-class guard
before specialization to the native sheaf categories.
The scalar Hom equivalence projects from the named adjunction; pointwise lemmas
keep that construction folded. A private constructed module-restriction helper
separates the ring-linearity check from ordinary adjoint uniqueness.

Validation: all six delivered Lean files compile cleanly as one import-ordered packet
and are accepted by the per-file 60-second check. The four original inline
scalar-comparison signatures were independently checked against the moved API in a
temporary module; all four checks compiled. Private construction helpers use no_expose;
public exposure and visibility are preserved.

Change record: `coord/changes/T1-adic-finite-reduction-data-location.md`, including the
complete downstream consumer table. No consumer source requires a forced adaptation.

## Proved and sorry left

Original holes: 1. Closed: `AlgebraicGeometry.Scheme.adic_constructible_finite_reductions`
(node `lem-sfb-adic-constructible-finite-reductions`). The assigned module now has zero holes.
All previously proved scalar constructions remain proved in the data companion.

Added holes: 4, one public theorem per new module:

- `AlgebraicGeometry.Scheme.adicFiniteReduction_tor`, node
  `lem-sfb-adic-finite-reduction-tor`: residue comparison and finite ideal filtration.
- `AlgebraicGeometry.Scheme.adicFiniteCompletion_bounds`, node
  `lem-sfb-adic-finite-completion-bounds`: completion tower and the Milnor endpoint argument,
  assuming the uniform reduction Tor bounds and no etale origins.
- `AlgebraicGeometry.Scheme.adicFiniteEtale_origins`, node
  `lem-sfb-adic-finite-etale-origins`: individual constructible etale origins with Tor
  bounds, assuming the reduction bounds; no compatibility or marked zero origin.
- `AlgebraicGeometry.Scheme.adicFiniteEtale_transitions`, node
  `lem-sfb-adic-finite-etale-transitions`: normalized quotient maps and cocycle for any
  given bounded constructible finite-Tor origins and comparison isomorphisms.

This is a decomposition, not a net proof gain: one upper hole closed, four lower holes
added. The choices of origins and isomorphisms introduced here occur inside the proof of the
existential conclusion. Existing universal construction choices are retained. No definition
has a hole.

## No longer needed

No mathematical dependency or module is pruned. Removed direct private imports from the
construction companion: CoefficientProEtaleTorAmplitude, Mathlib.RingTheory.Noetherian.Defs,
KFlatRingedToposPullback, TensorColimitsIndependentCoefficients, ChangeOfRingsKFlat,
DerivedChangeOfRingsIndependentCoefficients, FlatOnSite, DerivedChangeOfRingsCochainModel,
and WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian. The construction
proofs use the source's proved interfaces, and required public imports remain reexported.
The unused private adicFiniteTwoDerivedComparisons helper and the common derived-pullback
argument of adicFinitePullChangeComparison are removed after reusing
resolving_module_square_iso. The parent's old proof dependencies remain in the four
argument-step nodes, the construction node, and their source interfaces. They are still
needed for the same Stacks argument. The main theorem privately imports the four steps.
No public declaration is withdrawn and no upstream declaration is removed or replaced
by a hole.

The parent node's proof and proof_deps now describe the actual combination of these four
steps. Its public theorem statement is unchanged. The integral-models unit's route is
unchanged. The searches found ordinary adic completion and bounded-representative lemmas,
but no direct theorem on these arbitrary-ring normalized derived sheaf towers. In
particular the existing complete-residue bounds for padic coefficients do not apply to
an arbitrary Noetherian coefficient ring and ideal. Mathlib preimageIso supplies the
generic lifting subroutine for the transitions step, but not the constructible-domain
check, the concrete comparison identification or the normalized quotient cocycle.

## Where the brief, the DAG or earlier work was wrong

The pre-existing data file does not meet the 60-second compile bound on this server:
the untouched baseline took 70.3 seconds. This is a performance issue, not a mathematical
counterexample or a tool failure. The original final theorem is otherwise unchanged.

The canonical comparison in the statement and the comparison used by the general
constructible equivalence have different implementations. The etale-origins step explicitly
requires identifying them through uniqueness of derived inverse image and the ordinary
module adjunction; an arbitrary derived equivalence is insufficient. The transitions step
similarly retains the actual normalized comparisons, not unspecified isomorphisms.

A dependency audit found a pre-existing cycle outside this packet between
`lem-pc-ring-hom-extension-differential` and its adjacent-degree helper. No new node
points back to this item. Those existing records are left for the maintainer to reconcile.

The new statements were checked against the empty scheme, zero complex, zero ideal,
unit ideal, n=0, repeated quotient indices and a=b. The Tor step needs no completeness;
the origins step has no prescribed marking; the transitions step accepts arbitrary
markings and uses faithfulness to enforce the cocycle. The completion step retains the
endpoint b by using epimorphisms on H^b, rather than losing a degree.

## New nodes

`lem-sfb-adic-finite-reduction-data` attaches the relocated, fully proved construction API;
it adds no mathematical assertion or hole. It retains the original K-flat and adjunction
proof dependencies and the sectionwise normalizations.

`lem-sfb-adic-finite-reduction-tor` realizes Stacks 09C2 (2) through the finite ideal
filtration of a quotient-module test, following sites-cohomology lemma-bounded (0942).

`lem-sfb-adic-finite-completion-bounds` realizes Stacks 09C2 (1), assuming all reduction
Tor tests and using the complete-object unit, exact products and the Milnor sequence.

`lem-sfb-adic-finite-etale-origins` realizes Stacks 09C2 (3)-(4): common strata,
nilpotent-reduction lissity, constructible comparison and reflection of the Tor interval.

`lem-sfb-adic-finite-etale-transitions` realizes the original proof steps 8-10: quotient
constructibility, lifting the normalized comparison isomorphisms and faithfulness for
the quotient cocycle. It does not construct the family or assert completeness.

All five nodes carry the parent chapter/unit, source, complete proof steps, actual
Mathlib searches and Lean attachments. Their source docstrings describe the full remaining
arguments. The original unit and chapter records are untouched.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

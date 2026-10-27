## What changed

Proved `Algebra.CotangentResolution.isZero_cotangentComplex_of_etale` with its existing
signature and public imports unchanged. The proof follows Stacks, Cotangent Complex,
Tags 08R2(5), 08R0 and 08R1: the square-zero lifting bijections give a formally étale
algebra, finite presentation gives étaleness, and Mathlib supplies both weakly étale
flatness assertions. Apply the existing derived-diagonal criterion and cotangent
bootstrap, then preserve the zero object under each integer-degree homology functor.

Two proved private helpers supply the elementary homological calculations.
`flat_surjection_diagonal` proves invertibility of the precise projective-resolution
multiplication used by the diagonal criterion: flat extension preserves the
augmentation's quasi-isomorphism; ordinary multiplication is bijective for a
surjection; the single-complex comparisons are invertible; extension of the complex
shape preserves quasi-isomorphisms and derived localization inverts them.
`flat_tor_vanishing` computes positive Tor using a projective resolution and applies
Mathlib's exactness of tensoring with a flat module.

Added private proof imports for Mathlib's module-category descent (flat scalar
extension), weak étaleness, extension of complex shapes with homology, and preservation
of colimits by adjoints. Removed redundant direct imports for flat-category theory
and preservation of homology because they are already exposed by these dependencies.

Updated the item's node proof and proof dependencies to match this argument. No
statements, definitions, source-library modules or consumers were changed. The item
is a supporting node below the unit's realized route; no unit statement or proof step
is bypassed. The latest blueprint unit and the source's three tags were read.

## Proved and sorry left

Closed 1 of 1 original holes:
`Algebra.CotangentResolution.isZero_cotangentComplex_of_etale`
(node `lem-trf-etale-cotangent-vanishing`). Both private helpers are fully proved.
Validation: `lcompile.py` compiled the proof cleanly in 6.6 seconds; all four
new import directions passed `tools/import_direction.py may`. A source comparison
confirmed the original theorem signature and public imports are verbatim unchanged;
all Lean lines are at most 100 characters.
Zero holes remain in the item; zero holes were added or split off.

The proof uses the existing declarations
`Algebra.CotangentResolution.derived_diagonal_cotangent_vanishing` and
`Algebra.CotangentResolution.cotangentComplex_isZero_of_tor_and_diagonal`.
Their existing proofs are still `sorry` in their own modules; this delivery proves
the assigned theorem from those stated dependencies and does not claim the entire
transitive cotangent theory is closed.

The constructions allow zero rings and arbitrary commutative rings. Surjectivity
uses the tensor `c ⊗ 1` and needs no nontriviality. Positive Tor degrees are exactly
successor naturals. Homology vanishing covers every integer.

## No longer needed

Removed the private import `Sheaf.Algebra.Homology.FlatSurjectionDerivedSelfTensor`.
The node `lem-trf-flat-epimorphism-derived-self-tensor` and that module are no longer
needed by this item's proof. Its specialized calculation is proved directly for the
projective-resolution model required by the retained diagonal criterion. The node
edge is removed; no declaration or module is withdrawn. All other original declared
proof dependencies remain used. No other nodes or modules are proposed for pruning.

## Where the brief, the DAG or earlier work was wrong

The planned flat-surjection theorem and derived-diagonal criterion formalize canonical
multiplication using different constructions. The former uses a chosen left-derived
tensor functor; the latter uses a projective-resolution augmentation. Their signatures
cannot simply be composed without proving a comparison. The direct flat-extension
calculation avoids this comparison and supplies precisely the latter hypothesis.
The mathematical source argument and the assigned statement need no correction.

The first delivery preflight flagged the additional `open scoped TensorProduct`
command as an interface change. Removed it and wrote the pure tensor with
`TensorProduct.tmul` explicitly, preserving the original public command environment.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

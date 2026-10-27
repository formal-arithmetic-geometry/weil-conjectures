## What changed

Replaced `finiteCoefficientTensorPullbackEncoding` with a derived comparison proof.
It constructs the square of left derived functors, applies the existing composition
identity for their tensor comparisons, identifies the published geometric comparisons,
and transports the resulting equality along the exact-encoding isomorphisms. Both
native projection contexts and all existing public statements remain unchanged. The
private naturality calculation is the generic tensor-transport argument already proved
in `Sheaf.Paper.SpDirectImageEtaleMate`, specialized here without importing its
unrelated etale projection dependencies. Local proved instance caches keep the
internal module closedness, braiding and graded tensor inference explicit. Generic
component-to-square and abstract derived-square lemmas keep the large concrete
constructions behind checked interfaces. The theorem locally disables the optional
`cleanup.letToHave` transformation to avoid expanding its dependent let bindings.
Serial elaboration avoids the asynchronous elaborator overhead in this file. The derived
proof respects irreducible definitions and uses no increased heartbeat or time limit;
kernel checking remains enabled.

Added `Sheaf.Paper.FiniteCoefficientHeartEncoding`. Its coefficient heart functor,
right square and adjunction mate are actual constructions. Its equivalence,
additivity and existence of a strong monoidal structure are proved. Its only remaining
obligation is monoidality of that specified mate for compatible heart tensor structures.
This is an underived tensor-and-unit equation, with no derived functor or projection.

Exposed the existing `sectionPushforward_smul`, `sectionPushforwardIso`, and
`encodingPushforwardNatIso` in the unclaimed module
`Sheaf.Paper.FiniteDiscreteEncodingPullbackFixed`, retaining their types and bodies.
The public mate construction therefore refers to public data declarations. Added their
names to that node's Lean attachment. No source-library file was changed.

Validation: the assigned module compiled in 28.0 s. Removed its profiler settings and
phase traces before the required delivery checks. The three unchanged external
declaration consumers compiled against the
exposed helpers: `FiniteDiscreteEncodingCompactification` (6.8 s),
`FiniteLocalizingSmoothLocalFormula` (49.3 s), and
`SupportedFiniteImageClassicalOrigin` (8.6 s). Their temporary unchanged source copies
were removed from the packet after checking.

## Proved and sorry left

Original item: one hole. Closed its body at
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteCoefficientTensorPullbackEncoding`
(node `lem-sfb-finite-coefficient-tensor-pullback-encoding`). No sorry remains in that module.

Added one hole:
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.coefficientHeartPullIso_monoidal`
(node `lem-sfb-finite-coefficient-heart-tensor-square`). It is exactly `:= by sorry`.
The heart functor and both square isomorphisms have complete constructions, and
`coefficientHeartEncoding_isEquivalence`, `coefficientHeartEncoding_additive`, and
`coefficientHeartEncoding_monoidal` are proved. The private tensor-transport calculation
in the assigned module is also proved. `FiniteDiscreteEncodingPullbackFixed` retains
zero sorries.

This is a decomposition: the packet replaces one upper hole with one strictly lower
hole. It does not claim a proof without sorry dependencies. No witness data are
selected from the remaining theorem to define any public object; its existential tensor
structures are used only inside the proof of the original existence theorem.

## No longer needed

No original import was removed and no module is withdrawn. The parent no longer uses
the planned `lem-sfb-constant-scalar-geometric-adjunctions` interface: the already proved
normalized identity-on-sections comparison in `FiniteDiscreteEncodingPullbackFixed`
constructs the concrete right square directly. The old tensor/Tor and internal-operation
nodes are no longer direct proof dependencies of the parent, but remain used by the
heart constructions. They are not globally pruned.

The exact-four-functor theorem `lem-sf-exact-derived-tensor-square` was examined but is
not imported: the adopted source theorem
`Functor.map_leftDerivedTensorComparison_comp_eq_of_iso` directly handles the left
derived pullbacks. The parent DAG now records the actual heart-square and native
comparison-normalization dependencies. No blueprint unit statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The former plan left the passage from the ordinary square to the published derived
comparisons implicit. The adopted composition theorem implements that passage; its
exactness and flat-preservation requirements are supplied by the existing pro-etale
pullback and coefficient-equivalence instances. No statement dispute is asserted.

Independent arbitrary monoidal structures on the two heart encodings would not justify
monoidality of their specified adjunction mate. The new statement instead asks for
compatible structures for the explicitly constructed mate, and its proof in words retains
the normalized pure-tensor and scalar-unit formulas. Its hypotheses permit the zero ring
and empty schemes; the argument uses their same balanced tensor universal properties.

## New nodes

`lem-sfb-finite-coefficient-heart-tensor-square` isolates the underived normalization
step of the existing finite-coefficient transport proof. The derived localization,
native comparison normalization, and transport to the published coefficient encodings
are proved in the parent. The new node records the precise mate, compatible tensor
structures, sources, proof steps, dependency declarations, and Mathlib searches.

Change record: `coord/changes/Q9-normalized-coefficient-pushforward-visibility.md`.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

The module defines and states `AlgebraicGeometry.weakRelativeNoetherNormalization`, the
weak relative Noether normalization lemma from Stacks Project Tag 0GTG.  It uses one
universe `u` for the two commutative rings, their `Algebra R A` structure, and the
canonical affine morphism `Scheme.Spec.map (Opposite.op (CommRingCat.ofHom
(algebraMap R A)))`.  The hypothesis `hft` is exactly finite type as recorded by the
dependency node: the conjunction of `LocallyOfFiniteType` and `QuasiCompact` for that
morphism.  The natural number `N` is the fibre-dimension bound.  The hypothesis `hN`
quantifies over every target point `y` and says that `topologicalKrullDim` of the
scheme-theoretic fibre (`Scheme.Hom.fiber`) is at most `(N : ℕ∞)`.  The conclusion
supplies `d : ℕ` with `0 ≤ d` and `d ≤ N`, an `R`-algebra homomorphism
`g : MvPolynomial (Fin d) R →ₐ[R] A`, and says that the induced affine morphism
`Scheme.Spec.map (Opposite.op (CommRingCat.ofHom g.toRingHom))` is
`Scheme.Hom.IsQuasiFinite` in the Stacks sense.  The proof is intentionally `sorry` at
stage 2.

The statement dependencies used are: `Mathlib.AlgebraicGeometry.Scheme`, declaration
`AlgebraicGeometry.Scheme`; `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, declarations
`AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`;
`Mathlib.AlgebraicGeometry.Fiber`, declaration `AlgebraicGeometry.Scheme.Hom.fiber`;
`Mathlib.Topology.KrullDimension`, declaration `topologicalKrullDim`;
`Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`, declaration
`AlgebraicGeometry.Scheme.Hom.IsQuasiFinite`; and
`Mathlib.Algebra.MvPolynomial.Basic`, declaration `MvPolynomial` (with its canonical
`MvPolynomial.aeval` universal-property interface available for proofs).

Edge cases checked against the source statement and proof are `N = 0` (the conclusion
allows `d = 0`), `d = 0` (the polynomial ring is `MvPolynomial (Fin 0) R`), empty
fibres (their Krull dimension is below every natural bound), and zero rings (the affine
scheme and point quantifiers are permitted to be empty).  No nonzero, nonempty, or
reduced hypothesis was added.  The lower bound `0 ≤ d` is retained verbatim from the
node, even though it is automatic for `d : ℕ`.

Searches for an existing declaration: `msearch.py ... leanfinder` with query “finite type
morphism of affine schemes fibres dimension at most N quasi-finite polynomial algebra”
returned only generic finite and quasi-finite declarations and no relative Noether
normalization theorem; `msearch.py ... loogle` with query
“Scheme.Hom.IsQuasiFinite, MvPolynomial, topologicalKrullDim” returned no hits (the
project predicate is not in Mathlib); `msearch.py ... grep` over Mathlib with
“NoetherNormalization|weakRelativeNoether|IsQuasiFinite” returned no relative theorem;
the corresponding grep over `WeilConjectures` and `lean/Sheaf` found no declaration of
this lemma.  Direct `rg` for `lemma-weak-relative-noether-normalization` and
`weakRelativeNoetherNormalization` likewise found no existing declaration.  The DAG
search found this item and its three citers, but no pre-existing Lean record for the
item.

No new definition nodes or dependency modules were needed.  No statement correction or
`STATEMENT-DISPUTED` issue was found.

## Second reading by Q31

The node and the Lean file were read clause by clause.  The affine scheme morphism in
Lean is induced by exactly `R → A` via `algebraMap`; `hft` renders finite type as the two
recorded components, with no extra separatedness or finite-presentation assumption.
The fibre hypothesis quantifies all points of `Spec R` and uses the recorded fibre and
Krull-dimension declarations.  The conclusion has the same integer interval
`0 ≤ d ≤ N`, the same polynomial ring in `d` variables, the same `R`-algebra map, and
the same quasi-finite induced morphism.  The zero-coordinate and empty-fibre cases are
included.  The file compiles cleanly with only the expected `sorry` declaration warning.


## Maintainer second reading (2026-10-18)

The independent maintainer reader checked the immutable delivery at
`d106552089e5dbb3e616829749abb614ed64d15c`. The theorem signature and the node's
`lean.statement` agree verbatim. All objects, hypotheses and conclusion clauses agree
with the node and Stacks Tag 0GTG. The actual `IsQuasiFinite` definition includes finite
type and isolated fibre points; finite type makes these discrete fibres quasi-compact,
hence finite. There is no extra nonzero, Noetherian, reduced, or field assumption.
Zero rings, empty fibres, N = 0 and d = 0 are included; a common arbitrary universe
accommodates both rings. No statement correction or dependency-interface repair is needed.

Two mechanical omissions were repaired in this complete replacement module. H8: replace
the short proof summary by all nine node proof steps, including their citations.
H9 / brief-stage2 section 3: add ordinary imports for the already stated proof dependencies
and their recorded Mathlib leaves. No declaration or theorem signature was changed;
the sole local theorem proof remains `sorry`. The generic coordinate-drop proof node
is not yet recorded with a Lean declaration, so there is no module for it to import.
It is a proof dependency, not a missing object needed to type this stage-2 statement.

The original module was reproduced with `scompile.py Q31
lem-trf-weak-relative-noether-normalization <snapshot module>`: exit 0, sandbox 3.7 s,
library 1.7 s, no diagnostics, using the wrapper's isolated side overlay.
The current wrapper dispatches this overlay compile to the server; no direct SSH,
lake build, repository edit, or live Lean write was used by the reviewer.

The corrected complete module was compiled with the same wrapper and item arguments,
using `fixes/lean/Sheaf/TraceFormula/WeakRelativeNoetherNormalization.lean`: exit 0;
power-perturbation dependency overlay 1.9 s, sandbox 2.0 s, library 1.9 s; no diagnostics.
The signature remains byte-for-byte equal to `lean.statement`; every line is at most
100 characters. Independent searches of Mathlib, upstream WeilConjectures and the side
Sheaf tree found only field-base normalization, generic-domain spreading, and Zariski
factorization variants, not this arbitrary-base bounded-fibre theorem. None of the
item's statement or proof dependencies occurs in the current route-pivot dropped list;
no route-pivot repair note exists for this item.

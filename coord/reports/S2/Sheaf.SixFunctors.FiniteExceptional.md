## What changed

Relocated the existing construction block from FiniteExceptional to
FiniteExceptionalData, publicly re-exported by the original module, to permit acyclic
imports of two strict quotient obligations. Every original name, signature and data body
is preserved. Proved the assembly theorem finite_exceptional: normalization follows from
the specified unique normalized isomorphism; the unit and counit equations follow from
Mathlib unit_mateEquiv and mateEquiv_counit and cancellation of q with its inverse.
The two remaining geometric clauses are isolated in new one-theorem modules.
Refactored quotient_comp and quotient_id through a proved private quotient_map helper
to avoid expensive kernel unfolding of constant sheafification. This is a proof-only
performance change, preserving both statements.

## Proved and sorry left

Closed the original hole WeilConjectures.FiniteExceptional.finite_exceptional by a
complete proof from smaller statements. This is a decomposition, not a new axiom-free
geometric proof: 1 original hole reduced, 2 new holes added, net -1.
The current source had 3 original holes after X3's independent six proofs landed.
X3's six proofs are preserved and are not counted as this delivery's work.

Original holes retained unchanged in FiniteExceptionalData, node lem-coef-finite-exceptional:

- WeilConjectures.FiniteExceptional.adjunction_existsUnique.
- WeilConjectures.FiniteExceptional.dualFormula_existsUnique.

New holes:

- WeilConjectures.FiniteExceptional.exceptional_quotient_isIso,
  node lem-sf-finite-exceptional-quotient-is-iso.
- WeilConjectures.FiniteExceptional.exceptional_quotient_coherence,
  node lem-sf-finite-exceptional-quotient-coherence.

All 31 original named declarations were checked against the synchronized source: no
signature or non-theorem body changed. All four delivered Lean modules compile without errors or warnings. The final theorem
compiled in 11.5 seconds against the sandbox data modules.

Thus four named theorem holes remain across the delivery; none occurs in a definition.
The quotient statements are strict parts of the original conjunction, with none of the
normalization or adjunction-unit/counit assertions repackaged as a hypothesis.

## No longer needed

No mathematical dependency or module is withdrawn. The original unit route remains.
The original module's direct imports are supplied through the public data-module import;
private imports for preservation proofs move with those proofs. No source declaration
or dependency used by an existing upstream proof is pruned. The two split modules use
only the data interface in their statements. Their geometric proof dependencies remain
recorded in their nodes for subsequent workers.

The direct import statements moved to the data file are:

- `Sheaf.Paper.SixFunctorOperationDatum`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`.
- `Sheaf.Paper.FiniteTorAmplitude`.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`.
- `Sheaf.Paper.DerivedPullbackTensorHom`.
- `Sheaf.AlgebraicGeometry.SfOpenExceptionalBaseChange`.
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`.
- `Sheaf.SixFunctors.FiniteDualizing`.
- `Sheaf.SixFunctors.CoefDualFormulaScalarTranspose`.
- `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingPullbackComparison`.
- `Sheaf.Paper.ExceptionalFiniteOperations`.
- `Sheaf.Paper.FiniteCtfTriangulated`.
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`.

## Where the brief, the DAG or earlier work was wrong

The initially mirrored source lagged X3's six-proof landing, while the current queue
already reported three holes. This packet preserves the synchronized three-hole source.
The final theorem also contains purely formal consequences of the defined mate: its
unit/counit clauses do not need a further geometric theorem.

Edge cases checked in the statements and proof plans: positive exponents are n+1,
self-quotients use the actual identity coefficient map, associators are the prescribed
reassoc maps, and no nonempty-scheme or coefficient-flatness hypothesis was added.

## New nodes

def-sf-finite-exceptional-constructions records the relocated construction interface.
The two quotient nodes isolate respectively invertibility (duality comparison plus its
counit normalization) and coherence (scalar comparison composition/identity plus mate
pasting). Both are proper subsets of the original theorem, and have complete source-based
proof plans. Blueprint searches found only broader exceptional-scalar propositions in
sec-six-functors-basics, with no attached Lean declaration, and the original combined
finite-exceptional node. They do not provide this exact restricted normalized interface.

Change record: coord/changes/S2-finite-exceptional-constructions-relocation.md.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

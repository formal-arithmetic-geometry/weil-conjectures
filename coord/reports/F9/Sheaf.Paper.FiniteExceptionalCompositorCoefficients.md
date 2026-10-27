## What changed

Replaced the proof hole in
`WeilConjectures.FiniteExceptionalCompositorCoefficients.finiteExceptionalCompositorCoefficients`
by the categorical counit calculation. The proof computes both inverse Hom transposes,
identifies them with the stated commonTranspose, and applies injectivity of the Hom
equivalence. Private proved helpers expose the conjugate counit and the two calculations.
The target signature and the public definitions are unchanged.

The geometric left-adjoint square is isolated in the new module
`Sheaf.Paper.FiniteCompactSupportCoefficientSquare`. It is precisely Step 1 of the
existing proof plan, with finite endpoint stages and the existing Allowed predicate;
it asserts no right-adjoint equation. The original theorem converts its narrower
FiniteChange hypothesis to Allowed and combines the left square with the completed
mate calculation. The original unit route is retained.

## Proved and sorry left

The original hole in
`WeilConjectures.FiniteExceptionalCompositorCoefficients.finiteExceptionalCompositorCoefficients`
is closed relative to the new geometric square. This is a decomposition, not a net
proof: one original hole closed and one new hole added.

The only remaining hole in the packet is
`WeilConjectures.FiniteCompactSupportCoefficientSquare.finiteCompactSupportCoefficientSquare`
(node `lem-sf-finite-compact-support-coefficient-square`). It has a source and a complete
natural-language proof in its docstring. No definition contains sorry.

## No longer needed

The item no longer directly imports `Sheaf.SixFunctors.CompactCoefficientComposition`
or `Sheaf.Paper.FiniteFreeCompactComposition`: its private proof only needs the left
square, which retains these dependencies in its own DAG proof plan. The unproved square
does not import them before using their declarations in a Lean proof. Consequently neither
underlying node is claimed globally unnecessary and no module is withdrawn.
The original node no longer directly needs
`lem-sf-compact-coefficient-composition` or
`lem-coef-finite-free-compact-composition`; they remain reachable through the new node.
The obsolete direct tool_uses entries for those two nodes are removed from the
item node; their mathematical dependencies remain in the new square.
No blueprint unit or source-library declaration is pruned.

## Where the brief, the DAG or earlier work was wrong

The existing Step 1 describes the quotient and finite-free composition results as
exactly the square required here. Their Lean statements instead use fixed-scalar
module sheaves, universal coefficient tensor models, and retained etale-origin
compositors. The present target uses arbitrary normalized Operation and Scalar
presentations on intrinsic finite-Tor categories. Transport through finiteLeft,
finiteAlpha, the operation datum's finiteCompositionNormalization, and QNormalized
is therefore a substantive missing argument. This is the new square's responsibility.

An additional existing theorem,
`AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility_composition`,
handles arbitrary finite coefficient ring maps and supplied compactifications. Its
pro-etale arrow is the normalized transport of reductionDirectImageComparison;
identifying that with the PurCompactSupport mate used by QNormalized still requires
the same normalization transport. No claim that the presentations agree by definitional
equality has been used.

## New nodes

`lem-sf-finite-compact-support-coefficient-square` records the left-adjoint geometric
composition square, a strict part of the original five-step argument. It retains the
positive quotient, ramified retained level, identity, and composite cases. At identity
levels, identity geometric maps, empty schemes, or zero objects the asserted equation
is the same normalized composition square; it assumes no flatness of quotient maps.
The item node now cites this step and retains its four categorical steps. There are
no statement or definition changes and no change records.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

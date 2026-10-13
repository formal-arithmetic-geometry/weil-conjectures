## What changed

Replaced the original sorry with a composition of two commuting coefficient squares. Added `AffineClosedImmersionCoefficientSquare` for the restricted coefficient adjunction map and `AffineKoszulHomCoefficientComplexSquare` for the finite free complex coordinate calculation. Added and proved `AffineKoszulHomCoefficientHomologySquare`: its private generic helper applies homology, the exact-functor homology comparison, and natural extension homology, then composes their commuting squares. The original module applies a proved generic square-transport helper and specializes the Hom functor parameter by reflexivity. All existing public imports and the original theorem signature remain unchanged.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.affine_koszul_coefficient_hom_coordinates`. Added 2 holes. This is a decomposition (net holes closed minus added = -1), not a sorry-free proof of the coordinate calculation.

The two remaining sorry declarations are `AlgebraicGeometry.affine_closedImmersion_coefficient_square` (node `lem-sc-affine-closed-immersion-coefficient-square`) and `AlgebraicGeometry.affine_koszul_hom_coefficient_complex_square` (node `lem-sc-affine-koszul-hom-coefficient-complex-square`). Each is strictly smaller than the original argument, is in its own module, and has the full construction and proof in its docstring. `AlgebraicGeometry.affine_koszul_hom_coefficient_homology_square` is proved from the complex square and existing exactness results. All private helpers are proved; the original module has no sorry.

## No longer needed

Removed the original direct proof imports `Sheaf.AlgebraicGeometry.AffineQuotientRestrictedIso`, `Sheaf.Algebra.Homology.HomComplexToSingle`, `Mathlib.LinearAlgebra.ExteriorPower.Basis`, and `Sheaf.AlgebraicGeometry.TildePreservesFiniteLimits`. They remain dependencies of the new intermediate modules. `ExtendHomology`, `PreservesQuasiIso`, and `QuasicoherentKernel` are proof imports only in the new homology square module. No node or module is claimed globally unnecessary: the affine quotient, Hom-to-single, exterior basis, and exactness arguments are still needed. Pruned globally: none.

Every old direct proof dependency is accounted for: `lem-sc-affine-quotient-restricted-iso` now belongs to the closed-immersion square; `lem-sc-hom-complex-to-single`, `lem-weil-pbc-exterior-power-free-basis`, and `new-j3-koszul-quotient-coefficient-complex` belong to the complex square; `lem-sc-tilde-preserves-finite-limits` belongs to the homology square. All five leave the original node's direct `proof_deps`, but remain in the delivered argument. The quotient-coefficient construction also remains a public statement dependency of the original module.

## Where the brief, the DAG or earlier work was wrong

The original DAG describes the needed calculations correctly in words, but its listed Lean dependencies do not state the coefficient naturality or identify the adjunction unit with the quotient map. These are now separate intermediate statements; the original theorem follows by a real composition and naturality argument. No existing statement or definition was changed. No forced adaptations or change records were necessary.

## New nodes

`lem-sc-affine-closed-immersion-coefficient-square`, module `Sheaf.AlgebraicGeometry.AffineClosedImmersionCoefficientSquare`: identifies both restricted coefficient objects and the actual adjunction-unit map with the affine quotient. It has no Koszul complexes or homology.

`lem-sc-affine-koszul-hom-coefficient-complex-square`, module `Sheaf.AlgebraicGeometry.AffineKoszulHomCoefficientComplexSquare`: constructs the finite free coordinate isomorphisms and their coefficient square before taking homology. It has an arbitrary ideal and no closed immersion or adjunction map. Its Hom functor parameter is required to equal the specified canonical functor. Edge cases checked mathematically: empty sequence, degrees above n, zero ring, empty chart, and quotient by the unit ideal.

`lem-sc-affine-koszul-hom-coefficient-homology-square`, module `Sheaf.AlgebraicGeometry.AffineKoszulHomCoefficientHomologySquare`: proved homology transport of the previous square using exactness and extension naturality. It introduces no hole. The unit realization record is empty, and the decomposition retains the original route and source.

## Second reading by D2

1. Compared the original module against the repository with diff. The sole existing public theorem signature and every existing public import are byte-for-byte unchanged. Its docstring is unchanged. The added helpers are private, and no existing definition or statement was altered. No change record is needed.

2. Compiled all four delivered modules in import order with lcompile.py: clean, no errors or warnings. Exactly the two named public split theorems have `:= by sorry`; there are no new definitions, arbitrary witness choices, forbidden declarations, or hidden holes. Explicit axiom probes and the delivery probe verify only propext, Classical.choice, Quot.sound and sorryAx from open imported statements. The generic transport helper has no sorryAx. The original theorem is therefore a checked reduction with remaining dependencies, not a completed sorry-free calculation.

3. Read each new statement, its docstring, node, and underlying constructions. Checked the signs: the Hom differential is -(-1)^k precomposition, agreeing with the dual boundary (-1)^(k+1); negative degrees and the -1-to-0 boundary vanish. Checked n=0, n=1, m>n, I=bottom, I=top, zero rings and empty charts. The geometric square is the localized quotient map; the complex square is independent of closed immersions and homology. Both are true and strictly smaller pieces, not renamings of the original. Read Stacks Tags 0BQZ, 01I9 and 01HV. Independent leanfinder searches for coefficient-variable finite-free internal Hom naturality and the affine closed-immersion quotient square, loogle for the canonical unit, msearch grep for unit/restriction formulas, and local rg found component lemmas but no existing coefficient square. The existing affine dual comparison has structure-sheaf coefficients only and cannot provide the quotient square. Neither remaining hole has a short proof from the currently available declarations.

4. Read the reduction from the original theorem downward. It maps and vertically composes actual coefficient squares; the homology helper composes the mapped square, exact-functor comparison and extension comparison using their naturality. The original proof plan is retained through smaller steps. Checked imports against statement needs and actual proof/instance needs; all new proof imports are private. The unit sk-thm-picard-duality has empty realization slots, and no realized unit node is bypassed. Expanded No longer needed to account for all five old direct proof dependencies; none is globally pruned.

5. Compared node statements with Lean signatures and proof steps with the code. New nodes have sources, searches, provenance, chapter/unit, blueprint ancestry and verbatim Lean statements. Corrected the homology square node to record both restriction limits and colimits dependencies used in instance synthesis, and its cited complex square statement dependency. No Lean change was necessary.

Second reading changed only the DAG dependency accounting and this report. One original hole closed and two simpler holes added: decomposition, net -1.

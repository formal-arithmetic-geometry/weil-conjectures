## What changed

Proved `AlgebraicGeometry.Scheme.picard_riemannRoch` without changing its statement,
any public definition, or any public import. Added three proved private helpers in the
same module for skyscraper support, its Euler characteristic, and the weighted degree
of the actual valuation-bounded `Divisor.associatedModule`.

The divisor argument uses `regular_curve_divisor_calculus` for the modification exact
sequence, proves its quotient coherent by the cokernel presentation, computes its H0
by evaluation, and obtains the Euler increment from `eulerChar_zero_dim_support`.
Tensor additivity and additive-homomorphism extensionality extend the single-point
calculation to every integral divisor. Principal degree zero follows from O(div f)=O.

Reused the existing source declarations, rather than copying their proofs:
`Modules.eulerChar_eq_degree_add`,
`Modules.eulerChar_eq_finrankH_zero_sub_finrankH_one`,
`Modules.eulerChar_eq_coherentDegree_add`,
`serreDuality_residueTrace`, `degree_relativeDifferentials`,
`Modules.finrankH_one_eq_zero_of_degree`, `finrankH_zero_eq`,
`isAmple_of_degree_pos`, and `isAffine_compl_of_isAmple_dual_toModules`.
The source coherent proof performs torsion reduction, saturated line subbundles,
rank induction and determinant multiplicativity; the source ampleness proof uses
one- and two-point dimension drops and descent. Thus the unit RR/G/H route stays.
The coherent determinant is transported through `exteriorSheafIsoExteriorPower`.

For arbitrary field extension, extracted the normalized differential isomorphism and
trace equation from `picard_rr_duality` applied to omega. Naturality of the constructed
`moduleCohomologyExtResolutionEquiv` transports its trace equation to exactly the
Ext-resolution cohomology map in this statement. Bijectivity uses
`H.baseChange_bijective_of_isSeparated` and the adjunction pullback isomorphism.
Degree and Euler base change use the existing source comparison theorems.

Updated only `proof`, `proof_deps`, `proof_origin` and obsolete `tool_uses` of
`sk-thm-picard-rr` to record this route. No source-library files were edited.
No declaration data is chosen from a mere existence theorem: witnesses from the
calculus and duality theorem are used only inside proposition proofs.

Validation: the final zero-hole module compiled on the project server in 27.4s
with no warnings after removal of redundant private imports. The required delivery
preflight additionally checks the complete packet.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.Scheme.picard_riemannRoch`
(node `sk-thm-picard-rr`): 1 of 1 proved. Added 0 holes, split off 0 statements.
There are 0 `sorry` tokens in the delivered module and no other delivered Lean module.

All three private helpers are fully proved:
`picardRR_skyscraper_support`, `picardRR_skyscraper_euler`,
and `picardRR_divisor_degree`. The proof still uses the existing named declarations
`regular_curve_divisor_calculus` and `picard_rr_duality`; their outstanding proofs
remain the intended downstream work, not newly added holes.

## No longer needed

Removed the following original private imports:

- `Mathlib.AlgebraicGeometry.AlgClosed.Basic`
- `Mathlib.LinearAlgebra.Dimension.Constructions`
- `Sheaf.AlgebraicGeometry.Curve.ProperProjective`
- `Sheaf.AlgebraicGeometry.GlobalSectionsGeomConnected`
- `Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact`
- `Sheaf.AlgebraicGeometry.RegularCurveTorsionfreeFree`
- `Sheaf.AlgebraicGeometry.TorsionSubsheafQuotient`
- `Sheaf.AlgebraicGeometry.VectorBundleLineSubbundle`
- `Sheaf.AlgebraicGeometry.VeryAmpleSeparationCriterion`
- `WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism`
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper`
- `WeilConjectures.AlgebraicGeometry.Cohomology.LongExact`
- `WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch`
- `WeilConjectures.AlgebraicGeometry.ModulePullbackTensor`
- `WeilConjectures.AlgebraicGeometry.ModuleSupportProperOverBase`
- `WeilConjectures.AlgebraicGeometry.Modules.Ample`
- `WeilConjectures.AlgebraicGeometry.Picard.Group`
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`
- `WeilConjectures.AlgebraicGeometry.Regular`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`

The removed Sheaf proof imports are replaced by existing source
proofs or instances; `EulerCharZeroDimSupport` is retained for the skyscraper
calculation. The source RR coherent formula replaces a second torsion/rank-induction
implementation. `RegularCurveDivisorCalculus`, `PicardRRDuality`, and
`ExteriorSheafComparison` remain needed. Source modules removed as direct imports
may remain available through public source dependencies; this delivery does not
withdraw them or claim they disappear from the targets' transitive import closure.
The redundant trial imports of `Modules.FiniteDescent`, `Curve.AdelicLocal` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced` were also removed;
existing public dependencies already expose their declarations.

No longer needed as direct planned dependencies: `lem-sc-proper-dim-one-projective`
(the statement already assumes projectivity), `lem-pc-closed-immersion-coherent-cohomology`
(cokernel finite presentation proves coherence directly),
`lem-sc-torsion-subsheaf-quotient`, `lem-sc-regular-curve-torsionfree-free`,
`lem-sc-vector-bundle-line-subbundle`, `lem-sc-determinant-short-exact`
(the existing coherent source theorem implements the whole argument),
`lem-sc-pic-group` (the source trace pairing already uses the required dual),
and `lem-sc-very-ample-separation-criterion`, `lem-pc-very-ample-descends`,
`lem-weil-pbc-closed-point-residue-field-base`, `lem-weil-pbc-module-pullback-tensor`
(the existing source ampleness proof implements G).
`lem-pc-finrank-field-base-change` is not directly needed because the existing Euler
and degree base-change theorems and the canonical bijective cohomology comparison
supply precisely the required clauses.

Removed obsolete direct tool approvals for `lem-pc-projective-proper`,
`lem-pc-vanishing-above-dim`, `lem-weil-pbc-coherent-kernel-cokernel-locnoeth`,
`lem-weil-pbc-module-support-proper-over-base`, `lem-sc-pic-group`,
`lem-sc-proper-dim-one-projective`, `lem-pc-closed-immersion-coherent-cohomology`,
`lem-weil-pbc-closed-point-residue-field-base`, and
`lem-weil-pbc-module-pullback-tensor`. Their source-library declarations and proofs
are preserved verbatim, including all transitive proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The planned argument is valid, but much of its torsion, determinant, high-degree
vanishing and ampleness work was already implemented in the adopted source library.
The source audit records those declarations, and they can be reused over the present
field hypotheses. The remaining weighted-divisor comparison is needed because the
present statement uses the explicit valuation-bounded associated module.

No mathematical statement or definition repair was required. No new nodes.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

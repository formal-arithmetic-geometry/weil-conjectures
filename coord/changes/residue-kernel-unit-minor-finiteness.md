# ModuleCat.residue_kernel_unit_minor_matrix_core

## Reason

The Lean signature omitted finite generation, although its DAG statement and proof explicitly
say finite free. The infinite-free version is false. Let A=k[t]_(t), F=⊕_{n≥0} A e_n,
and T(e_n)=e_n-t e_{n+1}. Take R=A, X=A×F, Y=F, and f(a,x)=T(x).
The residue map is (a,x)↦x, with kernel k. T is injective (coefficient induction)
but not surjective: a preimage of e_0 would have coefficients 1,t,t²,… and hence infinite
support. Its cokernel is A[1/t], a nonzero t-divisible module. If the asserted normal form
existed, f's nonzero kernel and torsion-freeness of free C over the domain A force g=0.
Thus the cokernel would be free C. A nonzero free module cannot be t-divisible for a nonunit t:
a basis vector cannot be t times another vector. Contradiction.

Restore precisely the finite scalar-extension hypotheses already stated by the DAG.
No Challenge target changes. The only downstream declaration that applies the core already
assumes X,Y are finite over R, so these new hypotheses follow by finite tensor base change.
Every downstream statement retains its meaning; this corrects an overgeneral intermediate lemma.
The node's informal statement already says finite free and remains unchanged.

## Old

```lean
theorem residue_kernel_unit_minor_matrix_core (R : Type v) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] [IsLocalRing A] (X Y : ModuleCat.{v} R) (f : X ⟶ Y) (hX : Module.Free A ((ModuleCat.extendScalars (algebraMap R A)).obj X)) (hY : Module.Free A ((ModuleCat.extendScalars (algebraMap R A)).obj Y)) (𝔭 : Ideal R) [𝔭.IsPrime] (hres : Nonempty (LinearMap.ker ((ModuleCat.extendScalars ((IsLocalRing.residue A).comp (algebraMap R A))).map f).hom ≃ₗ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField A)) : ∃ (U C : ModuleCat.{v} A) (g : A →ₗ[A] C), Module.Free A C ∧ ∃ (eX : ((ModuleCat.extendScalars (algebraMap R A)).obj X) ≃ₗ[A] (U × A)) (eY : ((ModuleCat.extendScalars (algebraMap R A)).obj Y) ≃ₗ[A] (U × C)), ∀ x, eY (((ModuleCat.extendScalars (algebraMap R A)).map f).hom x) = ((eX x).1, g (eX x).2)
```

## New

```lean
theorem residue_kernel_unit_minor_matrix_core (R : Type v) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] [IsLocalRing A] (X Y : ModuleCat.{v} R) (f : X ⟶ Y) (hX : Module.Free A ((ModuleCat.extendScalars (algebraMap R A)).obj X)) (hY : Module.Free A ((ModuleCat.extendScalars (algebraMap R A)).obj Y)) (hfX : Module.Finite A ((ModuleCat.extendScalars (algebraMap R A)).obj X)) (hfY : Module.Finite A ((ModuleCat.extendScalars (algebraMap R A)).obj Y)) (𝔭 : Ideal R) [𝔭.IsPrime] (hres : Nonempty (LinearMap.ker ((ModuleCat.extendScalars ((IsLocalRing.residue A).comp (algebraMap R A))).map f).hom ≃ₗ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField A)) : ∃ (U C : ModuleCat.{v} A) (g : A →ₗ[A] C), Module.Free A C ∧ ∃ (eX : ((ModuleCat.extendScalars (algebraMap R A)).obj X) ≃ₗ[A] (U × A)) (eY : ((ModuleCat.extendScalars (algebraMap R A)).obj Y) ≃ₗ[A] (U × C)), ∀ x, eY (((ModuleCat.extendScalars (algebraMap R A)).map f).hom x) = ((eX x).1, g (eX x).2)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.ResidueKernelUnitMinorMatrixCore | H2 | Restore two missing finite hypotheses; prove block elimination from a pivot. |
| Sheaf.Algebra.Homology.ResidueKernelUnitMinorKernel | unclaimed | Forced proof adaptation only: register hfX,hfY as local instances, import finite tensor base change, and supply the two new finite witnesses after exposing the scalar-extension tensor action and choosing (algebraMap R A).toAlgebra. Existing statement and visibility stay identical. |

These are all modules returned by tools/downstream.py with --uses for the declaration.
The core's public finiteness import is required by its restored signature; the caller's
added tensor-finiteness import is proof-only. All other downstream modules keep their files
and statements. No target definition is changed, so no target semantic rereview is opened.

## Status

landed 20261013T215606-L-898650 2026-10-13 (merge of deliver/H2/Sheaf.Algebra.Homology.ResidueKernelUnitMinorMatrixCore)

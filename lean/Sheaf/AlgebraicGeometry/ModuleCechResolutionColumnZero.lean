module

public import Sheaf.AlgebraicGeometry.ModuleCechComparison

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The resolution augmentation identifies Cech cochains with degree-zero column homology.
Source: Stacks Project, Tag 01EQ, the beta construction; Tag 01DZ, left exactness of sections.
(blueprint: lem-sc-module-cech-resolution-column-zero)

Proof: the resolution augmentation identifies F with the kernel of I^0 → I^1.
For each finite intersection, sections preserve this kernel, since sections are left exact.
Restriction of scalars preserves the underlying kernel. Taking the product over tuples
also preserves kernels: a tuple lies in the kernel exactly when every coordinate does.
There are no incoming boundaries in degree zero. Thus the product augmentation identifies
Cech n-cochains of F with the zeroth homology of the column. The source is concentrated
in degree zero and its zeroth homology is itself; the induced map is this identification.
The choice of the chain-map proof ha has no effect, by proof irrelevance. This argument
requires no positive-degree vanishing assumption. -/
theorem moduleCech_resolution_column_zero {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) (F : X.Modules) (I : InjectiveResolution F)
    (ha : (CategoryTheory.cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (I.ι.f 0).val) ≫ (moduleCechDouble U I).d 0 1 = 0)
    (n : ℕ) :
    let A := (CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat
    let a : A ⟶ (moduleCechDouble U I).X 0 :=
      (CategoryTheory.cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (I.ι.f 0).val)
    QuasiIsoAt
      ((CochainComplex.fromSingle₀Equiv ((moduleCechDouble U I).flip.X n)
        (A.X n)).symm
        ⟨a.f n, by simpa [a, A, moduleCechDouble] using congrArg (fun f ↦ f.f n) ha⟩) 0 := by
  sorry

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.AlgebraicGeometry.BertiniUniversalFamily
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import WeilConjectures.ZetaSeries
import Sheaf.AlgebraicGeometry.BertiniSingularFibreEquations
import Sheaf.LinearAlgebra.SymmetricAlgebraKernelFactor

/-!
# A Bertini singular fibre lies in the first-order evaluation kernel

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of `lemma-bertini`.
(blueprint: lem-zl-bertini-singular-fibre-kernel).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

/-- The inclusion of a linear kernel into coefficient affine space, written on coordinate
rings. Each variable maps to its coordinate functional restricted to the kernel.
Source: Stacks Project, Tag 0FD6, final paragraph, the kernel as a subspace of `V`.
(blueprint: lem-zl-bertini-singular-fibre-kernel). -/
def bertiniLinearKernelCoefficientMap {k K : Type u} [Field k] [Field K]
    (c : k →+* K) {r d : ℕ}
    (E : (Fin (r + 1) → K) →ₗ[K] K × (Fin d → K)) :
    Spec (CommRingCat.of (SymmetricAlgebra K (Module.Dual K E.ker))) ⟶
      Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin (r + 1))) k)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom
    ((algebraMap K (SymmetricAlgebra K (Module.Dual K E.ker))).comp c)
    (fun i ↦ SymmetricAlgebra.ι K (Module.Dual K E.ker)
      ((LinearMap.proj i.down).comp E.ker.subtype))))

/-- On a fixed affine smooth chart, the singular fibre embeds into the first-order kernel.
The compatibility records the actual coefficient coordinates.

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of `lemma-bertini`;
Algebra Tag 00T7 supplies the one-way hypersurface criterion at non-flat parameters.
(blueprint: lem-zl-bertini-singular-fibre-kernel).

Proof: At the specified point choose a generating section nonvanishing there and shrink
inside its generating locus. Write the other sections as multiples `f_j` of this generator,
with `f_i = 1`. Relative smooth dimension `d` identifies the cotangent fibre with a vector
space of dimension `d`. The conormal surjection for the immersion into the projective chart
makes the `df_j` span that space: projective coordinate ratios pull back to these functions.
Choose a basis of the cotangent fibre and define `E(e_j) = (f_j, df_j)`. Column `i` is
`(1, 0)`, and subtracting `f_j` times that column yields `(0, df_j)`. Thus `E` is onto.

The universal section has local equation `F = sum x_j f_j`; its relative differential over
coefficient space is `sum x_j df_j`, because the ambient projection is smooth by base change.
At a point where this differential is nonzero, the hypersurface criterion supplies a smooth
open neighbourhood in the universal zero scheme. Consequently all coefficients of `F` and
`dF` vanish on the nonsmooth subset. They belong to its vanishing ideal and vanish on the
reduced singular scheme, and therefore on its scheme-theoretic fibre at `z`.

That fibre is a closed subscheme of coefficient affine space over `kappa(z)`: the universal
zero scheme and the reduced singular scheme both have closed inclusions into the ambient
product, and passage to fibres preserves closed immersions. Its coordinate quotient kills
all the homogeneous linear equations `E x = 0`. Choose a vector-space complement to `ker E`.
In bases respecting the resulting direct sum, those equations kill precisely the complementary
coordinates. The quotient polynomial algebra is therefore the symmetric algebra of the dual
of `ker E`. The induced surjective quotient to the fibre ring gives the required closed
immersion `j`. Restricting the coordinate functionals to `ker E` identifies its composite
with coefficient space exactly with the original coefficient projection. The construction
is independent of the preliminary open shrinking because the fibre lies over `z`, hence lies
entirely in that open. This includes zero-dimensional charts and zero-dimensional kernels.
No flatness of the hypersurface is inferred. -/
theorem bertini_singular_fibre_kernel
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (L : Y.Modules) [L.IsInvertible] (r : ℕ)
    (s : ULift.{u} (Fin (r + 1)) → Γ(L, ⊤))
    (hgen : Epi (L.freeHomEquiv.symm (fun i ↦
      (SheafOfModules.unitHomEquiv L) (Scheme.Modules.homOfGlobalSection L (s i)))))
    [IsImmersion (ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin (r + 1))) f L
      (fun i ↦ (SheafOfModules.unitHomEquiv L)
        (Scheme.Modules.homOfGlobalSection L (s i))) hgen)] (U : Y.Opens) (_hU : IsAffineOpen U)
    (d : ℕ) [SmoothOfRelativeDimension d (U.ι ≫ f)] (z : U) :
    ∃ E : (Fin (r + 1) → (U : Scheme).residueField z) →ₗ[
            (U : Scheme).residueField z]
            (U : Scheme).residueField z × (Fin d → (U : Scheme).residueField z),
          Function.Surjective E ∧
          ∃ j : (bertiniSingularToSource f L s ∣_ U).fiber z ⟶
              Spec (CommRingCat.of (SymmetricAlgebra ((U : Scheme).residueField z)
                (Module.Dual ((U : Scheme).residueField z) E.ker))),
            IsClosedImmersion j ∧
            j ≫ bertiniLinearKernelCoefficientMap ((U.ι ≫ f).residueFieldAlgebraMap z) E =
              (bertiniSingularToSource f L s ∣_ U).fiberι z ≫
                ((bertiniSingularToSource f L s) ⁻¹ᵁ U).ι ≫
                (bertiniSingularIdeal f L s).subschemeι ≫ bertiniUniversalProjection f L s := by
  obtain ⟨E, hE, A, hA, hKA, e, H, hH, hzero, hcoef⟩ :=
    bertini_singular_fibre_equations f L r s hgen U _hU d z
  let := hA
  let := hKA
  obtain ⟨G, hG, hGphi⟩ := symmetricAlgebra_factor_through_dual_kernel E H hH hzero
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom G.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hG
  let j := e.hom ≫ Spec.map (CommRingCat.ofHom G.toRingHom)
  refine ⟨E, hE, j, inferInstance, ?_⟩
  dsimp only [j, bertiniLinearKernelCoefficientMap]
  rw [Category.assoc, ← Spec.map_comp]
  have hpoly :
      (CommRingCat.ofHom (MvPolynomial.eval₂Hom
        ((algebraMap _ (SymmetricAlgebra _ (Module.Dual _ E.ker))).comp
          ((U.ι ≫ f).residueFieldAlgebraMap z))
        (fun i : ULift.{u} (Fin (r + 1)) ↦
          SymmetricAlgebra.ι _ _ ((LinearMap.proj i.down).comp E.ker.subtype))) ≫
            CommRingCat.ofHom G.toRingHom) =
      CommRingCat.ofHom (MvPolynomial.eval₂Hom
        ((algebraMap ((U : Scheme).residueField z) A).comp
          ((U.ι ≫ f).residueFieldAlgebraMap z))
        (fun i : ULift.{u} (Fin (r + 1)) ↦
          H (SymmetricAlgebra.ι _ _ (LinearMap.proj i.down)))) := by
    ext i
    · simp
    · have hr : E.ker.dualRestrict (LinearMap.proj i.down) =
          (LinearMap.proj i.down).comp E.ker.subtype := by
        ext x
        rfl
      simpa [hr] using hGphi (LinearMap.proj i.down)
  rw [hpoly]
  exact hcoef

end

end AlgebraicGeometry

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
public import Sheaf.AlgebraicGeometry.BertiniSingularFibreKernel
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The first-order kernel containing a Bertini singular fibre

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of `lemma-bertini`.
(blueprint: lem-zl-bertini-singular-first-order-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

/-- Locally the reduced singular scheme embeds fibrewise into the kernel of a surjective
first-order evaluation map. The displayed equality identifies the resulting coefficients
with the original universal family, rather than merely giving an abstract embedding.

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of `lemma-bertini`, the
surjection to first-order values and its kernel; Algebra Tag 00T7 supplies the one-way
hypersurface criterion needed at non-flat parameters.
(blueprint: lem-zl-bertini-singular-first-order-model).

Proof: Choose a generating section nonvanishing at the specified point and a smooth affine
neighbourhood on which it generates the invertible sheaf and the differentials are free of
rank `d`. Shrink inside a standard smooth chart, so the structure morphism has relative
dimension `d` everywhere on this neighbourhood. Divide the other sections by this generator,
obtaining functions `f_i`, with one of them equal to one. On each residue field the conormal
surjection for the immersion into the projective affine chart makes the `df_i` span the
cotangent fibre. Choose its basis and define `E(e_i) = (f_i, df_i)`. The distinguished column
is `(1,0)`; subtracting `f_i` times it gives `(0,df_i)`, proving surjectivity.
On coefficient space times the affine chart the universal section is the function
`F = sum x_i f_i` in the pulled-back generator. Smooth base change identifies its relative
differential with `sum x_i df_i`. If that differential were nonzero at a point of the zero
scheme, the hypersurface criterion would make the projection smooth near that point.
Consequently both `F` and all coefficients of `dF` vanish on the non-smooth subset. Its
reduced induced structure kills these functions, so its residue-field fibre is a closed
subscheme of the linear zero scheme of `E`. The latter has coordinate algebra the symmetric
algebra of the dual of `ker E`: choose a complement to the kernel, solve the surjective
linear equations there, and use the universal property of the symmetric algebra. The
quotient to the singular fibre is surjective, hence gives a closed immersion `j`. This
identification sends each polynomial variable to its coordinate functional restricted to
the kernel, which is exactly the displayed coefficient-map equality. The construction
includes a zero-dimensional source, a zero-dimensional kernel and the zero coefficient
vector, and never infers flatness of the universal hypersurface. -/
theorem bertini_singular_first_order_model
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (L : Y.Modules) [L.IsInvertible] (r : ℕ)
    (s : ULift.{u} (Fin (r + 1)) → Γ(L, ⊤))
    (hgen : Epi (L.freeHomEquiv.symm (fun i ↦
      (SheafOfModules.unitHomEquiv L) (Scheme.Modules.homOfGlobalSection L (s i)))))
    [IsImmersion (ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin (r + 1))) f L
      (fun i ↦ (SheafOfModules.unitHomEquiv L)
        (Scheme.Modules.homOfGlobalSection L (s i))) hgen)] :
    ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧
      ∃ d : ℕ, SmoothOfRelativeDimension d (U.ι ≫ f) ∧
        ∀ z : U, ∃ E : (Fin (r + 1) → (U : Scheme).residueField z) →ₗ[
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
  intro y
  obtain ⟨V, U, hV, hU, hy, e, d, hrel⟩ :=
    Smooth.exists_smoothOfRelativeDimension_resLE f y
  have := hrel
  have hsm : SmoothOfRelativeDimension d (U.ι ≫ f) := by
    rw [← Scheme.Hom.resLE_comp_ι f e]
    have : SmoothOfRelativeDimension (d + 0) (f.resLE V U e ≫ V.ι) := inferInstance
    simpa only [Nat.add_zero] using this
  have := hsm
  exact ⟨U, hy, hU, d, hsm, fun z ↦
    bertini_singular_fibre_kernel f L r s hgen U hU d z⟩

end

end AlgebraicGeometry

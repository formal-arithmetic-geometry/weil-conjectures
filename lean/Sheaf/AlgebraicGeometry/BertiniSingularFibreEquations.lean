/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q7
-/
module

public import Sheaf.AlgebraicGeometry.BertiniUniversalFamily
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import WeilConjectures.ZetaSeries
import Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion
import Sheaf.AlgebraicGeometry.HypersurfaceNonzeroRelativeDifferential
import Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
import WeilConjectures.AlgebraicGeometry.Modules.Differentials
import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-!
# First-order equations vanish on a Bertini singular fibre

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph of `lemma-bertini`.
(blueprint: lem-zl-bertini-singular-fibre-equations).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

noncomputable section

/-- The singular fibre is an affine quotient on which all first-order evaluation equations
vanish. The coefficient equation fixes the coordinates of the presentation.

Source: Stacks Project, Varieties, Tag 0FD6, final paragraph, with Algebra Tag 00T7 for the
one-way hypersurface criterion, including the zero parameter.
(blueprint: lem-zl-bertini-singular-fibre-equations).

Proof: Choose a generating section nonvanishing at z and restrict to its generating locus.
The fibre is unchanged by this restriction. Divide each section by the generator to obtain
regular functions f_j with f_i=1. The cotangent fibre over k has dimension d since U is smooth
of relative dimension d. Choose its basis. The immersion into the projective affine chart
is unramified and the conormal surjection makes the differentials df_j span this fibre,
because projective ratios pull back to f_j. Define E(e_j)=(f_j(z),df_j(z)). The distinguished
column is (1,0); subtracting f_j(z) times it produces (0,df_j(z)). Thus E is surjective.

The universal section in the pulled-back generator has equation F=sum x_j f_j, and its
relative differential over coefficient space is dF=sum x_j df_j. The ambient projection
is smooth by base change. Wherever dF is nonzero the hypersurface differential criterion
makes the universal zero-scheme projection smooth on an open neighbourhood. Thus every
coefficient of F and dF vanishes on the nonsmooth set and belongs to the vanishing ideal
of its reduced induced structure. These coefficients remain zero after passage to the
scheme-theoretic fibre over z. Every linear functional on the target of E is a linear
combination of its value and differential coordinate functionals, so the displayed hzero
holds for every such functional.

The universal zero scheme is closed in coefficient space times Y, and the reduced singular
scheme is closed in the universal zero scheme. Base changing their composite to kappa(z)
gives a closed immersion of the fibre into coefficient affine space over kappa(z). In
particular the fibre is affine; take its actual coordinate ring A. The closed immersion
gives a surjective coordinate quotient from kappa(z)[x_0,...,x_r] to A. Identifying this
polynomial algebra with the symmetric algebra of the dual of the coordinate vector space
yields H. Its generators are exactly the original coefficient functions, so the Spec map
followed by the fibre affine identification has the stated coefficient compatibility.
The construction includes an empty fibre, whose coordinate ring is the zero ring, and d=0;
no flatness of the universal zero scheme is needed. -/
theorem bertini_singular_fibre_equations
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
          ∃ (A : Type u) (_ : CommRing A) (_ : Algebra ((U : Scheme).residueField z) A),
            ∃ (e : (bertiniSingularToSource f L s ∣_ U).fiber z ≅ Spec (CommRingCat.of A))
              (H : SymmetricAlgebra ((U : Scheme).residueField z)
                (Module.Dual ((U : Scheme).residueField z)
                  (Fin (r + 1) → (U : Scheme).residueField z)) →ₐ[
                    (U : Scheme).residueField z] A),
              Function.Surjective H ∧
              (∀ φ : Module.Dual ((U : Scheme).residueField z)
                  ((U : Scheme).residueField z × (Fin d → (U : Scheme).residueField z)),
                H (SymmetricAlgebra.ι _ _ (E.dualMap φ)) = 0) ∧
              e.hom ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom
                ((algebraMap ((U : Scheme).residueField z) A).comp
                  ((U.ι ≫ f).residueFieldAlgebraMap z))
                (fun i : ULift.{u} (Fin (r + 1)) ↦
                  H (SymmetricAlgebra.ι _ _ (LinearMap.proj i.down))))) =
    (bertiniSingularToSource f L s ∣_ U).fiberι z ≫
                ((bertiniSingularToSource f L s) ⁻¹ᵁ U).ι ≫
                (bertiniSingularIdeal f L s).subschemeι ≫ bertiniUniversalProjection f L s := by
  sorry

end

end AlgebraicGeometry

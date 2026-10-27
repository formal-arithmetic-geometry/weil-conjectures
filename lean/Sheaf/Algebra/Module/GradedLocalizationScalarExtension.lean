/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Sheaf.Algebra.Module.LocalizedHomogeneousPiece
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Scalar extension of homogeneous localized module pieces

Source: Stacks Project, constructions.tex, Tag 01N2 (lemma-base-change-map-proj),
standard-open calculation, generalized to graded modules by the DAG's agent-supplied
fraction argument; algebra.tex, Tags 07JZ and 00DD.
(blueprint: lem-sfb-graded-module-localization-scalar-extension)
-/

@[expose] public section

universe u v w t

open TensorProduct

namespace LocalizedModule

/-- Coefficient extension commutes with every homogeneous localized module piece.
The action on `S ⊗[R] M` is the scalar extension of the action of `A` on `M`,
extended to `S ⊗[R] A`; on pure tensors it is `(s ⊗ a) • (t ⊗ x) = st ⊗ (a • x)`.
The submodules `H` and `K` have exactly the existing homogeneous-fraction sets as
carriers, so their operations are inherited from ordinary module localization.
The equality on fractions specifies the comparison, including its normalization.

Source: Stacks Project, constructions.tex, Tag 01N2 (lemma-base-change-map-proj),
proof on standard opens, with the agent-supplied arbitrary graded-module refinement
in the DAG; algebra.tex, Tags 07JZ (module fractions) and 00DD (tensor and colimits).
(blueprint: lem-sfb-graded-module-localization-scalar-extension)

Proof plan:
1. For fixed j use the sequence D_m = M_(md+j), with transitions multiplication by
   f^(n-m). Fractions x/f^m form a compatible cocone. Common denominators show
   closure under addition and coefficient scalars, producing H and K.
2. These cocones are colimits: for compatible linear maps v_m, set v(x/f^m)=v_m(x).
   If x/f^m=y/f^n, the module-localization relation gives k with
   f^(k+n)x=f^(k+m)y. Compatibility at stage k+m+n proves well-definedness.
   Common denominators give linearity and every fraction occurs in a cocone leg,
   giving uniqueness. The same proof works with R-linear or S-linear test cocones.
3. Tensoring with S preserves the first colimit (tensor-colimit dependency,
   Tag 00DD), after interchanging tensor factors. The grading projections split
   M_i into M, so tensoring preserves those inclusions without flatness.
   The resulting S ⊗ D_m identify with N_(md+j), compatibly with transitions.
   The two colimit properties give mutually inverse R-linear comparison maps.
4. Their leg formula is exactly the displayed fraction equation. That formula
   gives S-linearity on generating pure tensors, hence the S-linear equivalence.
   All equalities use multiplication by a power of f, never cancellation; the
   argument includes nilpotent f, arbitrary negative j and unbounded gradings. -/
theorem exists_gradedLocalization_scalarExtension_equiv
    {R : Type u} {S : Type v} {A : Type w} {M : Type t}
    [CommRing R] [CommRing S] [CommRing A] [AddCommGroup M]
    [Algebra R S] [Algebra R A] [Module R M] [Module A M] [IsScalarTower R A M]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
    (𝓜 : ℤ → Submodule R M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (i : ℤ) (a : A) (x : M),
      a ∈ 𝒜 n → x ∈ 𝓜 i → a • x ∈ 𝓜 ((n : ℤ) + i))
    {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) (j : ℤ) :
    let ρ : (S ⊗[R] A) →ₐ[S] Module.End S (S ⊗[R] M) :=
      AlgHom.liftEquiv R S A _
        ((Module.End.baseChangeHom R S M).comp (Algebra.lsmul R R M))
    letI : Module (S ⊗[R] A) (S ⊗[R] M) := Module.compHom _ ρ.toRingHom
    letI : IsScalarTower S (S ⊗[R] A) (S ⊗[R] M) :=
      IsScalarTower.of_algebraMap_smul
        (fun s x ↦ congrArg (fun g : Module.End S (S ⊗[R] M) ↦ g x) (ρ.commutes s))
    ∃ (H : Submodule R (LocalizedModule.Away f M))
      (K : Submodule S (LocalizedModule.Away (1 ⊗ₜ[R] f : S ⊗[R] A) (S ⊗[R] M))),
      (H : Set (LocalizedModule.Away f M)) =
        homogeneousPieceAway (fun i ↦ (𝓜 i).toAddSubgroup) f (d : ℤ) j ∧
      (K : Set (LocalizedModule.Away (1 ⊗ₜ[R] f : S ⊗[R] A) (S ⊗[R] M))) =
        homogeneousPieceAway (fun i ↦ ((𝓜 i).baseChange S).toAddSubgroup)
          (1 ⊗ₜ[R] f : S ⊗[R] A) (d : ℤ) j ∧
      ∃ e : (S ⊗[R] H) ≃ₗ[S] K,
        ∀ (s : S) (m : ℕ) (x : M), x ∈ 𝓜 (j + (m : ℤ) * (d : ℤ)) →
          ∀ z : H, (z : LocalizedModule.Away f M) =
            mk x (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          (e (s ⊗ₜ[R] z) :
            LocalizedModule.Away (1 ⊗ₜ[R] f : S ⊗[R] A) (S ⊗[R] M)) =
            mk (s ⊗ₜ[R] x)
              (⟨(1 ⊗ₜ[R] f : S ⊗[R] A) ^ m, ⟨m, rfl⟩⟩ :
                Submonoid.powers (1 ⊗ₜ[R] f : S ⊗[R] A)) := by
  sorry

end LocalizedModule

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Localization.Basic
import Sheaf.Algebra.FiniteProjectiveTorAcyclic
import Sheaf.Algebra.Homology.TermwiseTorAcyclicBaseComparison
import Sheaf.Algebra.Homology.FlatLocalizedBaseComparison
import Mathlib.RingTheory.Flat.Localization
/-!
# Tor-independent tensor comparison for a bounded projective complex

Source: Stacks Project, perfect.tex, Tag 08IB, lemma-compare-base-change
(blueprint: lem-pc-tor-independent-projective-complex-tensor).
-/

@[expose] public section

set_option autoImplicit false

universe uR₁ uA₁ uB₁ uD₁ v₁ w₁

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace ModuleCat

/-- (blueprint: lem-pc-tor-independent-projective-complex-tensor) Stacks Project,
Tag 08IB, local affine Tor-independent tensor comparison.

Proof: finite projective A-modules are summands of finite free modules. By
`lem-pc-finite-projective-tor-acyclic`, Tor-independence of A and B therefore
implies higher Tor vanishing for each term of Q. Apply
`lem-pc-termwise-tor-acyclic-base-comparison` to make the universal counit
invertible. The equation comparison_eq and reflection of isomorphisms by
restriction of scalars make the ordinary cohomology comparison invertible. Localization is flat by
`lem-weil-pbc-localization-flat`. By `lem-pc-flat-localized-base-comparison`,
using flat tensor exactness,
tensoring with D preserves the kernel/image sequences defining ordinary
cohomology.
Consequently cohomology commutes with this tensor. Tensor associativity identifies
(Q tensor_R B) tensor_E D with Q tensor_A D, compatibly with differentials.
The equations in `BaseDerivedTensorCohomologyModel` identify the displayed map
with precisely the composite of these isomorphisms, so it is an isomorphism. -/
theorem torIndependent_projectiveComplex_tensor
    {R : Type uR₁} {A : Type uA₁} {B : Type uB₁} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [HasDerivedCategory.{w₁} (ModuleCat.{max uR₁ uA₁ uB₁ uD₁ v₁} R)]
    [HasDerivedCategory.{w₁} (ModuleCat.{max uR₁ uA₁ uB₁ uD₁ v₁} B)]
    (hTor : ∀ i : ℕ, 0 < i →
      IsZero (((CategoryTheory.Tor'
        (ModuleCat.{max uR₁ uA₁ uB₁ uD₁ v₁} (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} R)) i).obj
          (ModuleCat.of (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} R)
            (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} A))).obj
          (ModuleCat.of (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} R)
            (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} B))))
    (Q : CochainComplex (ModuleCat.{max uR₁ uA₁ uB₁ uD₁ v₁} A) ℤ)
    (hbounded : ∃ m n : ℤ, ∀ i : ℤ, i < m ∨ n < i → IsZero (Q.X i))
    (hprojective : ∀ i : ℤ, Module.Finite A (Q.X i) ∧ Module.Projective A (Q.X i))
    (D : Type uD₁) [CommRing D] [Algebra (A ⊗[R] B) D]
    (hlocalization : ∃ S : Submonoid (A ⊗[R] B), IsLocalization S D) :
    ∀ i : ℤ, IsIso ((baseDerivedTensorCohomologyModel R A B Q D).localizedComparison i) := by
  let : Algebra (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} R)
      (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} A) :=
    ULift.algebra' R (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} A)
  let : Algebra (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} R)
      (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} B) :=
    ULift.algebra' R (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} B)
  let M := baseDerivedTensorCohomologyModel R A B Q D
  have hterms : ∀ (n : ℤ) (i : ℕ), 0 < i →
      IsZero (((CategoryTheory.Tor'
        (ModuleCat.{max uR₁ uA₁ uB₁ uD₁ v₁}
          (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} R)) i).obj
        (@ModuleCat.of (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} R) _
          (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} (Q.X n)) inferInstance
          (Module.compHom _ (algebraMap (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} R)
            (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} A))))).obj
        (ModuleCat.of (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} R)
          (ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} B))) := by
    intro n
    have := (hprojective n).1
    have := (hprojective n).2
    obtain ⟨m, r, s, _, _, hsplit⟩ :=
      Module.Finite.exists_comp_eq_id_of_projective A (Q.X n)
    let s' : ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} (Q.X n) →ₗ[
        ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} A]
        (Fin m → ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} A) :=
      { toFun := fun x k ↦ ULift.up (s x.down k)
        map_add' := by intros; ext k; exact congrFun (s.map_add _ _) k
        map_smul' := by intros; ext k; exact congrFun (s.map_smul _ _) k }
    let r' : (Fin m → ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} A) →ₗ[
        ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} A]
        ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} (Q.X n) :=
      { toFun := fun x ↦ ULift.up (r (fun k ↦ (x k).down))
        map_add' := by intros; exact congrArg ULift.up (r.map_add _ _)
        map_smul' := by intros; exact congrArg ULift.up (r.map_smul _ _) }
    have hs' : r'.comp s' = LinearMap.id := by
      ext x
      exact LinearMap.congr_fun hsplit x.down
    exact CategoryTheory.finiteProjective_tor_acyclic
      (R := ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} R)
      (A := ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} A)
      (B := ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} B)
      (P := ULift.{max uR₁ uA₁ uB₁ uD₁ v₁} (Q.X n))
      hTor m s' r' hs'
  have := M.counit_isIso_of_termwise_tor_acyclic hbounded hterms
  have hc : ∀ i : ℤ, IsIso (M.comparison i) := by
    intro i
    have h := M.comparison_eq i
    let F := restrictScalars.{max uR₁ uA₁ uB₁ uD₁ v₁}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom
    let C := ((extendScalars.{_, _, max uR₁ uA₁ uB₁ uD₁ v₁}
      (algebraMap A (A ⊗[R] B))).mapHomologicalComplex (.up ℤ)).obj Q
    have hi : IsIso (F.map (M.comparison i) ≫ ((C.sc i).mapHomologyIso F).inv) := by
      rw [h]
      infer_instance
    have := (isIso_comp_right_iff _ _).mp hi
    exact isIso_of_reflects_iso (M.comparison i)
      (restrictScalars.{max uR₁ uA₁ uB₁ uD₁ v₁}
        Algebra.TensorProduct.includeRight.toRingHom)
  obtain ⟨S, hS⟩ := hlocalization
  have := hS
  exact M.localizedComparison_isIso_of_flat (IsLocalization.flat D S) hc

end ModuleCat

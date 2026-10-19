/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.Finite

import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import Sheaf.RingTheory.HenselianLocalTargetEtaleMaps
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Morphisms of finite étale algebras over a henselian local ring

Source: Stacks Project, Algebra, Tag 04GK, the full-faithfulness argument.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CommAlgCat.FiniteEtale

/-- Reduction induces a bijection on morphisms between finite étale algebras.
Source: Stacks Project, Algebra, Tag 04GK, proof of full faithfulness.
(blueprint: lem-weil-pbc-henselian-finite-etale-map-bijective).

Proof: Decompose each finite étale algebra into local factors using henselian étale
retractions and the finite-product-local theorem (04GG). Their reductions are finite
separable fields: finiteness makes each maximal ideal lie over the maximal ideal of R,
and the étale prime-generation theorem (00U4) identifies that ideal with its extension.
A map from a finite product to a nonzero local ring selects exactly one factor, because
the standard orthogonal idempotents map to idempotents summing to one. Thus it suffices
to compare maps between two local factors S and T. Decompose S ⊗[R] T into local finite
étale factors Aᵢ. A map S → T gives a surjection S ⊗[R] T → T and hence selects a factor
Aᵢ. The projection Aᵢ → T retracts jᵢ : T → Aᵢ; its kernel is a finite direct summand.
Reduction makes the projection a surjection of fields, so the kernel has zero reduction
and vanishes by Nakayama. Conversely, an invertible jᵢ gives the map S → Aᵢ → T.
These constructions are inverse. Over the residue field, maps select exactly the indices
for which the reduced jᵢ is invertible. Such a jᵢ is invertible precisely when its
reduction is: Nakayama first gives surjectivity; the finite flat R-module Aᵢ is free,
so the surjection splits R-linearly, and Nakayama kills its finite kernel. Reduction
preserves the selected index, proving bijectivity for local factors and then products.
The zero algebra is the empty product; maps to it are unique, and maps from it to a
nonzero algebra do not exist, so these cases obey the same product formula. -/
theorem bijective_baseChange_residueField_map_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S T : CommAlgCat.FiniteEtale.{max u v} R) :
    Function.Bijective
      ((baseChange.{max u v} R (IsLocalRing.ResidueField R)).map :
        (S ⟶ T) →
          ((baseChange.{max u v} R (IsLocalRing.ResidueField R)).obj S ⟶
            (baseChange.{max u v} R (IsLocalRing.ResidueField R)).obj T)) := by
  classical
  obtain ⟨n, A, rings, algebras, henselian, localMaps, ⟨e⟩, hfin, _⟩ :=
    HenselianLocalRing.finite_over_henselian_exists_algEquiv_pi R T
  let := rings
  let := algebras
  let := henselian
  have (i : Fin n) : Module.Finite R (A i) := hfin i
  have hformal : Algebra.FormallyEtale R (∀ i, A i) :=
    Algebra.FormallyEtale.of_equiv e
  have (i : Fin n) : Algebra.FormallyEtale R (A i) :=
    (Algebra.FormallyEtale.pi_iff A).mp hformal i
  let k := IsLocalRing.ResidueField R
  let e₀ : (TensorProduct R k T) ≃ₐ[k] (∀ i, TensorProduct R k (A i)) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : k ≃ₐ[k] k) e).trans
      (Algebra.TensorProduct.piRight R k k A)
  have hcomponent (f : S →ₐ[R] T) (x : TensorProduct R k S) (i : Fin n) :
      e₀ (Algebra.TensorProduct.map (AlgHom.id k k) f x) i =
        Algebra.TensorProduct.map (AlgHom.id k k)
          ((Pi.evalAlgHom R A i).comp (e.toAlgHom.comp f)) x := by
    induction x with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp_all only [map_add, Pi.add_apply]
  have hlocal (i : Fin n) :=
    Algebra.bijective_residueField_tensor_map_of_henselian_target R S (A i)
  constructor
  · intro f g hfg
    have hi (i : Fin n) :
        (Pi.evalAlgHom R A i).comp (e.toAlgHom.comp f.hom.hom) =
          (Pi.evalAlgHom R A i).comp (e.toAlgHom.comp g.hom.hom) := by
      apply (hlocal i).1
      apply AlgHom.ext
      intro x
      have hh := congrArg (fun h ↦ (e₀ (h.hom.hom x)) i) hfg
      change e₀ (Algebra.TensorProduct.map (AlgHom.id k k) f.hom.hom x) i =
        e₀ (Algebra.TensorProduct.map (AlgHom.id k k) g.hom.hom x) i at hh
      simpa only [hcomponent] using hh
    apply InducedCategory.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    apply e.injective
    exact funext fun i ↦ DFunLike.congr_fun (hi i) x
  · intro f₀
    let fi (i : Fin n) : (TensorProduct R k S) →ₐ[k] (TensorProduct R k (A i)) :=
      (Pi.evalAlgHom k (fun i ↦ TensorProduct R k (A i)) i).comp (e₀.toAlgHom.comp f₀.hom.hom)
    choose f hf using fun i ↦ (hlocal i).2 (fi i)
    let g : S →ₐ[R] T := e.symm.toAlgHom.comp (AlgHom.pi f)
    refine ⟨⟨CommAlgCat.ofHom g⟩, ?_⟩
    apply InducedCategory.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    apply e₀.injective
    funext i
    have hh := DFunLike.congr_fun (hf i) x
    change e₀ (Algebra.TensorProduct.map (AlgHom.id k k) g x) i = _
    rw [hcomponent]
    have hg : (Pi.evalAlgHom R A i).comp (e.toAlgHom.comp g) = f i := by
      ext s
      simp [g]
    rw [hg]
    exact hh

end CommAlgCat.FiniteEtale

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Etale.Weakly

/-!
# Weakly étale morphisms of affine schemes

For a weakly étale `R`-algebra `S`, the morphism `Spec S ⟶ Spec R` is weakly étale: it is flat,
and its diagonal is the spectrum of the multiplication `S ⊗[R] S → S`.
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

namespace AlgebraicGeometry

/-- For a weakly étale `R`-algebra `S`, the morphism `Spec S ⟶ Spec R` is weakly étale. -/
instance weaklyEtale_SpecMap_algebraMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.WeaklyEtale R S] :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have hflat : RingHom.Flat (algebraMap R S) := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 hflat
  have : Flat (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.lmul' R : S ⊗[R] S →ₐ[R] S).toRingHom)) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (Algebra.WeaklyEtale.flat_lmul' R S)
  refine ⟨inferInstance, ?_⟩
  rw [diagonal_SpecMap]
  infer_instance

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.FieldTheory.GaloisUnitsCohomology
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

import WeilConjectures.AlgebraicGeometry.EtaleUnitsStalkEvaluationSurjective
import WeilConjectures.AlgebraicGeometry.EtaleUnitsStalkEvaluationInjective

/-!
# Bijectivity of evaluation on the geometric stalk of units

## References

* Stacks Project, Tags 03QU and 03QV
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

/-- A stalk homomorphism satisfying the evaluation formula is bijective
(Stacks, Tags 03QU and 03QV). -/
theorem etale_units_stalk_evaluation_bijective (K : Type u) [Field K] :
    let Ω := AlgebraicClosure K
    let S := Spec (.of K)
    let p := pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    ∀ f : (p.sheafFiber (A := AddCommGrpCat.{u + 1})).obj S.gmSheaf →+
        Field.galoisUnitsTopRep K,
      (∀ (X : S.Etale) (x : p.fiber.obj X) (z : S.gmSheaf.obj.obj (op X)),
        algebraMap (SeparableClosure K) Ω
            (Additive.toMul (f (p.toPresheafFiber X x S.gmSheaf.obj z)) :
              (SeparableClosure K)ˣ) =
          (ΓSpecIso (.of Ω)).hom
            (x.left.appTop ((Additive.toMul z.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤)))) →
      Function.Bijective f := by
  dsimp
  intro f hf
  exact ⟨etale_units_stalk_evaluation_injective K f hf,
    etale_units_stalk_evaluation_surjective K f hf⟩

end AlgebraicGeometry.Scheme

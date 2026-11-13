/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension

/-!
# Affine weakly contractible covering families on the small pro-etale site

## References

* Stacks Project, Tags 0990, 098I, 090L and 090K.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Every object of the small pro-etale site has a covering family of affine objects
weakly contractible for sheaves on the full small site of `X`
(Stacks, Tags 0990, 098I, 090L and 090K). -/
theorem exists_affine_weaklyContractible_covering_family
    (X : Scheme.{u}) (U : X.ProEt) :
    ∃ (I : Type (u + 1)) (V : I → X.ProEt) (f : ∀ i : I, V i ⟶ U),
      Presieve.ofArrows V f ∈ precoverage X U ∧
      (∀ i : I, IsAffine (V i).left) ∧
      (∀ (i : I) (F G : Sheaf (topology X) (Type (u + 1))) (e : F ⟶ G),
        Epi e → Function.Surjective (e.hom.app (op (V i)))) := by
  classical
  let A := U.left.affineOpenCover
  choose D hD φ hcover hcontract using
    fun j : A.I₀ ↦ exists_affine_contractible_extension (A.X j)
  let (j : A.I₀) : CommRing (D j) := hD j
  let p (j : A.I₀) := Spec.map (CommRingCat.ofHom (φ j))
  let C := A.openCover.weaken
    (zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale))
  let E (j : A.I₀) : Scheme.Cover.{0} proetalePrecoverage (Spec (A.X j)) :=
    .singleton (p j) (hcover j)
  let B := (C.bind E).reindex (Equiv.ulift : ULift.{u + 1} _ ≃ _)
  have hB (i : B.I₀) : WeaklyEtale (B.f i) := Scheme.Cover.map_prop (Scheme.Cover.forgetQc B) i
  let V (i : B.I₀) : X.ProEt := ProEt.mk (B.f i ≫ U.hom)
  let f (i : B.I₀) : V i ⟶ U := MorphismProperty.Over.homMk (B.f i)
  refine ⟨B.I₀, V, f, ?_, ?_, ?_⟩
  · change (Presieve.ofArrows V f).map (ProEt.forget X ⋙ Over.forget X) ∈
      proetalePrecoverage U.left
    rw [Presieve.map_ofArrows]
    change B.presieve₀ ∈ proetalePrecoverage U.left
    exact B.mem₀
  · intro i
    change IsAffine (Spec (CommRingCat.of (D i.down.1)))
    infer_instance
  · intro i F G e he
    exact hcontract i.down.1 X (B.f i ≫ U.hom) F G e he

end AlgebraicGeometry.Scheme.ProEt

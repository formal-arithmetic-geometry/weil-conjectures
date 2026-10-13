/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Category.Ring.Colimits

/-! # Descending a module comparison along compatible coefficient maps

Source: Stacks Project, Algebra, Tag 05N7 (2), (3), used in Tag 02JO (3).
(blueprint: lem-pc-compatible-module-model-descent)
-/

@[expose] public section

universe v w x
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- An equivalence between two finitely presented module base changes descends
along a compatible family of coefficient maps. No algebra model or flatness
hypothesis is needed.

Source: Stacks Project, Algebra, Tag 05N7 (2), (3); Tag 02JO (3), final paragraph.
(blueprint: lem-pc-compatible-module-model-descent)

Proof:
1. On the cofinal tail above k, the algebras B_j = F(j) tensor B have colimit
   c.pt tensor B. The compatibility assumptions make them Q-algebras and make
   their coprojections Q-linear. This colimit assertion follows by tensor
   representatives and eventual equality. If the index is only a preorder,
   take its poset reflection: mutually comparable indices give inverse ring
   maps, so both the diagram and its colimit descend up to canonical isomorphism.
2. At k the modules B_k tensor_Q L and B_k tensor_B M are finitely presented
   over B_k, by finite presentation under base change. Their base changes to
   the colimit are the two modules in eM, by tensor cancellation.
3. Apply Tag 05N7 (2) to eM and its inverse, take a common later stage, and apply
   part (3) to their two composites and the identity maps. At a common upper
   bound the descended maps are inverse, hence define a linear equivalence.
4. Base change this equivalence to every later stage. Compatibility of q
   and tensor cancellation identify those modules with the displayed ones.
   Transport from the poset reflection to original indices if necessary.
   Empty presentations and zero modules need no separate argument, and no
   flatness is used to descend maps, equalities, or inverse identities.
-/
theorem exists_eventually_compatible_module_equiv
    {I : Type v} [Preorder I] [IsDirectedOrder I]
    (F : I ⥤ CommRingCat.{v}) (c : Cocone F) (hc : IsColimit c)
    {i : I} {B M : Type w} [CommRing B] [AddCommMonoid M]
    [Algebra (F.obj i : Type v) B] [Module B M] [Module.FinitePresentation B M]
    (Q L : Type x) [CommRing Q] [AddCommMonoid L] [Module Q L]
    [Module.FinitePresentation Q L]
    (qC : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      Q →+* (c.pt : Type v) ⊗[F.obj i] B)
    (eM : letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      letI : Algebra Q ((c.pt : Type v) ⊗[F.obj i] B) := qC.toAlgebra
      letI : Algebra B ((c.pt : Type v) ⊗[F.obj i] B) :=
        Algebra.TensorProduct.rightAlgebra
      Nonempty (((c.pt : Type v) ⊗[F.obj i] B) ⊗[Q] L ≃ₗ[
        (c.pt : Type v) ⊗[F.obj i] B] ((c.pt : Type v) ⊗[F.obj i] B) ⊗[B] M))
    (k : I) (hik : i ≤ k)
    (q : ∀ (j : I) (hkj : k ≤ j),
      letI := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
      Q →+* (F.obj j : Type v) ⊗[F.obj i] B)
    (hqC : ∀ (j : I) (hkj : k ≤ j),
      letI := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
      letI : Algebra (F.obj i : Type v) (c.pt : Type v) := (c.ι.app i).hom.toAlgebra
      let t : F.obj j →ₐ[F.obj i] c.pt :=
        { (c.ι.app j).hom with
          commutes' := fun s ↦ ConcreteCategory.congr_hom
            (c.w (homOfLE (hik.trans hkj))) s }
      (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) B)).toRingHom.comp
        (q j hkj) = qC)
    (hq : ∀ (j l : I) (hkj : k ≤ j) (hkl : k ≤ l) (hjl : j ≤ l),
      letI := (F.map (homOfLE (hik.trans hkj))).hom.toAlgebra
      letI := (F.map (homOfLE (hik.trans hkl))).hom.toAlgebra
      let t : F.obj j →ₐ[F.obj i] F.obj l :=
        { (F.map (homOfLE hjl)).hom with
          commutes' := fun s ↦ (ConcreteCategory.congr_hom
            (F.map_comp (homOfLE (hik.trans hkj)) (homOfLE hjl)) s).symm }
      (Algebra.TensorProduct.map t (AlgHom.id (F.obj i) B)).toRingHom.comp
        (q j hkj) = q l hkl) :
    ∃ (j₀ : I) (hkj₀ : k ≤ j₀), ∀ (j : I) (h₀ : k ≤ j₀) (h₁ : j₀ ≤ j),
      letI := (F.map (homOfLE (hik.trans (h₀.trans h₁)))).hom.toAlgebra
      let E := (F.obj j : Type v) ⊗[F.obj i] B
      letI : Algebra Q E := (q j (h₀.trans h₁)).toAlgebra
      letI : Algebra B E := Algebra.TensorProduct.rightAlgebra
      Nonempty (E ⊗[Q] L ≃ₗ[E] E ⊗[B] M) := by sorry

end AlgebraicGeometry

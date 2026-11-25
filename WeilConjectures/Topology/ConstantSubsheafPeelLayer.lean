/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
import WeilConjectures.Topology.AbelianOpenExtensionByZeroStalks
import WeilConjectures.Topology.AbelianSheafShortExactStalkwise
import WeilConjectures.Topology.ConstantSubsheafLowerLayerGenerator
import WeilConjectures.Topology.AbelianIntegerOpenInclusion
/-! # One layer of the integer subsheaf filtration

## References

* Stacks Project, Tag 0A38.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

private theorem hom_eq_zero_of_stalk_map_eq_zero {X : TopCat.{u}}
    {F G : Sheaf AddCommGrpCat X} (f : F ⟶ G)
    (h : ∀ x : X, (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f.hom = 0) :
    f = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply TopCat.Presheaf.section_ext G W.unop
  intro x hx
  change TopCat.Presheaf.germ G.obj W.unop x hx (f.hom.app (op W.unop) s) =
    TopCat.Presheaf.germ G.obj W.unop x hx 0
  have hh := congrArg (fun k ↦ k (TopCat.Presheaf.germ F.obj W.unop x hx s)) (h x)
  simpa only [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    AddCommGrpCat.zero_apply, map_zero] using hh

/-- Remove the layer with positive stalk generator `b + 1`, retaining finite generation.
The bound is independent of signs in the chosen integer stalk identifications.
This constructs just one subobject and one quotient, not a finite filtration. -/
theorem constantSubsheaf_peel_layer
    (X : TopCat.{u})
    (hqc : ∀ U V : Opens X, IsCompact (U : Set X) → IsCompact (V : Set X) →
      IsCompact ((U ⊓ V : Opens X) : Set X))
    (K C : Sheaf AddCommGrpCat X)
    (ι : K ⟶ C)
    [Mono ι]
    (hC : Nonempty (C ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))))
    (hgen : ∃ (n : ℕ) (U : Fin n → Opens X)
      (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
      ∃ g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ K, Epi g)
    (e : ∀ x : X, TopCat.Presheaf.stalk C.obj x ≅ AddCommGrpCat.of (ULift.{u} ℤ))
    (b : ℕ)
    (hb : ∀ x : X, ∃ a : ℕ, a ≤ b + 1 ∧
      Set.range (fun t : ToType (TopCat.Presheaf.stalk K.obj x) ↦
        (e x).hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map ι.hom t)) =
      Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z)) :
    ∃ (L : Sheaf AddCommGrpCat X) (l : L ⟶ K), Mono l ∧
      (∃ (n : ℕ) (U : Fin n → Opens X)
      (_ : ∀ i, IsCompact ((U i : Opens X) : Set X)),
      ∃ g : (∐ fun i => (abelianOpenExtensionByZero (U i)).obj
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (U i)))
          AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ⟶ L, Epi g) ∧
      (∀ x : X, ∃ a : ℕ, a ≤ b ∧
      Set.range (fun t : ToType (TopCat.Presheaf.stalk L.obj x) ↦
        (e x).hom ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (l ≫ ι).hom t)) =
      Set.range (fun z : ULift.{u} ℤ ↦ (a : ℤ) • z)) ∧
      ∃ S : ShortComplex (Sheaf AddCommGrpCat X), S.ShortExact ∧
        ∃ (U V : Opens X),
        IsCompact (U : Set X) ∧ IsCompact (V : Set X) ∧ V ≤ U ∧
        Nonempty (S.X₁ ≅ (abelianOpenExtensionByZero V).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ∧
        Nonempty (S.X₂ ≅ (abelianOpenExtensionByZero U).obj
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ)))) ∧
        Nonempty (S.X₃ ≅ cokernel l) := by
  classical
  obtain ⟨L, l, hl, hLgen, hLb, U, V, hU, hV, hVU, q, hQzero, hq⟩ :=
    constantSubsheaf_lower_layer_generator X hqc K C ι hC hgen e b hb
  obtain ⟨f, hf⟩ := abelianIntegerOpen_exists_inclusion X U V hVU
  obtain ⟨_, _, _, hOutsideV, _⟩ := abelianOpenExtensionByZero_stalks X V
  obtain ⟨_, _, _, hOutsideU, _⟩ := abelianOpenExtensionByZero_stalks X U
  have hcomp : f ≫ q = 0 := by
    apply hom_eq_zero_of_stalk_map_eq_zero
    intro x
    by_cases hx : x ∈ V
    · exact (hQzero x (Or.inl hx)).eq_of_tgt _ _
    · exact (hOutsideV _ x hx).eq_of_src _ _
  let S := ShortComplex.mk f q hcomp
  have hS : S.ShortExact := by
    apply (TopCat.shortExact_iff_stalkFunctor_map_shortExact S).2
    intro x
    let T := S.map (Sheaf.forget AddCommGrpCat X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
    change T.ShortExact
    by_cases hxV : x ∈ V
    · have hfiso : IsIso T.f := hf x hxV
      let := hfiso
      have hzero : IsZero T.X₃ := hQzero x (Or.inl hxV)
      have hgzero : T.g = 0 := hzero.eq_of_tgt _ _
      exact ShortComplex.ShortExact.mk' ((T.exact_iff_epi hgzero).2 inferInstance)
        inferInstance (epi_of_target_iso_zero _ hzero.isoZero)
    · have hzero : IsZero T.X₁ := hOutsideV _ x hxV
      by_cases hxU : x ∈ U
      · have hgiso : IsIso T.g := hq x hxU hxV
        let := hgiso
        have hfzero : T.f = 0 := hzero.eq_of_src _ _
        exact ShortComplex.ShortExact.mk' ((T.exact_iff_mono hfzero).2 inferInstance)
          (mono_of_source_iso_zero _ hzero.isoZero) inferInstance
      · have hzero₂ : IsZero T.X₂ := hOutsideU _ x hxU
        have hzero₃ : IsZero T.X₃ := hQzero x (Or.inr hxU)
        exact ShortComplex.ShortExact.mk' (T.exact_of_isZero_X₂ hzero₂)
          (mono_of_source_iso_zero _ hzero.isoZero)
          (epi_of_target_iso_zero _ hzero₃.isoZero)
  exact ⟨L, l, hl, hLgen, hLb, S, hS, U, V, hU, hV, hVU,
    ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩

end TopCat.Sheaf

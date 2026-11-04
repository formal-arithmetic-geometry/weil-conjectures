/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryPresentation

/-! # Compositor coherence of representatively normalized derived comparisons

Let `r_T : D(C_T) ⥤ D(S_T)` be functors on derived categories (for `T = X, Y, Z`) equipped with
comparisons `ε_T P : r_T (Q P) ⟶ Q (ρ_T P)` to additive functors `ρ_T : C_T ⥤ S_T`, and let
`Φ_f`, `Ψ_f` be functors on derived categories presented by additive functors `F_f`, `H_f`.
Suppose that comparisons `ν_f : Φ_f ⋙ r ≅ r ⋙ Ψ_f` are normalized by ordinary comparisons
`o_f : F_f ⋙ ρ ≅ ρ ⋙ H_f` on all complexes. If the ordinary comparisons are compatible with
ordinary compositors, if the derived compositors represent the ordinary ones, and if every
object of `D(C_Y)` is isomorphic to `Q P` with `ε_Y P` invertible, then the comparisons `ν`
are compatible with the derived compositors.

Source: Stacks Project, Tag 05RU (universal property of localization); this is the formal part
of the blueprint argument `lem-sp-complete-projection-reduction-square`, proof step 1.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Two natural transformations agreeing at an object agree at every isomorphic object. -/
lemma NatTrans.app_eq_app_of_iso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (α β : F ⟶ G) {X Y : C} (e : X ≅ Y) (h : α.app X = β.app X) : α.app Y = β.app Y := by
  rw [← cancel_epi (F.map e.hom), α.naturality, β.naturality, h]

namespace Functor

open DerivedPresentation

variable {CX CY CZ SX SY SZ : Type*} [Category CX] [Category CY] [Category CZ]
  [Category SX] [Category SY] [Category SZ]
  [Abelian CX] [Abelian CY] [Abelian CZ] [Abelian SX] [Abelian SY] [Abelian SZ]
  [HasDerivedCategory CX] [HasDerivedCategory CY] [HasDerivedCategory CZ]
  [HasDerivedCategory SX] [HasDerivedCategory SY] [HasDerivedCategory SZ]

/-- Compositor coherence of normalized comparisons: see the module docstring. -/
theorem derivedComparison_comp_coherence
    {Φg : DerivedCategory CY ⥤ DerivedCategory CZ} {Φi : DerivedCategory CZ ⥤ DerivedCategory CX}
    {Φig : DerivedCategory CY ⥤ DerivedCategory CX}
    {Fg : CY ⥤ CZ} {Fi : CZ ⥤ CX} {Fig : CY ⥤ CX} [Fg.Additive] [Fi.Additive] [Fig.Additive]
    (pg : DerivedPresentation Φg Fg) (pi : DerivedPresentation Φi Fi)
    (pig : DerivedPresentation Φig Fig)
    {Ψg : DerivedCategory SY ⥤ DerivedCategory SZ} {Ψi : DerivedCategory SZ ⥤ DerivedCategory SX}
    {Ψig : DerivedCategory SY ⥤ DerivedCategory SX}
    {Hg : SY ⥤ SZ} {Hi : SZ ⥤ SX} {Hig : SY ⥤ SX} [Hg.Additive] [Hi.Additive] [Hig.Additive]
    (qg : DerivedPresentation Ψg Hg) (qi : DerivedPresentation Ψi Hi)
    (qig : DerivedPresentation Ψig Hig)
    (rX : DerivedCategory CX ⥤ DerivedCategory SX) (rY : DerivedCategory CY ⥤ DerivedCategory SY)
    (rZ : DerivedCategory CZ ⥤ DerivedCategory SZ)
    (ρX : CX ⥤ SX) (ρY : CY ⥤ SY) (ρZ : CZ ⥤ SZ) [ρX.Additive] [ρY.Additive] [ρZ.Additive]
    (εX : ∀ P : CochainComplex CX ℤ, rX.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((ρX.mapHomologicalComplex (.up ℤ)).obj P))
    (εY : ∀ P : CochainComplex CY ℤ, rY.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((ρY.mapHomologicalComplex (.up ℤ)).obj P))
    (εZ : ∀ P : CochainComplex CZ ℤ, rZ.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((ρZ.mapHomologicalComplex (.up ℤ)).obj P))
    (hεX : ∀ {P P' : CochainComplex CX ℤ} (h : P ⟶ P'),
      rX.map (DerivedCategory.Q.map h) ≫ εX P' =
        εX P ≫ DerivedCategory.Q.map ((ρX.mapHomologicalComplex (.up ℤ)).map h))
    (nug : Φg ⋙ rZ ≅ rY ⋙ Ψg) (nui : Φi ⋙ rX ≅ rZ ⋙ Ψi) (nuig : Φig ⋙ rX ≅ rY ⋙ Ψig)
    (og : Fg ⋙ ρZ ≅ ρY ⋙ Hg) (oi : Fi ⋙ ρX ≅ ρZ ⋙ Hi) (oig : Fig ⋙ ρX ≅ ρY ⋙ Hig)
    (hg : ∀ P : CochainComplex CY ℤ,
      rZ.map (pg.hom.app P) ≫ εZ ((Fg.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex og (.up ℤ)).hom.app P) =
      nug.hom.app (DerivedCategory.Q.obj P) ≫ Ψg.map (εY P) ≫
        qg.hom.app ((ρY.mapHomologicalComplex (.up ℤ)).obj P))
    (hi : ∀ P : CochainComplex CZ ℤ,
      rX.map (pi.hom.app P) ≫ εX ((Fi.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex oi (.up ℤ)).hom.app P) =
      nui.hom.app (DerivedCategory.Q.obj P) ≫ Ψi.map (εZ P) ≫
        qi.hom.app ((ρZ.mapHomologicalComplex (.up ℤ)).obj P))
    (hig : ∀ P : CochainComplex CY ℤ,
      rX.map (pig.hom.app P) ≫ εX ((Fig.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex oig (.up ℤ)).hom.app P) =
      nuig.hom.app (DerivedCategory.Q.obj P) ≫ Ψig.map (εY P) ≫
        qig.hom.app ((ρY.mapHomologicalComplex (.up ℤ)).obj P))
    (c : Φig ≅ Φg ⋙ Φi) (c₀ : Fig ≅ Fg ⋙ Fi)
    (hc : DerivedRepresents pig (pg.comp pi) c.hom c₀.hom)
    (d : Ψig ≅ Ψg ⋙ Ψi) (d₀ : Hig ≅ Hg ⋙ Hi)
    (hd : DerivedRepresents qig (qg.comp qi) d.hom d₀.hom)
    (ho : ∀ M : CY, ρX.map (c₀.inv.app M) ≫ oig.hom.app M =
      oi.hom.app (Fg.obj M) ≫ Hi.map (og.hom.app M) ≫ d₀.inv.app (ρY.obj M))
    (hres : ∀ K : DerivedCategory CY, ∃ P : CochainComplex CY ℤ,
      Nonempty (DerivedCategory.Q.obj P ≅ K) ∧ IsIso (εY P))
    (K : DerivedCategory CY) :
    rX.map (c.inv.app K) ≫ nuig.hom.app K =
      nui.hom.app (Φg.obj K) ≫ Ψi.map (nug.hom.app K) ≫ d.inv.app (rY.obj K) := by
  obtain ⟨P, ⟨e⟩, hP⟩ := hres K
  let α : (Φg ⋙ Φi) ⋙ rX ⟶ rY ⋙ Ψig := Functor.whiskerRight c.inv rX ≫ nuig.hom
  let β : (Φg ⋙ Φi) ⋙ rX ⟶ rY ⋙ Ψig :=
    Functor.whiskerLeft Φg nui.hom ≫ Functor.whiskerRight nug.hom Ψi ≫
      Functor.whiskerLeft rY d.inv
  refine NatTrans.app_eq_app_of_iso α β e ?_
  dsimp only [α, β, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have := hP
  rw [← cancel_mono (Ψig.map (εY P) ≫ qig.hom.app ((ρY.mapHomologicalComplex (.up ℤ)).obj P))]
  have hcP := hc.inv (τ := c) (τ₀ := c₀) P
  have hdP := hd.inv (τ := d) (τ₀ := d₀) ((ρY.mapHomologicalComplex (.up ℤ)).obj P)
  rw [DerivedPresentation.comp_hom_app] at hcP hdP
  have hdn := d.inv.naturality (εY P)
  dsimp only [Functor.comp_map] at hdn
  have hqi : Ψi.map (DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex og (.up ℤ)).hom.app P)) ≫
      qi.hom.app ((Hg.mapHomologicalComplex (.up ℤ)).obj
        ((ρY.mapHomologicalComplex (.up ℤ)).obj P)) =
      qi.hom.app ((ρZ.mapHomologicalComplex (.up ℤ)).obj
        ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map ((Hi.mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex og (.up ℤ)).hom.app P)) :=
    qi.hom.naturality ((NatIso.mapHomologicalComplex og (.up ℤ)).hom.app P)
  have hnui := nui.hom.naturality (pg.hom.app P)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnui
  have hεP := hεX ((NatTrans.mapHomologicalComplex c₀.inv (.up ℤ)).app P)
  have hoP : DerivedCategory.Q.map ((ρX.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex c₀.inv (.up ℤ)).app P)) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex oig (.up ℤ)).hom.app P) =
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex oi (.up ℤ)).hom.app
        ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      DerivedCategory.Q.map ((Hi.mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex og (.up ℤ)).hom.app P)) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex d₀.inv (.up ℤ)).app
        ((ρY.mapHomologicalComplex (.up ℤ)).obj P)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext n
    exact ho (P.X n)
  simp only [Category.assoc]
  calc rX.map (c.inv.app (DerivedCategory.Q.obj P)) ≫
        nuig.hom.app (DerivedCategory.Q.obj P) ≫ Ψig.map (εY P) ≫
          qig.hom.app ((ρY.mapHomologicalComplex (.up ℤ)).obj P)
      = rX.map (c.inv.app (DerivedCategory.Q.obj P) ≫ pig.hom.app P) ≫
          εX ((Fig.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex oig (.up ℤ)).hom.app P) := by
        rw [← hig, Functor.map_comp, Category.assoc]
    _ = rX.map (Φi.map (pg.hom.app P)) ≫
          rX.map (pi.hom.app ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) ≫
          εX (((Fg ⋙ Fi).mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((ρX.mapHomologicalComplex (.up ℤ)).map
            ((NatTrans.mapHomologicalComplex c₀.inv (.up ℤ)).app P)) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex oig (.up ℤ)).hom.app P) := by
        rw [hcP, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
          reassoc_of% hεP]
    _ = rX.map (Φi.map (pg.hom.app P)) ≫
          rX.map (pi.hom.app ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) ≫
          εX ((Fi.mapHomologicalComplex (.up ℤ)).obj ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex oi (.up ℤ)).hom.app
            ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) ≫
          DerivedCategory.Q.map ((Hi.mapHomologicalComplex (.up ℤ)).map
            ((NatIso.mapHomologicalComplex og (.up ℤ)).hom.app P)) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex d₀.inv (.up ℤ)).app
            ((ρY.mapHomologicalComplex (.up ℤ)).obj P)) := by
        rw [hoP]
        rfl
    _ = nui.hom.app (Φg.obj (DerivedCategory.Q.obj P)) ≫ Ψi.map (nug.hom.app
          (DerivedCategory.Q.obj P)) ≫ d.inv.app (rY.obj (DerivedCategory.Q.obj P)) ≫
          Ψig.map (εY P) ≫ qig.hom.app ((ρY.mapHomologicalComplex (.up ℤ)).obj P) := by
        have hg' := congrArg Ψi.map (hg P)
        simp only [Functor.map_comp] at hg'
        rw [← reassoc_of% hdn, hdP]
        simp only [Category.assoc]
        rw [← reassoc_of% hg', reassoc_of% hqi, ← reassoc_of% hnui, ← reassoc_of% (hi _)]

/-- Naturality of a comparison `r (Q P) ⟶ Q (ρ P)` assembled from an exact functor `F`, the
counit of a functor `red` on derived categories and an exact functor `T`. -/
lemma mapDerivedCategoryFactors_counit_naturality
    {A B C S : Type*} [Category A] [Category B] [Category C] [Category S]
    [Abelian A] [Abelian B] [Abelian C] [Abelian S]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory S]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (red : DerivedCategory B ⥤ DerivedCategory C) (ord : B ⥤ C) [ord.Additive]
    (counit : DerivedCategory.Q ⋙ red ⟶ ord.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (T : C ⥤ S) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    {P P' : CochainComplex A ℤ} (h : P ⟶ P') :
    T.mapDerivedCategory.map (red.map (F.mapDerivedCategory.map (DerivedCategory.Q.map h))) ≫
      T.mapDerivedCategory.map (red.map (F.mapDerivedCategoryFactors.hom.app P')) ≫
      T.mapDerivedCategory.map (counit.app ((F.mapHomologicalComplex (.up ℤ)).obj P')) ≫
      T.mapDerivedCategoryFactors.hom.app
        ((ord.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P')) =
    (T.mapDerivedCategory.map (red.map (F.mapDerivedCategoryFactors.hom.app P)) ≫
      T.mapDerivedCategory.map (counit.app ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      T.mapDerivedCategoryFactors.hom.app
        ((ord.mapHomologicalComplex (.up ℤ)).obj ((F.mapHomologicalComplex (.up ℤ)).obj P))) ≫
      DerivedCategory.Q.map ((T.mapHomologicalComplex (.up ℤ)).map
        ((ord.mapHomologicalComplex (.up ℤ)).map ((F.mapHomologicalComplex (.up ℤ)).map h))) := by
  have h1 := F.mapDerivedCategoryFactors.hom.naturality h
  have h2 := counit.naturality ((F.mapHomologicalComplex (.up ℤ)).map h)
  have h3 := T.mapDerivedCategoryFactors.hom.naturality
    ((ord.mapHomologicalComplex (.up ℤ)).map ((F.mapHomologicalComplex (.up ℤ)).map h))
  dsimp only [Functor.comp_map, Functor.comp_obj] at h1 h2 h3
  rw [← T.mapDerivedCategory.map_comp_assoc, ← red.map_comp, h1, red.map_comp,
    T.mapDerivedCategory.map_comp, Category.assoc,
    ← T.mapDerivedCategory.map_comp_assoc (red.map (DerivedCategory.Q.map _)), h2,
    T.mapDerivedCategory.map_comp, Category.assoc, h3]
  simp only [Category.assoc]

end Functor

end CategoryTheory

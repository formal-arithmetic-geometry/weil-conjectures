/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.NoetherianSpace
public import WeilConjectures.Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.Topology.Sheaves.FilteredColimit
public import WeilConjectures.Topology.Sheaves.Godement

/-!
# Cohomology of filtered colimits of abelian sheaves on a noetherian space

Let `X` be a noetherian topological space and let `D : J ⥤ Sh(X)` be a filtered diagram of abelian
sheaves on `X`. Every open of `X` is quasi-compact, so the sections of the colimit of `D` over any
open are the filtered colimit of the sections of the `D j`. Consequently a filtered colimit of
flasque sheaves is flasque, and every cohomology class of the colimit of `D` comes from a
cohomology class of some `D j`. The latter is proved by induction on the degree, embedding `D`
into the diagram of its Godement sheaves, whose colimit is flasque.

This is the surjectivity half of [Stacks, Cohomology, Lemma 20.19.1][stacks-project] (tag `02UY`),
which is all that is needed for vanishing theorems.

## Main statements

- `TopCat.Sheaf.isFlasque_of_isColimit`: a filtered colimit of flasque sheaves on a noetherian
  space is flasque.
- `TopCat.Sheaf.exists_H_map_colimit_ι_eq`: every class in `H^q(X, colim D)` comes from
  `H^q(X, D j)` for some `j`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X : TopCat.{u}} [NoetherianSpace X]

instance (priority := low) : QuasiSeparatedSpace X where
  inter_isCompact _ _ _ _ _ _ := NoetherianSpace.isCompact _

variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- **A filtered colimit of flasque sheaves on a noetherian space is flasque.** -/
theorem isFlasque_of_isColimit
    {D : J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    {c : Cocone D} (hc : IsColimit c) (hD : ∀ j, Presheaf.IsFlasque (D.obj j).obj) :
    Presheaf.IsFlasque c.pt.obj where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    obtain ⟨j, t, rfl⟩ := exists_app_eq_of_isColimit hc (NoetherianSpace.isCompact _) s
    have := (hD j).epi i
    obtain ⟨t', rfl⟩ := (AddCommGrpCat.epi_iff_surjective _).1 this t
    exact ⟨(c.ι.app j).hom.app U t', (NatTrans.naturality_apply (c.ι.app j).hom i t').symm⟩

/-- The embedding of a diagram of abelian sheaves into the diagram of their Godement sheaves. -/
noncomputable def toGodementDiagram
    (D : J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    D ⟶ D ⋙ godement where
  app j := toGodement.app (D.obj j)
  naturality _ _ f := toGodement.naturality (D.map f)

instance (D : J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    Mono (toGodementDiagram D) :=
  have (j : J) : Mono ((toGodementDiagram D).app j) := mono_toGodement (D.obj j)
  NatTrans.mono_of_mono_app _

/-- **Cohomology of filtered colimits.** On a noetherian space, every cohomology class of the
colimit of a filtered diagram `D` of abelian sheaves comes from a cohomology class of some `D j`.
-/
theorem exists_H_map_colimit_ι_eq (q : ℕ) :
    ∀ (D : J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
      (ξ : Sheaf.H (colimit D) q), ∃ (j : J) (ξ' : Sheaf.H (D.obj j) q),
        Sheaf.H.map (colimit.ι D j) q ξ' = ξ := by
  induction q with
  | zero =>
    intro D ξ
    obtain ⟨j, t, ht⟩ := exists_app_eq_of_isColimit (colimit.isColimit D)
      (NoetherianSpace.isCompact (⊤ : Opens X).1) (Sheaf.H.equiv₀ _ isTerminalTop ξ)
    refine ⟨j, (Sheaf.H.equiv₀ _ isTerminalTop).symm t, ?_⟩
    rw [Sheaf.H.equiv₀_symm_naturality]
    rw [colimit.cocone_ι] at ht
    exact (Sheaf.H.equiv₀ _ isTerminalTop).symm_apply_eq.2 ht
  | succ q ih =>
    intro D ξ
    let η := toGodementDiagram D
    let S : ShortComplex
        (J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
      ShortComplex.mk η (cokernel.π η) (cokernel.condition η)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel _) inferInstance inferInstance
    have hSc : (S.map colim).ShortExact := hS.map colim
    have hflasque : Presheaf.IsFlasque (S.map colim).X₂.obj :=
      isFlasque_of_isColimit (colimit.isColimit (D ⋙ godement)) fun j ↦
        isFlasque_godement (D.obj j)
    have : Subsingleton (Sheaf.H (S.map colim).X₂ (q + 1)) :=
      IsFlasque.subsingleton_H (X := X) (S.map colim).X₂ q
    obtain ⟨y, rfl⟩ := Sheaf.H.δSucc_surjective hSc q ξ
    obtain ⟨j, y', rfl⟩ := ih (cokernel η) y
    have hSj : (S.map ((evaluation J _).obj j)).ShortExact := hS.map _
    let φ : S.map ((evaluation J _).obj j) ⟶ S.map colim :=
      { τ₁ := colimit.ι D j
        τ₂ := colimit.ι (D ⋙ godement) j
        τ₃ := colimit.ι (cokernel η) j
        comm₁₂ := colimit.ι_map η j
        comm₂₃ := colimit.ι_map (cokernel.π η) j }
    exact ⟨j, Sheaf.H.δSucc hSj q y', Sheaf.H.map_δSucc hSj hSc φ q y'⟩

end TopCat.Sheaf

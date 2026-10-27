/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q123
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Composition comparison for restricted module transport

Source: `sec-proetale-coefficients/sk-def-sfb-module-pushforward-pullback`, proof,
pushforward-composition and final pullback-composition sentences, in the blueprint
`main-20261015` (blueprint: lem-sfb-coefficient-composition-module-comparison).

The coefficient maps are monoid morphisms and need not be invertible. The isomorphism
on the underlying functors is assumed to respect the restricted module actions.
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

/-- Transport module objects along a lax monoidal functor, then restrict scalars along
the given monoid morphism. This is the composite of the recorded `mapMod` and `Mod.comap`,
with no new action construction.
Source: blueprint `main-20261015`, module pushforward-composition sentence
(blueprint: lem-sfb-coefficient-composition-module-comparison). -/
def restrictedModuleTransport (F : C ⥤ D) [F.LaxMonoidal]
    {A : C} [MonObj A] {B : D} [MonObj B] (ψ : B ⟶ F.obj A) [IsMonHom ψ] :
    Mod C A ⥤ Mod D B :=
  F.mapMod A ⋙ Mod.comap ψ

/-- Composition comparison for restricted module transport and its left adjoints.
Source: blueprint `main-20261015`, `sk-def-sfb-module-pushforward-pullback`, proof,
pushforward-composition and final pullback-composition sentences
(blueprint: lem-sfb-coefficient-composition-module-comparison).

Proof plan (the five steps of the DAG node):
1. Unfold `mapMod` (def-sfb-modobj-transport) and `Mod.comap`
   (def-sfb-modobj-restriction) twice to obtain the displayed actions; both functors
   keep the underlying maps given by the original functors.
2. Compose the stipulated forward linearity equation with the inverse components
   on the left and their left tensor whiskerings on the right. Tensor functoriality
   and the two inverse identities prove inverse linearity. The module morphism
   criterion (sk-def-sfb-module-objects) then lifts each component isomorphism.
3. Naturality of `c` on each underlying module morphism proves naturality of the
   lifts. Faithfulness of the module forgetful functor proves uniqueness of the lift.
4. Compose the adjunctions using def-weil-pbc-composite-adjunction. Apply
   lem-weil-pbc-conjugate-iso-unit-equation to the lifted right-adjoint comparison;
   it gives the unique left-adjoint isomorphism satisfying the stated unit equation.
5. In the component formula of def-weil-pbc-adjunction-conjugate, substitute that
   unit equation. Naturality of the right-adjoint comparison and the triangle
   identity identify the conjugate with that comparison. Conjugation preserves
   inverses, giving the inverse clause. Only the components of `c` are inverted. -/
theorem coefficientCompositionModuleComparison
    (P : C ⥤ D) (Q : D ⥤ E) (H : C ⥤ E)
    [P.LaxMonoidal] [Q.LaxMonoidal] [H.LaxMonoidal]
    (c : P ⋙ Q ≅ H) [NatTrans.IsMonoidal c.hom]
    (A : C) (B : D) (R : E) [MonObj A] [MonObj B] [MonObj R]
    (ψ : B ⟶ P.obj A) (χ : R ⟶ Q.obj B) (φ : R ⟶ H.obj A)
    [IsMonHom ψ] [IsMonHom χ] [IsMonHom φ]
    (hcompat : φ = χ ≫ Q.map ψ ≫ c.hom.app A)
    (hlinear : ∀ M : Mod C A,
      Mod.act (((P.restrictedModuleTransport ψ) ⋙
        Q.restrictedModuleTransport χ).obj M).X ≫ c.hom.app M.X =
      R ◁ c.hom.app M.X ≫ Mod.act ((H.restrictedModuleTransport φ).obj M).X) :
    (∀ M : Mod C A,
      Mod.act (((P.restrictedModuleTransport ψ) ⋙
        Q.restrictedModuleTransport χ).obj M).X =
        χ ▷ Q.obj (P.obj M.X) ≫ LaxMonoidal.μ Q B (P.obj M.X) ≫
          Q.map (ψ ▷ P.obj M.X ≫ LaxMonoidal.μ P A M.X ≫ P.map (Mod.act M.X)) ∧
      Mod.act ((H.restrictedModuleTransport φ).obj M).X =
        φ ▷ H.obj M.X ≫ LaxMonoidal.μ H A M.X ≫ H.map (Mod.act M.X)) ∧
    (∀ M : Mod C A,
      Mod.act ((H.restrictedModuleTransport φ).obj M).X ≫ c.inv.app M.X =
        R ◁ c.inv.app M.X ≫ Mod.act (((P.restrictedModuleTransport ψ) ⋙
          Q.restrictedModuleTransport χ).obj M).X) ∧
    (∀ (M N : Mod C A) (t : M ⟶ N),
      c.hom.app M.X ≫ H.map t.hom = (P ⋙ Q).map t.hom ≫ c.hom.app N.X) ∧
    ∃ δ : (P.restrictedModuleTransport ψ ⋙ Q.restrictedModuleTransport χ) ≅
        H.restrictedModuleTransport φ,
      (∀ M : Mod C A,
        (δ.hom.app M).hom = c.hom.app M.X ∧ (δ.inv.app M).hom = c.inv.app M.X) ∧
      (∀ δ' : (P.restrictedModuleTransport ψ ⋙ Q.restrictedModuleTransport χ) ≅
          H.restrictedModuleTransport φ,
        (∀ M : Mod C A,
          (δ'.hom.app M).hom = c.hom.app M.X ∧ (δ'.inv.app M).hom = c.inv.app M.X) →
        δ' = δ) ∧
      ∀ (S_P : Mod D B ⥤ Mod C A) (S_Q : Mod E R ⥤ Mod D B)
        (S_H : Mod E R ⥤ Mod C A)
        (adjP : S_P ⊣ P.restrictedModuleTransport ψ)
        (adjQ : S_Q ⊣ Q.restrictedModuleTransport χ)
        (adjH : S_H ⊣ H.restrictedModuleTransport φ),
        ∃ d : S_H ≅ S_Q ⋙ S_P,
          (∀ M : Mod E R,
            adjH.unit.app M ≫ (H.restrictedModuleTransport φ).map (d.hom.app M) =
              (adjQ.comp adjP).unit.app M ≫ δ.hom.app ((S_Q ⋙ S_P).obj M)) ∧
          (∀ d' : S_H ≅ S_Q ⋙ S_P,
            (∀ M : Mod E R,
              adjH.unit.app M ≫ (H.restrictedModuleTransport φ).map (d'.hom.app M) =
                (adjQ.comp adjP).unit.app M ≫ δ.hom.app ((S_Q ⋙ S_P).obj M)) →
            d' = d) ∧
          conjugateEquiv (adjQ.comp adjP) adjH d.hom = δ.hom ∧
          conjugateEquiv adjH (adjQ.comp adjP) d.inv = δ.inv := by
  have _ := hcompat
  let δ : (P.restrictedModuleTransport ψ ⋙ Q.restrictedModuleTransport χ) ≅
      H.restrictedModuleTransport φ :=
    NatIso.ofComponents (fun M ↦ Mod.isoMk (c.app M.X) (hlinear M)) (by
      intro M N t
      apply Mod.hom_ext
      exact c.hom.naturality t.hom)
  refine ⟨?_, ?_, ?_, δ, ?_, ?_, ?_⟩
  · intro M
    exact ⟨rfl, rfl⟩
  · intro M
    exact Mod.act_hom (δ.inv.app M)
  · intro M N t
    exact (c.hom.naturality t.hom).symm
  · intro M
    exact ⟨rfl, rfl⟩
  · intro δ' hδ'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply Mod.hom_ext
    exact (hδ' M).1
  · intro S_P S_Q S_H adjP adjQ adjH
    let adj := adjQ.comp adjP
    let d : S_H ≅ S_Q ⋙ S_P := (conjugateIsoEquiv adj adjH).symm δ
    have hd (M : Mod E R) :
        adjH.unit.app M ≫ (H.restrictedModuleTransport φ).map (d.hom.app M) =
          adj.unit.app M ≫ δ.hom.app ((S_Q ⋙ S_P).obj M) :=
      (unit_conjugateEquiv_symm adj adjH δ.hom M).symm
    refine ⟨d, hd, ?_, ?_, ?_⟩
    · intro d' hd'
      apply Iso.ext
      apply NatTrans.ext
      funext M
      apply (adjH.homEquiv M ((S_Q ⋙ S_P).obj M)).injective
      change adjH.unit.app M ≫ (H.restrictedModuleTransport φ).map (d'.hom.app M) =
        adjH.unit.app M ≫ (H.restrictedModuleTransport φ).map (d.hom.app M)
      exact (hd' M).trans (hd M).symm
    · exact (conjugateEquiv adj adjH).apply_symm_apply δ.hom
    · exact (conjugateEquiv adjH adj).apply_symm_apply δ.inv

end CategoryTheory.Functor

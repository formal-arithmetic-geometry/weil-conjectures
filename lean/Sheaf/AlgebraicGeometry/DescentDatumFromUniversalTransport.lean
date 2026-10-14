/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Recovering transport identities by faithfully flat base change

Source: Stacks Project, Tags 023V and 02VW.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A natural universal transport morphism compatible with an actual descent datum after a
 flat surjective base change already satisfies the identity and cocycle axioms. Lift the
 finitely many base maps to the covering scheme by iterated pullbacks. The resulting map to
 the test scheme is flat and surjective, hence epi. Pullback points lift uniquely by the
 cartesian square. Compatibility transfers the identity and cocycle equations from `E`;
 cancel the covering epimorphism to obtain them before base change. Naturality follows from
 the universal property of the pullback defining the universal transport.

Source: Stacks Project, Tags 023V and 02VW.
(blueprint: lem-pd-datum-from-universal-transport) -/
theorem exists_descentDatum_of_universalTransport
    {X X' Y : Scheme.{u}} {p : X ⟶ Y} {ι : X' ⟶ X} [Flat ι] [Surjective ι]
    {p' : X' ⟶ Y} (hp : ι ≫ p = p') (V : Over X) (V' : Over X')
    (q : V'.left ⟶ V.left) (hq : IsPullback q V'.hom V.hom ι)
    (E : Over.DescentDatum p' V')
    (t : pullback (V.hom ≫ p) p ⟶ V.left)
    (ht : t ≫ V.hom = pullback.snd (V.hom ≫ p) p)
    (hcompat : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X')
      (h : f₁ ≫ p' = f₂ ≫ p') (a : Over.mk f₁ ⟶ V'),
      pullback.lift (a.left ≫ q) (f₂ ≫ ι) (by
        calc
          (a.left ≫ q) ≫ (V.hom ≫ p) = (a.left ≫ V'.hom) ≫ (ι ≫ p) := by
            rw [Category.assoc, ← Category.assoc q, hq.w]
            simp only [Category.assoc]
          _ = f₁ ≫ p' := by simp only [Over.w a, Over.mk_hom, hp]
          _ = (f₂ ≫ ι) ≫ p := by rw [Category.assoc, hp, h]) ≫ t =
        (E.transport f₁ f₂ h a).left ≫ q) :
    ∃ D : Over.DescentDatum p V, D.IsBaseChange hp hq.w E := by
  let τ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
      (a : Over.mk f₁ ⟶ V) : Over.mk f₂ ⟶ V :=
    Over.homMk (pullback.lift a.left f₂ (by simpa using h) ≫ t) (by simp [ht])
  have hτ {T T' : Scheme.{u}} (g : T' ⟶ T) (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V) :
      τ (g ≫ f₁) (g ≫ f₂) (by simp [h]) ((Over.homMk g : Over.mk (g ≫ f₁) ⟶ Over.mk f₁) ≫ a) =
        (Over.homMk g : Over.mk (g ≫ f₂) ⟶ Over.mk f₂) ≫ τ f₁ f₂ h a := by
    ext
    simp only [τ, Over.homMk_left, Over.comp_left]
    have hl : pullback.lift (f := V.hom ≫ p) (g := p) (g ≫ a.left) (g ≫ f₂) (by simp [h]) =
        g ≫ pullback.lift a.left f₂ (by simpa using h) := by
      apply pullback.hom_ext <;> simp
    simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ t) hl
  have hself {T : Scheme.{u}} (f : T ⟶ X) (a : Over.mk f ⟶ V) :
      τ f f rfl a = a := by
    let g := pullback.fst f ι
    let f' := pullback.snd f ι
    have hg : Flat g := inferInstance
    have hg' : Surjective g := inferInstance
    have : Epi g := Flat.epi_of_flat_of_surjective g
    let a' : Over.mk f' ⟶ V' := Over.homMk
      (hq.lift (g ≫ a.left) f' (by simp [g, f', ← pullback.condition]))
      (hq.lift_snd _ _ _)
    have ha' : a'.left ≫ q = g ≫ a.left := hq.lift_fst _ _ _
    apply Over.OverMorphism.ext
    apply (cancel_epi g).mp
    have he := hcompat f' f' rfl a'
    simp only [E.transport_self] at he
    change g ≫ (τ f f rfl a).left = g ≫ a.left
    have hn := congrArg Over.Hom.left (hτ g f f rfl a)
    simp only [Over.comp_left, Over.homMk_left] at hn
    rw [← hn]
    simpa [τ, ha', g, f', ← pullback.condition] using he
  have htest {T T' : Scheme.{u}} (g : T' ⟶ T) (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (i₁ i₂ : T' ⟶ X')
      (hi₁ : i₁ ≫ ι = g ≫ f₁) (hi₂ : i₂ ≫ ι = g ≫ f₂)
      (h' : i₁ ≫ p' = i₂ ≫ p') (a : Over.mk f₁ ⟶ V)
      (a' : Over.mk i₁ ⟶ V') (ha' : a'.left ≫ q = g ≫ a.left) :
      g ≫ (τ f₁ f₂ h a).left = (E.transport i₁ i₂ h' a').left ≫ q := by
    have hn := congrArg Over.Hom.left (hτ g f₁ f₂ h a)
    simp only [Over.comp_left, Over.homMk_left] at hn
    rw [← hn]
    simpa only [τ, Over.homMk_left, Over.comp_left, ha', hi₂] using
      hcompat i₁ i₂ h' a'
  have hcocycle {T : Scheme.{u}} (f₁ f₂ f₃ : T ⟶ X)
      (h₁₂ : f₁ ≫ p = f₂ ≫ p) (h₂₃ : f₂ ≫ p = f₃ ≫ p)
      (a : Over.mk f₁ ⟶ V) :
      τ f₂ f₃ h₂₃ (τ f₁ f₂ h₁₂ a) = τ f₁ f₃ (h₁₂.trans h₂₃) a := by
    let g₁ := pullback.fst f₁ ι
    let i₁ := pullback.snd f₁ ι
    let g₂ := pullback.fst (g₁ ≫ f₂) ι
    let i₂ := pullback.snd (g₁ ≫ f₂) ι
    let g₃ := pullback.fst ((g₂ ≫ g₁) ≫ f₃) ι
    let i₃ := pullback.snd ((g₂ ≫ g₁) ≫ f₃) ι
    let g := g₃ ≫ g₂ ≫ g₁
    let j₁ := g₃ ≫ g₂ ≫ i₁
    let j₂ := g₃ ≫ i₂
    let j₃ := i₃
    have hg₁ : j₁ ≫ ι = g ≫ f₁ := by
      simp only [j₁, g, g₁, i₁, Category.assoc, ← pullback.condition]
    have hg₂ : j₂ ≫ ι = g ≫ f₂ := by
      simp only [j₂, g, g₂, i₂, Category.assoc, ← pullback.condition]
    have hg₃ : j₃ ≫ ι = g ≫ f₃ := by
      simp only [j₃, i₃, g, g₃, Category.assoc, ← pullback.condition]
    have hj₁₂ : j₁ ≫ p' = j₂ ≫ p' := by
      rw [← hp, ← Category.assoc, hg₁, ← Category.assoc, hg₂]
      simp only [Category.assoc, h₁₂]
    have hj₂₃ : j₂ ≫ p' = j₃ ≫ p' := by
      rw [← hp, ← Category.assoc, hg₂, ← Category.assoc, hg₃]
      simp only [Category.assoc, h₂₃]
    have : Flat g₁ := inferInstance
    have : Flat g₂ := inferInstance
    have : Flat g₃ := inferInstance
    have : Surjective g₁ := inferInstance
    have : Surjective g₂ := inferInstance
    have : Surjective g₃ := inferInstance
    have : Epi g := Flat.epi_of_flat_of_surjective g
    let a' : Over.mk j₁ ⟶ V' := Over.homMk
      (hq.lift (g ≫ a.left) j₁ (by simpa [Category.assoc] using hg₁.symm))
      (hq.lift_snd _ _ _)
    have ha' : a'.left ≫ q = g ≫ a.left := hq.lift_fst _ _ _
    have hb' := htest g f₁ f₂ h₁₂ j₁ j₂ hg₁ hg₂ hj₁₂ a a' ha'
    apply Over.OverMorphism.ext
    apply (cancel_epi g).mp
    rw [htest g f₂ f₃ h₂₃ j₂ j₃ hg₂ hg₃ hj₂₃ (τ f₁ f₂ h₁₂ a)
      (E.transport j₁ j₂ hj₁₂ a') hb'.symm,
      htest g f₁ f₃ (h₁₂.trans h₂₃) j₁ j₃ hg₁ hg₃ (hj₁₂.trans hj₂₃) a a' ha',
      E.transport_transport]
  refine ⟨{ transport := τ
            transport_homMk_comp := hτ
            transport_self := hself
            transport_transport := hcocycle }, ?_⟩
  intro T f₁ f₂ h a
  exact hcompat f₁ f₂ h a

end AlgebraicGeometry

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Sheaf.AlgebraicGeometry.AffineFpqcDescent
import Sheaf.AlgebraicGeometry.InvariantOpenEffectiveDescent

/-!
# Gluing effective affine descents

Source: Stacks Project, Descent, Tags 0AP4 and 0245;
Groupoid Schemes, proof of Tag 0H8K.
(blueprint: lem-pd-invariant-affine-descent-gluing).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

private theorem transport_left_congr
    {X Y T : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    (D : Over.DescentDatum p V) {f₁ f₂ g₁ g₂ : T ⟶ X}
    (h : f₁ ≫ p = f₂ ≫ p) (k : g₁ ≫ p = g₂ ≫ p)
    (a : Over.mk f₁ ⟶ V) (b : Over.mk g₁ ⟶ V)
    (h₁ : f₁ = g₁) (h₂ : f₂ = g₂) (hab : a.left = b.left) :
    (D.transport f₁ f₂ h a).left = (D.transport g₁ g₂ k b).left := by
  subst g₁ g₂
  have : a = b := Over.OverMorphism.ext hab
  subst b
  rfl

private theorem exists_datum_on_invariant_open
    {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X}
    (D : Over.DescentDatum p V) (U : V.left.Opens)
    (hU : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
      (a : Over.mk f₁ ⟶ V), Set.range a.left ⊆ U →
        Set.range (D.transport f₁ f₂ h a).left ⊆ U) :
    ∃ E : Over.DescentDatum p (Over.mk (U.ι ≫ V.hom)),
      ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
        (a : Over.mk f₁ ⟶ Over.mk (U.ι ≫ V.hom)),
        (E.transport f₁ f₂ h a).left ≫ U.ι =
          (D.transport f₁ f₂ h (Over.homMk (a.left ≫ U.ι)
            (by simpa only [Over.mk_hom, Category.assoc] using Over.w a))).left := by
  let embed {T : Scheme.{u}} {f : T ⟶ X}
      (a : Over.mk f ⟶ Over.mk (U.ι ≫ V.hom)) : Over.mk f ⟶ V :=
    Over.homMk (a.left ≫ U.ι)
      (by simpa only [Over.mk_hom, Category.assoc] using Over.w a)
  have hrange {T : Scheme.{u}} {f : T ⟶ X}
      (a : Over.mk f ⟶ Over.mk (U.ι ≫ V.hom)) : Set.range (embed a).left ⊆ U := by
    change Set.range (a.left ≫ U.ι) ⊆ U
    rintro _ ⟨x, rfl⟩
    exact (U.ι_apply (a.left x)) ▸ (a.left x).property
  let tr {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
      (a : Over.mk f₁ ⟶ Over.mk (U.ι ≫ V.hom)) :
      Over.mk f₂ ⟶ Over.mk (U.ι ≫ V.hom) :=
    Over.homMk
      (IsOpenImmersion.lift U.ι (D.transport f₁ f₂ h (embed a)).left
        (by simpa using hU f₁ f₂ h (embed a) (hrange a)))
      (by
        change _ ≫ U.ι ≫ V.hom = f₂
        rw [← Category.assoc, IsOpenImmersion.lift_fac]
        exact Over.w _)
  have fac {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
      (a : Over.mk f₁ ⟶ Over.mk (U.ι ≫ V.hom)) :
      (tr f₁ f₂ h a).left ≫ U.ι = (D.transport f₁ f₂ h (embed a)).left := by
    exact IsOpenImmersion.lift_fac _ _ _
  have embtr {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
      (a : Over.mk f₁ ⟶ Over.mk (U.ι ≫ V.hom)) :
      embed (tr f₁ f₂ h a) = D.transport f₁ f₂ h (embed a) := by
    apply Over.OverMorphism.ext
    exact fac f₁ f₂ h a
  refine ⟨{
    transport := tr
    transport_homMk_comp := ?_
    transport_self := ?_
    transport_transport := ?_
  }, fac⟩
  · intro T T' g f₁ f₂ h a
    apply Over.OverMorphism.ext
    apply (cancel_mono U.ι).mp
    simp only [Over.comp_left, Category.assoc, fac]
    have he : embed ((Over.homMk g : Over.mk (g ≫ f₁) ⟶ Over.mk f₁) ≫ a) =
        (Over.homMk g : Over.mk (g ≫ f₁) ⟶ Over.mk f₁) ≫ embed a := by
      ext
      simp [embed, Category.assoc]
    rw [he]
    exact congrArg Over.Hom.left (D.transport_homMk_comp g f₁ f₂ h (embed a))
  · intro T f a
    apply Over.OverMorphism.ext
    apply (cancel_mono U.ι).mp
    rw [fac, D.transport_self]
    rfl
  · intro T f₁ f₂ f₃ h₁₂ h₂₃ a
    apply Over.OverMorphism.ext
    apply (cancel_mono U.ι).mp
    rw [fac, embtr, fac, D.transport_transport]

set_option backward.isDefEq.respectTransparency false in
private theorem exists_datum_over_mono_base
    {X X' Y Y' : Scheme.{u}} {p : X ⟶ Y} {p' : X' ⟶ Y'}
    (i : X' ⟶ X) (j : Y' ⟶ Y) [Mono i] [Mono j]
    (hc : i ≫ p = p' ≫ j) {V : Over X} (D : Over.DescentDatum p V)
    (r : V.left ⟶ X') (hr : r ≫ i = V.hom) :
    ∃ E : Over.DescentDatum p' (Over.mk r),
      ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X') (h : f₁ ≫ p' = f₂ ≫ p')
        (a : Over.mk f₁ ⟶ Over.mk r),
        (E.transport f₁ f₂ h a).left =
          (D.transport (f₁ ≫ i) (f₂ ≫ i)
            (by simpa only [Category.assoc, hc] using congrArg (· ≫ j) h)
            (Over.homMk a.left (by
              simpa only [Over.mk_hom, ← hr, ← Category.assoc] using
                congrArg (· ≫ i) (Over.w a)))).left := by
  let embed {T : Scheme.{u}} {f : T ⟶ X'}
      (a : Over.mk f ⟶ Over.mk r) : Over.mk (f ≫ i) ⟶ V :=
    Over.homMk a.left (by
      simpa only [Over.mk_hom, ← hr, ← Category.assoc] using congrArg (· ≫ i) (Over.w a))
  let tr {T : Scheme.{u}} (f₁ f₂ : T ⟶ X') (h : f₁ ≫ p' = f₂ ≫ p')
      (a : Over.mk f₁ ⟶ Over.mk r) : Over.mk f₂ ⟶ Over.mk r :=
    Over.homMk
      (D.transport (f₁ ≫ i) (f₂ ≫ i)
        (by simpa only [Category.assoc, hc] using congrArg (· ≫ j) h) (embed a)).left
      (by
        apply (cancel_mono i).mp
        simpa only [Over.mk_hom, Category.assoc, hr] using Over.w
          (D.transport (f₁ ≫ i) (f₂ ≫ i)
            (by simpa only [Category.assoc, hc] using congrArg (· ≫ j) h) (embed a)))
  have embtr {T : Scheme.{u}} (f₁ f₂ : T ⟶ X') (h : f₁ ≫ p' = f₂ ≫ p')
      (a : Over.mk f₁ ⟶ Over.mk r) :
      embed (tr f₁ f₂ h a) = D.transport (f₁ ≫ i) (f₂ ≫ i)
        (by simpa only [Category.assoc, hc] using congrArg (· ≫ j) h) (embed a) := by
    ext
    rfl
  refine ⟨{
    transport := tr
    transport_homMk_comp := ?_
    transport_self := ?_
    transport_transport := ?_
  }, fun _ _ _ _ => rfl⟩
  · intro T T' g f₁ f₂ h a
    apply Over.OverMorphism.ext
    change (D.transport _ _ _ (embed (_ ≫ a))).left =
      g ≫ (D.transport _ _ _ (embed a)).left
    have hp : (f₁ ≫ i) ≫ p = (f₂ ≫ i) ≫ p := by
      simpa only [Category.assoc, hc] using congrArg (· ≫ j) h
    refine (transport_left_congr D _
      (by simpa only [Category.assoc] using congrArg (g ≫ ·) hp) _
      ((Over.homMk g : Over.mk (g ≫ f₁ ≫ i) ⟶ Over.mk (f₁ ≫ i)) ≫ embed a)
      (Category.assoc g f₁ i) (Category.assoc g f₂ i) rfl).trans ?_
    exact congrArg Over.Hom.left (D.transport_homMk_comp g (f₁ ≫ i) (f₂ ≫ i)
      (by simpa only [Category.assoc, hc] using congrArg (· ≫ j) h) (embed a))
  · intro T f a
    apply Over.OverMorphism.ext
    change (D.transport (f ≫ i) (f ≫ i) _ (embed a)).left = a.left
    exact congrArg Over.Hom.left (D.transport_self (f ≫ i) (embed a))
  · intro T f₁ f₂ f₃ h₁₂ h₂₃ a
    apply Over.OverMorphism.ext
    change (D.transport _ _ _ (embed (tr f₁ f₂ h₁₂ a))).left = _
    rw [embtr f₁ f₂ h₁₂ a]
    change (D.transport _ _ _ (D.transport _ _ _ (embed a))).left =
      (D.transport _ _ _ (embed a)).left
    exact congrArg Over.Hom.left (D.transport_transport (f₁ ≫ i) (f₂ ≫ i) (f₃ ≫ i)
      (by simpa only [Category.assoc, hc] using congrArg (· ≫ j) h₁₂)
      (by simpa only [Category.assoc, hc] using congrArg (· ≫ j) h₂₃) (embed a))

set_option backward.isDefEq.respectTransparency false in
private theorem isEffective_of_affine_above_affine_open
    {X Y : Scheme.{u}} {p : X ⟶ Y} [IsFinite p] [Flat p] [Surjective p]
    {V : Over X} [IsAffine V.left] (D : Over.DescentDatum p V)
    (B : Y.Opens) (hB : IsAffineOpen B)
    (hVB : Set.range (V.hom ≫ p) ⊆ B) : D.IsEffective := by
  let XB := p ⁻¹ᵁ B
  let i : XB.toScheme ⟶ X := XB.ι
  let pB : XB.toScheme ⟶ B.toScheme := p ∣_ B
  have hc : i ≫ p = pB ≫ B.ι := (morphismRestrict_ι p B).symm
  have hrange : Set.range V.hom ⊆ Set.range i := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hVB ⟨x, by simp⟩
  let r : V.left ⟶ XB.toScheme := IsOpenImmersion.lift i V.hom hrange
  have hr : r ≫ i = V.hom := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨E, hE⟩ := exists_datum_over_mono_base i B.ι hc D r hr
  have : IsAffine B.toScheme := hB
  have : IsAffine XB.toScheme := hB.preimage p
  have : Flat pB := inferInstance
  have : Surjective pB := MorphismProperty.of_isPullback (P := @Surjective)
    (isPullback_morphismRestrict p B).flip inferInstance
  have : QuasiCompact pB := inferInstance
  have : IsAffineHom r := inferInstance
  have : IsAffineHom (Over.mk r).hom := by assumption
  obtain ⟨W, q, hq, hinv⟩ := E.isEffective_of_isAffineHom_fpqc pB
    pB.singleton_mem_fpqcPrecoverage
  refine ⟨Over.mk (W.hom ≫ B.ι), q, ?_, ?_⟩
  · have hpaste : IsPullback q (r ≫ i) (W.hom ≫ B.ι) p :=
      hq.paste_vert (isPullback_morphismRestrict p B)
    rw [hr] at hpaste
    exact hpaste
  · intro T f₁ f₂ h a
    let b := D.transport f₁ f₂ h a
    let g₁ : T ⟶ XB.toScheme := a.left ≫ r
    let g₂ : T ⟶ XB.toScheme := b.left ≫ r
    have hg₁ : g₁ ≫ i = f₁ := by simp [g₁, Category.assoc, hr, Over.w a]
    have hg₂ : g₂ ≫ i = f₂ := by simp [g₂, Category.assoc, hr, Over.w b]
    have hg : g₁ ≫ pB = g₂ ≫ pB := by
      apply (cancel_mono B.ι).mp
      calc
        (g₁ ≫ pB) ≫ B.ι = (g₁ ≫ i) ≫ p := by simp only [Category.assoc, hc]
        _ = f₁ ≫ p := by rw [hg₁]
        _ = f₂ ≫ p := h
        _ = (g₂ ≫ pB) ≫ B.ι := by rw [← hg₂]; simp only [Category.assoc, hc]
    let aB : Over.mk g₁ ⟶ Over.mk r := Over.homMk a.left
    have ht := hinv g₁ g₂ hg aB
    rw [hE] at ht
    have he := transport_left_congr D
      (by simpa only [Category.assoc, hc] using congrArg (· ≫ B.ι) hg) h
      (Over.homMk aB.left (by
        simpa only [Over.mk_hom, ← hr, ← Category.assoc] using
          congrArg (· ≫ i) (Over.w aB))) a hg₁ hg₂ rfl
    rw [he] at ht
    exact ht

/-- Effective affine descents glue along a covering by transport-invariant affine opens.
Source: Stacks Project, Descent, Tags 0AP4 and 0245; proof of Tag 0H8K.
(blueprint: lem-pd-invariant-affine-descent-gluing).

Proof: The opens U in hcover cover V and are invariant in both directions, using inverse
transport. Restrict D to each U above the chosen affine B in Y. The inverse image X_B
is affine, since p is finite. Thus U -> X_B is affine, and faithfully flat affine descent
(0245) gives its effective affine model over B. The intersections of the U are invariant
open subschemes. Descent of open immersions and full faithfulness identify their descents
as open subschemes of each affine model. On triple intersections the transition maps
satisfy the cocycle condition, since they do so after base change and base change is
faithful. Glue the models along these open identifications (0AP4). The structure maps
agree on intersections, so the glued scheme lies over Y. The local pullback squares
assemble to a pullback square for V; the local invariant projections assemble to q.
They satisfy transport invariance since it holds on the covering. This gives exactly
D.IsEffective. If V is empty, glue the empty family to the empty Y-scheme. -/
theorem isEffective_of_invariant_affine_neighbourhoods
    {X Y : Scheme.{u}} {p : X ⟶ Y} [IsFinite p] [Flat p] [Surjective p]
    {V : Over X} (D : Over.DescentDatum p V)
    (hcover : ∀ v : V.left,
      ∃ U : V.left.Opens, v ∈ U ∧ IsAffineOpen U ∧
        (∃ B : Y.Opens, IsAffineOpen B ∧ U ≤ (V.hom ≫ p) ⁻¹ᵁ B) ∧
        ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
          (a : Over.mk f₁ ⟶ V), Set.range a.left ⊆ U →
            Set.range (D.transport f₁ f₂ h a).left ⊆ U) : D.IsEffective := by
  classical
  choose U hv hAffine hBase hInvariant using hcover
  have hrestrict := fun v : V.left => exists_datum_on_invariant_open D (U v) (hInvariant v)
  choose E hcompat using hrestrict
  refine isEffective_of_effective_open_cover p.singleton_mem_fpqcPrecoverage D U
    (fun x => ⟨x, hv x⟩) E (fun v => hcompat v) ?_
  intro v
  have : IsAffine (Over.mk ((U v).ι ≫ V.hom)).left := hAffine v
  obtain ⟨B, hB, hUB⟩ := hBase v
  apply isEffective_of_affine_above_affine_open (E v) B hB
  rintro _ ⟨x, rfl⟩
  exact hUB x.property

end CategoryTheory.Over.DescentDatum

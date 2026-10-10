/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.AffineFinitePresentation
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.Descent.Iso
public import WeilConjectures.AlgebraicGeometry.AffineTransitionLimit.OpensCone
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme

/-!
# Descent of schemes over a limit to a finite stage

The predicates `AlgebraicGeometry.DescendsAt`, `AlgebraicGeometry.DescendsAtWithOpen` and
`AlgebraicGeometry.DescendsToStage` saying that a scheme over a cofiltered limit is the base
change of a finite-stage model, and their first properties: a quasi-compact open descends
(`AlgebraicGeometry.exists_descendsAtWithOpen`), and affine schemes over an affine open of a
stage descend.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section FinitePresentationDescent
section Descent

set_option backward.defeqAttrib.useBackward true
variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} {c : Cone D} (hc : IsLimit c)
  [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

variable (D c) in
/-- (Implementation) The comparison morphism to the base change of a finite-stage model. -/
noncomputable def isPullbackLift {k k' : I} (f : k' ⟶ k) {X Y : Scheme.{u}} {g : X ⟶ c.pt}
    {p : Y ⟶ D.obj k} {h : X ⟶ Y} (H : IsPullback h g p (c.π.app k)) :
    X ⟶ pullback p (D.map f) :=
  pullback.lift h (g ≫ c.π.app k') (by rw [H.w, ← c.w f, Category.assoc])

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
@[reassoc (attr := simp)]
lemma isPullbackLift_fst {k k' : I} (f : k' ⟶ k) {X Y : Scheme.{u}} {g : X ⟶ c.pt}
    {p : Y ⟶ D.obj k} {h : X ⟶ Y} (H : IsPullback h g p (c.π.app k)) :
    isPullbackLift D c f H ≫ pullback.fst p (D.map f) = h := pullback.lift_fst ..

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
@[reassoc (attr := simp)]
lemma isPullbackLift_snd {k k' : I} (f : k' ⟶ k) {X Y : Scheme.{u}} {g : X ⟶ c.pt}
    {p : Y ⟶ D.obj k} {h : X ⟶ Y} (H : IsPullback h g p (c.π.app k)) :
    isPullbackLift D c f H ≫ pullback.snd p (D.map f) = g ≫ c.π.app k' := pullback.lift_snd ..

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
lemma isPullback_isPullbackLift {k k' : I} (f : k' ⟶ k) {X Y : Scheme.{u}} {g : X ⟶ c.pt}
    {p : Y ⟶ D.obj k} {h : X ⟶ Y} (H : IsPullback h g p (c.π.app k)) :
    IsPullback (isPullbackLift D c f H) g (pullback.snd p (D.map f)) (c.π.app k') := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback p (D.map f))
  rw [isPullbackLift_fst, c.w f]
  exact H

variable (D c) in
/-- (Implementation) The property that `g : X ⟶ lim Dⱼ` is the base change along
`lim Dⱼ ⟶ D_k` of a scheme of finite presentation over the stage `D_k`. -/
def DescendsAt (k : I) {X : Scheme.{u}} (g : X ⟶ c.pt) : Prop :=
  ∃ (Y : Scheme.{u}) (p : Y ⟶ D.obj k) (h : X ⟶ Y), LocallyOfFinitePresentation p ∧
    CompactSpace Y ∧ QuasiSeparatedSpace Y ∧ IsPullback h g p (c.π.app k)

variable (D c) in
/-- (Implementation) Refinement of `AlgebraicGeometry.DescendsAt` remembering a descent of a
quasi-compact open `W ⊆ X` to a quasi-compact open of the finite-stage model. -/
def DescendsAtWithOpen (k : I) {X : Scheme.{u}} (g : X ⟶ c.pt) (W : X.Opens) : Prop :=
  ∃ (Y : Scheme.{u}) (p : Y ⟶ D.obj k) (h : X ⟶ Y) (O : Y.Opens),
    LocallyOfFinitePresentation p ∧ CompactSpace Y ∧ QuasiSeparatedSpace Y ∧
      IsPullback h g p (c.π.app k) ∧ IsCompact (O : Set Y) ∧ h ⁻¹ᵁ O = W

variable (D c) in
/-- (Implementation) The property that `g : X ⟶ lim Dⱼ` is the base change of a scheme of
finite presentation over one of the stages. -/
def DescendsToStage {X : Scheme.{u}} (g : X ⟶ c.pt) : Prop := ∃ k, DescendsAt D c k g

omit [IsCofiltered I] in
lemma DescendsAt.mono {k k' : I} (f : k' ⟶ k) {X : Scheme.{u}} {g : X ⟶ c.pt}
    (H : DescendsAt D c k g) : DescendsAt D c k' g := by
  obtain ⟨Y, p, h, hp, hcpt, hqs, hsq⟩ := H
  have := hp; have := hcpt; have := hqs
  exact ⟨pullback p (D.map f), pullback.snd _ _, isPullbackLift D c f hsq, inferInstance,
    inferInstance, inferInstance, isPullback_isPullbackLift f hsq⟩

omit [IsCofiltered I] in
lemma DescendsAtWithOpen.mono {k k' : I} (f : k' ⟶ k) {X : Scheme.{u}} {g : X ⟶ c.pt}
    {W : X.Opens} (H : DescendsAtWithOpen D c k g W) : DescendsAtWithOpen D c k' g W := by
  obtain ⟨Y, p, h, O, hp, hcpt, hqs, hsq, hOc, hO⟩ := H
  have := hp; have := hcpt; have := hqs
  have : QuasiCompact (pullback.fst p (D.map f)) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  refine ⟨pullback p (D.map f), pullback.snd _ _, isPullbackLift D c f hsq,
    pullback.fst p (D.map f) ⁻¹ᵁ O, inferInstance, inferInstance, inferInstance,
    isPullback_isPullbackLift f hsq,
    QuasiCompact.isCompact_preimage _ O.isOpen hOc, ?_⟩
  rw [← Scheme.Hom.comp_preimage, isPullbackLift_fst, hO]

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
lemma DescendsAtWithOpen.descendsAt {k : I} {X : Scheme.{u}} {g : X ⟶ c.pt} {W : X.Opens}
    (H : DescendsAtWithOpen D c k g W) : DescendsAt D c k g := by
  obtain ⟨Y, p, h, O, hp, hcpt, hqs, hsq, -, -⟩ := H
  exact ⟨Y, p, h, hp, hcpt, hqs, hsq⟩

include hc in
/-- (Implementation) A quasi-compact open of a scheme over the limit descends to a
finite stage (Stacks Project Tag 01ZB). -/
lemma exists_descendsAtWithOpen {k : I} {X : Scheme.{u}} {g : X ⟶ c.pt}
    (H : DescendsAt D c k g) (W : X.Opens) (hW : IsCompact (W : Set X)) :
    ∃ k' : I, DescendsAtWithOpen D c k' g W := by
  obtain ⟨Y, p, h, hp, hcpt, hqs, hsq⟩ := H
  have := hp; have := hcpt; have := hqs
  have hlim : IsLimit ((baseChangeCone D c p).extend hsq.isoPullback.hom) :=
    (isLimitBaseChangeCone D c p hc).ofIsoLimit
      (Cone.ext hsq.isoPullback.symm (fun j ↦ by simp))
  obtain ⟨j, O, hOc, hO⟩ := exists_preimage_eq (baseChangeDiagram D p) _ hlim W hW
  refine ⟨j.left, pullback p (D.map j.hom), pullback.snd _ _, isPullbackLift D c j.hom hsq, O,
    inferInstance, inferInstance, inferInstance, isPullback_isPullbackLift j.hom hsq, hOc, ?_⟩
  have hmap : isPullbackLift D c j.hom hsq =
      ((baseChangeCone D c p).extend hsq.isoPullback.hom).π.app j := by
    apply pullback.hom_ext <;>
      simp [Cone.extend, IsPullback.isoPullback_hom_fst]
  rw [← hO, hmap]

include hc in
/-- (Implementation) **An affine scheme of finite presentation over the limit that lies over an
affine open of one of the stages descends to a finite stage.**

The system is base changed to the affine open `V ⊆ Dᵢ₀`: the base changed system has affine
stages, so the affine case
`AlgebraicGeometry.Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine`
applies to it. -/
lemma DescendsToStage.of_isAffine {i₀ : I} {X : Scheme.{u}} [IsAffine X] (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] {V : (D.obj i₀).Opens} (hV : IsAffineOpen V)
    (q : X ⟶ V.toScheme) (hq : q ≫ V.ι = g ≫ c.π.app i₀) : DescendsToStage D c g := by
  have : IsAffine V.toScheme := hV
  have : ∀ j : Over i₀, IsAffine ((baseChangeDiagram D V.ι).obj j) := fun j ↦
    inferInstanceAs (IsAffine (pullback V.ι (D.map j.hom)))
  have hsnd : pullback.lift q g hq ≫ pullback.snd V.ι (c.π.app i₀) = g := pullback.lift_snd ..
  have hmono : MorphismProperty.monomorphisms Scheme.{u} (pullback.snd V.ι (c.π.app i₀)) :=
    inferInstanceAs (Mono _)
  have hcomp : LocallyOfFinitePresentation
      (pullback.lift q g hq ≫ pullback.snd V.ι (c.π.app i₀)) := by
    rw [hsnd]
    exact ‹LocallyOfFinitePresentation g›
  have : @LocallyOfFinitePresentation X (baseChangeCone D c V.ι).pt (pullback.lift q g hq) :=
    MorphismProperty.of_postcomp (W := @LocallyOfFinitePresentation)
      (W' := MorphismProperty.monomorphisms Scheme.{u}) _ (pullback.snd V.ι (c.π.app i₀))
      hmono hcomp
  obtain ⟨j, Y, hYaff, p, hp, h, hsq⟩ :=
    Scheme.exists_isPullback_of_locallyOfFinitePresentation_of_isAffine
      (baseChangeDiagram D V.ι) (baseChangeCone D c V.ι)
      (isLimitBaseChangeCone D c V.ι hc) (pullback.lift q g hq)
  have := hYaff
  have := hp
  have : IsOpenImmersion ((baseChangeDiagramπ D V.ι).app j) :=
    inferInstanceAs (IsOpenImmersion (pullback.snd V.ι (D.map j.hom)))
  have hP : LocallyOfFinitePresentation (p ≫ (baseChangeDiagramπ D V.ι).app j) := inferInstance
  refine ⟨j.left, Y, p ≫ (baseChangeDiagramπ D V.ι).app j, h, hP, inferInstance,
    inferInstance, ?_⟩
  rw [← hsnd]
  exact hsq.paste_vert (isPullback_baseChangeCone_π D c V.ι j)

include hc in
/-- (Implementation) An affine open of a scheme over the limit that lies over an affine open of
one of the stages descends to a finite stage. -/
lemma DescendsToStage.of_isAffineOpen {i₀ : I} {X : Scheme.{u}} (g : X ⟶ c.pt)
    [LocallyOfFinitePresentation g] {W : X.Opens} (hW : IsAffineOpen W)
    {V : (D.obj i₀).Opens} (hV : IsAffineOpen V) (hle : W ≤ (g ≫ c.π.app i₀) ⁻¹ᵁ V) :
    DescendsToStage D c (W.ι ≫ g) := by
  have : IsAffine W.toScheme := hW
  refine DescendsToStage.of_isAffine hc _ hV ((g ≫ c.π.app i₀).resLE V W hle) ?_
  rw [Scheme.Hom.resLE_comp_ι, Category.assoc]

omit [IsCofiltered I] [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] in
lemma DescendsToStage.comp_iso {X X' : Scheme.{u}} (e : X' ≅ X) {g : X ⟶ c.pt}
    (H : DescendsToStage D c g) : DescendsToStage D c (e.hom ≫ g) := by
  obtain ⟨k, Y, p, h, hp, hcpt, hqs, hsq⟩ := H
  refine ⟨k, Y, p, e.hom ≫ h, hp, hcpt, hqs, ?_⟩
  have hiso : IsPullback e.hom (e.hom ≫ g) g (𝟙 c.pt) := IsPullback.of_horiz_isIso ⟨by simp⟩
  simpa using hiso.paste_horiz hsq

end Descent

end FinitePresentationDescent

end AlgebraicGeometry

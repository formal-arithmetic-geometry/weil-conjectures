/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteSupportOriginComparison
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionBinarySquare
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionCompactificationTransport
import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.FiniteProjectionInputNaturality

/-! # Finite projection coherence in operation coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.CompactSupportFiniteProjection

private theorem reflect_associativity
    {C₀ C₁ C₂ C₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    (Φ₀ : C₀ ⥤ D₀) (Φ₁ : C₁ ⥤ D₁) (Φ₂ : C₂ ⥤ D₂) (Φ₃ : C₃ ⥤ D₃)
    {F : C₀ ⥤ C₁} {G : C₁ ⥤ C₂} {H : C₂ ⥤ C₃}
    {FG : C₀ ⥤ C₂} {GH : C₁ ⥤ C₃} {L R : C₀ ⥤ C₃}
    {f : D₀ ⥤ D₁} {g : D₁ ⥤ D₂} {h : D₂ ⥤ D₃}
    {fg : D₀ ⥤ D₂} {gh : D₁ ⥤ D₃} {l r : D₀ ⥤ D₃}
    (tF : F ⋙ Φ₁ ≅ Φ₀ ⋙ f) (tG : G ⋙ Φ₂ ≅ Φ₁ ⋙ g)
    (tH : H ⋙ Φ₃ ≅ Φ₂ ⋙ h) (tFG : FG ⋙ Φ₂ ≅ Φ₀ ⋙ fg)
    (tGH : GH ⋙ Φ₃ ≅ Φ₁ ⋙ gh) (tL : L ⋙ Φ₃ ≅ Φ₀ ⋙ l)
    (tR : R ⋙ Φ₃ ≅ Φ₀ ⋙ r)
    (e₁ : F ⋙ G ≅ FG) (e₂ : FG ⋙ H ≅ L) (e₃ : G ⋙ H ≅ GH)
    (e₄ : F ⋙ GH ≅ R) (e₅ : L ≅ R)
    (o₁ : f ⋙ g ≅ fg) (o₂ : fg ⋙ h ≅ l) (o₃ : g ⋙ h ≅ gh)
    (o₄ : f ⋙ gh ≅ r) (o₅ : l ≅ r)
    (hc₁ : Functor.whiskerRight e₁.hom Φ₂ ≫ tFG.hom =
      Functor.whiskerLeft F tG.hom ≫ Functor.whiskerRight tF.hom g ≫
        Functor.whiskerLeft Φ₀ o₁.hom)
    (hc₂ : Functor.whiskerRight e₂.hom Φ₃ ≫ tL.hom =
      Functor.whiskerLeft FG tH.hom ≫ Functor.whiskerRight tFG.hom h ≫
        Functor.whiskerLeft Φ₀ o₂.hom)
    (hc₃ : Functor.whiskerRight e₃.hom Φ₃ ≫ tGH.hom =
      Functor.whiskerLeft G tH.hom ≫ Functor.whiskerRight tG.hom h ≫
        Functor.whiskerLeft Φ₁ o₃.hom)
    (hc₄ : Functor.whiskerRight e₄.hom Φ₃ ≫ tR.hom =
      Functor.whiskerLeft F tGH.hom ≫ Functor.whiskerRight tF.hom gh ≫
        Functor.whiskerLeft Φ₀ o₄.hom)
    (ht : Functor.whiskerRight e₅.hom Φ₃ ≫ tR.hom =
      tL.hom ≫ Functor.whiskerLeft Φ₀ o₅.hom)
    (he : Functor.whiskerRight o₁.hom h ≫ o₂.hom ≫ o₅.hom =
      (Functor.associator f g h).hom ≫ Functor.whiskerLeft f o₃.hom ≫ o₄.hom) :
    Functor.whiskerRight
      (Functor.whiskerRight e₁.hom H ≫ e₂.hom ≫ e₅.hom) Φ₃ =
    Functor.whiskerRight
      ((Functor.associator F G H).hom ≫ Functor.whiskerLeft F e₃.hom ≫ e₄.hom) Φ₃ := by
  apply NatTrans.ext
  funext K
  apply (cancel_mono (tR.hom.app K)).1
  have ht' := congr_app ht K
  have hc₁' := congr_app hc₁ K
  have hc₂' := congr_app hc₂ K
  have hc₃' := congr_app hc₃ (F.obj K)
  have hc₄' := congr_app hc₄ K
  have he' := congr_app he (Φ₀.obj K)
  have hn₁ := tH.hom.naturality (e₁.hom.app K)
  have hn₂ := o₃.hom.naturality (tF.hom.app K)
  dsimp only [Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.comp_map] at ht' hc₁' hc₂' hc₃' hc₄' he' hn₁ hn₂ ⊢
  simp only [Functor.map_comp, Functor.associator_hom_app,
    Category.id_comp, Category.assoc] at he' ⊢
  rw [ht', reassoc_of% hc₂', reassoc_of% hn₁]
  simp only [← Functor.map_comp_assoc]
  rw [hc₁']
  simp only [Functor.map_comp, Category.assoc]
  rw [he', reassoc_of% hn₂, ← reassoc_of% hc₃', ← hc₄']

private def supportCongr {D : FiniteFieldDatum.{u}}
    {B : SixFunctorSpace D → Type*} [∀ X, Category (B X)] (S : SixFunctorPushStage D B)
    {X Y : SixFunctorSpace D} {f f' : X ⟶ Y} (e : f = f')
    (c : Compactification f.hom.left) :
    S.support f c ≅ S.support f'
      (Eq.mp (congrArg (fun t : X ⟶ Y ↦ Compactification t.hom.left) e) c) := by
  subst f'
  exact Iso.refl _

private theorem supportCongr_comparison
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y : SixFunctorSpace D} {f f' : X ⟶ Y} (e : f = f')
    [QuasiCompact f.hom.left] [QuasiCompact f'.hom.left]
    (c : Compactification f.hom.left) :
    letI := c.hasCompactification
    letI := (Eq.mp (congrArg (fun t : X ⟶ Y ↦ Compactification t.hom.left) e) c).hasCompactification
    letI := Padic.finite_coefficientExtensionRing C.l E n hn
    Functor.whiskerRight (supportCongr S.finite e c).hom
        (originInclusion (C := C) (E := E) (n := n) (hn := hn) Y) ≫
      (originSupportComparison S f'
        (Eq.mp (congrArg (fun t : X ⟶ Y ↦ Compactification t.hom.left) e) c)).hom =
    (originSupportComparison S f c).hom ≫
      Functor.whiskerLeft (originInclusion (C := C) (E := E) (n := n) (hn := hn) X)
        (AlgebraicGeometry.ProEtale.originCompactSupportCongr
          (ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n))
          f.hom.left (congrArg (fun t : X ⟶ Y ↦ t.hom.left) e)).hom := by
  subst f'
  simp [supportCongr, AlgebraicGeometry.ProEtale.originCompactSupportCongr]

private theorem supportCongr_cancel
    {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type*}
    [∀ X, Category (B X)] (S : SixFunctorPushStage D B)
    {X Y : SixFunctorSpace D} {f f' : X ⟶ Y} (e : f = f')
    (c : Compactification f.hom.left) (K : B X) {N : B Y}
    (a : (S.support f c).obj K ⟶ N)
    (b : (S.support f'
      (Eq.mp (congrArg (fun t : X ⟶ Y ↦ Compactification t.hom.left) e) c)).obj K ⟶ N)
    (hab : (supportCongr S e c).inv.app K ≫ a = b) : HEq a b := by
  subst f'
  exact heq_of_eq (by simpa [supportCongr] using hab)

private theorem comparison_square_cancel
    {A : Type*} [Category A] {a₀ a₁ b₀ b₁ c₀ c₁ d₀ d₁ e₀ e₁ f₀ f₁ : A}
    (r : a₀ ⟶ a₁) (s : a₁ ⟶ b₁) (s₀ : a₀ ⟶ b₀) (u : b₀ ⟶ b₁)
    (q₁ : b₁ ⟶ c₁) (q₀ : b₀ ⟶ c₀) (v : c₀ ⟶ c₁)
    (p₁ : c₁ ⟶ d₁) (p₀ : c₀ ⟶ d₀) (w : d₀ ⟶ d₁) [Mono w]
    (a₁' : a₁ ⟶ e₁) (a₀' : a₀ ⟶ e₀) (z : e₀ ⟶ e₁)
    (t₁ : e₁ ⟶ f₁) (t₀ : e₀ ⟶ f₀) (x : f₀ ⟶ f₁)
    (b₁' : f₁ ⟶ d₁) (b₀' : f₀ ⟶ d₀)
    (hs : r ≫ s = s₀ ≫ u) (hn : u ≫ q₁ = q₀ ≫ v)
    (hf : v ≫ p₁ = p₀ ≫ w) (ha : r ≫ a₁' = a₀' ≫ z)
    (ht : z ≫ t₁ = t₀ ≫ x) (hb : x ≫ b₁' = b₀' ≫ w)
    (he : s ≫ q₁ ≫ p₁ = a₁' ≫ t₁ ≫ b₁') :
    s₀ ≫ q₀ ≫ p₀ = a₀' ≫ t₀ ≫ b₀' := by
  apply (cancel_mono w).1
  calc
    (s₀ ≫ q₀ ≫ p₀) ≫ w = r ≫ (s ≫ q₁ ≫ p₁) := by
      simp only [Category.assoc]
      rw [reassoc_of% hs, reassoc_of% hn, hf]
    _ = r ≫ (a₁' ≫ t₁ ≫ b₁') := by rw [he]
    _ = (a₀' ≫ t₀ ≫ b₀') ≫ w := by
      simp only [Category.assoc]
      rw [reassoc_of% ha, reassoc_of% ht, hb]

private theorem input_naturality_identity
    {A B Q R : Type*} [Category A] [Category B] [Category Q] [Category R]
    (F : A ⥤ B) (TX : A ⥤ R ⥤ A) (TY : B ⥤ Q ⥤ B) (P : Q ⥤ R)
    {K K' : A} (L : Q) (a : K ⟶ K')
    (q : (TY.obj (F.obj K)).obj L ⟶ F.obj ((TX.obj K).obj (P.obj L)))
    (q' : (TY.obj (F.obj K')).obj L ⟶ F.obj ((TX.obj K').obj (P.obj L)))
    (h : (TY.map (F.map a)).app L ≫ (TY.obj (F.obj K')).map (𝟙 L) ≫ q' =
      q ≫ F.map ((TX.map a).app (P.obj L) ≫ (TX.obj K').map (P.map (𝟙 L)))) :
    (TY.map (F.map a)).app L ≫ q' = q ≫ F.map ((TX.map a).app (P.obj L)) := by
  rw [(TY.obj (F.obj K')).map_id L, Category.id_comp, P.map_id L,
    (TX.obj K').map_id (P.obj L), Category.comp_id] at h
  exact h

section
attribute [local irreducible] partialTensor torPull

private theorem component_square_change
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn)
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf df : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg dfg : Compactification (f ≫ g).hom.left)
    (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left)
    (hs :
      ((partialTensor S Z).map ((S.finite.composition f g df cg dfg).hom.app K)).app L ≫
          component S g cg ((S.finite.support f df).obj K) L ≫
          (S.finite.support g cg).map
            (component S f df K ((torPull S g).obj L)) =
        component S (f ≫ g) dfg K L ≫
          (S.finite.composition f g df cg dfg).hom.app
            (((partialTensor S X).obj K).obj ((torPull S (f ≫ g)).obj L)) ≫
          (S.finite.support g cg).map ((S.finite.support f df).map
            (((partialTensor S X).obj K).map (torPullComposition S f g L).hom))) :
      ((partialTensor S Z).map ((S.finite.composition f g cf cg cfg).hom.app K)).app L ≫
          component S g cg ((S.finite.support f cf).obj K) L ≫
          (S.finite.support g cg).map
            (component S f cf K ((torPull S g).obj L)) =
        component S (f ≫ g) cfg K L ≫
          (S.finite.composition f g cf cg cfg).hom.app
            (((partialTensor S X).obj K).obj ((torPull S (f ≫ g)).obj L)) ≫
          (S.finite.support g cg).map ((S.finite.support f cf).map
            (((partialTensor S X).obj K).map (torPullComposition S f g L).hom)) := by
  let : IsSeparated (f ≫ g).hom.left :=
    inferInstanceAs (IsSeparated (f.hom.left ≫ g.hom.left))
  let : LocallyOfFiniteType (f ≫ g).hom.left :=
    inferInstanceAs (LocallyOfFiniteType (f.hom.left ≫ g.hom.left))
  let : QuasiCompact (f ≫ g).hom.left :=
    inferInstanceAs (QuasiCompact (f.hom.left ≫ g.hom.left))
  let TX := (partialTensor S X).obj K
  let TZ := fun {M N : sixFunctorFiniteCategory D C E n hn Z} (a : M ⟶ N) ↦
    ((partialTensor S Z).map a).app L
  let G := S.finite.support g cg
  let rf := S.finite.comparison f cf df
  let rfg := S.finite.comparison (f ≫ g) cfg dfg
  let c := (torPullComposition S f g L).hom
  let M := TX.obj ((torPull S (f ≫ g)).obj L)
  let N := TX.obj ((torPull S f).obj ((torPull S g).obj L))
  have hc := congrArg Iso.hom (S.finite.composition_comparison
    f g cf df cg cg cfg dfg)
  simp only [Iso.trans_hom, S.finite.comparison_refl, Iso.refl_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_id', Category.comp_id] at hc
  have hcK := congr_app hc K
  have hcM := congr_app hc M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app] at hcK hcM
  have ht := congrArg (fun a ↦ ((partialTensor S Z).map a).app L) hcK
  simp only [Functor.map_comp, NatTrans.comp_app] at ht
  have hn := component_input_naturality S g cg (rf.hom.app K) (𝟙 L)
  have hn' := input_naturality_identity G (partialTensor S Y) (partialTensor S Z)
    (torPull S g) L (rf.hom.app K)
    (component S g cg ((S.finite.support f cf).obj K) L)
    (component S g cg ((S.finite.support f df).obj K) L) hn
  have hf := component_compactification S f cf df K ((torPull S g).obj L)
  have hfg := component_compactification S (f ≫ g) cfg dfg K L
  have hr := rf.hom.naturality (TX.map c)
  exact comparison_square_cancel
    (TZ (rfg.hom.app K))
    (TZ ((S.finite.composition f g df cg dfg).hom.app K))
    (TZ ((S.finite.composition f g cf cg cfg).hom.app K))
    (TZ (G.map (rf.hom.app K)))
    (component S g cg ((S.finite.support f df).obj K) L)
    (component S g cg ((S.finite.support f cf).obj K) L)
    (G.map (((partialTensor S Y).map (rf.hom.app K)).app ((torPull S g).obj L)))
    (G.map (component S f df K ((torPull S g).obj L)))
    (G.map (component S f cf K ((torPull S g).obj L))) (G.map (rf.hom.app N))
    (component S (f ≫ g) dfg K L) (component S (f ≫ g) cfg K L)
    (rfg.hom.app M) ((S.finite.composition f g df cg dfg).hom.app M)
    ((S.finite.composition f g cf cg cfg).hom.app M) (G.map (rf.hom.app M))
    (G.map ((S.finite.support f df).map (TX.map c)))
    (G.map ((S.finite.support f cf).map (TX.map c))) ht
    hn'
    (by simpa only [Functor.map_comp] using congrArg G.map hf) hfg hcM
    (by simpa only [Functor.map_comp] using congrArg G.map hr.symm) hs

end

/-- The composition square and compositor pentagon for the prescribed finite projection.
Source: current blueprint, sec-six-functors/sk-rem-sf-pf-done/
fix-prop-projection-formula.proof.md, composition/coherence sentence; compatible
compactification triangle assembly and the two-counit composition calculation.
(blueprint: lem-sf-finite-projection-composition-transport).

Proof: choose compatible compactifications for f, g and their composite using the
compatible-triangle theorem. Realize K and L in fixed-scalar coordinates. The first
input and its tensor with the pulled-back second input are bounded constructible and
have etale-origin witnesses. finiteCompositionNormalization identifies the actual
operation compositor, through its two support realizations, with the inverse of the
canonical origin compositor. finitePullCompositionNormalization identifies the
pullback comparison, and torPullComposition is its full-subcategory lift.
Use the general cartesianCompactSupportCompositor and compositionProjectionMate
lemmas underlying projectionCompatibleTriangleAssembly: the raw proper/open
triangle map equals the canonical origin compositor on both origin inputs, and
its triangle projection equation holds without a whole operation datum. Substituting
those normalizations gives the displayed composition square.
Compactification refinement compatibility extends it from compatible triangles to
arbitrary cf, cg and cfg. For three maps, the two canonical origin compositor paths
are equal by origin-composition associativity (equivalently associative pasting of
the three proper/open mate calculations). Conjugate by the three support realizations
and use finiteCompositionNormalization twice on each path. The internal realization
units cancel and the equality transport along Category.assoc is precisely the one
in the displayed HEq. No invertibility of a projection component is used. Identity
maps, zero objects and empty schemes satisfy the same equations; the first input
is never required to have finite Tor amplitude. -/
theorem component_composition_coherence
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorFiniteOperations D C E n hn) :
    (∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : sixFunctorFiniteCategory D C E n hn X)
    (L : finiteTorConstructibleCategory C.l E n hn Z.obj.left),
      ((partialTensor S Z).map ((S.finite.composition f g cf cg cfg).hom.app K)).app L ≫
          component S g cg ((S.finite.support f cf).obj K) L ≫
          (S.finite.support g cg).map
            (component S f cf K ((torPull S g).obj L)) =
        component S (f ≫ g) cfg K L ≫
          (S.finite.composition f g cf cg cfg).hom.app
            (((partialTensor S X).obj K).obj ((torPull S (f ≫ g)).obj L)) ≫
          (S.finite.support g cg).map ((S.finite.support f cf).map
            (((partialTensor S X).obj K).map (torPullComposition S f g L).hom))) ∧
    (∀ {X Y Z W : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated h.hom.left] [LocallyOfFiniteType h.hom.left] [QuasiCompact h.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K : sixFunctorFiniteCategory D C E n hn X),
    HEq ((S.finite.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
      (S.finite.support h ch).map ((S.finite.composition f g cf cg cfg).hom.app K))
      ((S.finite.composition f (g ≫ h) cf cgh
        (Eq.mp (congrArg (fun t : X ⟶ W ↦ Compactification t.hom.left)
          (Category.assoc f g h)) cfgh)).hom.app K ≫
        (S.finite.composition g h cg ch cgh).hom.app ((S.finite.support f cf).obj K))) := by
  constructor
  · intro X Y Z f g _ _ _ _ _ _ cf cg cfg K L
    obtain ⟨df, dfg, hs⟩ := exists_component_binary_square S f g cg
    exact component_square_change S f g cf df cg cfg dfg K L (hs K L)
  · intro X Y Z W f g h _ _ _ _ _ _ _ _ _ cf cg ch cfg cgh cfgh K
    let := cf.hasCompactification
    let := cg.hasCompactification
    let := ch.hasCompactification
    let := cfg.hasCompactification
    let := cgh.hasCompactification
    let := cfgh.hasCompactification
    let := Padic.finite_coefficientExtensionRing C.l E n hn
    let : QuasiCompact (f ≫ g).hom.left :=
      inferInstanceAs (QuasiCompact (f.hom.left ≫ g.hom.left))
    let : QuasiCompact (g ≫ h).hom.left :=
      inferInstanceAs (QuasiCompact (g.hom.left ≫ h.hom.left))
    let : QuasiCompact ((f ≫ g) ≫ h).hom.left :=
      inferInstanceAs (QuasiCompact ((f.hom.left ≫ g.hom.left) ≫ h.hom.left))
    let : QuasiCompact (f ≫ (g ≫ h)).hom.left :=
      inferInstanceAs (QuasiCompact (f.hom.left ≫ (g.hom.left ≫ h.hom.left)))
    let c' := Eq.mp (congrArg (fun t : X ⟶ W ↦ Compactification t.hom.left)
      (Category.assoc f g h)) cfgh
    let := c'.hasCompactification
    let : HasCompactification (f.hom.left ≫ g.hom.left) := cfg.hasCompactification
    let : HasCompactification (g.hom.left ≫ h.hom.left) := cgh.hasCompactification
    let : HasCompactification ((f.hom.left ≫ g.hom.left) ≫ h.hom.left) :=
      cfgh.hasCompactification
    let : HasCompactification (f.hom.left ≫ g.hom.left ≫ h.hom.left) :=
      c'.hasCompactification
    let : HasCompactification ((f ≫ g).hom.left ≫ h.hom.left) :=
      cfgh.hasCompactification
    let : HasCompactification (f.hom.left ≫ (g ≫ h).hom.left) :=
      c'.hasCompactification
    let A := ULift.{u + 1} (Padic.coefficientExtensionRing C.l E n)
    let Φ := fun T : SixFunctorSpace D ↦
      originInclusion (C := C) (E := E) (n := n) (hn := hn) T
    have hmap := reflect_associativity (Φ X) (Φ Y) (Φ Z) (Φ W)
      (originSupportComparison S f cf) (originSupportComparison S g cg)
      (originSupportComparison S h ch) (originSupportComparison S (f ≫ g) cfg)
      (originSupportComparison S (g ≫ h) cgh)
      (originSupportComparison S ((f ≫ g) ≫ h) cfgh)
      (originSupportComparison S (f ≫ g ≫ h) c')
      (S.finite.composition f g cf cg cfg).symm
      (S.finite.composition (f ≫ g) h cfg ch cfgh).symm
      (S.finite.composition g h cg ch cgh).symm
      (S.finite.composition f (g ≫ h) cf cgh c').symm
      (supportCongr S.finite (Category.assoc f g h) cfgh)
      (AlgebraicGeometry.ProEtale.originComposition A f.hom.left g.hom.left)
      (AlgebraicGeometry.ProEtale.originComposition A (f ≫ g).hom.left h.hom.left)
      (AlgebraicGeometry.ProEtale.originComposition A g.hom.left h.hom.left)
      (AlgebraicGeometry.ProEtale.originComposition A f.hom.left (g ≫ h).hom.left)
      (AlgebraicGeometry.ProEtale.originCompactSupportCongr A
        ((f ≫ g) ≫ h).hom.left
        (congrArg (fun t : X ⟶ W ↦ t.hom.left) (Category.assoc f g h)))
      (originSupportComparison_composition S f g cf cg cfg)
      (originSupportComparison_composition S (f ≫ g) h cfg ch cfgh)
      (originSupportComparison_composition S g h cg ch cgh)
      (originSupportComparison_composition S f (g ≫ h) cf cgh c')
      (supportCongr_comparison S (Category.assoc f g h) cfgh)
      (AlgebraicGeometry.ProEtale.originComposition_assoc A f.hom.left g.hom.left h.hom.left)
    have : (Φ W).Faithful := by
      constructor
      intro M N a b hab
      apply ObjectProperty.hom_ext
      apply (realization (C := C) (E := E) (n := n) (hn := hn) W).inverse.map_injective
      exact congrArg (fun t ↦ t.hom) hab
    have hi :
        Functor.isoWhiskerRight (S.finite.composition f g cf cg cfg).symm
            (S.finite.support h ch) ≪≫
          (S.finite.composition (f ≫ g) h cfg ch cfgh).symm ≪≫
          supportCongr S.finite (Category.assoc f g h) cfgh =
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (S.finite.support f cf)
            (S.finite.composition g h cg ch cgh).symm ≪≫
          (S.finite.composition f (g ≫ h) cf cgh c').symm := by
      apply Iso.ext
      apply NatTrans.ext
      funext M
      apply (Φ W).map_injective
      exact congr_app hmap M
    have hh := congrArg (fun e ↦ e.inv.app K) hi
    simp only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, NatTrans.comp_app, Functor.associator_inv_app,
      Category.comp_id, Category.assoc] at hh
    exact supportCongr_cancel S.finite (Category.assoc f g h) cfgh K _ _ hh

end WeilConjectures.CompactSupportFiniteProjection

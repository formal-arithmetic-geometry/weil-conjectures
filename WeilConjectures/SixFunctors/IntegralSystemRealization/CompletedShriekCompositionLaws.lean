/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FieldShriekCompositionQcqs
public import WeilConjectures.ProEtaleCoefficients.SixFunctorOperationDatum.SixFunctorOperationDatum
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemExpressionDomain
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportSiteCoherence
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerCompositionMaps
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationSystemRealization
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemCompositorAssociativity
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import WeilConjectures.SixFunctors.IntegralSystemRealization.SystemPushCompositionLaws
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.SystemProperOpenSupport
import WeilConjectures.SixFunctors.IntegralSystemRealization.ConstructibleReductionGood
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.ProperSupportStepBounds
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.OpenSupportStepBounds

/-! # Completed shriek composition laws

Source: blueprint latest, sec-six-functors/sk-thm-sf-compatibility,
fix-prop-coherence, opening sentence; Stacks Project, Tags 0F7B, 0F7C, 0F7D,
0F7J and 0F7K (blueprint: lem-sf-completed-shriek-composition-laws).

The construction and all system identities precede finite evaluation. Realization
uses the recursive normalized comparisons; field passage is raw localization and
inclusion of a common finite coefficient stage. No structural separatedness over k
is imposed in the integral bound or specified-compositor statements.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Quasi-compactness of the open in a compactification of a quasi-compact map.
Source: Stacks 0F7J (blueprint: lem-sf-completed-shriek-composition-laws). -/
instance completedShriekOpenQC {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c : Compactification f) : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance

/-- The specified system compact-support candidate, with no evaluation of its levels.
Source: Stacks 0F7J (blueprint: lem-sf-completed-shriek-composition-laws). -/
def completedShriekF (o : Operations l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : System l E X ⥤ System l E Y :=
  (systemInterpretation l E o).compactSupport f c

/-- Equality transport of exact open extension, retaining its canonical construction.
Source: Stacks 0F7D (blueprint: lem-sf-completed-shriek-composition-laws). -/
def completedShriekOpenCongr (o : Operations l E) {X Y : Scheme.{u}}
    {j k : X ⟶ Y} [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) :
    Operations.shriek l E o j ≅ Operations.shriek l E o k := by
  subst k
  exact Iso.refl _

/-- The actual proper/open interchange followed by the open and proper compositors.
Source: Stacks 0F7J (blueprint: lem-sf-completed-shriek-composition-laws). -/
def completedShriekA {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o) {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) [QuasiCompact T.cf.i] [QuasiCompact T.cg.i]
    [QuasiCompact T.q] :
    completedShriekF l E o T.cf ⋙ completedShriekF l E o T.cg ⟶
      completedShriekF l E o T.cfg :=
  Functor.whiskerLeft (Operations.shriek l E o T.cf.i)
    (Functor.whiskerRight
      (R.properOpen.gamma T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)
      (Operations.push l E o T.cg.g)) ≫
  Functor.whiskerRight
    ((R.compositors.openComp l E T.cf.i T.q).hom ≫
      (completedShriekOpenCongr l E o T.i_q).hom)
    (Operations.push l E o T.p ⋙ Operations.push l E o T.cg.g) ≫
  Functor.whiskerLeft (Operations.shriek l E o T.cfg.i)
    ((R.compositors.pushComp l E T.p T.cg.g).hom ≫
      eqToHom (congrArg (Operations.push l E o) T.p_g))

/-- The unit for proper system image, in the canonical constant-ring coordinates.
Source: Stacks 07A7 (blueprint: lem-sf-completed-shriek-composition-laws). -/
def completedShriekPushId {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o) (X : Scheme.{u}) : Operations.push l E o (𝟙 X) ≅ 𝟭 _ :=
  R.canonicalBridge.push l E (𝟙 X) ≪≫
    ProEtale.SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) X

/-- The identity compactification identifies with the identity functor canonically.
Source: Stacks 0F7K (blueprint: lem-sf-completed-shriek-composition-laws). -/
def completedShriekId {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o) (X : Scheme.{u}) :
    completedShriekF l E o (Compactification.ofIsProper (𝟙 X)) ≅ 𝟭 _ :=
  Functor.isoWhiskerRight
    (R.canonicalBridge.shriek l E (𝟙 X) ≪≫
      ProEtale.SemilinearProperOpen.jId (scalarRings l E) (scalarTransitions l E) X) _ ≪≫
    Functor.leftUnitor _ ≪≫ completedShriekPushId l E R X

/-- Reverse refinement, including the normalized clopen projection in noncartesian squares.
Source: Stacks 0F7B, 0F7J (blueprint: lem-sf-completed-shriek-composition-laws). -/
def completedShriekRefinement {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o) {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} [QuasiCompact c.i] [QuasiCompact d.i]
    (r : c.Refinement d) : completedShriekF l E o d ⟶ completedShriekF l E o c :=
  Functor.whiskerRight
    (Functor.whiskerRight (completedShriekPushId l E R X).inv
      (Operations.shriek l E o d.i) ≫
      R.properOpen.gamma c.i (𝟙 X) r.hom d.i
        (r.i_hom.trans (Category.id_comp d.i).symm))
    (Operations.push l E o d.g) ≫
  Functor.whiskerLeft (Operations.shriek l E o c.i)
    ((R.compositors.pushComp l E r.hom d.g).hom ≫
      eqToHom (congrArg (Operations.push l E o) r.hom_g))

/-- All three intermediate systems for one supplied compactification have the normalized,
constructible, witnessed common cohomology and Tor bounds of the node.
Source: Stacks 0941, 0F7J (blueprint: lem-sf-completed-shriek-composition-laws). -/
def completedShriekDomain (o : Operations l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : System l E X) : Prop :=
  Good l E X M ∧ Good l E c.Z ((Operations.shriek l E o c.i).obj M) ∧
    Good l E Y ((completedShriekF l E o c).obj M)

private theorem completedShriekRefinement_isIso {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (R : Realizations l E D o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (M : System l E X) :
    IsIso ((completedShriekRefinement l E R r).app M) := by
  have := systemProperOpenGammaIsIso l E o D R c.i (𝟙 X) r.hom d.i
    (r.i_hom.trans (Category.id_comp d.i).symm)
  dsimp only [completedShriekRefinement, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

private def completedShriekPushComp {o : Operations l E} (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (w : f ≫ g = fg) :
    Operations.push l E o f ⋙ Operations.push l E o g ≅ Operations.push l E o fg :=
  c.pushComp l E f g ≪≫ eqToIso (congrArg (Operations.push l E o) w)

private theorem completedShriekConjugateTransport
    {A B I : Type*} [Category A] [Category B]
    (L : I → A ⥤ B) (R₀ : I → B ⥤ A) (a : ∀ i, L i ⊣ R₀ i)
    {L' : A ⥤ B} {R' : B ⥤ A} (a' : L' ⊣ R')
    {i j : I} (e : i = j) (d : L i ≅ L') :
    conjugateIsoEquiv a' (a j) (eqToIso (congrArg L e.symm) ≪≫ d) =
      conjugateIsoEquiv a' (a i) d ≪≫ eqToIso (congrArg R₀ e) := by
  cases e
  simp

private theorem completedShriekPushAssocRaw {o : Operations l E}
    (c : Compositors l E o)
    {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (M : System l E X) :
    (Operations.push l E o h).map ((c.pushComp l E f g).hom.app M) ≫
        (c.pushComp l E (f ≫ g) h).hom.app M =
      (c.pushComp l E g h).hom.app ((Operations.push l E o f).obj M) ≫
        (c.pushComp l E f (g ≫ h)).hom.app M ≫
        eqToHom (congrArg (fun k ↦ (Operations.push l E o k).obj M)
          (Category.assoc f g h).symm) := by
  have hp := congrArg Iso.hom (integralSystemCompositorAssociativity l E c f g h)
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom] at hp
  have hh := ProEtale.StrictTower.conjugate_triangle_assoc
    (o.direct h).adj (o.direct g).adj (o.direct f).adj
    (o.direct (g ≫ h)).adj (o.direct (f ≫ g)).adj (o.direct (f ≫ g ≫ h)).adj
    (c.pullComp g h) (c.pullComp f g)
    (eqToIso (congrArg (pull l E) (Category.assoc f g h).symm) ≪≫
      c.pullComp (f ≫ g) h) (c.pullComp f (g ≫ h))
    (by simpa only [Iso.trans_hom, Category.assoc] using hp.symm)
  have ht := congrArg Iso.hom (completedShriekConjugateTransport
    (pull l E) (Operations.push l E o)
    (fun f ↦ (o.direct f).adj) ((o.direct h).adj.comp (o.direct (f ≫ g)).adj)
    (Category.assoc f g h) (c.pullComp (f ≫ g) h))
  simp only [Iso.trans_hom, conjugateIsoEquiv_apply_hom] at ht
  simp only [Iso.trans_hom] at hh
  rw [ht] at hh
  have hm := congr_app hh M
  apply (cancel_mono
    ((eqToIso (congrArg (Operations.push l E o) (Category.assoc f g h))).hom.app M)).mp
  simpa only [Compositors.pushComp, conjugateIsoEquiv_apply_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    eqToIso.hom, eqToIso.inv, eqToHom_app, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, NatTrans.id_app, Category.comp_id] using hm.symm

private theorem completedShriekPushAssoc {o : Operations l E}
    (c : Compositors l E o)
    {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (fg : X ⟶ Z) (gh : Y ⟶ W) (fgh : X ⟶ W)
    (wfg : f ≫ g = fg) (wgh : g ≫ h = gh)
    (wl : fg ≫ h = fgh) (wr : f ≫ gh = fgh) (M : System l E X) :
    (Operations.push l E o h).map
        ((completedShriekPushComp l E c f g fg wfg).hom.app M) ≫
      (completedShriekPushComp l E c fg h fgh wl).hom.app M =
    (completedShriekPushComp l E c g h gh wgh).hom.app
        ((Operations.push l E o f).obj M) ≫
      (completedShriekPushComp l E c f gh fgh wr).hom.app M := by
  subst fg
  subst gh
  subst fgh
  simpa only [completedShriekPushComp, eqToIso_refl, Iso.trans_refl,
    Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app,
    eqToHom_refl, Category.comp_id] using
    completedShriekPushAssocRaw l E c f g h M

private theorem completedShriekVertical {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o)
    {A C E₀ B₀ D₀ F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D₀) (j : E₀ ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E₀) (p₁ : B₀ ⟶ D₀) (p₂ : D₀ ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (r : A ⟶ E₀) (p : B₀ ⟶ F) [IsProper r] [IsProper p]
    (hr : r₁ ≫ r₂ = r) (hp : p₁ ≫ p₂ = p)
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ p = r ≫ j) (M : System l E A) :
    (Operations.shriek l E o j).map
        ((completedShriekPushComp l E R.compositors r₁ r₂ r hr).hom.app M) ≫
      (R.properOpen.gamma k r p j h).app M ≫
      (completedShriekPushComp l E R.compositors p₁ p₂ p hp).inv.app
        ((Operations.shriek l E o k).obj M) =
    (R.properOpen.gamma i r₂ p₂ j h₂).app ((Operations.push l E o r₁).obj M) ≫
      (Operations.push l E o p₂).map ((R.properOpen.gamma k r₁ p₁ i h₁).app M) := by
  subst r
  subst p
  simpa only [completedShriekPushComp, eqToIso_refl, Iso.trans_refl] using
    R.properOpen.vertical k i j r₁ r₂ p₁ p₂ h₁ h₂ h M

private def completedShriekRefinementOpen {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (R : Realizations l E D o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d) (M : System l E X) :
    (Operations.shriek l E o d.i).obj M ⟶
      (Operations.push l E o r.hom).obj ((Operations.shriek l E o c.i).obj M) :=
  (Operations.shriek l E o d.i).map ((completedShriekPushId l E R X).inv.app M) ≫
    (R.properOpen.gamma c.i (𝟙 X) r.hom d.i
      (r.i_hom.trans (Category.id_comp d.i).symm)).app M

private theorem completedShriekRefinementOpen_comp {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (R : Realizations l E D o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e)
    (M : System l E X) :
    completedShriekRefinementOpen l E R (r.comp s) M =
      completedShriekRefinementOpen l E R s M ≫
        (Operations.push l E o s.hom).map (completedShriekRefinementOpen l E R r M) ≫
        (R.compositors.pushComp l E r.hom s.hom).hom.app
          ((Operations.shriek l E o c.i).obj M) := by
  let gr := R.properOpen.gamma c.i (𝟙 X) r.hom d.i
    (r.i_hom.trans (Category.id_comp d.i).symm)
  let gs := R.properOpen.gamma d.i (𝟙 X) s.hom e.i
    (s.i_hom.trans (Category.id_comp e.i).symm)
  let gsr := R.properOpen.gamma c.i (𝟙 X) (r.hom ≫ s.hom) e.i
    ((r.comp s).i_hom.trans (Category.id_comp e.i).symm)
  let k := R.compositors.pushComp l E r.hom s.hom
  have hv :
      (Operations.shriek l E o e.i).map
          ((completedShriekPushComp l E R.compositors (𝟙 X) (𝟙 X) (𝟙 X)
            (Category.id_comp _)).hom.app M) ≫
        gsr.app M ≫ k.inv.app ((Operations.shriek l E o c.i).obj M) =
      gs.app ((Operations.push l E o (𝟙 X)).obj M) ≫
        (Operations.push l E o s.hom).map (gr.app M) := by
    simpa only [completedShriekPushComp, eqToIso_refl, Iso.trans_refl] using
      completedShriekVertical l E R c.i d.i e.i (𝟙 X) (𝟙 X) r.hom s.hom
        (𝟙 X) (r.hom ≫ s.hom) (Category.id_comp _) rfl
        (r.i_hom.trans (Category.id_comp d.i).symm)
        (s.i_hom.trans (Category.id_comp e.i).symm)
        ((r.comp s).i_hom.trans (Category.id_comp e.i).symm) M
  change (Operations.shriek l E o e.i).map
      ((completedShriekPushId l E R X).inv.app M) ≫ gsr.app M =
    ((Operations.shriek l E o e.i).map
      ((completedShriekPushId l E R X).inv.app M) ≫ gs.app M) ≫
      (Operations.push l E o s.hom).map
        ((Operations.shriek l E o d.i).map
          ((completedShriekPushId l E R X).inv.app M) ≫ gr.app M) ≫
      k.hom.app ((Operations.shriek l E o c.i).obj M)
  simp only [Functor.map_comp, Category.assoc]
  have hn := gs.naturality ((completedShriekPushId l E R X).inv.app M)
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  rw [← Category.assoc (gs.app M), ← hn]
  simp only [Category.assoc]
  rw [← Category.assoc (gs.app ((Operations.push l E o (𝟙 X)).obj M)), ← hv]
  have hu := systemPushIdentityPair l E o R.compositors R.canonicalBridge X M
  change (completedShriekPushComp l E R.compositors (𝟙 X) (𝟙 X) (𝟙 X)
    (Category.id_comp _)).hom.app M =
      (Operations.push l E o (𝟙 X)).map ((completedShriekPushId l E R X).hom.app M) at hu
  rw [hu]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← Category.assoc ((Operations.shriek l E o e.i).map
    ((Operations.push l E o (𝟙 X)).map ((completedShriekPushId l E R X).inv.app M)))]
  rw [← Functor.map_comp, ← Functor.map_comp]
  simp

private theorem completedShriekRefinement_comp {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (R : Realizations l E D o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d e : Compactification f} (r : c.Refinement d) (s : d.Refinement e) :
    completedShriekRefinement l E R (r.comp s) =
      completedShriekRefinement l E R s ≫ completedShriekRefinement l E R r := by
  ext M
  change (Operations.push l E o e.g).map
      (completedShriekRefinementOpen l E R (r.comp s) M) ≫
      (completedShriekPushComp l E R.compositors (r.hom ≫ s.hom) e.g c.g
        (r.comp s).hom_g).hom.app ((Operations.shriek l E o c.i).obj M) =
    ((Operations.push l E o e.g).map (completedShriekRefinementOpen l E R s M) ≫
      (completedShriekPushComp l E R.compositors s.hom e.g d.g s.hom_g).hom.app
        ((Operations.shriek l E o d.i).obj M)) ≫
      (Operations.push l E o d.g).map (completedShriekRefinementOpen l E R r M) ≫
      (completedShriekPushComp l E R.compositors r.hom d.g c.g r.hom_g).hom.app
        ((Operations.shriek l E o c.i).obj M)
  rw [completedShriekRefinementOpen_comp l E R r s M]
  simp only [Functor.map_comp, Category.assoc, completedShriekPushComp]
  have hp := completedShriekPushAssoc l E R.compositors
    r.hom s.hom e.g (r.hom ≫ s.hom) d.g c.g rfl s.hom_g (r.comp s).hom_g r.hom_g
      ((Operations.shriek l E o c.i).obj M)
  simp only [completedShriekPushComp, eqToIso_refl, Iso.trans_refl] at hp
  rw [hp]
  have hn := (completedShriekPushComp l E R.compositors s.hom e.g d.g
    s.hom_g).hom.naturality (completedShriekRefinementOpen l E R r M)
  dsimp only [Functor.comp_map] at hn
  simp only [completedShriekPushComp] at hn
  rw [← Category.assoc
    ((R.compositors.pushComp l E s.hom e.g ≪≫
      eqToIso (congrArg (Operations.push l E o) s.hom_g)).hom.app _), ← hn]
  simp only [Category.assoc]

/-- System refinement laws are identities of the actual derived arrows, before evaluation.
Source: Stacks 0F7B--0F7K (blueprint: lem-sf-completed-shriek-composition-laws).

Proof: vertical pasting for identity-left refinement squares, the two-identity
proper compositor normalization, and naturality compose the open comparison factors.
Associativity of the proper compositors then composes the refinements themselves.
Each refinement is invertible by proper/open support. Thus the identity refinement
is an invertible idempotent and equals the identity. For parallel refinements,
precompose with the dense common refinement of the source with itself. The two
resulting scheme maps coincide by separatedness and density; cancel its invertible
comparison. All equations hold before finite evaluation and without domain bounds. -/
theorem completedShriekRefinementLaws (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] :
    (∀ (c : Compactification f) (M : System l E X),
      (completedShriekRefinement l E R (.id c)).app M = 𝟙 _) ∧
    (∀ (c d e : Compactification f) (r : c.Refinement d) (s : d.Refinement e),
      completedShriekRefinement l E R (r.comp s) =
        completedShriekRefinement l E R s ≫ completedShriekRefinement l E R r) ∧
    (∀ (c d : Compactification f) (r : c.Refinement d) (M : System l E X),
      completedShriekDomain l E o c M → completedShriekDomain l E o d M →
        IsIso ((completedShriekRefinement l E R r).app M)) ∧
    (∀ (c d : Compactification f) (r s : c.Refinement d) (M : System l E X),
      completedShriekDomain l E o c M → completedShriekDomain l E o d M →
        (completedShriekRefinement l E R r).app M =
          (completedShriekRefinement l E R s).app M) := by
  have _ := hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c M
    have hi := completedShriekRefinement_isIso l E R (.id c) M
    have h := congr_app (completedShriekRefinement_comp l E R (.id c) (.id c)) M
    have hid : (Compactification.Refinement.id c).comp (.id c) = .id c :=
      Compactification.Refinement.id_comp _
    rw [hid, NatTrans.comp_app] at h
    apply (cancel_mono ((completedShriekRefinement l E R (.id c)).app M)).mp
    simpa only [Category.id_comp] using h.symm
  · intro c d e r s
    exact completedShriekRefinement_comp l E R r s
  · intro c d r M _ _
    exact completedShriekRefinement_isIso l E R r M
  · intro c d r s M _ _
    let k := Compactification.inf c c
    let t : k.Refinement c := Compactification.infFst c c
    have : IsSchemeTheoreticallyDominant k.i :=
      Compactification.isSchemeTheoreticallyDominant_inf_i c c
    have hrs : t.comp r = t.comp s := Subsingleton.elim _ _
    have hi := completedShriekRefinement_isIso l E R t M
    apply (cancel_mono ((completedShriekRefinement l E R t).app M)).mp
    rw [← NatTrans.comp_app, ← NatTrans.comp_app,
      ← completedShriekRefinement_comp l E R t r,
      ← completedShriekRefinement_comp l E R t s, hrs]

section RefinementPasting

private abbrev CompletedShriekPastingData (Obj : Scheme.{u} → Type (u + 2))
    [∀ X, Category.{u + 2} (Obj X)]
    (R : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → Obj X ⥤ Obj Y)
    (J : ∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j], Obj X ⥤ Obj Y) : Type (u + 2) :=
  (∀ X : Scheme.{u}, R (𝟙 X) ≅ 𝟭 (Obj X)) ×
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (_e : f ≫ g = fg), R f ⋙ R g ≅ R fg) ×
  (∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion fg]
    (_e : f ≫ g = fg), J f ⋙ J g ≅ J fg) ×
  (∀ {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (_h : k ≫ p = r ≫ i), R r ⋙ J i ⟶ J k ⋙ R p)

variable {Obj : Scheme.{u} → Type (u + 2)} [∀ X, Category.{u + 2} (Obj X)]
  {R₀ : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → Obj X ⥤ Obj Y}
  {J₀ : ∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j], Obj X ⥤ Obj Y}

private abbrev CompletedShriekPastingData.obj
    (_K : CompletedShriekPastingData.{u} Obj R₀ J₀) (X : Scheme.{u}) := Obj X

private abbrev CompletedShriekPastingData.R
    (_K : CompletedShriekPastingData.{u} Obj R₀ J₀)
    {X Y : Scheme.{u}} (f : X ⟶ Y) := R₀ f

private abbrev CompletedShriekPastingData.J
    (_K : CompletedShriekPastingData.{u} Obj R₀ J₀)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] := J₀ j

private abbrev CompletedShriekPastingData.rId
    (K : CompletedShriekPastingData.{u} Obj R₀ J₀) (X : Scheme.{u}) := K.1 X

private abbrev CompletedShriekPastingData.pComp
    (K : CompletedShriekPastingData.{u} Obj R₀ J₀) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (e : f ≫ g = fg) := K.2.1 f g fg e

private abbrev CompletedShriekPastingData.gamma
    (K : CompletedShriekPastingData.{u} Obj R₀ J₀) {V W S T : Scheme.{u}}
    (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) := K.2.2.2 k r p i h

set_option genSizeOfSpec false in
set_option genInjectivity false in
private structure CompletedShriekPastingLaws
    (K : CompletedShriekPastingData.{u} Obj R₀ J₀) : Prop where
  pAssoc {X Y Z W : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    (fg : X ⟶ Z) (gh : Y ⟶ W) (fgh : X ⟶ W)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hl : fg ≫ h = fgh) (hr : f ≫ gh = fgh) (M : K.obj X) :
    (K.R h).map ((K.pComp f g fg hfg).hom.app M) ≫
        (K.pComp fg h fgh hl).hom.app M =
      (K.pComp g h gh hgh).hom.app ((K.R f).obj M) ≫
        (K.pComp f gh fgh hr).hom.app M
  pRight {X Y : Scheme.{u}} (f : X ⟶ Y) (M : K.obj X) :
    (K.pComp f (𝟙 Y) f (Category.comp_id f)).hom.app M =
      (K.rId Y).hom.app ((K.R f).obj M)
  vertical : ∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : K.obj A),
      (K.J j).map ((K.pComp r₁ r₂ (r₁ ≫ r₂) rfl).hom.app M) ≫
          (K.gamma k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
          (K.pComp p₁ p₂ (p₁ ≫ p₂) rfl).inv.app ((K.J k).obj M) =
        (K.gamma i r₂ p₂ j h₂).app ((K.R r₁).obj M) ≫
          (K.R p₂).map ((K.gamma k r₁ p₁ i h₁).app M)
  horizontal : ∀ {A C E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : K.obj A),
      (K.jCompNamed i j (i ≫ j) rfl).hom.app ((K.R r).obj M) ≫
          (K.gamma (k ≫ l) r q (i ≫ j) h).app M ≫
          (K.R q).map ((K.jCompNamed k l (k ≫ l) rfl).inv.app M) =
        (K.J j).map ((K.gamma k r p i h₁).app M) ≫
          (K.gamma l p q j h₂).app ((K.J k).obj M)

namespace CompletedShriekPasting

private noncomputable def compositionF (K : CompletedShriekPastingData.{u} Obj R₀ J₀)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : K.obj X ⥤ K.obj Y := K.J c.i ⋙ K.R c.g

private noncomputable def compositionD (K : CompletedShriekPastingData.{u} Obj R₀ J₀)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h) [QuasiCompact T.cf.i] [QuasiCompact T.cg.i]
    [QuasiCompact T.q] :
    compositionF K T.cf ⋙ compositionF K T.cg ⟶ compositionF K T.cfg :=
  Functor.whiskerLeft (K.J T.cf.i)
    (Functor.whiskerRight (K.gamma T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)
      (K.R T.cg.g)) ≫
  Functor.whiskerRight (K.jCompNamed T.cf.i T.q T.cfg.i T.i_q).hom
    (K.R T.p ⋙ K.R T.cg.g) ≫
  Functor.whiskerLeft (K.J T.cfg.i) (K.pComp T.p T.cg.g T.cfg.g T.p_g).hom

private noncomputable def compositionC (K : CompletedShriekPastingData.{u} Obj R₀ J₀)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} [QuasiCompact c.i] [QuasiCompact d.i]
    (r : c.Refinement d) : compositionF K d ⟶ compositionF K c :=
  Functor.whiskerRight (Functor.whiskerRight (K.rId X).inv (K.J d.i) ≫
    K.gamma c.i (𝟙 X) r.hom d.i (r.i_hom.trans (Category.id_comp d.i).symm))
      (K.R d.g) ≫
  Functor.whiskerLeft (K.J c.i) (K.pComp r.hom d.g c.g r.hom_g).hom

private noncomputable def compositionH (K : CompletedShriekPastingData.{u} Obj R₀ J₀)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    {T₁ T₂ : Compactification.Triangle f h}
    [QuasiCompact T₁.cf.i] [QuasiCompact T₁.cg.i]
    [QuasiCompact T₂.cf.i] [QuasiCompact T₂.cg.i]
    (r : AlgebraicGeometry.ProEtale.StrictTower.CompositionRefinement T₁ T₂) :
    compositionF K T₂.cf ⋙ compositionF K T₂.cg ⟶
      compositionF K T₁.cf ⋙ compositionF K T₁.cg :=
  Functor.whiskerRight (compositionC K r.rf) (compositionF K T₂.cg) ≫
    Functor.whiskerLeft (compositionF K T₁.cf) (compositionC K r.rh)

private theorem pastingD_app (K : CompletedShriekPastingData.{u} Obj R₀ J₀)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h)
    [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.q]
    (M : K.obj X) :
    (compositionD K T).app M =
      (K.R T.cg.g).map ((K.gamma T.q T.cf.g T.p T.cg.i T.isPullback.w.symm).app
        ((K.J T.cf.i).obj M)) ≫
      (K.R T.cg.g).map ((K.R T.p).map
        ((K.jCompNamed T.cf.i T.q T.cfg.i T.i_q).hom.app M)) ≫
      (K.pComp T.p T.cg.g T.cfg.g T.p_g).hom.app ((K.J T.cfg.i).obj M) := by
  rfl

private theorem pastingC_app (K : CompletedShriekPastingData.{u} Obj R₀ J₀)
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} [QuasiCompact c.i] [QuasiCompact d.i]
    (r : c.Refinement d) (M : K.obj X) :
    (compositionC K r).app M =
      (K.R d.g).map ((K.J d.i).map ((K.rId X).inv.app M) ≫
        (K.gamma c.i (𝟙 X) r.hom d.i
        (r.i_hom.trans (Category.id_comp d.i).symm)).app M) ≫
      (K.pComp r.hom d.g c.g r.hom_g).hom.app ((K.J c.i).obj M) := by
  rfl

private theorem refinement (K : CompletedShriekPastingData.{u} Obj R₀ J₀)
    (L : CompletedShriekPastingLaws K)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T S : Compactification.Triangle f h)
    [QuasiCompact T.cf.i] [QuasiCompact T.cg.i] [QuasiCompact T.cfg.i]
    [QuasiCompact T.q]
    [QuasiCompact S.cf.i] [QuasiCompact S.cg.i] [QuasiCompact S.cfg.i]
    [QuasiCompact S.q] (r : AlgebraicGeometry.ProEtale.StrictTower.CompositionRefinement S T) :
    compositionD K T ≫ compositionC K r.rfh =
      compositionH K r ≫ compositionD K S := by
  let U := T.cf.Z
  let V := T.cfg.Z
  let C0 := T.cg.Z
  let U' := S.cf.Z
  let V' := S.cfg.Z
  let B' := S.cg.Z
  let ga := K.gamma S.cf.i (𝟙 X) r.rf.hom T.cf.i
    (r.rf.i_hom.trans (Category.id_comp _).symm)
  let gd := K.gamma S.cg.i (𝟙 Y) r.rh.hom T.cg.i
    (r.rh.i_hom.trans (Category.id_comp _).symm)
  let ge := K.gamma S.cfg.i (𝟙 X) r.rfh.hom T.cfg.i
    (r.rfh.i_hom.trans (Category.id_comp _).symm)
  let gf := K.gamma S.q r.rf.hom r.rfh.hom T.q r.b_comm
  let gb := K.gamma T.q T.cf.g T.p T.cg.i T.isPullback.w.symm
  let gc := K.gamma S.q S.cf.g S.p S.cg.i S.isPullback.w.symm
  let aT := K.jCompNamed T.cf.i T.q T.cfg.i T.i_q
  let ar := K.jCompNamed S.cf.i S.q S.cfg.i S.i_q
  let pt := K.pComp r.rf.hom T.cf.g S.cf.g r.rf.hom_g
  let kh := K.pComp r.rfh.hom T.p (r.rfh.hom ≫ T.p) rfl
  let kd := K.pComp S.p r.rh.hom (r.rfh.hom ≫ T.p) r.p_comm.symm
  let gg := K.gamma S.q S.cf.g (r.rfh.hom ≫ T.p) T.cg.i
    (by rw [r.p_comm, ← Category.assoc, S.isPullback.w.symm,
      Category.assoc, r.rh.i_hom])
  have hh (M : K.obj X) :
      aT.hom.app ((K.R (𝟙 X)).obj M) ≫ ge.app M ≫
        (K.R r.rfh.hom).map (ar.inv.app M) =
      (K.J T.q).map (ga.app M) ≫ gf.app ((K.J S.cf.i).obj M) := by
    have hh₀ := L.horizontal S.cf.i S.q T.cf.i T.q
      (𝟙 X) r.rf.hom r.rfh.hom
      (r.rf.i_hom.trans (Category.id_comp _).symm) r.b_comm
      (by rw [Category.assoc, r.b_comm, ← Category.assoc, r.rf.i_hom,
        Category.id_comp]) M
    have transport (i : X ⟶ V) (j : X ⟶ V')
        [IsOpenImmersion i] [QuasiCompact i] [IsOpenImmersion j] [QuasiCompact j]
        (hi : T.cf.i ≫ T.q = i) (hj : S.cf.i ≫ S.q = j) :
        (K.jCompNamed T.cf.i T.q i hi).hom.app ((K.R (𝟙 X)).obj M) ≫
          (K.gamma j (𝟙 X) r.rfh.hom i
            (by rw [← hi, ← hj, Category.assoc, r.b_comm,
              ← Category.assoc, r.rf.i_hom, Category.id_comp])).app M ≫
          (K.R r.rfh.hom).map
            ((K.jCompNamed S.cf.i S.q j hj).inv.app M) =
        (K.J T.q).map (ga.app M) ≫
          gf.app ((K.J S.cf.i).obj M) := by
      subst i
      subst j
      simpa only [ga, gf] using hh₀
    exact transport T.cfg.i S.cfg.i T.i_q S.i_q
  have hv₁ (N : K.obj U') :
      (K.J T.cg.i).map (pt.hom.app N) ≫ gg.app N ≫
        kh.inv.app ((K.J S.q).obj N) =
      gb.app ((K.R r.rf.hom).obj N) ≫
        (K.R T.p).map (gf.app N) := by
    have hv₀ := L.vertical S.q T.q T.cg.i r.rf.hom T.cf.g
      r.rfh.hom T.p r.b_comm T.isPullback.w.symm
      (by rw [← Category.assoc, r.b_comm, Category.assoc,
        T.isPullback.w.symm, Category.assoc]) N
    have transport (p : U' ⟶ Y) [IsProper p] (hp : r.rf.hom ≫ T.cf.g = p) :
        (K.J T.cg.i).map ((K.pComp r.rf.hom T.cf.g p hp).hom.app N) ≫
          (K.gamma S.q p (r.rfh.hom ≫ T.p) T.cg.i
            (by rw [← hp, ← Category.assoc, r.b_comm, Category.assoc,
              T.isPullback.w.symm, Category.assoc])).app N ≫
          kh.inv.app ((K.J S.q).obj N) =
        gb.app ((K.R r.rf.hom).obj N) ≫
          (K.R T.p).map (gf.app N) := by
      subst p
      simpa only [kh, gb, gf] using hv₀
    exact transport S.cf.g r.rf.hom_g
  have hv₂ (N : K.obj U') :
      (K.J T.cg.i).map ((K.rId Y).hom.app ((K.R S.cf.g).obj N)) ≫
          gg.app N ≫ kd.inv.app ((K.J S.q).obj N) =
        gd.app ((K.R S.cf.g).obj N) ≫
          (K.R r.rh.hom).map (gc.app N) := by
    have hv₀ := L.vertical S.q S.cg.i T.cg.i S.cf.g (𝟙 Y)
      S.p r.rh.hom S.isPullback.w.symm
      (r.rh.i_hom.trans (Category.id_comp _).symm)
      (by rw [← Category.assoc, S.isPullback.w.symm, Category.assoc,
        r.rh.i_hom, Category.comp_id]) N
    have transport (p : U' ⟶ Y) (q : V' ⟶ C0)
        [IsProper p] [IsProper q] (hp : S.cf.g ≫ 𝟙 Y = p)
        (hq : S.p ≫ r.rh.hom = q) :
        (K.J T.cg.i).map
            ((K.pComp S.cf.g (𝟙 Y) p hp).hom.app N) ≫
          (K.gamma S.q p q T.cg.i
            (by rw [← hp, ← hq, ← Category.assoc, S.isPullback.w.symm,
              Category.assoc, r.rh.i_hom, Category.comp_id])).app N ≫
          (K.pComp S.p r.rh.hom q hq).inv.app ((K.J S.q).obj N) =
        gd.app ((K.R S.cf.g).obj N) ≫
          (K.R r.rh.hom).map (gc.app N) := by
      subst p
      subst q
      exact hv₀
    simpa only [gg, kd, gd, gc, L.pRight] using
      transport S.cf.g (r.rfh.hom ≫ T.p) (Category.comp_id _) r.p_comm.symm
  let ta (M : K.obj X) := (K.J T.cf.i).map ((K.rId X).inv.app M) ≫ ga.app M
  let td (N : K.obj Y) := (K.J T.cg.i).map ((K.rId Y).inv.app N) ≫ gd.app N
  let te (M : K.obj X) := (K.J T.cfg.i).map ((K.rId X).inv.app M) ≫ ge.app M
  have hh' (M : K.obj X) :
      aT.hom.app M ≫ te M =
        (K.J T.q).map (ta M) ≫ gf.app ((K.J S.cf.i).obj M) ≫
          (K.R r.rfh.hom).map (ar.hom.app M) := by
    have hh₁ : aT.hom.app M ≫ te M ≫
        (K.R r.rfh.hom).map (ar.inv.app M) =
        (K.J T.q).map (ta M) ≫ gf.app ((K.J S.cf.i).obj M) := by
      dsimp only [te, ta]
      have hn := aT.hom.naturality ((K.rId X).inv.app M)
      dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn
      simp only [← Category.assoc]
      rw [← hn]
      simp only [Category.assoc]
      rw [hh]
      simp only [Functor.map_comp, Category.assoc]
    apply (cancel_mono ((K.R r.rfh.hom).map (ar.inv.app M))).mp
    simpa only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      Functor.comp_obj, CategoryTheory.Functor.map_id, Category.comp_id] using hh₁
  have hv₂' (N : K.obj U') :
      gg.app N = td ((K.R S.cf.g).obj N) ≫
        (K.R r.rh.hom).map (gc.app N) ≫
          kd.hom.app ((K.J S.q).obj N) := by
    apply (cancel_epi ((K.J T.cg.i).map
      ((K.rId Y).hom.app ((K.R S.cf.g).obj N)))).mp
    apply (cancel_mono (kd.inv.app ((K.J S.q).obj N))).mp
    dsimp only [td]
    simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
      Functor.id_obj, CategoryTheory.Functor.map_id, Category.id_comp]
    simpa only [Category.assoc] using hv₂ N
  have hv (N : K.obj U') :
      gb.app ((K.R r.rf.hom).obj N) ≫
        (K.R T.p).map (gf.app N) ≫
          kh.hom.app ((K.J S.q).obj N) =
      (K.J T.cg.i).map (pt.hom.app N) ≫ td ((K.R S.cf.g).obj N) ≫
        (K.R r.rh.hom).map (gc.app N) ≫
          kd.hom.app ((K.J S.q).obj N) := by
    rw [← hv₂']
    apply (cancel_mono (kh.inv.app ((K.J S.q).obj N))).mp
    simp only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
      Category.comp_id]
    exact (hv₁ N).symm
  have core (M : K.obj X) :
      gb.app ((K.J T.cf.i).obj M) ≫
        (K.R T.p).map (aT.hom.app M) ≫ (K.R T.p).map (te M) ≫
          kh.hom.app ((K.J S.cfg.i).obj M) =
      (K.J T.cg.i).map ((K.R T.cf.g).map (ta M)) ≫
        (K.J T.cg.i).map (pt.hom.app ((K.J S.cf.i).obj M)) ≫
        td ((K.R S.cf.g).obj ((K.J S.cf.i).obj M)) ≫
        (K.R r.rh.hom).map (gc.app ((K.J S.cf.i).obj M)) ≫
        (K.R r.rh.hom).map ((K.R S.p).map (ar.hom.app M)) ≫
          kd.hom.app ((K.J S.cfg.i).obj M) := by
    rw [← Category.assoc ((K.R T.p).map _), ← Functor.map_comp, hh']
    simp only [Functor.map_comp, Category.assoc]
    have hn := gb.naturality (ta M)
    have hk := kh.hom.naturality (ar.hom.app M)
    have hd := kd.hom.naturality (ar.hom.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hn hk hd
    rw [← Category.assoc (gb.app _), ← hn]
    simp only [Category.assoc]
    rw [hk]
    rw [hd]
    simpa only [Category.assoc] using congrArg
      (fun k ↦ (K.J T.cg.i).map ((K.R T.cf.g).map (ta M)) ≫ k ≫
        (K.R (r.rfh.hom ≫ T.p)).map (ar.hom.app M))
      (hv ((K.J S.cf.i).obj M))
  let l := K.pComp T.p T.cg.g T.cfg.g T.p_g
  let m := K.pComp r.rfh.hom T.cfg.g S.cfg.g r.rfh.hom_g
  let n := K.pComp r.rh.hom T.cg.g S.cg.g r.rh.hom_g
  let o := K.pComp S.p S.cg.g S.cfg.g S.p_g
  let z := K.pComp (r.rfh.hom ≫ T.p) T.cg.g S.cfg.g
    (by rw [Category.assoc, T.p_g, r.rfh.hom_g])
  ext M
  unfold compositionH
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, pastingD_app, pastingC_app, compositionF,
    Functor.comp_map, Functor.comp_obj, Functor.map_comp, Category.assoc]
  change
    (K.R T.cg.g).map (gb.app ((K.J T.cf.i).obj M)) ≫
      (K.R T.cg.g).map ((K.R T.p).map (aT.hom.app M)) ≫
      l.hom.app ((K.J T.cfg.i).obj M) ≫
      (K.R T.cfg.g).map ((K.J T.cfg.i).map ((K.rId X).inv.app M)) ≫
      (K.R T.cfg.g).map (ge.app M) ≫
      m.hom.app ((K.J S.cfg.i).obj M) =
    (K.R T.cg.g).map ((K.J T.cg.i).map
      ((K.R T.cf.g).map ((K.J T.cf.i).map ((K.rId X).inv.app M)))) ≫
      (K.R T.cg.g).map ((K.J T.cg.i).map
        ((K.R T.cf.g).map (ga.app M))) ≫
      (K.R T.cg.g).map ((K.J T.cg.i).map
        (pt.hom.app ((K.J S.cf.i).obj M))) ≫
      (K.R T.cg.g).map ((K.J T.cg.i).map
        ((K.rId Y).inv.app ((K.R S.cf.g).obj ((K.J S.cf.i).obj M)))) ≫
      (K.R T.cg.g).map
        (gd.app ((K.R S.cf.g).obj ((K.J S.cf.i).obj M))) ≫
      n.hom.app ((K.J S.cg.i).obj
        ((K.R S.cf.g).obj ((K.J S.cf.i).obj M))) ≫
      (K.R S.cg.g).map (gc.app ((K.J S.cf.i).obj M)) ≫
      (K.R S.cg.g).map ((K.R S.p).map (ar.hom.app M)) ≫
      o.hom.app ((K.J S.cfg.i).obj M)
  have hn₁ := n.hom.naturality (gc.app ((K.J S.cf.i).obj M))
  have hn₂ := n.hom.naturality ((K.R S.p).map (ar.hom.app M))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn₁ hn₂
  rw [← Category.assoc (n.hom.app _), ← hn₁]
  simp only [Category.assoc]
  rw [← Category.assoc (n.hom.app _), ← hn₂]
  simp only [Category.assoc]
  rw [← L.pAssoc S.p r.rh.hom T.cg.g (r.rfh.hom ≫ T.p) S.cg.g
    S.cfg.g r.p_comm.symm r.rh.hom_g
    (by rw [Category.assoc, T.p_g, r.rfh.hom_g]) S.p_g]
  rw [← Category.assoc ((K.R T.cfg.g).map _), ← Functor.map_comp]
  change
    (K.R T.cg.g).map (gb.app ((K.J T.cf.i).obj M)) ≫
      (K.R T.cg.g).map ((K.R T.p).map (aT.hom.app M)) ≫
      l.hom.app ((K.J T.cfg.i).obj M) ≫
      (K.R T.cfg.g).map (te M) ≫ m.hom.app ((K.J S.cfg.i).obj M) = _
  have hl := l.hom.naturality (te M)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hl
  rw [← Category.assoc (l.hom.app _), ← hl]
  simp only [Category.assoc]
  rw [← L.pAssoc r.rfh.hom T.p T.cg.g (r.rfh.hom ≫ T.p) T.cfg.g
    S.cfg.g rfl T.p_g (by rw [Category.assoc, T.p_g, r.rfh.hom_g]) r.rfh.hom_g]
  simp only [← Category.assoc]
  apply (cancel_mono (z.hom.app ((K.J S.cfg.i).obj M))).mpr
  simp only [← Functor.map_comp]
  congr 1
  simpa only [ta, td, Category.assoc, Functor.map_comp] using core M

end CompletedShriekPasting

end RefinementPasting

/-- Proper/open/compact-support words, allowing arbitrary nesting and input families.
Tensor and pullback contexts retain the expressly stated admissibility hypotheses.
Source: blueprint fix-prop-coherence (blueprint: lem-sf-completed-shriek-composition-laws). -/
def Expression.isSupportWord {B : Scheme.{u}} {I : Type u} {X : I → Over B}
    {W : Over B} : Expression B I X W → Prop
  | .var _ => True
  | .push _ _ e => e.isSupportWord
  | .shriek _ _ _ e => e.isSupportWord
  | .compactSupport _ _ e => e.isSupportWord
  | .pull _ _ => False
  | .tensor _ _ => False

private theorem completedShriekGeometricRoot {B : Scheme.{u}} {I : Type u}
    {X : I → Over B} {W : Over B} (e : Expression B I X W) (he : e.geometric) :
    LocallyOfFiniteType W.hom ∧ QuasiCompact W.hom := by
  cases e <;> exact ⟨he.1, he.2.1⟩

/-- Integral compact-support words have all uniform intermediate bounds automatically.
Structural separatedness over k is not a hypothesis.
Source: Stacks 0F10, 0941 (blueprint: lem-sf-completed-shriek-composition-laws).

Proof: the residue-field Tor lemma supplies initial common Tor intervals from the
first reduction. Cover each finite-type target by finitely many affines. Over each
chart every separated finite-type letter has separated finite-type source over k.
Proper restriction and the arbitrary-finite-ring bound give [a,b+2d] uniformly in
n; exact open extension and its normalized tensor comparison preserve [a,b]. Take
minimum lower and maximum upper endpoints on each finite cover and use finite-cover
CTF locality. Integral open reduction and complete proper-image reduction identify
each intermediate system with the reduction of the corresponding complete expression.
Iterate over the finitely many letters. Empty covers have zero objects and interval
[0,0]. No intersections of affines are asserted affine, and no scheme is assumed
separated over k. -/
theorem completedShriekIntegralBounds (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))} (e : Expression _ I X W)
    (ge : e.geometric) (he : e.isSupportWord) (K : ∀ i, Integral l E (X i).left)
    (hK : ∀ i, sfIntegralConstructible l E (X i).left (K i)) :
    e.domain l E o K ∧
      sfIntegralConstructible l E W.left
        ((e.evaluate (integralInterpretation l E)).obj K) := by
  have _ := R
  have initial (i : I) := constructibleReduction_good l E D hl (X i) (K i) (hK i)
  have inputDomain : ∀ i, sfIntegralConstructible l E (X i).left (K i) ∧
      Good l E (X i).left ((calculus l E (X i).left).reduction.obj (K i)) :=
    fun i ↦ ⟨hK i, initial i⟩
  have bounds : e.admissible l E o ((inputReduction l E X).obj K) ∧
      sfIntegralConstructible l E W.left
        ((e.evaluate (integralInterpretation l E)).obj K) := by
    induction e with
    | var i => exact ⟨⟨initial i, trivial⟩, hK i⟩
    | pull f e ih => exact False.elim he
    | tensor e t ihe iht => exact False.elim he
    | @push U V f hp e ih =>
      have h := ih ge.2.2 he
      have : IsProper f.left := hp
      have : LocallyOfFiniteType U.hom := (completedShriekGeometricRoot e ge.2.2).1
      have : QuasiCompact U.hom := (completedShriekGeometricRoot e ge.2.2).2
      have : LocallyOfFiniteType V.hom := ge.1
      have : QuasiCompact V.hom := ge.2.1
      obtain ⟨hs, hk⟩ := properSupportStep_bounds l E D hl o f
        (e.systemObj l E o ((inputReduction l E X).obj K))
        (e.admissibleGood l E o _ h.1)
        ((e.evaluate (integralInterpretation l E)).obj K) h.2
      exact ⟨⟨hs, h.1⟩, hk⟩
    | @shriek U V j hj hq e ih =>
      have h := ih ge.2.2 he
      have : IsOpenImmersion j.left := hj
      have : QuasiCompact j.left := hq
      have : LocallyOfFiniteType U.hom := (completedShriekGeometricRoot e ge.2.2).1
      have : QuasiCompact U.hom := (completedShriekGeometricRoot e ge.2.2).2
      have : LocallyOfFiniteType V.hom := ge.1
      have : QuasiCompact V.hom := ge.2.1
      obtain ⟨hs, hk⟩ := openSupportStep_bounds l E D hl o j
        (e.systemObj l E o ((inputReduction l E X).obj K))
        (e.admissibleGood l E o _ h.1)
        ((e.evaluate (integralInterpretation l E)).obj K) h.2
      exact ⟨⟨hs, h.1⟩, hk⟩
    | @compactSupport U V f c e ih =>
      have h := ih ge.2.2.2.2.2 he
      have : QuasiCompact f.left := ge.2.2.2.2.1
      have : QuasiCompact c.i := completedShriekOpenQC c
      have : LocallyOfFiniteType U.hom :=
        (completedShriekGeometricRoot e ge.2.2.2.2.2).1
      have : QuasiCompact U.hom := (completedShriekGeometricRoot e ge.2.2.2.2.2).2
      have : LocallyOfFiniteType V.hom := ge.1
      have : QuasiCompact V.hom := ge.2.1
      have : LocallyOfFiniteType (compactAmbient (f := f) c).hom :=
        inferInstanceAs (LocallyOfFiniteType (c.g ≫ V.hom))
      have : QuasiCompact (compactAmbient (f := f) c).hom :=
        inferInstanceAs (QuasiCompact (c.g ≫ V.hom))
      have : IsOpenImmersion (compactOpen (f := f) c).left :=
        inferInstanceAs (IsOpenImmersion c.i)
      have : QuasiCompact (compactOpen (f := f) c).left :=
        inferInstanceAs (QuasiCompact c.i)
      have : IsProper (compactProper (f := f) c).left :=
        inferInstanceAs (IsProper c.g)
      obtain ⟨hs, hk⟩ := openSupportStep_bounds l E D hl o (compactOpen (f := f) c)
        (e.systemObj l E o ((inputReduction l E X).obj K))
        (e.admissibleGood l E o _ h.1)
        ((e.evaluate (integralInterpretation l E)).obj K) h.2
      obtain ⟨hs', hk'⟩ := properSupportStep_bounds l E D hl o
        (compactProper (f := f) c)
        ((Operations.shriek l E o c.i).obj
          (e.systemObj l E o ((inputReduction l E X).obj K))) hs
        ((ringedOpen l E c.i).obj
          ((e.evaluate (integralInterpretation l E)).obj K)) hk
      exact ⟨⟨hs', h.1, hs⟩, hk'⟩
  exact ⟨⟨inputDomain, bounds.1⟩, bounds.2⟩

section SpecifiedFieldComponents

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (o : Operations l E) (R : Realizations l E D o)
  {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
  {U V W : Over (Spec (CommRingCat.of D.k))}
  [LocallyOfFiniteType (U.left ↘ Spec (.of D.k))]
  [QuasiCompact (U.left ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (V.left ↘ Spec (.of D.k))]
  [QuasiCompact (V.left ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (W.left ↘ Spec (.of D.k))]
  [QuasiCompact (W.left ↘ Spec (.of D.k))]
  (f : U ⟶ V) (g : V ⟶ W)
  [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
  [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
  (d : Compactification g.left) (c : Compactification (f.left ≫ d.i))
  (e : Expression _ I X U)
  (ge : (Expression.compactSupport g d (.compactSupport f c.restrict e)).geometric)
  (gt : (Expression.compactSupport (f ≫ g) (d.comp c) e).geometric)
  (K : ∀ i, Integral l E (X i).left)
  (he : (Expression.compactSupport g d (.compactSupport f c.restrict e)).domain l E o K)
  (ht : (Expression.compactSupport (f ≫ g) (d.comp c) e).domain l E o K)
  (hK : sfIntegralConstructible l E U.left
    ((e.evaluate (integralInterpretation l E)).obj K))

end SpecifiedFieldComponents

section SpecifiedCommonStageComponents

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
  {U V W : Over (Spec (CommRingCat.of D.k))}
  [LocallyOfFiniteType (U.left ↘ Spec (.of D.k))]
  [QuasiCompact (U.left ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (V.left ↘ Spec (.of D.k))]
  [QuasiCompact (V.left ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (W.left ↘ Spec (.of D.k))]
  [QuasiCompact (W.left ↘ Spec (.of D.k))]
  (f : U ⟶ V) (g : V ⟶ W)
  [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
  [IsSeparated g.left] [LocallyOfFiniteType g.left] [QuasiCompact g.left]
  (d : Compactification g.left) (c : Compactification (f.left ≫ d.i))
  (Sf : SfCompactSupportCoefficientAction l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) Ω c.restrict)
  (Sg : SfCompactSupportCoefficientAction l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) Ω d)
  (Sfg : SfCompactSupportCoefficientAction l D.k
    (PurCompactSupport.coefficientPrimeUnit l D hl) Ω (d.comp c))

end SpecifiedCommonStageComponents

end WeilConjectures.IntegralSystemRealization

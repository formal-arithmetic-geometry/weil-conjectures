module

public import Sheaf.Paper.FieldShriekCompositionQcqs
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.SixFunctors.IntegralSystemOperations
public import Sheaf.SixFunctors.IntegralSystemExpressionDomain
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.CompactSupportSiteCoherence
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps
public import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.SixFunctors.IntegralSystemCompositorAssociativity
import all Sheaf.AlgebraicGeometry.StrictTowerDirectImageCoherence
import Sheaf.SixFunctors.SystemPushCompositionLaws
import Sheaf.SixFunctors.SystemProperOpenSupport
import Sheaf.SixFunctors.ConstructibleReductionGood
import Sheaf.SixFunctors.ProperSupportStepBounds
import Sheaf.SixFunctors.OpenSupportStepBounds

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

/-- Use a compatible tower with the named source and target compactifications. The
only extra arrows are equality transports of the three given compactifications.
Source: Stacks 0F7J (blueprint: lem-sf-completed-shriek-composition-laws). -/
def completedShriekAOn {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o) {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (T : Compactification.Triangle f g) [QuasiCompact T.cf.i] [QuasiCompact T.cg.i]
    [QuasiCompact T.q] (hf : cf = T.cf) (hg : cg = T.cg) (hfg : T.cfg = cfg) :
    completedShriekF l E o cf ⋙ completedShriekF l E o cg ⟶ completedShriekF l E o cfg :=
  eqToHom (congrArg₂ (fun a b ↦ completedShriekF l E o a ⋙ completedShriekF l E o b)
    hf hg) ≫ completedShriekA l E R T ≫ eqToHom (congrArg (completedShriekF l E o) hfg)

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

private theorem rightUnitOfIdentityPair {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (S : D ⥤ D) (u : S ≅ 𝟭 D) (a : F ⋙ S ≅ F)
    (b : S ⋙ S ≅ S)
    (ha : ∀ M, S.map (a.hom.app M) ≫ a.hom.app M =
      b.hom.app (F.obj M) ≫ a.hom.app M)
    (hb : ∀ N, b.hom.app N = S.map (u.hom.app N)) (M : C) :
    a.hom.app M = u.hom.app (F.obj M) := by
  have hh := (cancel_mono (a.hom.app M)).mp (ha M)
  rw [hb] at hh
  have hn := u.hom.naturality (a.hom.app M)
  have hn' := u.hom.naturality (u.hom.app (F.obj M))
  dsimp only [Functor.id_map] at hn hn'
  rw [hh] at hn
  exact (cancel_epi (u.hom.app (S.obj (F.obj M)))).mp (hn.symm.trans hn')

private theorem completedShriekPushRight {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (R : Realizations l E D o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : System l E X) :
    (completedShriekPushComp l E R.compositors f (𝟙 Y) f
      (Category.comp_id f)).hom.app M =
      (completedShriekPushId l E R Y).hom.app ((Operations.push l E o f).obj M) := by
  exact rightUnitOfIdentityPair (Operations.push l E o f)
    (Operations.push l E o (𝟙 Y)) (completedShriekPushId l E R Y)
    (completedShriekPushComp l E R.compositors f (𝟙 Y) f (Category.comp_id f))
    (completedShriekPushComp l E R.compositors (𝟙 Y) (𝟙 Y) (𝟙 Y) (Category.id_comp _))
    (fun N ↦ completedShriekPushAssoc l E R.compositors f (𝟙 Y) (𝟙 Y) f (𝟙 Y) f
      (Category.comp_id _) (Category.id_comp _) (Category.comp_id _) (Category.comp_id _) N)
    (systemPushIdentityPair l E o R.compositors R.canonicalBridge Y) M

private def completedShriekOpenComp {o : Operations l E} (c : Compositors l E o)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion fg]
    (h : f ≫ g = fg) :
    Operations.shriek l E o f ⋙ Operations.shriek l E o g ≅
      Operations.shriek l E o fg :=
  c.openComp l E f g ≪≫ completedShriekOpenCongr l E o h

-- The A--F calculation is parametric in its categories and functors, keeping
-- the derived coefficient-site constructions folded at every naturality step.
-- The private calculation only needs the universe of the actual system categories.
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

private abbrev CompletedShriekPastingData.jCompNamed
    (K : CompletedShriekPastingData.{u} Obj R₀ J₀) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion fg]
    (e : f ≫ g = fg) := K.2.2.1 f g fg e

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

private def completedShriekPasting {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (z : Realizations l E D o) :
    CompletedShriekPastingData (System l E) (Operations.push l E o)
      (Operations.shriek l E o) :=
  ⟨completedShriekPushId l E z, completedShriekPushComp l E z.compositors,
    completedShriekOpenComp l E z.compositors, z.properOpen.gamma⟩

private theorem completedShriekPasting_laws {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (z : Realizations l E D o) :
    CompletedShriekPastingLaws (completedShriekPasting l E z) where
  pAssoc := completedShriekPushAssoc l E z.compositors
  pRight := completedShriekPushRight l E z
  vertical := by
    intro A C E₀ B₀ D₀ F k i j r₁ r₂ p₁ p₂ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
    simpa only [completedShriekPasting, CompletedShriekPastingData.obj,
      CompletedShriekPastingData.R,
      CompletedShriekPastingData.J, CompletedShriekPastingData.rId,
      CompletedShriekPastingData.pComp, CompletedShriekPastingData.jCompNamed,
      CompletedShriekPastingData.gamma, completedShriekPushComp,
      eqToIso_refl, Iso.trans_refl] using
      z.properOpen.vertical k i j r₁ r₂ p₁ p₂ h₁ h₂ h M
  horizontal := by
    intro A C E₀ B₀ D₀ F k ll i j r p q _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
    simpa only [completedShriekPasting, CompletedShriekPastingData.obj,
      CompletedShriekPastingData.R,
      CompletedShriekPastingData.J, CompletedShriekPastingData.rId,
      CompletedShriekPastingData.pComp, CompletedShriekPastingData.jCompNamed,
      CompletedShriekPastingData.gamma, completedShriekOpenComp,
      completedShriekOpenCongr, Iso.trans_refl] using
      z.properOpen.horizontal k ll i j r p q h₁ h₂ h M

/-- Refinement of composition towers, including noncartesian intermediate faces.
Source: Stacks 0F7J (blueprint: lem-sf-completed-shriek-composition-laws).

Proof: let A,B,C,D,E,F be the six squares in proof step 3 of the node. Horizontal
pasting gives Gamma_E = Gamma_F Gamma_A and vertical pasting gives
Gamma_C Gamma_D = Gamma_F Gamma_B. Naturality commutes the disjoint Gamma_A and
Gamma_B. Substitute these equalities and the proper/open compositors to obtain the
reverse refinement equation below. Invertible comparisons and common refining
towers then give choice independence and the forward refinement square. -/
theorem completedShriekTowerRefinement (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (T₁ T₂ : Compactification.Triangle f g) [QuasiCompact T₁.q] [QuasiCompact T₂.q]
    (r : AlgebraicGeometry.ProEtale.StrictTower.CompositionRefinement T₁ T₂) :
    completedShriekA l E R T₂ ≫ completedShriekRefinement l E R r.rfh =
      Functor.whiskerRight (completedShriekRefinement l E R r.rf)
        (completedShriekF l E o T₂.cg) ≫
      Functor.whiskerLeft (completedShriekF l E o T₁.cf)
        (completedShriekRefinement l E R r.rh) ≫ completedShriekA l E R T₁ := by
  have _ := hl
  simpa only [completedShriekA, completedShriekRefinement, completedShriekF,
    systemInterpretation, CompletedShriekPasting.compositionD,
    CompletedShriekPasting.compositionC, CompletedShriekPasting.compositionH,
    CompletedShriekPasting.compositionF, completedShriekPasting,
    CompletedShriekPastingData.obj, CompletedShriekPastingData.R,
    CompletedShriekPastingData.J, CompletedShriekPastingData.rId,
    CompletedShriekPastingData.pComp, CompletedShriekPastingData.jCompNamed,
    CompletedShriekPastingData.gamma,
    completedShriekOpenComp, completedShriekPushComp, Iso.trans_hom,
    eqToIso.hom, Category.assoc] using
    CompletedShriekPasting.refinement (completedShriekPasting l E R)
      (completedShriekPasting_laws l E R) T₂ T₁ r

end RefinementPasting

/-- Associativity on compatible towers is an equation in the derived system category.
Source: Stacks 0F7J--0F7K (blueprint: lem-sf-completed-shriek-composition-laws).

Proof: use the three proper/open squares A=(U,V;Y,T), B=(V,Xbar;T,Ybar),
C=(T,Ybar;Z,Zbar) of node proof step 4. Horizontal and vertical pasting expand the
two arrows into Gamma_B Gamma_A Gamma_C and Gamma_B Gamma_C Gamma_A. The disjoint
A,C factors commute by naturality. Associativity of the proper/open compositors
removes parentheses on a common compatible triple tower. For the four given
triangles use a common refining tower and the normalized-domain refinement
isomorphisms to transport the equation, including all intermediate systems.
No compatibility of unrelated triangle interiors is assumed. The resulting
component equality is in the system category, before finite evaluation. -/
theorem completedShriekAssociativity (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification h)
    (cfg : Compactification (f ≫ g)) (cgh : Compactification (g ≫ h))
    (cfgh : Compactification ((f ≫ g) ≫ h))
    (Tfg : Compactification.Triangle f g) (Tgh : Compactification.Triangle g h)
    (Tfg_h : Compactification.Triangle (f ≫ g) h)
    (Tf_gh : Compactification.Triangle f (g ≫ h))
    [QuasiCompact Tfg.q] [QuasiCompact Tgh.q]
    [QuasiCompact Tfg_h.q] [QuasiCompact Tf_gh.q]
    (hfgf : cf = Tfg.cf) (hfgg : cg = Tfg.cg) (hfgfg : Tfg.cfg = cfg)
    (hghg : cg = Tgh.cf) (hghh : ch = Tgh.cg) (hghgh : Tgh.cfg = cgh)
    (hlfg : cfg = Tfg_h.cf) (hlh : ch = Tfg_h.cg) (hlall : Tfg_h.cfg = cfgh)
    (hrf : cf = Tf_gh.cf) (hrgh : cgh = Tf_gh.cg)
    (hrall : Tf_gh.cfg = cfgh.copy (Category.assoc f g h).symm)
    (M : System l E X) (hf : completedShriekDomain l E o cf M)
    (hg : completedShriekDomain l E o cg ((completedShriekF l E o cf).obj M))
    (hh : completedShriekDomain l E o ch
      ((completedShriekF l E o cg).obj ((completedShriekF l E o cf).obj M)))
    (hfg : completedShriekDomain l E o cfg M)
    (hhfg : completedShriekDomain l E o ch ((completedShriekF l E o cfg).obj M))
    (hgh : completedShriekDomain l E o cgh ((completedShriekF l E o cf).obj M))
    (hfgh : completedShriekDomain l E o cfgh M) :
    (Functor.whiskerRight (completedShriekAOn l E R cf cg cfg Tfg hfgf hfgg hfgfg)
        (completedShriekF l E o ch) ≫
      completedShriekAOn l E R cfg ch cfgh Tfg_h hlfg hlh hlall).app M =
    ((Functor.associator (completedShriekF l E o cf) (completedShriekF l E o cg)
        (completedShriekF l E o ch)).hom ≫
      Functor.whiskerLeft (completedShriekF l E o cf)
        (completedShriekAOn l E R cg ch cgh Tgh hghg hghh hghgh) ≫
      completedShriekAOn l E R cf cgh (cfgh.copy (Category.assoc f g h).symm)
        Tf_gh hrf hrgh hrall).app M := by
  sorry

/-- The unit-left triangle's intermediate open is the compactification open.
Source: Stacks 0F7K (blueprint: lem-sf-completed-shriek-composition-laws). -/
instance completedShriekUnitLeftQC {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c : Compactification f) : QuasiCompact (Compactification.Triangle.unitLeft c).q :=
  inferInstanceAs (QuasiCompact c.i)

/-- The unit-right triangle's intermediate open is the identity.
Source: Stacks 0F7K (blueprint: lem-sf-completed-shriek-composition-laws). -/
instance completedShriekUnitRightQC {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : QuasiCompact (Compactification.Triangle.unitRight c).q :=
  inferInstanceAs (QuasiCompact (𝟙 c.Z))

private def completedShriekPushUnit {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o) (X : Scheme.{u}) :
    Operations.push l E o (𝟙 X) ≅ 𝟭 (System l E X) :=
  completedShriekPushId l E R X

private theorem leftUnitOfIdentityPair {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (S : C ⥤ C) (u : S ≅ 𝟭 C) (a : S ⋙ F ≅ F)
    (b : S ⋙ S ≅ S)
    (ha : ∀ M, F.map (b.hom.app M) ≫ a.hom.app M =
      a.hom.app (S.obj M) ≫ a.hom.app M)
    (hb : ∀ M, b.hom.app M = S.map (u.hom.app M)) (M : C) :
    a.hom.app M = F.map (u.hom.app M) := by
  have hh := (cancel_mono (a.hom.app M)).mp (ha M)
  rw [hb] at hh
  have hn := a.hom.naturality (u.hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [← hh] at hn
  exact (cancel_epi (F.map (S.map (u.hom.app M)))).mp hn

private theorem completedShriekPushLeft {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (R : Realizations l E D o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : System l E X) :
    (completedShriekPushComp l E R.compositors (𝟙 X) f f
      (Category.id_comp f)).hom.app M =
      (Operations.push l E o f).map ((completedShriekPushUnit l E R X).hom.app M) := by
  exact leftUnitOfIdentityPair (Operations.push l E o f)
    (Operations.push l E o (𝟙 X)) (completedShriekPushUnit l E R X)
    (completedShriekPushComp l E R.compositors (𝟙 X) f f (Category.id_comp f))
    (completedShriekPushComp l E R.compositors (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp _))
    (fun N ↦ completedShriekPushAssoc l E R.compositors (𝟙 X) (𝟙 X) f (𝟙 X) f f
      (Category.id_comp _) (Category.id_comp _) (Category.id_comp _) (Category.id_comp _) N)
    (systemPushIdentityPair l E o R.compositors R.canonicalBridge X) M

private theorem identityVerticalBridge
    {A B : Type*} [Category A] [Category B]
    (J J' : A ⥤ B) (S S' : A ⥤ A) (T T' : B ⥤ B)
    (j : J ≅ J') (s : S ≅ S') (t : T ≅ T')
    (u : S' ≅ 𝟭 A) (v : T' ≅ 𝟭 B)
    (g : S ⋙ J ⟶ J ⋙ T) (g' : S' ⋙ J' ⟶ J' ⋙ T')
    (hc : ∀ M, g.app M ≫ t.hom.app (J.obj M) ≫ T'.map (j.hom.app M) =
      j.hom.app (S.obj M) ≫ J'.map (s.hom.app M) ≫ g'.app M)
    (hi : ∀ M, g'.app M ≫ v.hom.app (J'.obj M) = J'.map (u.hom.app M))
    (M : A) :
    g.app M ≫ (t ≪≫ v).hom.app (J.obj M) = J.map ((s ≪≫ u).hom.app M) := by
  apply (cancel_mono (j.hom.app M)).mp
  change (g.app M ≫ t.hom.app (J.obj M) ≫ v.hom.app (J.obj M)) ≫ j.hom.app M =
    J.map (s.hom.app M ≫ u.hom.app M) ≫ j.hom.app M
  have hv : v.hom.app (J.obj M) ≫ j.hom.app M =
      T'.map (j.hom.app M) ≫ v.hom.app (J'.obj M) := by
    simpa only [Functor.id_map] using (v.hom.naturality (j.hom.app M)).symm
  calc
    _ = (g.app M ≫ t.hom.app (J.obj M) ≫ T'.map (j.hom.app M)) ≫
        v.hom.app (J'.obj M) := by simp only [Category.assoc, hv]
    _ = j.hom.app (S.obj M) ≫ J'.map (s.hom.app M) ≫
        g'.app M ≫ v.hom.app (J'.obj M) := by rw [hc]; simp only [Category.assoc]
    _ = j.hom.app (S.obj M) ≫ J'.map (s.hom.app M ≫ u.hom.app M) := by
      rw [hi, Functor.map_comp]
    _ = _ := (j.hom.naturality (s.hom.app M ≫ u.hom.app M)).symm

private theorem identityHorizontalBridge
    {A B : Type*} [Category A] [Category B]
    (R R' : A ⥤ B) (J J' : A ⥤ A) (K K' : B ⥤ B)
    (r : R ≅ R') (j : J ≅ J') (k : K ≅ K')
    (u : J' ≅ 𝟭 A) (v : K' ≅ 𝟭 B)
    (g : R ⋙ K ⟶ J ⋙ R) (g' : R' ⋙ K' ⟶ J' ⋙ R')
    (hc : ∀ M, g.app M ≫ r.hom.app (J.obj M) ≫ R'.map (j.hom.app M) =
      k.hom.app (R.obj M) ≫ K'.map (r.hom.app M) ≫ g'.app M)
    (hi : ∀ M, g'.app M ≫ R'.map (u.hom.app M) = v.hom.app (R'.obj M))
    (M : A) :
    g.app M ≫ R.map ((j ≪≫ u).hom.app M) = (k ≪≫ v).hom.app (R.obj M) := by
  apply (cancel_mono (r.hom.app M)).mp
  change (g.app M ≫ R.map (j.hom.app M ≫ u.hom.app M)) ≫ r.hom.app M =
    (k.hom.app (R.obj M) ≫ v.hom.app (R.obj M)) ≫ r.hom.app M
  calc
    _ = g.app M ≫ r.hom.app (J.obj M) ≫
        R'.map (j.hom.app M ≫ u.hom.app M) := by
      simpa only [Category.assoc, Functor.id_obj] using
        congrArg (fun z ↦ g.app M ≫ z) (r.hom.naturality (j.hom.app M ≫ u.hom.app M))
    _ = (g.app M ≫ r.hom.app (J.obj M) ≫ R'.map (j.hom.app M)) ≫
        R'.map (u.hom.app M) := by simp only [Functor.map_comp, Category.assoc]
    _ = k.hom.app (R.obj M) ≫ K'.map (r.hom.app M) ≫
        g'.app M ≫ R'.map (u.hom.app M) := by rw [hc]; simp only [Category.assoc]
    _ = k.hom.app (R.obj M) ≫ K'.map (r.hom.app M) ≫ v.hom.app (R'.obj M) := by
      rw [hi]
    _ = _ := by
      simpa only [Functor.id_map, Category.assoc] using
        congrArg (fun z ↦ k.hom.app (R.obj M) ≫ z) (v.hom.naturality (r.hom.app M))

private def completedShriekOpenId {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o) (X : Scheme.{u}) :
    Operations.shriek l E o (𝟙 X) ≅ 𝟭 (System l E X) :=
  R.canonicalBridge.shriek l E (𝟙 X) ≪≫
    ProEtale.SemilinearProperOpen.jId (scalarRings l E) (scalarTransitions l E) X

private theorem leftIdentityBridge {C : Type*} [Category C]
    {J J' P P' : C ⥤ C} (a : J ⊣ P) (a' : J' ⊣ P')
    (b : P ≅ P') (e : P' ≅ 𝟭 C) :
    (a.ofNatIsoRight b).leftAdjointUniq a' ≪≫ Adjunction.leftAdjointIdIso a' e =
      Adjunction.leftAdjointIdIso a (b ≪≫ e) := by
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id a).injective
  ext M
  simp [Adjunction.leftAdjointUniq, Adjunction.leftAdjointIdIso,
    conjugateEquiv_symm_apply_app, Adjunction.ofNatIsoRight_counit]

private def completedShriekPullId {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o) (X : Scheme.{u}) : pull l E (𝟙 X) ≅ 𝟭 (System l E X) :=
  R.canonicalBridge.pull l E (𝟙 X) ≪≫
    ProEtale.SemilinearProperOpen.pId (scalarRings l E) (scalarTransitions l E) X

private theorem completedShriekPullId_push {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (R : Realizations l E D o) (X : Scheme.{u}) :
    conjugateIsoEquiv (o.direct (𝟙 X)).adj Adjunction.id
      (completedShriekPullId l E R X).symm = completedShriekPushUnit l E R X := by
  unfold completedShriekPullId completedShriekPushUnit completedShriekPushId
  rw [Iso.trans_symm, conjugateIsoEquiv_trans (o.direct (𝟙 X)).adj
    (ProEtale.SemilinearProperOpen.adj (scalarRings l E) (scalarTransitions l E) (𝟙 X))
    Adjunction.id]
  rfl

private theorem completedShriekPullId_open {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (R : Realizations l E D o) (X : Scheme.{u}) :
    Adjunction.leftAdjointIdIso (o.extension (𝟙 X)).adj
      (completedShriekPullId l E R X) = completedShriekOpenId l E R X := by
  exact (leftIdentityBridge (o.extension (𝟙 X)).adj
    (ProEtale.SemilinearProperOpen.jAdj (scalarRings l E) (scalarTransitions l E) (𝟙 X))
    (R.canonicalBridge.pull l E (𝟙 X))
    (ProEtale.SemilinearProperOpen.pId (scalarRings l E) (scalarTransitions l E) X)).symm

private theorem completedShriekOpenTransport {o : Operations l E}
    (c : Compositors l E o) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion fg]
    (w : f ≫ g = fg) :
    completedShriekOpenComp l E c f g fg w =
      Adjunction.leftAdjointCompIso (o.extension f).adj (o.extension g).adj
        (o.extension fg).adj
        (eqToIso (congrArg (pull l E) w.symm) ≪≫ c.pullComp f g).symm := by
  subst fg
  simp only [completedShriekOpenComp, completedShriekOpenCongr, eqToIso_refl,
    Iso.refl_trans, Iso.trans_refl, Compositors.openComp]

private theorem completedShriekPullUnitLeft {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (R : Realizations l E D o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (eqToIso (congrArg (pull l E) (Category.id_comp f).symm) ≪≫
      R.compositors.pullComp (𝟙 X) f).symm =
      Functor.isoWhiskerLeft (pull l E f) (completedShriekPullId l E R X) ≪≫
        Functor.rightUnitor (pull l E f) := by
  let a := (o.direct f).adj
  let b := (o.direct (𝟙 X)).adj
  let e := completedShriekPullId l E R X
  let k := eqToIso (congrArg (pull l E) (Category.id_comp f).symm) ≪≫
    R.compositors.pullComp (𝟙 X) f
  have hk : conjugateIsoEquiv (a.comp b) a k =
      Functor.isoWhiskerRight (completedShriekPushUnit l E R X) (Operations.push l E o f) ≪≫
        Functor.leftUnitor (Operations.push l E o f) := by
    have ht := completedShriekConjugateTransport (pull l E) (Operations.push l E o)
      (fun f ↦ (o.direct f).adj) (a.comp b) (Category.id_comp f)
      (R.compositors.pullComp (𝟙 X) f)
    rw [ht]
    apply Iso.ext
    ext M
    dsimp only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Iso.trans_hom, NatTrans.comp_app, Functor.leftUnitor_hom_app]
    exact (completedShriekPushLeft l E R f M).trans (Category.comp_id _).symm
  have hd := ProEtale.StrictTower.conjugate_unit a b e
    ((Functor.rightUnitor (pull l E f)).symm ≪≫
      Functor.isoWhiskerLeft (pull l E f) e.symm) (by
        ext M
        simp)
  rw [completedShriekPullId_push] at hd
  have h := (conjugateIsoEquiv (a.comp b) a).injective (hk.trans hd.symm)
  exact congrArg Iso.symm h

private theorem conjugateLeftUnit {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {R : D ⥤ C} {I RI : C ⥤ C}
    (a : F ⊣ R) (b : I ⊣ RI) (e : I ≅ 𝟭 C) :
    conjugateIsoEquiv (b.comp a) a
      ((Functor.leftUnitor F).symm ≪≫ Functor.isoWhiskerRight e.symm F) =
      Functor.isoWhiskerLeft R (conjugateIsoEquiv b Adjunction.id e.symm) ≪≫
        Functor.rightUnitor R := by
  rw [conjugateIsoEquiv_trans (b.comp a) (Adjunction.id.comp a) a,
    conjugateIsoEquiv_isoWhiskerRight b Adjunction.id a,
    conjugateIsoEquiv_iso_symm a (Adjunction.id.comp a),
    conjugateIsoEquiv_leftUnitor, Iso.symm_symm_eq]

private theorem completedShriekPullUnitRight {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (R : Realizations l E D o)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (eqToIso (congrArg (pull l E) (Category.comp_id f).symm) ≪≫
      R.compositors.pullComp f (𝟙 Y)).symm =
      Functor.isoWhiskerRight (completedShriekPullId l E R Y) (pull l E f) ≪≫
        Functor.leftUnitor (pull l E f) := by
  let a := (o.direct f).adj
  let b := (o.direct (𝟙 Y)).adj
  let e := completedShriekPullId l E R Y
  let k := eqToIso (congrArg (pull l E) (Category.comp_id f).symm) ≪≫
    R.compositors.pullComp f (𝟙 Y)
  have hk : conjugateIsoEquiv (b.comp a) a k =
      Functor.isoWhiskerLeft (Operations.push l E o f) (completedShriekPushUnit l E R Y) ≪≫
        Functor.rightUnitor (Operations.push l E o f) := by
    have ht := completedShriekConjugateTransport (pull l E) (Operations.push l E o)
      (fun f ↦ (o.direct f).adj) (b.comp a) (Category.comp_id f)
      (R.compositors.pullComp f (𝟙 Y))
    rw [ht]
    apply Iso.ext
    ext M
    dsimp only [Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Iso.trans_hom, NatTrans.comp_app, Functor.rightUnitor_hom_app]
    exact (completedShriekPushRight l E R f M).trans (Category.comp_id _).symm
  have hd := conjugateLeftUnit a b e
  rw [completedShriekPullId_push] at hd
  have h := (conjugateIsoEquiv (b.comp a) a).injective (hk.trans hd.symm)
  exact congrArg Iso.symm h

private theorem completedShriekOpenUnits {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (R : Realizations l E D o)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (M : System l E X) :
    ((completedShriekOpenComp l E R.compositors (𝟙 X) j j
      (Category.id_comp j)).hom.app M =
      (Operations.shriek l E o j).map ((completedShriekOpenId l E R X).hom.app M)) ∧
    ((completedShriekOpenComp l E R.compositors j (𝟙 Y) j
      (Category.comp_id j)).hom.app M =
      (completedShriekOpenId l E R Y).hom.app ((Operations.shriek l E o j).obj M)) := by
  constructor
  · rw [completedShriekOpenTransport]
    have h := Adjunction.leftAdjointCompIso_id_comp (o.extension (𝟙 X)).adj
      (o.extension j).adj _ (completedShriekPullId l E R X)
      (completedShriekPullUnitLeft l E R j)
    rw [h, completedShriekPullId_open]
    simp
  · rw [completedShriekOpenTransport]
    have h := Adjunction.leftAdjointCompIso_comp_id (o.extension j).adj
      (o.extension (𝟙 Y)).adj _ (completedShriekPullId l E R Y)
      (completedShriekPullUnitRight l E R j)
    rw [h, completedShriekPullId_open]
    simp

private theorem completedShriekGammaVerticalId {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (R : Realizations l E D o)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (h : j ≫ 𝟙 Y = 𝟙 X ≫ j) (M : System l E X) :
    (R.properOpen.gamma j (𝟙 X) (𝟙 Y) j h).app M ≫
        (completedShriekPushUnit l E R Y).hom.app ((Operations.shriek l E o j).obj M) =
      (Operations.shriek l E o j).map ((completedShriekPushUnit l E R X).hom.app M) := by
  exact identityVerticalBridge _ _ _ _ _ _ (R.canonicalBridge.shriek l E j)
    (R.canonicalBridge.push l E (𝟙 X)) (R.canonicalBridge.push l E (𝟙 Y))
    (ProEtale.SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) X)
    (ProEtale.SemilinearProperOpen.sId (scalarRings l E) (scalarTransitions l E) Y)
    _ _ (R.properOpen.canonical j (𝟙 X) (𝟙 Y) j h)
    ((ProEtale.SemilinearProperOpen.gamma_identities (scalarRings l E)
      (scalarTransitions l E)).1 j h) M

private theorem completedShriekGammaHorizontalId {D : FiniteFieldDatum.{u}}
    {o : Operations l E} (R : Realizations l E D o)
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p]
    (h : 𝟙 X ≫ p = p ≫ 𝟙 Y) (M : System l E X) :
    (R.properOpen.gamma (𝟙 X) p p (𝟙 Y) h).app M ≫
        (Operations.push l E o p).map ((completedShriekOpenId l E R X).hom.app M) =
      (completedShriekOpenId l E R Y).hom.app ((Operations.push l E o p).obj M) := by
  exact identityHorizontalBridge _ _ _ _ _ _ (R.canonicalBridge.push l E p)
    (R.canonicalBridge.shriek l E (𝟙 X)) (R.canonicalBridge.shriek l E (𝟙 Y))
    (ProEtale.SemilinearProperOpen.jId (scalarRings l E) (scalarTransitions l E) X)
    (ProEtale.SemilinearProperOpen.jId (scalarRings l E) (scalarTransitions l E) Y)
    _ _ (R.properOpen.canonical (𝟙 X) p p (𝟙 Y) h)
    ((ProEtale.SemilinearProperOpen.gamma_identities (scalarRings l E)
      (scalarTransitions l E)).2 p h) M

private theorem compactSupportLeftUnitCalculation
    {C D E₀ : Type*} [Category C] [Category D] [Category E₀]
    (I S : C ⥤ C) (J : C ⥤ D) (T : D ⥤ D) (F : D ⥤ E₀)
    (u : I ≅ 𝟭 C) (s : S ≅ 𝟭 C) (t : T ≅ 𝟭 D)
    (a : I ⋙ J ≅ J) (b : T ⋙ F ≅ F) (g : S ⋙ J ⟶ J ⋙ T)
    (ha : ∀ M, a.hom.app M = J.map (u.hom.app M))
    (hb : ∀ N, b.hom.app N = F.map (t.hom.app N))
    (hg : ∀ M, g.app M ≫ t.hom.app (J.obj M) = J.map (s.hom.app M))
    (M : C) :
    F.map (g.app (I.obj M)) ≫ F.map (T.map (a.hom.app M)) ≫
        b.hom.app (J.obj M) =
      F.map (J.map (S.map (u.hom.app M) ≫ s.hom.app M)) := by
  rw [hb]
  simp only [← Functor.map_comp]
  congr 1
  rw [t.hom.naturality]
  dsimp only [Functor.id_map]
  rw [← Category.assoc, hg, ha, ← Functor.map_comp]
  exact congrArg J.map (by
    simpa only [Functor.id_obj, Functor.id_map] using
      (s.hom.naturality (u.hom.app M)).symm)

private theorem compactSupportRightUnitCalculation
    {C D E₀ : Type*} [Category C] [Category D] [Category E₀]
    (J : C ⥤ D) (F : D ⥤ E₀) (I : E₀ ⥤ E₀)
    (T : D ⥤ D) (V : E₀ ⥤ E₀)
    (u : T ≅ 𝟭 D) (v : V ≅ 𝟭 E₀) (s : I ≅ 𝟭 E₀)
    (a : J ⋙ T ≅ J) (b : F ⋙ I ≅ F) (g : F ⋙ V ⟶ T ⋙ F)
    (ha : ∀ M, a.hom.app M = u.hom.app (J.obj M))
    (hb : ∀ N, b.hom.app N = s.hom.app (F.obj N))
    (hg : ∀ N, g.app N ≫ F.map (u.hom.app N) = v.hom.app (F.obj N))
    (M : C) :
    I.map (g.app (J.obj M)) ≫ I.map (F.map (a.hom.app M)) ≫
        b.hom.app (J.obj M) =
      I.map (v.hom.app (F.obj (J.obj M))) ≫ s.hom.app (F.obj (J.obj M)) := by
  rw [ha, hb, ← Category.assoc, ← Functor.map_comp, hg]

private theorem completedShriekId_app {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o) (X : Scheme.{u}) (M : System l E X) :
    (completedShriekId l E R X).hom.app M =
      (Operations.push l E o (𝟙 X)).map ((completedShriekOpenId l E R X).hom.app M) ≫
        (completedShriekPushUnit l E R X).hom.app M := by
  change (Operations.push l E o (𝟙 X)).map
      ((completedShriekOpenId l E R X).hom.app M) ≫
      𝟙 ((Operations.push l E o (𝟙 X)).obj M) ≫
        (completedShriekPushUnit l E R X).hom.app M = _
  exact congrArg
    (fun z ↦ (Operations.push l E o (𝟙 X)).map
      ((completedShriekOpenId l E R X).hom.app M) ≫ z)
    (Category.id_comp ((completedShriekPushUnit l E R X).hom.app M))

/-- Both system unit laws, with the canonical identity compactification.
Source: Stacks 0F7K (blueprint: lem-sf-completed-shriek-composition-laws).

Proof: the interchange square has identity horizontal or vertical arrows, so its
normalized clopen projection is the identity and the adjunction triangle identities
give the identity mate. The remaining maps are the unital proper/open compositors.
Refinement compatibility gives the same unit for every other compactification. -/
theorem completedShriekUnits (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f] (c : Compactification f) :
    (completedShriekA l E R (.unitLeft c)) =
      Functor.whiskerRight (completedShriekId l E R X).hom (completedShriekF l E o c) ≫
        (Functor.leftUnitor (completedShriekF l E o c)).hom ∧
    (completedShriekA l E R (.unitRight c)) =
      Functor.whiskerLeft (completedShriekF l E o c) (completedShriekId l E R Y).hom ≫
        (Functor.rightUnitor (completedShriekF l E o c)).hom := by
  have _ := hl
  constructor
  · ext M
    simp only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, completedShriekId_app]
    change (Operations.push l E o c.g).map
        ((R.properOpen.gamma c.i (𝟙 X) (𝟙 c.Z) c.i _).app
          ((Operations.shriek l E o (𝟙 X)).obj M)) ≫
      (Operations.push l E o c.g).map ((Operations.push l E o (𝟙 c.Z)).map
        ((completedShriekOpenComp l E R.compositors (𝟙 X) c.i c.i
          (Category.id_comp _)).hom.app M)) ≫
      (completedShriekPushComp l E R.compositors (𝟙 c.Z) c.g c.g
        (Category.id_comp _)).hom.app ((Operations.shriek l E o c.i).obj M) =
      (Operations.push l E o c.g).map ((Operations.shriek l E o c.i).map
        ((Operations.push l E o (𝟙 X)).map ((completedShriekOpenId l E R X).hom.app M) ≫
          (completedShriekPushUnit l E R X).hom.app M)) ≫ 𝟙 _
    apply Eq.trans ?_ (Category.comp_id _).symm
    exact compactSupportLeftUnitCalculation _ _ _ _ _
      (completedShriekOpenId l E R X) (completedShriekPushUnit l E R X)
      (completedShriekPushUnit l E R c.Z)
      (completedShriekOpenComp l E R.compositors (𝟙 X) c.i c.i (Category.id_comp _))
      (completedShriekPushComp l E R.compositors (𝟙 c.Z) c.g c.g (Category.id_comp _))
      (R.properOpen.gamma c.i (𝟙 X) (𝟙 c.Z) c.i _)
      (fun N ↦ (completedShriekOpenUnits l E R c.i N).1)
      (completedShriekPushLeft l E R c.g)
      (completedShriekGammaVerticalId l E R c.i _) M
  · ext M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app, completedShriekId_app]
    change (Operations.push l E o (𝟙 Y)).map
        ((R.properOpen.gamma (𝟙 c.Z) c.g c.g (𝟙 Y) _).app
          ((Operations.shriek l E o c.i).obj M)) ≫
      (Operations.push l E o (𝟙 Y)).map ((Operations.push l E o c.g).map
        ((completedShriekOpenComp l E R.compositors c.i (𝟙 c.Z) c.i
          (Category.comp_id _)).hom.app M)) ≫
      (completedShriekPushComp l E R.compositors c.g (𝟙 Y) c.g
        (Category.comp_id _)).hom.app ((Operations.shriek l E o c.i).obj M) =
      ((Operations.push l E o (𝟙 Y)).map ((completedShriekOpenId l E R Y).hom.app
        ((completedShriekF l E o c).obj M)) ≫
          (completedShriekPushUnit l E R Y).hom.app ((completedShriekF l E o c).obj M)) ≫ 𝟙 _
    apply Eq.trans ?_ (Category.comp_id _).symm
    exact compactSupportRightUnitCalculation _ _ _ _ _
      (completedShriekOpenId l E R c.Z) (completedShriekOpenId l E R Y)
      (completedShriekPushUnit l E R Y)
      (completedShriekOpenComp l E R.compositors c.i (𝟙 c.Z) c.i (Category.comp_id _))
      (completedShriekPushComp l E R.compositors c.g (𝟙 Y) c.g (Category.comp_id _))
      (R.properOpen.gamma (𝟙 c.Z) c.g c.g (𝟙 Y) _)
      (fun N ↦ (completedShriekOpenUnits l E R c.i N).2)
      (completedShriekPushRight l E R c.g)
      (completedShriekGammaHorizontalId l E R c.g _) M

/-- The comparison through a common refinement is assembled from the actual reverse maps.
Only inverses of the specified invertible maps are used.
Source: Stacks 0F7J (blueprint: lem-sf-completed-shriek-composition-laws). -/
def completedShriekComparisonVia (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {o : Operations l E} (R : Realizations l E D o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d e : Compactification f) (r : e.Refinement c) (s : e.Refinement d)
    (M : System l E X) (hc : completedShriekDomain l E o c M)
    (hd : completedShriekDomain l E o d M) (he : completedShriekDomain l E o e M) :
    (completedShriekF l E o c).obj M ≅ (completedShriekF l E o d).obj M :=
  @asIso _ _ _ _ ((completedShriekRefinement l E R r).app M)
      ((completedShriekRefinementLaws l E D hl o R).2.2.1 e c r M he hc) ≪≫
    (@asIso _ _ _ _ ((completedShriekRefinement l E R s).app M)
      ((completedShriekRefinementLaws l E D hl o R).2.2.1 e d s M he hd)).symm

private theorem completedShriekCommonSpan {C : Type*} [Category C]
    {A B S T Q : C} (a : A ≅ S) (b : B ≅ S) (c : A ≅ T) (d : B ≅ T)
    (u : S ≅ Q) (v : T ≅ Q)
    (ha : a.hom ≫ u.hom = c.hom ≫ v.hom)
    (hb : b.hom ≫ u.hom = d.hom ≫ v.hom) :
    a ≪≫ b.symm = c ≪≫ d.symm := by
  have ha' : a ≪≫ u = c ≪≫ v := Iso.ext ha
  have hb' : b ≪≫ u = d ≪≫ v := Iso.ext hb
  calc
    a ≪≫ b.symm = (a ≪≫ u) ≪≫ (b ≪≫ u).symm := by simp
    _ = (c ≪≫ v) ≪≫ (d ≪≫ v).symm := by rw [ha', hb']
    _ = c ≪≫ d.symm := by simp

/-- Independence of the common refining compactification and of its arrows.
Source: Stacks 0F7J (blueprint: lem-sf-completed-shriek-composition-laws).

Proof: use the dense common refinement of the two refining compactifications.
Refinements out of its scheme-theoretically dense open are unique, so the two
composites to each original compactification agree. The reverse-refinement cocycle
identifies the corresponding composites of system maps. Every reverse-refinement
map is invertible by the proper/open supported-counit theorem, including the maps
out of the dense common refinement; no additional domain bound on that refinement
is needed. Cancel those maps to identify the two comparison isomorphisms. -/
theorem completedShriekChoiceIndependence (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d e e' : Compactification f)
    (r : e.Refinement c) (s : e.Refinement d)
    (r' : e'.Refinement c) (s' : e'.Refinement d)
    (M : System l E X) (hc : completedShriekDomain l E o c M)
    (hd : completedShriekDomain l E o d M) (he : completedShriekDomain l E o e M)
    (he' : completedShriekDomain l E o e' M) :
    completedShriekComparisonVia l E D hl R c d e r s M hc hd he =
      completedShriekComparisonVia l E D hl R c d e' r' s' M hc hd he' := by
  let k := Compactification.inf e e'
  let t : k.Refinement e := Compactification.infFst e e'
  let t' : k.Refinement e' := Compactification.infSnd e e'
  have : IsSchemeTheoreticallyDominant k.i :=
    Compactification.isSchemeTheoreticallyDominant_inf_i e e'
  have hr : t.comp r = t'.comp r' := Subsingleton.elim _ _
  have hs : t.comp s = t'.comp s' := Subsingleton.elim _ _
  have laws := (completedShriekRefinementLaws l E D hl o R (f := f)).2.1
  have hcomp (a b z : Compactification f) (v : a.Refinement b) (w : b.Refinement z) :
      (completedShriekRefinement l E R w).app M ≫
          (completedShriekRefinement l E R v).app M =
        (completedShriekRefinement l E R (v.comp w)).app M :=
    (congr_app (laws a b z v w) M).symm
  have := completedShriekRefinement_isIso l E R r M
  have := completedShriekRefinement_isIso l E R s M
  have := completedShriekRefinement_isIso l E R r' M
  have := completedShriekRefinement_isIso l E R s' M
  have := completedShriekRefinement_isIso l E R t M
  have := completedShriekRefinement_isIso l E R t' M
  exact completedShriekCommonSpan
    (asIso ((completedShriekRefinement l E R r).app M))
    (asIso ((completedShriekRefinement l E R s).app M))
    (asIso ((completedShriekRefinement l E R r').app M))
    (asIso ((completedShriekRefinement l E R s').app M))
    (asIso ((completedShriekRefinement l E R t).app M))
    (asIso ((completedShriekRefinement l E R t').app M))
    (by
      have hraw : (completedShriekRefinement l E R r).app M ≫
          (completedShriekRefinement l E R t).app M =
          (completedShriekRefinement l E R r').app M ≫
            (completedShriekRefinement l E R t').app M := by
        rw [hcomp k e c t r, hcomp k e' c t' r', hr]
      simpa only [asIso_hom] using hraw)
    (by
      have hraw : (completedShriekRefinement l E R s).app M ≫
          (completedShriekRefinement l E R t).app M =
          (completedShriekRefinement l E R s').app M ≫
            (completedShriekRefinement l E R t').app M := by
        rw [hcomp k e d t s, hcomp k e' d t' s', hs]
      simpa only [asIso_hom] using hraw)

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

/-- Transport of an actual system arrow by the recursive natural realization isomorphisms.
This is used equally for a compositor, refinement, unit, or an arrow in an outer context.
Source: Stacks 0941 (blueprint: lem-sf-completed-shriek-composition-laws). -/
def completedShriekRealized {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))} (e t : Expression _ I X W)
    (ge : e.geometric) (gt : t.geometric)
    (K : ∀ i, Integral l E (X i).left) (he : e.domain l E o K) (ht : t.domain l E o K)
    (s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K)) :
    (e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K :=
  (R.comparison e ge).inv.app ⟨K, he⟩ ≫ (coefficientSequenceLimit l E W.left).map s ≫
    (R.comparison t gt).hom.app ⟨K, ht⟩

private theorem completedShriekTransportId {C C' : Type*} [Category C] [Category C']
    (F : C ⥤ C') {A : C} {B : C'} (c : F.obj A ≅ B) :
    c.inv ≫ F.map (𝟙 A) ≫ c.hom = 𝟙 B := by
  simp

/-- Realization identifies the maps with the specified completed integral generators,
including inside nested functors; it preserves identities and composites.
Source: Stacks 0941 (blueprint: lem-sf-completed-shriek-composition-laws).

Proof: the realization theorem identifies each canonical generator pair, and every
outer expression context, by c_t L(s) = r c_e. Cancel c_e. For a composite, the
adjacent c_t inverse and c_t cancel; the total-limit functor preserves composition.
The identity calculation uses the same cancellation. Apply these equations to the
system refinement, unit and associativity diagrams above; their integral diagrams
are the same prescribed arrows. Equality is not inferred from finite reductions. -/
theorem completedShriekRealizationLaws (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))} (e t v : Expression _ I X W)
    (ge : e.geometric) (gt : t.geometric) (gv : v.geometric)
    (K : ∀ i, Integral l E (X i).left)
    (he : e.domain l E o K) (ht : t.domain l E o K) (hv : v.domain l E o K)
    (s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K))
    (z : t.systemObj l E o ((inputReduction l E X).obj K) ⟶
      v.systemObj l E o ((inputReduction l E X).obj K)) :
    (completedShriekRealized l E R e e ge ge K he he (𝟙 _) = 𝟙 _) ∧
    (completedShriekRealized l E R e v ge gv K he hv (s ≫ z) =
      completedShriekRealized l E R e t ge gt K he ht s ≫
        completedShriekRealized l E R t v gt gv K ht hv z) ∧
    (∀ r : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K,
      CanonicalPair l E o R.compositors R.openComparisons R.canonicalBridge R.properOpen
        R.ringedModels R.ringedOpenComparisons R.ringedProperOpen
        ((inputReduction l E X).obj K) K e t s r →
      completedShriekRealized l E R e t ge gt K he ht s = r) := by
  have _ := hl
  refine ⟨?_, ?_, ?_⟩
  · exact completedShriekTransportId (coefficientSequenceLimit l E W.left)
      ((R.comparison e ge).app ⟨K, he⟩)
  · simp [completedShriekRealized, Functor.map_comp, Category.assoc]
  · intro r hr
    unfold completedShriekRealized
    rw [R.coherence e t ge gt ⟨K, he⟩ ht s r hr]
    exact (R.comparison e ge).inv_hom_id_app_assoc ⟨K, he⟩ r

/-- The finite canonical compositor in intrinsic coordinates, retaining the etale witness.
Source: Stacks 0F7J; thm-sf-comp-composition
(blueprint: lem-sf-completed-shriek-composition-laws). -/
def completedShriekFiniteA (A : Type u) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))
    (K : DerivedCategory (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (α : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      X).mapDerivedCategory.obj L.obj ≅ K) :
    (AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate A cg).obj
        ((AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate A cf).obj
          ((AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence X A).functor.obj K)) ⟶
      (AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate A cfg).obj
        ((AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence X A).functor.obj K) :=
  (AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate A cg).map
      ((AlgebraicGeometry.ProEtale.sfIntrinsicCompactSupportComparison A cf).hom.app K) ≫
    (AlgebraicGeometry.ProEtale.sfIntrinsicCompactSupportComparison A cg).hom.app
      ((AlgebraicGeometry.ProEtale.sfFixedCompactSupport A cf).obj K) ≫
    (AlgebraicGeometry.Scheme.sfIntrinsicDerivedEquivalence Z A).functor.map
      ((AlgebraicGeometry.ProEtale.sfFixedCompactSupport A cg).map
        ((AlgebraicGeometry.ProEtale.sfFixedCompactSupport A cf).map α.inv) ≫
      ProEtale.coherenceProEtaleCompositor (ULift.{u + 1, u} A) cf cg cfg L ≫
      (AlgebraicGeometry.ProEtale.sfFixedCompactSupport A cfg).map α.hom) ≫
    (AlgebraicGeometry.ProEtale.sfIntrinsicCompactSupportComparison A cfg).inv.app K

/-- Evaluation of the system compositor is the specified finite canonical compositor.
Source: Stacks 0F7J; thm-sf-comp-composition
(blueprint: lem-sf-completed-shriek-composition-laws).

Proof: expand the system arrow into proper/open interchange and the two compositors.
The normalized mate-evaluation equation identifies the interchange on the retained
etale witness. The ordinary adjunction normalizations identify both compositors.
The displayed factors are precisely the finite compactification construction of
thm-sf-comp-composition, transported through the fixed intrinsic equivalence and
input witness. That theorem supplies its finite unit and associativity laws. -/
theorem completedShriekFiniteEvaluation (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (T : Compactification.Triangle f g) [QuasiCompact T.q]
    (M : System l E X) (O : Origins l E X M) (n : ℕ)
    (w : AlgebraicGeometry.Scheme.FixedEtaleOriginWitness X
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) (O.level n)) :
    (coefficientSequenceDerivedEvaluation l E Z n).map ((completedShriekA l E R T).app M) ≫
      (supportEvaluation l E o T.cfg n).hom.app M =
    (supportEvaluation l E o T.cg n).hom.app ((completedShriekF l E o T.cf).obj M) ≫
      (AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate
        (Padic.coefficientExtensionRing l E (n + 1)) T.cg).map
        ((supportEvaluation l E o T.cf n).hom.app M) ≫
      (AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate
        (Padic.coefficientExtensionRing l E (n + 1)) T.cg).map
        ((AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate
          (Padic.coefficientExtensionRing l E (n + 1)) T.cf).map (O.evaluation n).inv) ≫
      completedShriekFiniteA (Padic.coefficientExtensionRing l E (n + 1))
        T.cf T.cg T.cfg (O.level n).obj w.complex w.iso ≫
      (AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate
        (Padic.coefficientExtensionRing l E (n + 1)) T.cfg).map (O.evaluation n).hom := by
  sorry

/-- The specified completed integral compositor is the normalized localized ringed mate,
followed by its proper and open compositors. Its data do not use realization by choice.
Source: Stacks 0F7J, 0941 (blueprint: lem-sf-completed-shriek-composition-laws). -/
def completedShriekIntegralA {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o) {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (T : Compactification.Triangle f g) [QuasiCompact T.cf.i] [QuasiCompact T.cg.i]
    [QuasiCompact T.q] :
    PurCompactSupport.image (PurCompactSupport.completed l E) T.cf ⋙
        PurCompactSupport.image (PurCompactSupport.completed l E) T.cg ⟶
      PurCompactSupport.image (PurCompactSupport.completed l E) T.cfg :=
  Functor.whiskerLeft (ringedOpen l E T.cf.i)
    (Functor.whiskerRight
      (R.ringedProperOpen.gamma T.q T.cf.g T.p T.cg.i T.isPullback.w.symm)
      (ringedPush l E T.cg.g)) ≫
  Functor.whiskerRight
    ((ringedOpenComp l E T.cf.i T.q).hom ≫
      (sfCompositionOpenCongr l E T.i_q).hom)
    (ringedPush l E T.p ⋙ ringedPush l E T.cg.g) ≫
  Functor.whiskerLeft (ringedOpen l E T.cfg.i)
    ((ringedPushComp l E T.p T.cg.g).hom ≫
      eqToHom (congrArg (ringedPush l E) T.p_g))

/-- The actual integral compositor, including in an arbitrary inner expression, is the
realization of the system compositor, with the stated intermediate-domain hypotheses.
Source: Stacks 0F7J, 0941 (blueprint: lem-sf-completed-shriek-composition-laws).

Proof: expand the compact-support constructors into open followed by proper image.
The normalized proper/open generator pairs, open and proper compositor pairs, and
support expansion pairs compose in CanonicalPair. Its outer-context constructors
retain the same arrow inside every nested functor. Apply realization coherence and
cancel the source comparison. Support words have identity completion comparison;
for a general inner expression its completion comparison cancels by naturality.
Thus the right side is the independently defined localized ringed compositor below,
not a freely chosen lift of its finite components. -/
theorem completedShriekIntegralComposition (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V W : Over (Spec (CommRingCat.of D.k))} (f : U ⟶ V) (g : V ⟶ W)
    [QuasiCompact f.left] [QuasiCompact g.left]
    (T : Compactification.Triangle f.left g.left) [QuasiCompact T.q]
    (e : Expression _ I X U)
    (ge : (Expression.compactSupport g T.cg (.compactSupport f T.cf e)).geometric)
    (gt : (Expression.compactSupport (f ≫ g) T.cfg e).geometric)
    (K : ∀ i, Integral l E (X i).left)
    (he : (Expression.compactSupport g T.cg (.compactSupport f T.cf e)).domain l E o K)
    (ht : (Expression.compactSupport (f ≫ g) T.cfg e).domain l E o K) :
    completedShriekRealized l E R
      (.compactSupport g T.cg (.compactSupport f T.cf e))
      (.compactSupport (f ≫ g) T.cfg e) ge gt K he ht
      ((completedShriekA l E R T).app
        (e.systemObj l E o ((inputReduction l E X).obj K))) =
    (completedShriekIntegralA l E R T).app
      ((e.evaluate (integralInterpretation l E)).obj K) := by
  sorry

/-- Raw rationalization of the realized integral map, in the actual constructible category.
The morphism is tensored with 1; no idempotent completion is introduced.
Source: blueprint fix-prop-coherence, raw localization paragraph
(blueprint: lem-sf-completed-shriek-composition-laws). -/
def completedShriekRationalMap {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (R : Realizations l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))} (e t : Expression _ I X W)
    (ge : e.geometric) (gt : t.geometric)
    (K : ∀ i, Integral l E (X i).left) (he : e.domain l E o K) (ht : t.domain l E o K)
    (ce : sfIntegralConstructible l E W.left ((e.evaluate (integralInterpretation l E)).obj K))
    (ct : sfIntegralConstructible l E W.left ((t.evaluate (integralInterpretation l E)).obj K))
    (s : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K)) :
    (sfRationalConstructibleLocalization l E W.left).obj ⟨_, ce⟩ ⟶
      (sfRationalConstructibleLocalization l E W.left).obj ⟨_, ct⟩ :=
  (sfRationalConstructibleLocalization l E W.left).map
    (ObjectProperty.homMk (completedShriekRealized l E R e t ge gt K he ht s))

/-- The raw rational arrows preserve the system equations, identities and composites.
In particular this applies to the refinement, both unit, and associativity equations.
Source: blueprint fix-prop-coherence, raw localization paragraph
(blueprint: lem-sf-completed-shriek-composition-laws).

Proof: realization identifies the prescribed integral arrows and preserves compositions
by cancellation of the intermediate c maps. The raw localization sends an arrow to
1 tensor that arrow. Composition of fractions is vu/t^(a+b), so identities, composition,
naturality and whiskering survive on arbitrary rational arrows. The three displayed
assertions apply to all the specific diagram paths above and their nested contexts. -/
theorem completedShriekRationalLaws (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))} (e t v : Expression _ I X W)
    (ge : e.geometric) (gt : t.geometric) (gv : v.geometric)
    (K : ∀ i, Integral l E (X i).left)
    (he : e.domain l E o K) (ht : t.domain l E o K) (hv : v.domain l E o K)
    (ce : sfIntegralConstructible l E W.left ((e.evaluate (integralInterpretation l E)).obj K))
    (ct : sfIntegralConstructible l E W.left ((t.evaluate (integralInterpretation l E)).obj K))
    (cv : sfIntegralConstructible l E W.left ((v.evaluate (integralInterpretation l E)).obj K))
    (s s' : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K))
    (z : t.systemObj l E o ((inputReduction l E X).obj K) ⟶
      v.systemObj l E o ((inputReduction l E X).obj K)) :
    (completedShriekRationalMap l E R e e ge ge K he he ce ce (𝟙 _) = 𝟙 _) ∧
    (completedShriekRationalMap l E R e v ge gv K he hv ce cv (s ≫ z) =
      completedShriekRationalMap l E R e t ge gt K he ht ce ct s ≫
        completedShriekRationalMap l E R t v gt gv K ht hv ct cv z) ∧
    (s = s' → completedShriekRationalMap l E R e t ge gt K he ht ce ct s =
      completedShriekRationalMap l E R e t ge gt K he ht ce ct s') := by
  obtain ⟨hid, hcomp, _⟩ :=
    completedShriekRealizationLaws l E D hl o R e t v ge gt gv K he ht hv s z
  refine ⟨?_, ?_, ?_⟩
  · unfold completedShriekRationalMap
    rw [hid]
    exact (sfRationalConstructibleLocalization l E W.left).map_id _
  · unfold completedShriekRationalMap
    rw [hcomp]
    change (sfRationalConstructibleLocalization l E W.left).map
      ((ObjectProperty.homMk (completedShriekRealized l E R e t ge gt K he ht s) :
          (⟨_, ce⟩ : sfIntegralConstructibleCategory l E W.left) ⟶ ⟨_, ct⟩) ≫
        (ObjectProperty.homMk (completedShriekRealized l E R t v gt gv K ht hv z) :
          (⟨_, ct⟩ : sfIntegralConstructibleCategory l E W.left) ⟶ ⟨_, cv⟩)) = _
    exact (sfRationalConstructibleLocalization l E W.left).map_comp _ _
  · intro h
    subst s'
    rfl

/-- Composition comparisons are invertible on the node's normalized common-bounds domain.
Source: Stacks 0F7J, 0941 (blueprint: lem-sf-completed-shriek-composition-laws).

Proof: the supported-counit theorem makes the specified proper/open map invertible
on arbitrary systems. Its two whiskers are therefore invertible. The open and proper
compositors and equality transports are isomorphisms, so their composite is invertible.
The displayed domain hypotheses are retained but no finite evaluation is needed. -/
theorem completedShriekComposition_isIso (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (T : Compactification.Triangle f g) [QuasiCompact T.q]
    (M : System l E X) (hf : completedShriekDomain l E o T.cf M)
    (hg : completedShriekDomain l E o T.cg ((completedShriekF l E o T.cf).obj M))
    (hfg : completedShriekDomain l E o T.cfg M) :
    IsIso ((completedShriekA l E R T).app M) := by
  have _ := hl
  have _ := hf
  have _ := hg
  have _ := hfg
  have := systemProperOpenGammaIsIso l E o D R T.q T.cf.g T.p T.cg.i
    T.isPullback.w.symm
  dsimp only [completedShriekA, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  infer_instance

/-- Comparison identity and cocycle through a common refinement.
Source: Stacks 0F7J (blueprint: lem-sf-completed-shriek-composition-laws).

Proof: substitute the definition as reverse-refinement map followed by inverse
reverse-refinement map. The adjacent inverse factors cancel. Independence of the
chosen common refinement, proved above by equalization, gives the same cocycle
for three arbitrary choices of common refining towers. -/
theorem completedShriekComparisonCocycle (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (a b c d : Compactification f)
    (r : d.Refinement a) (s : d.Refinement b) (t : d.Refinement c)
    (M : System l E X) (ha : completedShriekDomain l E o a M)
    (hb : completedShriekDomain l E o b M) (hc : completedShriekDomain l E o c M)
    (hd : completedShriekDomain l E o d M) :
    (completedShriekComparisonVia l E D hl R a a d r r M ha ha hd = Iso.refl _) ∧
    (completedShriekComparisonVia l E D hl R a b d r s M ha hb hd ≪≫
      completedShriekComparisonVia l E D hl R b c d s t M hb hc hd =
        completedShriekComparisonVia l E D hl R a c d r t M ha hc hd) := by
  constructor
  · exact Iso.self_symm_id _
  · simp only [completedShriekComparisonVia, Iso.trans_assoc, Iso.symm_self_id_assoc]

/-- The specified raw rationalization followed by inclusion of one common finite field.
Source: blueprint algebraically closed coefficient convention, finite-stage pairs
(blueprint: lem-sf-completed-shriek-composition-laws). -/
def completedShriekCommonStage (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (E₀ : Padic.FiniteCoefficientFields l Ω) (W : Scheme.{u}) :
    sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀) W ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω W :=
  sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀) W ⋙
    (GeneralAlgebraicallyClosedCoefficients.inclusion E₀ :
      GeneralAlgebraicallyClosedCoefficients.Stage l Ω W E₀ ⥤ _)

/-- At a common coefficient field the specified scalar functor preserves every equation,
identity and composite, and a further finite coefficient extension preserves it again.
Source: blueprint fix-prop-coherence, final coefficient-transport paragraph
(blueprint: lem-sf-completed-shriek-composition-laws).

Proof: represent the finite collection of inputs and diagram arrows over E₀. First
apply raw scalar localization to the canonical integral arrows; the result is exactly
the specified rational arrow, with each component tensored with 1. The functor to the
common-stage category preserves the identity and composition equations below. For a
further field E₁ apply the actual completed scalar-extension functor, then raw
localization and stage inclusion again. This sends each already established equation
to its image equation, including refinements and whiskered maps. No Karoubi envelope
or arbitrary finite-field lift is used. -/
theorem completedShriekCommonStageLaws (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω]
    [IsAlgClosure ℚ_[l] Ω] (E₀ E₁ : Padic.FiniteCoefficientFields l Ω) (h : E₀ ≤ E₁)
    (W : Scheme.{u})
    (A B C : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀) W)
    (s s' : A ⟶ B) (z : B ⟶ C) :
    ((completedShriekCommonStage l Ω E₀ W).map (𝟙 A) = 𝟙 _) ∧
    ((completedShriekCommonStage l Ω E₀ W).map (s ≫ z) =
      (completedShriekCommonStage l Ω E₀ W).map s ≫
        (completedShriekCommonStage l Ω E₀ W).map z) ∧
    (s = s' → (completedShriekCommonStage l Ω E₀ W).map s =
      (completedShriekCommonStage l Ω E₀ W).map s') ∧
    (s = s' → (completedShriekCommonStage l Ω E₁ W).map
        ((GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E₀ E₁ h).map s) =
      (completedShriekCommonStage l Ω E₁ W).map
        ((GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω W E₀ E₁ h).map s')) := by
  refine ⟨(completedShriekCommonStage l Ω E₀ W).map_id A,
    (completedShriekCommonStage l Ω E₀ W).map_comp s z, ?_, ?_⟩
  · intro hss
    subst s'
    rfl
  · intro hss
    subst s'
    rfl

/-- Quasi-compactness of the intermediate open in a restriction tower.
Source: Stacks 0F7J (blueprint: lem-sf-completed-shriek-composition-laws). -/
instance completedShriekRestrictQC {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact g] (d : Compactification g) (c : Compactification (f ≫ d.i)) :
    QuasiCompact (Compactification.Triangle.ofRestrict d c).q :=
  inferInstanceAs (QuasiCompact (pullback.fst c.g d.i))

/-- The normalized integral compositor agrees with the already recorded constructible
compact-support compositor, using precisely its two Roos realization comparisons.
Source: Stacks 0F7J; blueprint fix-prop-coherence
(blueprint: lem-sf-completed-shriek-composition-laws).

Proof: on the restriction tower the two proper/open maps have the same open adjunct,
namely inverse proper/open restriction. Uniqueness of the adjunct equates them. Open
composition is the same adjunction conjugate; naturality moves the proper compositor
past open composition, giving the recorded tower formula. Its common-refinement
normalization uniquely characterizes sfFieldShriekCompositionIntegral. The outer
Roos comparisons below therefore identify it with the actual completed integral map.
This supplies the specified compositor rather than a new isomorphic replacement. -/
theorem completedShriekSpecifiedIntegral (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (R : Realizations l E D o)
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    (f : X ⟶ Y) (g : Y ⟶ Z) [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d : Compactification g) (c : Compactification (f ≫ d.i))
    (K : sfIntegralConstructibleCategory l E X) :
    (completedShriekIntegralA l E R (Compactification.Triangle.ofRestrict d c)).app K.obj =
      (PurCompactSupport.image (PurCompactSupport.completed l E) d).map
        ((sfQcqsCompactSupportRealization l E D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
          c.restrict).hom.app K) ≫
      (sfQcqsCompactSupportRealization l E D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) d).hom.app
        ((sfCompactSupportFiniteIntegralFunctor l D.k
          (PurCompactSupport.coefficientPrimeUnit l D hl)
          c.restrict E).obj K) ≫
      (sfIntegralConstructible l E Z).ι.map
        ((sfFieldShriekCompositionIntegral D l hl c.restrict d (d.comp c) E).hom.app K) ≫
      (sfQcqsCompactSupportRealization l E D.k (PurCompactSupport.coefficientPrimeUnit l D hl)
        (d.comp c)).inv.app K := by
  sorry

private theorem completedShriekCancelComparisons {C C' : Type*}
    [Category C] [Category C'] (F : C ⥤ C') {A B : C} {T U V : C'}
    (a : A ≅ B) (b : F.obj B ≅ T) (c : U ≅ V)
    (s : F.obj A ⟶ U) (t : T ⟶ V)
    (h : s = F.map a.hom ≫ b.hom ≫ t ≫ c.inv) :
    b.inv ≫ F.map a.inv ≫ s ≫ c.hom = t := by
  rw [h]
  simp [Category.assoc]

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

/-- The actual realized system compositor, in the constructible functor coordinates.
Only the two specified Roos comparisons change coordinates; the middle map is the
entire-system compositor transported by the recursive realization isomorphisms.
Source: Stacks 0F7J and the blueprint realization paragraph
(blueprint: lem-sf-completed-shriek-composition-laws). -/
def completedShriekConstructibleRealizedCompositor :
    (sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) d E).obj
      ((sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c.restrict E).obj ⟨_, hK⟩) ⟶
    (sfCompactSupportFiniteIntegralFunctor l D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) (d.comp c) E).obj ⟨_, hK⟩ :=
  ObjectProperty.homMk
    ((sfQcqsCompactSupportRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) d).inv.app
      ((sfCompactSupportFiniteIntegralFunctor l D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c.restrict E).obj ⟨_, hK⟩) ≫
    (PurCompactSupport.image (PurCompactSupport.completed l E) d).map
      ((sfQcqsCompactSupportRealization l E D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c.restrict).inv.app ⟨_, hK⟩) ≫
    completedShriekRealized l E R
      (.compactSupport g d (.compactSupport f c.restrict e))
      (.compactSupport (f ≫ g) (d.comp c) e) ge gt K he ht
      ((completedShriekA l E R (Compactification.Triangle.ofRestrict d c)).app
        (e.systemObj l E o ((inputReduction l E X).obj K))) ≫
    (sfQcqsCompactSupportRealization l E D.k
      (PurCompactSupport.coefficientPrimeUnit l D hl) (d.comp c)).hom.app ⟨_, hK⟩)

/-- The specified finite-field compositor is the raw rationalization of the realized
system compositor, after the prescribed constructible realization comparisons.
This identifies its actual components, so the transported unit, associativity and
refinement equations concern the recorded field comparison.
Source: Stacks 0F7J, blueprint raw rationalization paragraph
(blueprint: lem-sf-completed-shriek-composition-laws).

Proof: integral realization identifies the middle system arrow with the normalized
completed proper/open map. The specified-integral theorem identifies its Roos
conjugate with sfFieldShriekCompositionIntegral. Apply raw localization to this
equality. The uniquely determining normalization of sfFieldShriekCompositionRational
then identifies its component with exactly the displayed localized realized map.
This keeps the two Roos comparisons and recursive inner-expression comparison;
there is no new arbitrary lift or choice of a field-coefficient transformation. -/
theorem completedShriekSpecifiedRational :
    HEq ((sfFieldShriekCompositionRational D l hl c.restrict d (d.comp c) E).hom.app
      ((sfRationalConstructibleLocalization l E U.left).obj ⟨_, hK⟩))
      ((sfRationalConstructibleLocalization l E W.left).map
        (completedShriekConstructibleRealizedCompositor l E D hl o R f g d c e
          ge gt K he ht hK)) := by
  have hreal := completedShriekIntegralComposition l E D hl o R f g
    (Compactification.Triangle.ofRestrict d c) e ge gt K he ht
  have hspec := completedShriekSpecifiedIntegral l E D hl o R f.left g.left d c ⟨_, hK⟩
  have hcomp : completedShriekConstructibleRealizedCompositor l E D hl o R f g d c e
      ge gt K he ht hK =
      (sfFieldShriekCompositionIntegral D l hl c.restrict d (d.comp c) E).hom.app
        ⟨_, hK⟩ := by
    apply ObjectProperty.hom_ext
    exact completedShriekCancelComparisons
      (PurCompactSupport.image (PurCompactSupport.completed l E) d)
      ((sfQcqsCompactSupportRealization l E D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) c.restrict).app ⟨_, hK⟩)
      ((sfQcqsCompactSupportRealization l E D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) d).app
          ((sfCompactSupportFiniteIntegralFunctor l D.k
            (PurCompactSupport.coefficientPrimeUnit l D hl) c.restrict E).obj ⟨_, hK⟩))
      ((sfQcqsCompactSupportRealization l E D.k
        (PurCompactSupport.coefficientPrimeUnit l D hl) (d.comp c)).app ⟨_, hK⟩)
      _ _ (hreal.trans hspec)
  have hrat := (sfFieldShriekCompositionRational_existsUnique D l hl c.restrict d
    (d.comp c) E).exists.choose_spec ((sfRationalConstructibleLocalization l E U.left).obj
      ⟨_, hK⟩)
  exact hrat.trans (heq_of_eq (congrArg
    (sfRationalConstructibleLocalization l E W.left).map hcomp.symm))

end SpecifiedFieldComponents

private theorem completedShriekMapHEq {C C' : Type*} [Category C] [Category C']
    (F : C ⥤ C') {A A' B B' : C} (ha : A = A') (hb : B = B')
    {s : A ⟶ B} {t : A' ⟶ B'} (h : HEq s t) : HEq (F.map s) (F.map t) := by
  cases ha
  cases hb
  cases h
  rfl

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

/-- The unique Qbar compositor has exactly the common-stage image of the realized
entire-system compositor on every finite representative and nested input expression.
The unique gamma is the one of lem-zl-field-shriek-composition-qcqs; its defining
finite-stage formula is retained as well as the realized-system identification.
Source: Stacks 0F7J and the blueprint common finite-field transport paragraph
(blueprint: lem-sf-completed-shriek-composition-laws).

Proof: take the unique gamma normalized at all finite stages by the recorded
rational compositor. At the chosen stage, the preceding specified-rational theorem
identifies that component with raw localization of the actual realized map.
Applying the canonical inclusion gives exactly completedShriekCommonStage.map.
Thus the unit, associativity and refinement equations transported above are equations
of this gamma. All actions are universally quantified normalized actions; no choice
of an unrelated common-stage functor or transformation is introduced. -/
theorem completedShriekSpecifiedCommonStage :
    ∃ γ : Sf.system.functor ⋙ Sg.system.functor ≅ Sfg.system.functor,
      (∀ (E₀ : Padic.FiniteCoefficientFields l Ω)
        (L : GeneralAlgebraicallyClosedCoefficients.Stage l Ω U.left E₀),
        HEq (γ.hom.app ⟨E₀, L⟩)
          ((GeneralAlgebraicallyClosedCoefficients.inclusion E₀).map
            ((sfFieldShriekCompositionRational D l hl c.restrict d (d.comp c)
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀)).hom.app L))) ∧
      ∀ (E₀ : Padic.FiniteCoefficientFields l Ω)
        (o : Operations l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀))
        (R : Realizations l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀) D o)
        {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
        (e : Expression _ I X U)
        (ge : (Expression.compactSupport g d (.compactSupport f c.restrict e)).geometric)
        (gt : (Expression.compactSupport (f ≫ g) (d.comp c) e).geometric)
        (K : ∀ i, Integral l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀) (X i).left)
        (he : (Expression.compactSupport g d (.compactSupport f c.restrict e)).domain l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀) o K)
        (ht : (Expression.compactSupport (f ≫ g) (d.comp c) e).domain l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀) o K)
        (hK : sfIntegralConstructible l (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀)
          U.left ((e.evaluate (integralInterpretation l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀))).obj K)),
        HEq (γ.hom.app ⟨E₀, (sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀) U.left).obj ⟨_, hK⟩⟩)
          ((completedShriekCommonStage l Ω E₀ W.left).map
            (completedShriekConstructibleRealizedCompositor l
              (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀) D hl o R f g d c e
              ge gt K he ht hK)) := by
  obtain ⟨γ, hγ, _⟩ :=
    sfFieldShriekCompositionQbar_existsUnique D l hl c.restrict d (d.comp c) Ω Sf Sg Sfg
  refine ⟨γ, hγ, ?_⟩
  intro E₀ o R I _ X e ge gt K he ht hK
  refine (hγ E₀ _).trans ?_
  exact completedShriekMapHEq (GeneralAlgebraicallyClosedCoefficients.inclusion E₀) rfl rfl
    (completedShriekSpecifiedRational l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E₀) D hl o R f g d c e
      ge gt K he ht hK)

end SpecifiedCommonStageComponents

end WeilConjectures.IntegralSystemRealization

module

public import
WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekCompactificationBaseChange
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.Compactification.BaseChange
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.RefinementExchangeCoherence
import all Sheaf.Paper.RefinementExchangeCoherence
public import Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
public import Sheaf.AlgebraicGeometry.EtaleClopenMateNormalization
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.ExchangeFunctoriality
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.AlgebraicGeometry.TowerMateEvaluationScalars
public import Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import WeilConjectures.Compactification.Cofiltered
import Sheaf.AlgebraicGeometry.SingleLevelFiniteProperOpenTransport
import all Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
import Sheaf.CategoryTheory.MateIsoAlongEquivalences
public import Sheaf.Paper.RelativeCompactSupportPasting
import Sheaf.Paper.CompositionExchangeTowerH


/-! # Finite evaluation of compact-support exchanges and refinements

Source: Stacks Project, Tags 0F7B, 0F7C, 0F7F and 0ATU, and the strict-tower evaluation
refinement (blueprint: lem-pur-finite-compact-support-evaluation-refinement).

The ordinary maps are constructed from the ordinary adjunctions and clopen projector.
They are not defined as evaluations of tower maps. All comparisons use the existing
normalized evaluation maps and the composition-adjunction normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.StrictTower.FiniteCompactSupport
open MateEvaluationScalars
attribute [local irreducible] G R J adj towers_hasDerivedCategory
  Scheme.proEtaleRingModuleAdjunction Scheme.proEtaleRingModulePullback
  Scheme.proEtaleRingModuleDirectImage Scheme.proEtaleRingModuleAdjunctionNormalized
variable (B : Type (u + 1)) [CommRing B]

/-- The existing ordinary localization at the fixed coefficient universe of this site.
Source: Stacks 05RU (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
instance ordinaryDerivedCategory (X : Scheme.{u}) : HasDerivedCategory.{u + 2} (Modules B X) :=
  Scheme.proEtaleRingModules_hasDerivedCategory X (coefficients B X)

/-- Ordinary inverse-image composition, descended from the normalized module compositor.
Source: Stacks 07A7 (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def pullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) :
    g.{u} B (f ≫ h) ≅ g.{u} B h ⋙ g.{u} B f :=
  Functor.mapDerivedCategoryNatIso
    (moduleGComp.{u} B f h) ≪≫
    Functor.mapDerivedCategoryCompIso (modulePullback.{u} B h) (modulePullback.{u} B f)

/-- Ordinary direct-image composition with the composition-adjunction normalization.
Source: Stacks 07A7, 0D6E (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def pushComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Y ⟶ Z) :
    r.{u} B f ⋙ r.{u} B h ≅ r.{u} B (f ≫ h) :=
  conjugateIsoEquiv ((dAdj.{u} B h).comp (dAdj.{u} B f)) (dAdj.{u} B (f ≫ h)) (pullComp B f h)

/-- The ordinary identity inverse image, normalized by constant sections.
Source: Stacks 07A7 (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def pullId (X : Scheme.{u}) :
    g.{u} B (𝟙 X) ≅ 𝟭 (DerivedCategory (Modules B X)) :=
  Functor.mapDerivedCategoryNatIso
    (Adjunction.leftAdjointIdIso (clopenModuleAdj.{u} B (𝟙 X)) (moduleRId.{u} B X)) ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The ordinary direct-image identity is the conjugate of the exact identity.
Source: Stacks 07A7 (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def pushId (X : Scheme.{u}) :
    r.{u} B (𝟙 X) ≅ 𝟭 (DerivedCategory (Modules B X)) :=
  (conjugateIsoEquiv Adjunction.id (dAdj.{u} B (𝟙 X)) (pullId B X)).symm

/-- The ordinary square uses exactly the normalized inverse-image compositors.
Source: Stacks 07A7 (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def square {V W S T : Scheme.{u}} (k : V ⟶ W) (f : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = f ≫ i) :
    g.{u} B i ⋙ g.{u} B f ≅ g.{u} B p ⋙ g.{u} B k :=
  (pullComp B f i).symm ≪≫ eqToIso (congrArg (g.{u} B) h.symm) ≪≫ pullComp B k p

/-- The ordinary proper-square exchange is the derived unit-square-counit mate.
Source: Stacks 07A7 (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def properExchange {V W S T : Scheme.{u}} (k : V ⟶ W) (f : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = f ≫ i) :
    r.{u} B p ⋙ g.{u} B i ⟶ g.{u} B k ⋙ r.{u} B f :=
  _root_.AlgebraicGeometry.ProEtale.RelativeCompactSupport.ordinaryE B k f p i h

/-- Ordinary compact support relative to a supplied compactification, on unbounded complexes.
Source: Stacks 0F7F (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def ordinaryF {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    DerivedCategory (Modules B X) ⥤ DerivedCategory (Modules B Y) :=
  j.{u} B c.i ⋙ r.{u} B c.g

/-- The ordered ordinary exchange: proper mate followed by the canonical open comparison.
Source: Stacks 0F7F (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def ordinaryE {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (c : Compactification f) (c' : Compactification f')
    (x : X' ⟶ X) (y : Y' ⟶ Y) (s : c'.Z ⟶ c.Z)
    (si : IsPullback x c'.i c.i s) (sp : IsPullback s c'.g c.g y) :
    ordinaryF B c ⋙ g.{u} B y ⟶ g.{u} B x ⋙ ordinaryF B c' :=
  _root_.AlgebraicGeometry.ProEtale.RelativeCompactSupport.ordinaryH B c c' y x s sp si

/-- The ordinary refinement is the proper mate of the intrinsic clopen-section projector,
followed by the proper direct image, identity and composition comparisons.
Source: Stacks 0F7B, 0F7C (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def ordinaryC {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (v : c.Refinement d)
    (hf : QuasiCompact f := by infer_instance) : ordinaryF B d ⟶ ordinaryF B c := by
  letI : QuasiCompact c.i := c.quasiCompact_openImmersion hf
  letI : QuasiCompact d.i := d.quasiCompact_openImmersion hf
  exact Functor.whiskerRight
    (Functor.whiskerRight (pushId B X).inv (j.{u} B d.i) ≫
      singleDerivedGamma.{u} B c.i (𝟙 X) v.hom d.i
        (v.i_hom.trans (Category.id_comp d.i).symm)) (r.{u} B d.g) ≫
    Functor.whiskerLeft (j.{u} B c.i)
      ((pushComp B v.hom d.g).hom ≫ (eqToIso (congrArg (r.{u} B) v.hom_g)).hom)

/-- The actual compact-support evaluation comparison, evaluating first R and then J.
Source: Stacks 07A7, 0F7F (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def evaluationF {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    compositionF B c ⋙ ev B Y n ⟶ ev B X n ⋙ ordinaryF B c :=
  (_root_.AlgebraicGeometry.ProEtale.RelativeCompactSupport.supportEval B c n).hom


/-- Evaluation carries the ordered proper/open compactification exchange to its ordinary
counterpart for every unbounded tower object.
Source: Stacks 07A7, 0F7F (blueprint: lem-pur-finite-compact-support-evaluation-refinement).
Proof: evaluate the proper unit-square-counit factors using
lem-cbc-tower-mate-evaluation-scalars, and the open factor using
lem-cbc-tower-open-beta-normalization. Naturality moves the two endpoint comparisons
through the composite. No boundedness, origin witness or faithfulness is used. -/
theorem finiteCompactSupportEvaluationRefinement [Finite B] {X Y X' Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (x : X' ⟶ X) (y : Y' ⟶ Y) (sf : IsPullback x f' f y)
    (c : Compactification f) (c' : Compactification f') (s : c'.Z ⟶ c.Z)
    (si : IsPullback x c'.i c.i s) (sp : IsPullback s c'.g c.g y)
    (M : Derived B X) (n : ℕ) :
    (ev B Y' n).map ((compositionE B c c' x y s si.w sp.w si).app M) ≫
        (evaluationF B c' n).app ((G B x).obj M) ≫
        (ordinaryF B c').map ((evalG B x n).hom.app M) =
      (evalG B y n).hom.app ((compositionF B c).obj M) ≫
        (g B y).map ((evaluationF B c n).app M) ≫
        (ordinaryE B c c' x y s si sp).app ((ev B X n).obj M) := by
  have _sf := sf
  change
    (ev B Y' n).map ((compositionE B c c' x y s si.w sp.w si).app M) ≫
        (_root_.AlgebraicGeometry.ProEtale.RelativeCompactSupport.supportEval B c' n).hom.app
          ((G B x).obj M) ≫
        (_root_.AlgebraicGeometry.ProEtale.RelativeCompactSupport.ordinaryJ B c'.i ⋙
          _root_.AlgebraicGeometry.ProEtale.RelativeCompactSupport.ordinaryR B c'.g).map
          ((evalG B x n).hom.app M) =
      (evalG B y n).hom.app
          ((_root_.AlgebraicGeometry.ProEtale.StrictTower.J B c.i ⋙
            _root_.AlgebraicGeometry.ProEtale.StrictTower.R B c.g).obj M) ≫
        (_root_.AlgebraicGeometry.ProEtale.ConstantCompactificationExchange.ordinaryG B y).map
          ((_root_.AlgebraicGeometry.ProEtale.RelativeCompactSupport.supportEval B c n).hom.app M) ≫
        (_root_.AlgebraicGeometry.ProEtale.RelativeCompactSupport.ordinaryH B c c' y x s
          sp si).app ((ev B X n).obj M)
  rw [compositionE_eq_towerH B c c' x y s si.w sp.w si]
  exact (_root_.AlgebraicGeometry.ProEtale.RelativeCompactSupport.finiteEvaluation B c c' y x s
    sp si M ((J B c.i).obj M) n).2.2


/-- Evaluation of the normalized proper/open refinement includes the identity and
composition adjunctions, and needs no étale-origin witness.
Source: Stacks 0F7B, 0F7C (blueprint: lem-pur-finite-compact-support-evaluation-refinement).
Proof: evaluate gamma in the identity-left refinement square using its intrinsic
clopen-section projector and lem-cbc-tower-mate-evaluation-scalars. Evaluate the outer
proper direct image. The unit/counit equations identify its identity and composition
comparisons with pushId and pushComp, also by
lem-sfb-derived-composition-adjunction-normalization. Compose the resulting equations. -/
theorem refinement_evaluation [Finite B] {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (v : c.Refinement d) (M : Derived B X) (n : ℕ) :
    (ev B Y n).map ((refinementComparison B v).app M) ≫ (evaluationF B c n).app M =
      (evaluationF B d n).app M ≫ (ordinaryC B v).app ((ev B X n).obj M) := by
  sorry

variable [Finite B]

/-- The existing finite fixed-module presentation in constant-ring coordinates, with
its unique discrete topology fixed internally.
Source: Stacks 03DA, 099R (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def finitePresentation (X : Scheme.{u}) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) ⥤
      DerivedCategory (Modules B X) := by
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := discreteTopology_bot B
  exact (C B X B (RingHom.id B)).mapDerivedCategory

/-- The retained bounded-below fixed-coefficient étale-origin witness, in the ordinary
constant-ring coordinates used by evaluation. The coefficient ring is B itself.
Source: Stacks 099R (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
structure Origin (X : Scheme.{u}) (N : DerivedCategory (Modules B X)) where
  /-- The bounded-below pro-etale object in the fixed-module presentation. -/
  F : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
  /-- The dependency's retained etale antecedent and its specified isomorphism. -/
  witness : Scheme.FixedEtaleOriginWitness X B F
  /-- The canonical coefficient presentation identifies the object with N. -/
  iso : (finitePresentation B X).obj F.obj ≅ N

/-- The existing etale-to-ordinary comparison with the unique discrete coefficient topology.
Source: Stacks 099R (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def etalePresentation (X : Scheme.{u}) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ⥤
      DerivedCategory (Modules B X) := by
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := discreteTopology_bot B
  exact HD B X B (RingHom.id B)

/-- The existing etale open-extension comparison, with its open-unit normalization.
Source: Stacks 09AF (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def etaleOpen {U X : Scheme.{u}} (k : U ⟶ X) [IsOpenImmersion k] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) k).mapDerivedCategoryPlus ⋙
        etalePresentation B X ≅ etalePresentation B U ⋙ j B k := by
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := discreteTopology_bot B
  exact hJ B k B (RingHom.id B)

/-- The existing normalized total direct-image comparison from the etale site.
Source: Stacks 099R (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def etalePush {U X : Scheme.{u}} (f : U ⟶ X) :
    Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) f ⋙ etalePresentation B X ⟶
      etalePresentation B U ⋙ r B f := by
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := discreteTopology_bot B
  exact hR B f B (RingHom.id B)

/-- The ordinary clopen-projector mate is exactly the normalized finite etale
proper/open comparison on a bounded-below etale antecedent. Specializing its left
proper map to the identity gives the refinement normalization of ordinaryC.
Source: Stacks 0F7B; lem-cbc-proper-open-interchange-coherence
(blueprint: lem-pur-finite-compact-support-evaluation-refinement).
Proof: lem-cbc-finite-clopen-mate-site-transport identifies the etale and fixed-module
clopen-projector mates including the normalized derived units and counits. The
coefficient-presentation comparisons are adjunction mates with the same units, so
transport further to Modules B. Composing gives precisely the displayed equality.
The normalizedComparison in that theorem is the comparison selected by the recorded
properOpenInterchangeCoherence; its identity-left specialization is properOpenComparison.
Applying the proper image of the compactification gives the required C normalization. -/
theorem ordinaryGamma_etale {V W S T : Scheme.{u}}
    (k : V ⟶ W) (f : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper f] [IsProper p] (h : k ≫ p = f ≫ i)
    (L : DerivedCategory.Plus (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (etaleOpen B i).hom.app ((Etale.rightDerivedLowerStarPlus
        (ModuleCat.{u + 1} B) f).obj L) ≫
      (j B i).map ((etalePush B f).app L) ≫
      (singleDerivedGamma B k f p i h).app ((etalePresentation B V).obj L) =
    (etalePresentation B T).map
        ((Etale.ClopenMateNormalization.normalizedComparison B k f p i h).hom.app L) ≫
      (etalePush B p).app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} B) k).mapDerivedCategoryPlus.obj L) ≫
      (r B p).map ((etaleOpen B k).hom.app L) := by
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := discreteTopology_bot B
  exact singleLevelFiniteProperOpenTransport B B (RingHom.id B) k f p i h L

private def originEtaleIso {X : Scheme.{u}} {N : DerivedCategory (Modules B X)}
    (w : Origin B X N) :
    (etalePresentation B X).obj w.witness.complex ≅ N := by
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := discreteTopology_bot B
  exact (H B X B (RingHom.id B)).mapDerivedCategoryPlusCompatibility.app
      w.witness.complex ≪≫
    (Functor.mapDerivedCategoryCompIso
      (comparisonUpperStar (ModuleCat.{u + 1} B) X) (C B X B (RingHom.id B))).app
        w.witness.complex.obj ≪≫
    (finitePresentation B X).mapIso w.witness.iso ≪≫ w.iso

private theorem ordinaryGamma_isIso {V W S T : Scheme.{u}}
    (k : V ⟶ W) (f : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper f] [IsProper p] (h : k ≫ p = f ≫ i)
    (N : DerivedCategory (Modules B V)) (w : Origin B V N) :
    IsIso ((singleDerivedGamma B k f p i h).app N) := by
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := discreteTopology_bot B
  have := hR_isIso B f B (RingHom.id B)
  have := hR_isIso B p B (RingHom.id B)
  have he := ordinaryGamma_etale B k f p i h w.witness.complex
  have hcomp : IsIso
      ((etaleOpen B i).hom.app
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) f).obj
            w.witness.complex) ≫
        (j B i).map ((etalePush B f).app w.witness.complex) ≫
        (singleDerivedGamma B k f p i h).app
          ((etalePresentation B V).obj w.witness.complex)) := by
    rw [he]
    dsimp only [etalePush, etaleOpen, etalePresentation]
    infer_instance
  have hi : IsIso
      ((singleDerivedGamma B k f p i h).app
        ((etalePresentation B V).obj w.witness.complex)) := by
    have : IsIso (etalePush B f) := hR_isIso B f B (RingHom.id B)
    have hp : IsIso
        ((etaleOpen B i).hom.app
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) f).obj
            w.witness.complex) ≫
          (j B i).map ((etalePush B f).app w.witness.complex)) := by infer_instance
    have hcomp' : IsIso
        (((etaleOpen B i).hom.app
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) f).obj
            w.witness.complex) ≫
          (j B i).map ((etalePush B f).app w.witness.complex)) ≫
          (singleDerivedGamma B k f p i h).app
            ((etalePresentation B V).obj w.witness.complex)) := by
      simpa only [Category.assoc] using hcomp
    exact IsIso.of_isIso_comp_left
      ((etaleOpen B i).hom.app
          ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) f).obj
            w.witness.complex) ≫
        (j B i).map ((etalePush B f).app w.witness.complex)) _
  have hn := (singleDerivedGamma B k f p i h).naturality (originEtaleIso B w).hom
  have hc : IsIso
      ((r B f ⋙ j B i).map (originEtaleIso B w).hom ≫
        (singleDerivedGamma B k f p i h).app N) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left ((r B f ⋙ j B i).map (originEtaleIso B w).hom) _

attribute [local irreducible] pushComp pushId singleDerivedGamma

/-- Invertibility on precisely the finite bounded-below étale-origin domain.
Source: Stacks 0F7B (blueprint: lem-pur-finite-compact-support-evaluation-refinement).
Proof: transport the ordinary clopen-projector proper mate to the normalized finite
étale mate by lem-cbc-finite-clopen-mate-site-transport. On this domain the latter is
an isomorphism by lem-cbc-proper-open-interchange-coherence. Proper direct image and
both normalized compositors preserve invertibility. -/
theorem ordinaryC_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    [QuasiCompact f]
    {c d : Compactification f} (v : c.Refinement d)
    (N : DerivedCategory (Modules B X)) (w : Origin B X N) :
    IsIso ((ordinaryC B v).app N) := by
  let : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  let : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  let h := v.i_hom.trans (Category.id_comp d.i).symm
  let e := pushComp B v.hom d.g ≪≫ eqToIso (congrArg (r B) v.hom_g)
  have ha : ordinaryC B v =
      refinementPasting (j B c.i) (j B d.i) (r B (𝟙 X)) (r B v.hom)
        (r B d.g) (r B c.g) (pushId B X) e
        (singleDerivedGamma B c.i (𝟙 X) v.hom d.i h) := by
    unfold ordinaryC
    exact (refinementPasting_normalized (j B c.i) (j B d.i) (r B (𝟙 X))
      (r B v.hom) (r B d.g) (r B c.g) (pushId B X) e
      (singleDerivedGamma B c.i (𝟙 X) v.hom d.i h)).symm
  exact comparison_transport_isIso (j B c.i) (j B d.i) (r B (𝟙 X)) (r B v.hom)
    (r B d.g) (r B c.g) (pushId B X) e
    (singleDerivedGamma B c.i (𝟙 X) v.hom d.i h) (ordinaryC B v) ha N
    (ordinaryGamma_isIso B c.i (𝟙 X) v.hom d.i h N w)

/-- Pullback retains the full finite étale-origin domain, with no restriction on the map.
Source: Stacks 099R (blueprint: lem-pur-finite-compact-support-evaluation-refinement).
Proof: retain the étale inverse image of the witness antecedent. Exactness preserves
its lower bound; the canonical site-comparison pullback and coefficient comparisons
supply the retained isomorphism. This is the finite specialization of
refinementFiniteOrigin_pullback. -/
theorem pullOrigin {X X' : Scheme.{u}} (x : X' ⟶ X)
    (N : DerivedCategory (Modules B X)) (w : Origin B X N) :
    Nonempty (Origin B X' ((g B x).obj N)) := by
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := discreteTopology_bot B
  let F := (ProEtale.upperStar (ModuleCat.{u + 1} B) x).mapDerivedCategoryPlus.obj w.F
  let L := (Etale.upperStar (ModuleCat.{u + 1} B) x).mapDerivedCategoryPlus.obj
    w.witness.complex
  let e := Functor.mapDerivedCategorySquareIso
    (ProEtale.comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} B) x)
  let ep := Functor.mapDerivedCategorySquareIso (openBetaFinitePull B x)
  refine ⟨{ F := F, witness := { complex := L, iso := ?_ }, iso := ?_ }⟩
  · exact (e.app w.witness.complex.obj).symm ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} B) x).mapDerivedCategory.mapIso w.witness.iso
  · exact (ep.app w.F.obj).symm ≪≫ (g B x).mapIso w.iso

/-- The specified common-refinement ratio: first C₁, then the inverse of C₂.
Source: Stacks 0ATU (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def ordinaryI {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d e : Compactification f} (v : e.Refinement c) (t : e.Refinement d)
    (N : DerivedCategory (Modules B X)) (w : Origin B X N)
    (hf : QuasiCompact f := by infer_instance) :
    (ordinaryF B c).obj N ≅ (ordinaryF B d).obj N := by
  letI := hf
  letI := ordinaryC_isIso B v N w
  letI := ordinaryC_isIso B t N w
  exact asIso ((ordinaryC B v).app N) ≪≫ (asIso ((ordinaryC B t).app N)).symm

/-- The constant strict tower on an ordinary complex, defined by exact descent of
constant diagrams with identity transitions.
Source: Stacks 015F; levelwise abelian diagrams
(blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def constantTower (X : Scheme.{u}) : DerivedCategory (Modules B X) ⥤ Derived B X :=
  (Functor.const ℕᵒᵖ : Modules B X ⥤ Towers B X).mapDerivedCategory

/-- Every evaluation of the actual constant tower is canonically the original object.
Source: Stacks 015F (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def constantEvaluation (X : Scheme.{u}) (n : ℕ) :
    constantTower B X ⋙ ev B X n ≅ 𝟭 (DerivedCategory (Modules B X)) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫ Functor.mapDerivedCategoryIdIso _

/-- The compact-support evaluation maps really are comparison isomorphisms at every
unbounded tower object, without a witness.
Source: Stacks 07A7, 0D6E (blueprint: lem-pur-finite-compact-support-evaluation-refinement).
Proof: evaluationF is the composite of evalR and evalJ; evalR_isIso uses a K-injective
strict tower and its evaluated K-injective resolution, and evalJ is the exact termwise
comparison. Whiskering and composition preserve these isomorphisms. -/
theorem evaluationF_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) : IsIso (evaluationF B c n) := by
  have := ‹Finite B›
  have := evalR_isIso B c.g n
  unfold evaluationF
  infer_instance

/-- Identity and composition for the ordinary normalized refinement maps, restricted
pointwise to the stated witnessed domain.
Source: Stacks 0F7C (blueprint: lem-pur-finite-compact-support-evaluation-refinement).
Proof: place a representative of N in its constant strict tower. Its evaluations are N,
so apply lem-cbc-complete-proetale-refinement-exchange-coherence and evaluate its actual
identity and composition equations. The two evaluation formulas identify all factors
with ordinaryC; preservation of the derived units and counits fixes the compositors.
For a general tower apply this separately at each evaluation; no uniform bound is used. -/
theorem ordinaryC_identity_composition {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (N : DerivedCategory (Modules B X)) (w : Origin B X N) :
    (∀ c : Compactification f, (ordinaryC B (Compactification.Refinement.id c)).app N =
      𝟙 ((ordinaryF B c).obj N)) ∧
    (∀ {c d e : Compactification f} (v : c.Refinement d) (t : d.Refinement e),
      (ordinaryC B (v.comp t)).app N = (ordinaryC B t).app N ≫ (ordinaryC B v).app N) := by
  sorry

/-- The finite refinement/exchange square, including arbitrary base change.
Source: Stacks 0F7F (blueprint: lem-pur-finite-compact-support-evaluation-refinement).
Proof: use the constant tower of N in the tower refinement/exchange coherence equation.
The preceding evaluation identities preserve its proper mate, open beta and normalized
refinement factors. This gives the displayed equality. The witness pulls back along x,
so the primed refinement is invertible on the same domain. -/
theorem ordinaryC_exchange {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (x : X' ⟶ X) (y : Y' ⟶ Y) (sf : IsPullback x f' f y)
    (c₁ c₂ : Compactification f) (c₁' c₂' : Compactification f')
    (s₁ : c₁'.Z ⟶ c₁.Z) (s₂ : c₂'.Z ⟶ c₂.Z)
    (si₁ : IsPullback x c₁'.i c₁.i s₁) (sp₁ : IsPullback s₁ c₁'.g c₁.g y)
    (si₂ : IsPullback x c₂'.i c₂.i s₂) (sp₂ : IsPullback s₂ c₂'.g c₂.g y)
    (v : c₁.Refinement c₂) (v' : c₁'.Refinement c₂')
    (hv : v'.hom ≫ s₂ = s₁ ≫ v.hom)
    (N : DerivedCategory (Modules B X)) (w : Origin B X N) :
    (ordinaryE B c₂ c₂' x y s₂ si₂ sp₂).app N ≫
        (ordinaryC B v' (MorphismProperty.IsStableUnderBaseChange.of_isPullback
          sf inferInstance)).app ((g B x).obj N) =
      (g B y).map ((ordinaryC B v).app N) ≫
        (ordinaryE B c₁ c₁' x y s₁ si₁ sp₁).app N := by
  sorry

private theorem ordinaryC_parallel {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c d : Compactification f} (r s : d.Refinement c)
    (N : DerivedCategory (Modules B X)) (w : Origin B X N) :
    (ordinaryC B r).app N = (ordinaryC B s).app N := by
  obtain ⟨e, t, ht⟩ := IsCofilteredOrEmpty.cone_maps (C := Compactification f)
    (r : d ⟶ c) (s : d ⟶ c)
  have ht' : t.comp r = t.comp s := ht
  have hh := congrArg (fun a ↦ (ordinaryC B a).app N) ht'
  rw [(ordinaryC_identity_composition B N w).2,
    (ordinaryC_identity_composition B N w).2] at hh
  have := ordinaryC_isIso B t N w
  exact (cancel_mono ((ordinaryC B t).app N)).1 hh

private theorem ordinaryI_refine {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₁ c₂ d e : Compactification f}
    (r₁ : d.Refinement c₁) (r₂ : d.Refinement c₂) (t : e.Refinement d)
    (N : DerivedCategory (Modules B X)) (w : Origin B X N) :
    ordinaryI B (t.comp r₁) (t.comp r₂) N w = ordinaryI B r₁ r₂ N w := by
  have := ordinaryC_isIso B r₁ N w
  have := ordinaryC_isIso B r₂ N w
  have := ordinaryC_isIso B t N w
  apply Iso.ext
  simp only [ordinaryI, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  simp only [(ordinaryC_identity_composition B N w).2, IsIso.inv_comp,
    Category.assoc, IsIso.hom_inv_id_assoc]

private theorem ordinaryI_independent {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {c₁ c₂ d e : Compactification f}
    (r₁ : d.Refinement c₁) (r₂ : d.Refinement c₂)
    (s₁ : e.Refinement c₁) (s₂ : e.Refinement c₂)
    (N : DerivedCategory (Modules B X)) (w : Origin B X N) :
    ordinaryI B r₁ r₂ N w = ordinaryI B s₁ s₂ N w := by
  obtain ⟨a, t, v, -⟩ := IsCofilteredOrEmpty.cone_objs d e
  rw [← ordinaryI_refine B r₁ r₂ t N w, ← ordinaryI_refine B s₁ s₂ v N w]
  apply Iso.ext
  simp only [ordinaryI, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  simp only [ordinaryC_parallel B (t.comp r₁) (v.comp s₁) N w,
    ordinaryC_parallel B (t.comp r₂) (v.comp s₂) N w]

/-- Independence of every common-refinement ratio and its cocycle.
Source: Stacks 0ATU (blueprint: lem-pur-finite-compact-support-evaluation-refinement).
Proof: a further refinement multiplies both C factors on the same side, so it cancels
in C₂ inverse times C₁. Common refinements and equalizers of parallel arrows exist by
lem-cbc-compactifiable-cofiltered, proving independence of objects and arrows. On a
common refinement of three compactifications the middle inverse pair cancels, giving
the cocycle. This argument uses ordinaryC identity/composition at N, not faithfulness. -/
theorem ordinaryI_independence_cocycle {X Y : Scheme.{u}} {f : X ⟶ Y}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (N : DerivedCategory (Modules B X)) (w : Origin B X N) :
    (∀ {c d e e' : Compactification f}
      (v : e.Refinement c) (t : e.Refinement d)
      (v' : e'.Refinement c) (t' : e'.Refinement d),
      ordinaryI B v t N w = ordinaryI B v' t' N w) ∧
    (∀ {c₁ c₂ c₃ d₁₂ d₂₃ d₁₃ : Compactification f}
      (u₁ : d₁₂.Refinement c₁) (u₂ : d₁₂.Refinement c₂)
      (v₂ : d₂₃.Refinement c₂) (v₃ : d₂₃.Refinement c₃)
      (t₁ : d₁₃.Refinement c₁) (t₃ : d₁₃.Refinement c₃),
      ordinaryI B u₁ u₂ N w ≪≫ ordinaryI B v₂ v₃ N w = ordinaryI B t₁ t₃ N w) := by
  constructor
  · intro c d e e' v t v' t'
    exact ordinaryI_independent B v t v' t' N w
  · intro c₁ c₂ c₃ d₁₂ d₂₃ d₁₃ u₁ u₂ v₂ v₃ t₁ t₃
    obtain ⟨d, t, v, -⟩ := IsCofilteredOrEmpty.cone_objs d₁₂ d₂₃
    rw [← ordinaryI_refine B u₁ u₂ t N w,
      ordinaryI_independent B v₂ v₃ (t.comp u₂) (v.comp v₃) N w,
      ordinaryI_independent B t₁ t₃ (t.comp u₁) (v.comp v₃) N w]
    have := ordinaryC_isIso B (t.comp u₂) N w
    apply Iso.ext
    simp only [ordinaryI, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      Category.assoc, IsIso.inv_hom_id_assoc]

/-- Common-refinement ratios intertwine the specified ordered ordinary exchanges.
Source: Stacks 0F7F, 0ATU (blueprint: lem-pur-finite-compact-support-evaluation-refinement).
Proof: write ordinaryC_exchange twice for the two maps from the common refinement.
The second primed C is invertible on the pulled-back witness, so cancel it. The
resulting ratios are exactly ordinaryI by its definition. Independence makes the result
independent of the chosen common refinements. -/
theorem ordinaryI_exchange {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (x : X' ⟶ X) (y : Y' ⟶ Y) (sf : IsPullback x f' f y)
    (c₁ c₂ d : Compactification f) (c₁' c₂' d' : Compactification f')
    (s₁ : c₁'.Z ⟶ c₁.Z) (s₂ : c₂'.Z ⟶ c₂.Z) (sd : d'.Z ⟶ d.Z)
    (si₁ : IsPullback x c₁'.i c₁.i s₁) (sp₁ : IsPullback s₁ c₁'.g c₁.g y)
    (si₂ : IsPullback x c₂'.i c₂.i s₂) (sp₂ : IsPullback s₂ c₂'.g c₂.g y)
    (sid : IsPullback x d'.i d.i sd) (spd : IsPullback sd d'.g d.g y)
    (v₁ : d.Refinement c₁) (v₂ : d.Refinement c₂)
    (v₁' : d'.Refinement c₁') (v₂' : d'.Refinement c₂')
    (hv₁ : v₁'.hom ≫ s₁ = sd ≫ v₁.hom) (hv₂ : v₂'.hom ≫ s₂ = sd ≫ v₂.hom)
    (N : DerivedCategory (Modules B X)) (w : Origin B X N)
    (w' : Origin B X' ((g B x).obj N)) :
    (g B y).map (ordinaryI B v₁ v₂ N w).hom ≫
        (ordinaryE B c₂ c₂' x y s₂ si₂ sp₂).app N =
      (ordinaryE B c₁ c₁' x y s₁ si₁ sp₁).app N ≫
        (ordinaryI B v₁' v₂' ((g B x).obj N) w'
          (MorphismProperty.IsStableUnderBaseChange.of_isPullback sf inferInstance)).hom := by
  have hf' : QuasiCompact f' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback sf inferInstance
  have := ordinaryC_isIso B v₁ N w
  have := ordinaryC_isIso B v₂ N w
  have := ordinaryC_isIso B v₁' ((g B x).obj N) w'
  have := ordinaryC_isIso B v₂' ((g B x).obj N) w'
  have h₁ := ordinaryC_exchange B x y sf d c₁ d' c₁' sd s₁
    sid spd si₁ sp₁ v₁ v₁' hv₁ N w
  have h₂ := ordinaryC_exchange B x y sf d c₂ d' c₂' sd s₂
    sid spd si₂ sp₂ v₂ v₂' hv₂ N w
  dsimp only [ordinaryI, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  apply (cancel_mono ((ordinaryC B v₂').app ((g B x).obj N))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [h₂]
  simp only [← Functor.map_comp_assoc, IsIso.inv_hom_id, Category.comp_id]
  exact h₁.symm

/-- The normalized comparison from ordinary exact pullback to the fixed-module
left derived pullback, using the coefficient-presentation adjunction mate.
Source: Stacks 03DA, 07A7 (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def presentationPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finitePresentation B Y ⋙ g B f ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor ⋙
        finitePresentation B X := by
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := discreteTopology_bot B
  exact Functor.mapDerivedCategorySquareIso (openBetaFinitePull B f) ≪≫
    Functor.isoWhiskerRight
      (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).symm _

/-- The total direct-image comparison is the mate of the normalized inverse-image one.
Source: Stacks 07A7, 0D6E (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def presentationPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ProEtale.lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctor ⋙
        finitePresentation B Y ⟶
      finitePresentation B X ⋙ r B f :=
  mateEquiv (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (dAdj B f) (TwoSquare.mk _ _ _ _ (presentationPull B f).hom) |>.natTrans

/-- Exact descent of the normalized open-extension scalar-presentation comparison.
Source: Stacks 03DA, 09AE (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def presentationOpen {U X : Scheme.{u}} (k : U ⟶ X) [IsOpenImmersion k] :
    finitePresentation B U ⋙ j B k ≅
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} B) k).mapDerivedCategory ⋙
        finitePresentation B X := by
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := discreteTopology_bot B
  exact Functor.mapDerivedCategorySquareIso (openBetaFiniteOpen B k)

/-- The scalar-presentation comparison for the supplied compact-support operation.
Source: Stacks 03DA, 0F7F (blueprint: lem-pur-finite-compact-support-evaluation-refinement). -/
def presentationF {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c ⋙
        finitePresentation B Y ⟶ finitePresentation B X ⋙ ordinaryF B c :=
  Functor.whiskerLeft
      (ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} B) c.i).mapDerivedCategory
      (presentationPush B c.g) ≫
    Functor.whiskerRight (presentationOpen B c.i).inv (r B c.g)

/-- The normalized finite exchange is the project's specified fixed-coefficient map
under the canonical coefficient-presentation comparisons.
Source: Stacks 0F7F; fix-lem-exchanges, finite stage
(blueprint: lem-pur-finite-compact-support-evaluation-refinement).
Proof: coefficient-presentation pull and push comparisons are mates, hence preserve
both derived units and counits. The proper factor is therefore the same derived
base-change mate (lem-weil-pbc-transport-identifies-exchange). The open factor agrees
by lem-cbc-tower-open-beta-normalization. Composing gives the specified ordered map
of def-exchange-projection, hence the map named in fix-lem-exchanges. On witnessed
objects thm-cbc-finite-level-proetale identifies it with the transported étale map. -/
theorem ordinaryE_specified {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (x : X' ⟶ X) (y : Y' ⟶ Y) (sf : IsPullback x f' f y)
    (c : Compactification f) (c' : Compactification f') (s : c'.Z ⟶ c.Z)
    (si : IsPullback x c'.i c.i s) (sp : IsPullback s c'.g c.g y)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))) :
    (presentationPull B y).hom.app
        ((ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj K) ≫
      (finitePresentation B Y').map
        ((ProEtale.rightDerivedLowerShriekOfCompactificationBaseChange
          (ModuleCat.{u + 1} B) c c' si sp.toCommSq).app K) ≫
      (presentationF B c').app
        ((ProEtale.upperStar (ModuleCat.{u + 1} B) x).leftDerivedFunctor.obj K) =
    (g B y).map ((presentationF B c).app K) ≫
      (ordinaryE B c c' x y s si sp).app ((finitePresentation B X).obj K) ≫
      (ordinaryF B c').map ((presentationPull B x).hom.app K) := by
  sorry

/-- Independence of compactification transports equations of composites through the
specified common-refinement ratios. This is the pointwise pasting transport used for
finite exchanges; the arrows may be any compactification-relative pasting factors.
Source: Stacks 0F7C, 0F7F, 0ATU
(blueprint: lem-pur-finite-compact-support-evaluation-refinement).
Proof: substitute the definitions of the two transported factors and cancel the
middle inverse pair. The equality h states the original compactification-relative
pasting. Independence and the cocycle identify all exterior ratios. Apply this to the
exchange factors using ordinaryI_exchange and ordinaryE_specified, which identifies
them with the specified finite maps on the witnessed domain of fix-lem-exchanges. -/
theorem transport_pasting {X₁ X₂ X₃ Y : Scheme.{u}}
    {f₁ : X₁ ⟶ Y} {f₂ : X₂ ⟶ Y} {f₃ : X₃ ⟶ Y}
    [QuasiCompact f₁] [QuasiCompact f₂] [QuasiCompact f₃]
    (N₁ : DerivedCategory (Modules B X₁)) (w₁ : Origin B X₁ N₁)
    (N₂ : DerivedCategory (Modules B X₂)) (w₂ : Origin B X₂ N₂)
    (N₃ : DerivedCategory (Modules B X₃)) (w₃ : Origin B X₃ N₃)
    {a₁ a₂ da : Compactification f₁} {b₁ b₂ db : Compactification f₂}
    {c₁ c₂ dc : Compactification f₃}
    (a : da.Refinement a₁) (a' : da.Refinement a₂)
    (b : db.Refinement b₁) (b' : db.Refinement b₂)
    (c : dc.Refinement c₁) (c' : dc.Refinement c₂)
    (h₁ : (ordinaryF B a₁).obj N₁ ⟶ (ordinaryF B b₁).obj N₂)
    (h₂ : (ordinaryF B b₁).obj N₂ ⟶ (ordinaryF B c₁).obj N₃)
    (h₁₂ : (ordinaryF B a₁).obj N₁ ⟶ (ordinaryF B c₁).obj N₃)
    (h : h₁ ≫ h₂ = h₁₂) :
    ((ordinaryI B a a' N₁ w₁).inv ≫ h₁ ≫ (ordinaryI B b b' N₂ w₂).hom) ≫
        ((ordinaryI B b b' N₂ w₂).inv ≫ h₂ ≫ (ordinaryI B c c' N₃ w₃).hom) =
      (ordinaryI B a a' N₁ w₁).inv ≫ h₁₂ ≫ (ordinaryI B c c' N₃ w₃).hom := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, ← h]

/-- Evaluation preserves both derived adjunction structure maps, with exactly the
same canonical evaluation comparisons as the compact-support formulas above.
Source: Stacks 07A6, 07A7 (blueprint: lem-pur-finite-compact-support-evaluation-refinement).
Proof: the transpose-preservation clause of lem-cbc-tower-mate-evaluation-scalars,
specialized to identity maps and counits, gives these two equalities. These are the
normalizations used when evaluating both e and C, rather than underived replacements. -/
theorem derived_adjunction_evaluation {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (∀ M : Derived B Y,
      (ev B Y n).map ((adj B f).unit.app M) ≫
          (evalR B f n).app ((G B f).obj M) ≫
          (r B f).map ((evalG B f n).hom.app M) =
        (dAdj B f).unit.app ((ev B Y n).obj M)) ∧
    (∀ N : Derived B X,
      (ev B X n).map ((adj B f).counit.app N) =
        (evalG B f n).hom.app ((R B f).obj N) ≫
          (g B f).map ((evalR B f n).app N) ≫
          (dAdj B f).counit.app ((ev B X n).obj N)) := by
  have := ‹Finite B›
  exact evaluation_units_counits B f n

/-- The specified coefficient-presentation comparisons are isomorphisms on the
ordinary unbounded compact-support operations.
Source: Stacks 03DA, 07A7 (blueprint: lem-pur-finite-compact-support-evaluation-refinement).
Proof: finitePresentation comes from the canonical equivalence of fixed-module sheaves
and modules over the constant coefficient sheaf. Transporting the exact pullback
adjunction through that equivalence identifies its right adjoint; conjugate uniqueness
makes presentationPush invertible with the specified mate normalization. The open
comparison is already a unit-normalized isomorphism, giving the claim for presentationF. -/
theorem presentation_isIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) : IsIso (presentationPush B f) ∧ IsIso (presentationF B c) := by
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := discreteTopology_bot B
  have he (Z : Scheme.{u}) : (finitePresentation B Z).IsEquivalence := by
    have := realization_equivalence B Z
    exact Functor.isEquivalence_mapDerivedCategory (C B Z B (RingHom.id B))
  have hp (U V : Scheme.{u}) (t : U ⟶ V) : IsIso (presentationPush B t) := by
    have := he U
    have := he V
    exact isIso_mateEquiv_of_isEquivalence_of_fullyFaithful
      (ProEtale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) t)
      (dAdj B t) (finitePresentation B V) (finitePresentation B U) (presentationPull B t)
  refine ⟨hp X Y f, ?_⟩
  have := hp c.Z Y c.g
  unfold presentationF
  infer_instance

end AlgebraicGeometry.ProEtale.StrictTower.FiniteCompactSupport









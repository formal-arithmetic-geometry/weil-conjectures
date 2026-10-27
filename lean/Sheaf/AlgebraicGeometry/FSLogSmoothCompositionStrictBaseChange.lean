module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.FSLogSmoothEtale
public import Sheaf.AlgebraicGeometry.FSStrictLogMorphism
import Sheaf.AlgebraicGeometry.LogUniqueInfinitesimalLifting
import Sheaf.AlgebraicGeometry.LogLocalInfinitesimalLiftingComposition
import Sheaf.AlgebraicGeometry.LogInfinitesimalPullback
import Sheaf.AlgebraicGeometry.StrictEtaleLogChartTransport
import Sheaf.AlgebraicGeometry.SaturatedLogBlowupChartCover
import Sheaf.AlgebraicGeometry.FSLogInfinitesimalCriterion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Composition and strict base change for logarithmic smoothness

Source: ILO, Exposé VI 1.1--1.8, VIII 3.3.8--3.3.11, X 1.1--1.3;
Kato 1988, Theorem 3.5
(blueprint: lem-sfb-log-smooth-composition-strict-base-change).

All log schemes use the locally Noetherian fs interface. Strictness and equality
of composites retain the canonical maps of log sections. The statement includes
existence of strict base changes and invariance for every representative, locality
for arbitrary jointly surjective strict étale families, and towers of length zero.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem smoothChart_of_etaleChart {X Y : FineSaturatedLogScheme.{u}}
    {f : EtaleLogHom X Y} (c : FSLogChart f) (hc : c.IsEtaleChart) :
    c.IsSmoothChart := by
  rcases hc with ⟨hK, hC, hu, he⟩
  have := hC
  have := he
  have ht : Nat.card (CommGroup.torsion c.cokernel) = Nat.card c.cokernel :=
    Nat.card_congr (isMulTorsion_of_finite.torsionMulEquiv.toEquiv)
  refine ⟨hK, inferInstance, ?_, inferInstance⟩
  intro x
  rw [ht]
  exact hu x

private theorem smooth_of_etale {X Y : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X Y) (hf : f.IsLogEtale) : f.IsLogSmooth := by
  intro x
  obtain ⟨c, hx, hc⟩ := hf x
  exact ⟨c, hx, smoothChart_of_etaleChart c hc⟩

private theorem etale_id (X : FineSaturatedLogScheme.{u}) :
    (EtaleLogHom.id X).IsLogEtale := by
  apply ((EtaleLogHom.id X).infinitesimal_criterion).2.mpr
  exact ⟨inferInstanceAs (LocallyOfFinitePresentation (𝟙 X.scheme)),
    EtaleLogMap.uniqueLifts_id X.logStructure⟩

private theorem etale_comp {X Y Z : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X Y) (g : EtaleLogHom Y Z)
    (hf : f.IsLogEtale) (hg : g.IsLogEtale) : (f.comp g).IsLogEtale := by
  obtain ⟨hfp, hfl⟩ := f.infinitesimal_criterion.2.mp hf
  obtain ⟨hgp, hgl⟩ := g.infinitesimal_criterion.2.mp hg
  have := hfp
  have := hgp
  apply (f.comp g).infinitesimal_criterion.2.mpr
  exact ⟨inferInstanceAs (LocallyOfFinitePresentation (f.base ≫ g.base)),
    f.toLogMap.uniqueLifts_comp g.toLogMap hfl hgl⟩

private theorem logSmooth_comp {X Y Z : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X Y) (g : EtaleLogHom Y Z)
    (hf : f.IsLogSmooth) (hg : g.IsLogSmooth) : (f.comp g).IsLogSmooth := by
  obtain ⟨hfp, hfl⟩ := f.infinitesimal_criterion.1.mp hf
  obtain ⟨hgp, hgl⟩ := g.infinitesimal_criterion.1.mp hg
  have := hfp
  have := hgp
  apply (f.comp g).infinitesimal_criterion.1.mpr
  exact ⟨inferInstanceAs (LocallyOfFinitePresentation (f.base ≫ g.base)),
    f.toLogMap.localLifts_comp g.toLogMap hfl hgl⟩

private theorem smooth_baseChange {X X' Y Y' : FineSaturatedLogScheme.{u}}
    (f : EtaleLogHom X Y) (h : EtaleLogHom Y' Y)
    (p : EtaleLogHom X' X) (q : EtaleLogHom X' Y') (c : EtaleLogHom X' Y)
    (hh : h.IsStrict) (hp : p.IsStrict) (hpb : IsPullback p.base q.base f.base h.base)
    (hpc : p.CompEq f c) (hqc : q.CompEq h c) (hf : f.IsLogSmooth) :
    q.IsLogSmooth := by
  obtain ⟨hfp, hfl⟩ := f.infinitesimal_criterion.1.mp hf
  have hqp : LocallyOfFinitePresentation q.base :=
    MorphismProperty.of_isPullback hpb hfp
  have hpc' : p.toLogMap.CompEq f.toLogMap c.toLogMap := hpc
  have hqc' : q.toLogMap.CompEq h.toLogMap c.toLogMap := hqc
  have hs : p.toLogMap.comp f.toLogMap = q.toLogMap.comp h.toLogMap :=
    (EtaleLogMap.eq_comp_of_compEq hpc').symm.trans
      (EtaleLogMap.eq_comp_of_compEq hqc')
  apply q.infinitesimal_criterion.1.mpr
  exact ⟨hqp, p.toLogMap.localLifts_pullback q.toLogMap f.toLogMap h.toLogMap hs
    ((strictLogPullback_universal f h hh).2 X' p q c hp hpb hpc hqc) hfl⟩

private theorem etaleChart_of_bijective {X Y : FineSaturatedLogScheme.{u}}
    {f : EtaleLogHom X Y} (c : FSLogChart f)
    (hc : Function.Bijective c.groupMap) (he : IsIso c.comparison) :
    c.IsEtaleChart := by
  have hk : c.groupMap.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr hc.1
  have hr : c.groupMap.range = ⊤ := MonoidHom.range_eq_top.mpr hc.2
  have hks : Subsingleton c.groupMap.ker := by
    rw [hk]
    infer_instance
  have hcs : Subsingleton c.cokernel := by
    change Subsingleton (Algebra.GrothendieckGroup c.Q ⧸ c.groupMap.range)
    rw [hr]
    exact QuotientGroup.subsingleton_quotient_top
  refine ⟨inferInstance, inferInstance, ?_, inferInstance⟩
  intro x
  simp only [Nat.card_unique, Nat.cast_one]
  exact ⟨isUnit_one, isUnit_one⟩

private theorem etale_blowup {X X' : FineSaturatedLogScheme.{u}}
    (b : EtaleLogHom X' X) (I : X.logStructure.IdealFamily)
    (hb : IsSaturatedLogBlowup b I) : b.IsLogEtale := by
  intro x
  obtain ⟨c, hx, hg, he⟩ := saturatedLogBlowup_chartCover b I hb x
  exact ⟨c, hx, etaleChart_of_bijective c hg he⟩

private theorem logEtale_tower (T : SaturatedLogBlowupTower.{u})
    (hb : ∀ i : Fin T.length, (T.arrow i).IsLogEtale) :
    ∃ p : ∀ i : Fin (T.length + 1), EtaleLogHom (T.level i) (T.level 0),
      (p 0).IsIdentity ∧
        (∀ i : Fin T.length, (T.arrow i).CompEq (p i.castSucc) (p i.succ)) ∧
        (p ⟨T.length, Nat.lt_succ_self T.length⟩).IsLogEtale := by
  let p : ∀ i : Fin (T.length + 1), EtaleLogHom (T.level i) (T.level 0) :=
    Fin.induction (EtaleLogHom.id (T.level 0))
      (fun i p ↦ (T.arrow i).comp p)
  refine ⟨p, EtaleLogHom.id_isIdentity _, ?_, ?_⟩
  · intro i
    exact (T.arrow i).comp_compEq (p i.castSucc)
  · have he : ∀ i, (p i).IsLogEtale := by
      apply Fin.induction
      · exact etale_id _
      · intro i hi
        exact etale_comp (T.arrow i) (p i.castSucc) (hb i) hi
    exact he _


/-- Log smooth composition, strict base change and locality, and log étaleness of
saturated log blowups and their finite towers.

Source: ILO VI 1.1--1.8, VIII 3.3.8--3.3.11, X 1.1--1.3; Kato 1988, Theorem 3.5
(blueprint: lem-sfb-log-smooth-composition-strict-base-change).

Proof:
1. Construct log identities and composites on relative etale triangles, retaining
   all section maps. A finite cokernel is its own torsion subgroup; together with
   ordinary etale implies smooth, this proves log etale implies log smooth directly.
2. Use local infinitesimal lifting composition and composition of local finite
   presentation to apply the fs infinitesimal criterion. This proves smooth and
   mixed composition.
3. The strict log product construction gives an fs locally Noetherian product and
   the universal property for every strict representative. Project an infinitesimal
   test, take a local lift, and pair it with the fixed second projection. Uniqueness
   in the product proves the top triangle; the criterion proves smooth base change.
4. Pointwise strict etale chart transport gives both directions of locality. For
   descent, choose a preimage of each source point from the jointly surjective family.
5. Saturated blowup chart covers have bijective group maps and isomorphic comparisons.
   Their kernels and cokernels are trivial, their orders are one, and one is a unit.
   Hence every representative is log etale.
6. Identity and composition preserve unique infinitesimal lifting. By the criterion
   they preserve log etaleness. Define tower composites by dependent Fin.induction;
   their composite equations follow from construction. A second induction proves
   every composite log etale, including the identity at length zero.

The four geometric inputs are separated into the modules
LogLocalInfinitesimalLiftingComposition, StrictLogPullbackUniversal,
StrictEtaleLogChartTransport and SaturatedLogBlowupChartCover.
-/
theorem fsLogSmooth_composition_strictBaseChange :
    (∀ (X Y Z : FineSaturatedLogScheme.{u})
      (f : EtaleLogHom X Y) (g : EtaleLogHom Y Z),
      f.IsLogSmooth → g.IsLogSmooth →
        ∃ c : EtaleLogHom X Z, f.CompEq g c ∧ c.IsLogSmooth) ∧
    (∀ (X Y : FineSaturatedLogScheme.{u}) (f : EtaleLogHom X Y),
      f.IsLogEtale → f.IsLogSmooth) ∧
    (∀ (X Y Z : FineSaturatedLogScheme.{u})
      (f : EtaleLogHom X Y) (g : EtaleLogHom Y Z),
      f.IsLogEtale → g.IsLogSmooth →
        ∃ c : EtaleLogHom X Z, f.CompEq g c ∧ c.IsLogSmooth) ∧
    (∀ (X Y Y' : FineSaturatedLogScheme.{u})
      (f : EtaleLogHom X Y) (h : EtaleLogHom Y' Y),
      f.IsLogSmooth → h.IsStrict →
        ∃ (X' : FineSaturatedLogScheme.{u}) (p : EtaleLogHom X' X)
          (q : EtaleLogHom X' Y') (c : EtaleLogHom X' Y),
          p.IsStrict ∧ IsPullback p.base q.base f.base h.base ∧
            p.CompEq f c ∧ q.CompEq h c ∧ q.IsLogSmooth) ∧
    (∀ (X X' Y Y' : FineSaturatedLogScheme.{u})
      (f : EtaleLogHom X Y) (h : EtaleLogHom Y' Y)
      (p : EtaleLogHom X' X) (q : EtaleLogHom X' Y') (c : EtaleLogHom X' Y),
      h.IsStrict → p.IsStrict → IsPullback p.base q.base f.base h.base →
        p.CompEq f c → q.CompEq h c → f.IsLogSmooth → q.IsLogSmooth) ∧
    (∀ (X Y : FineSaturatedLogScheme.{u}) (f : EtaleLogHom X Y)
      (ι : Type v) (U V : ι → FineSaturatedLogScheme.{u})
      (a : ∀ i : ι, EtaleLogHom (U i) X) (b : ∀ i : ι, EtaleLogHom (V i) Y)
      (r : ∀ i : ι, EtaleLogHom (U i) (V i)) (c : ∀ i : ι, EtaleLogHom (U i) Y),
      (∀ i : ι, (a i).IsStrict ∧ Etale (a i).base) →
        (∀ i : ι, (b i).IsStrict ∧ Etale (b i).base) →
        (∀ i : ι, (a i).CompEq f (c i) ∧ (r i).CompEq (b i) (c i)) →
        (∀ x : X.scheme, ∃ (i : ι) (z : (U i).scheme), (a i).base z = x) →
        (f.IsLogSmooth ↔ ∀ i : ι, (r i).IsLogSmooth) ∧
          (f.IsLogEtale ↔ ∀ i : ι, (r i).IsLogEtale)) ∧
    (∀ (X X' : FineSaturatedLogScheme.{u}) (b : EtaleLogHom X' X)
      (I : X.logStructure.IdealFamily), IsSaturatedLogBlowup b I → b.IsLogEtale) ∧
    (∀ T : SaturatedLogBlowupTower.{u},
      ∃ p : ∀ i : Fin (T.length + 1), EtaleLogHom (T.level i) (T.level 0),
        (p 0).IsIdentity ∧
          (∀ i : Fin T.length, (T.arrow i).CompEq (p i.castSucc) (p i.succ)) ∧
          (p ⟨T.length, Nat.lt_succ_self T.length⟩).IsLogEtale) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y Z f g hf hg
    exact ⟨f.comp g, f.comp_compEq g, logSmooth_comp f g hf hg⟩
  · intro X Y f hf
    exact smooth_of_etale f hf
  · intro X Y Z f g hf hg
    exact ⟨f.comp g, f.comp_compEq g, logSmooth_comp f g (smooth_of_etale f hf) hg⟩
  · intro X Y Y' f h hf hh
    obtain ⟨X', p, q, c, hp, hpb, hpc, hqc⟩ :=
      (strictLogPullback_universal f h hh).1 (f.infinitesimal_criterion.1.mp hf).1
    exact ⟨X', p, q, c, hp, hpb, hpc, hqc,
      smooth_baseChange f h p q c hh hp hpb hpc hqc hf⟩
  · intro X X' Y Y' f h p q c hh hp hpb hpc hqc hf
    exact smooth_baseChange f h p q c hh hp hpb hpc hqc hf
  · intro X Y f ι U V a b r c ha hb hc hcover
    constructor
    · constructor
      · intro hf i z
        exact ((strictEtale_logChart_transport f (a i) (b i) (r i) (c i)
          (ha i).1 (ha i).2 (hb i).1 (hb i).2 (hc i).1 (hc i).2 z).1.mp (hf _))
      · intro hr x
        obtain ⟨i, z, hz⟩ := hcover x
        rw [← hz]
        exact ((strictEtale_logChart_transport f (a i) (b i) (r i) (c i)
          (ha i).1 (ha i).2 (hb i).1 (hb i).2 (hc i).1 (hc i).2 z).1.mpr (hr i z))
    · constructor
      · intro hf i z
        exact ((strictEtale_logChart_transport f (a i) (b i) (r i) (c i)
          (ha i).1 (ha i).2 (hb i).1 (hb i).2 (hc i).1 (hc i).2 z).2.mp (hf _))
      · intro hr x
        obtain ⟨i, z, hz⟩ := hcover x
        rw [← hz]
        exact ((strictEtale_logChart_transport f (a i) (b i) (r i) (c i)
          (ha i).1 (ha i).2 (hb i).1 (hb i).2 (hc i).1 (hc i).2 z).2.mpr (hr i z))
  · intro X X' b I hb
    exact etale_blowup b I hb
  · intro T
    exact logEtale_tower T (fun i ↦ etale_blowup (T.arrow i) (T.center i) (T.isBlowup i))

end AlgebraicGeometry

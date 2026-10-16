module

public import Sheaf.CategoryTheory.SiteSystemFiniteCoverings
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Finite precoverages and sheaf pullback transport

Source: Stacks Project, Sites, 00WW, 00WX, 03CB and finite-family Situation 0A34.
(blueprint: lem-weil-pbc-site-system-finite-sheaf-transport)
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory

private theorem finite_pullback_cover
    {C : Type u} [Category.{v} C] (P : Precoverage C)
    [P.IsStableUnderFiniteBaseChange] [P.HasPullbacks]
    (hfinite : ∀ (X : C) (R : Presieve X), R ∈ P X → Finite R.uncurry)
    {X Y : C} (R : Presieve X) (hR : R ∈ P X) (g : Y ⟶ X) :
    have := P.hasPullbacks_of_mem g hR
    R.pullbackArrows g ∈ P Y := by
  classical
  have := P.hasPullbacks_of_mem g hR
  let I := R.uncurry
  have : Finite I := hfinite X R hR
  let Z : I → C := fun i ↦ i.val.1
  let f : ∀ i : I, Z i ⟶ X := fun i ↦ i.val.2
  have heq : Presieve.ofArrows Z f = R := by
    apply le_antisymm
    · rintro _ _ ⟨i⟩
      exact i.property
    · intro T a ha
      exact Presieve.ofArrows.mk (⟨⟨T, a⟩, ha⟩ : I)
  have (i : I) : HasPullback (f i) g := R.hasPullback g i.property
  have hc := Precoverage.IsStableUnderFiniteBaseChange.mem_coverings_of_isPullback
    (J := P) f (heq ▸ hR) g
    (fun i ↦ pullback.snd (f i) g) (fun i ↦ pullback.fst (f i) g)
    (fun i ↦ (IsPullback.of_hasPullback (f i) g).flip)
  have hpb : Presieve.ofArrows (fun i ↦ pullback (f i) g)
      (fun i ↦ pullback.snd (f i) g) = R.pullbackArrows g := by
    apply le_antisymm
    · rintro _ _ ⟨i⟩
      exact Presieve.pullbackArrows.mk _ _ i.property
    · rintro _ _ ⟨T, a, ha⟩
      exact Presieve.ofArrows.mk (⟨⟨T, a⟩, ha⟩ : I)
  dsimp only
  rw [← hpb]
  exact hc

/-- Continuity follows from finite covering pullbacks and preservation of pairwise pullbacks.
Source: Stacks Sites 00WV and 00WW. Proof: present a covering by its finite type of distinct
arrows, base change that family, and use the pairwise-pullback sheaf criterion.
(blueprint: lem-weil-pbc-site-system-finite-sheaf-transport) -/
theorem continuous_of_finite_pullbacks
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (U : C ⥤ D) (P : Precoverage C) (Q : Precoverage D)
    [P.IsStableUnderFiniteBaseChange] [P.HasPullbacks]
    (hfinite : ∀ (X : C) (R : Presieve X), R ∈ P X → Finite R.uncurry)
    (hcover : ∀ (X : C) (R : Presieve X), R ∈ P X → R.map U ∈ Q (U.obj X))
    (hpres : ∀ (X Y Z : C) (R : Presieve X), R ∈ P X →
      ∀ (f : Y ⟶ X) (g : Z ⟶ X), R f → PreservesLimit (cospan f g) U) :
    U.IsContinuous P.toGrothendieck Q.toGrothendieck := by
  constructor
  intro G
  have hG := G.property
  rw [isSheaf_iff_isSheaf_of_type] at hG
  rw [P.isSheaf_toGrothendieck_iff]
  intro X Y g R hR
  have := P.hasPullbacks_of_mem g hR
  rw [← Sieve.pullbackArrows_comm, ← Presieve.isSheafFor_iff_generate]
  have hT := finite_pullback_cover P hfinite R hR g
  let T := R.pullbackArrows g
  have : T.HasPairwisePullbacks := P.hasPairwisePullbacks_of_mem hT
  have : U.PreservesPairwisePullbacks T := by
    constructor
    intro Y Z f g hf hg
    exact hpres _ Y Z T hT f g hf
  rw [Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks]
  exact hG.isSheafFor_of_mem_precoverage (hcover _ T hT)

/-- A continuous equivalence with continuous inverse has exact sheaf pullback.
Source: Stacks Sites 00WW and 00WX. Proof: the unit and counit induce inverse sheaf
pushforwards. A left adjoint of an equivalence is an equivalence; hence it preserves
limits, and it preserves colimits as a left adjoint. Transfer to the constructed pullback.
(blueprint: lem-weil-pbc-site-system-finite-sheaf-transport) -/
theorem continuous_equivalence_pullback_exact
    {A B : Type u} [SmallCategory A] [SmallCategory B]
    (JA : GrothendieckTopology A) (JB : GrothendieckTopology B)
    (p : A ⥤ B) (e : B ⥤ A)
    (eta : 𝟭 A ≅ p ⋙ e) (epsilon : e ⋙ p ≅ 𝟭 B)
    [p.IsContinuous JA JB] [e.IsContinuous JB JA] :
    PreservesFiniteLimits (sheafPullback p (Type u) JA JB) ∧
    PreservesFiniteColimits (sheafPullback p (Type u) JA JB) := by
  have : (e ⋙ p).IsContinuous JB JB := Functor.isContinuous_comp e p JB JA JB
  have : (p ⋙ e).IsContinuous JA JA := Functor.isContinuous_comp p e JA JB JA
  let ec := e.sheafPushforwardContinuousComp p (Type u) JB JA JB ≪≫
    Functor.sheafPushforwardContinuousId' epsilon (Type u) JB
  let ea := p.sheafPushforwardContinuousComp e (Type u) JA JB JA ≪≫
    Functor.sheafPushforwardContinuousId' eta.symm (Type u) JA
  have : (p.sheafPushforwardContinuous (Type u) JA JB).IsEquivalence :=
    Functor.IsEquivalence.mk' _ ec.symm ea
  let adj := Functor.sheafAdjunctionContinuous p (Type u) JA JB
  have : (p.sheafPullback (Type u) JA JB).IsEquivalence :=
    adj.isEquivalence_left_of_isEquivalence_right
  have : PreservesLimitsOfSize.{0, 0} (p.sheafPullback (Type u) JA JB) :=
    adj.toEquivalence.symm.toAdjunction.rightAdjoint_preservesLimits
  have : PreservesFiniteLimits (p.sheafPullback (Type u) JA JB) :=
    PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _
  exact ⟨preservesFiniteLimits_of_natIso (sheafPullbackIso p (Type u) JA JB),
    preservesFiniteColimits_of_natIso (sheafPullbackIso p (Type u) JA JB)⟩

/-- Exact sheaf pullback is stable under composing continuous functors.
Source: Stacks Sites 03CB. Proof: compose the pullback adjunctions and identify the right
adjoint with pushforward along the composite. Uniqueness of left adjoints identifies
its pullback with the composite of the two exact pullbacks.
(blueprint: lem-weil-pbc-site-system-finite-sheaf-transport) -/
theorem continuous_composite_pullback_exact
    {A B C : Type u} [SmallCategory A] [SmallCategory B] [SmallCategory C]
    (JA : GrothendieckTopology A) (JB : GrothendieckTopology B)
    (JC : GrothendieckTopology C) (p : A ⥤ B) (q : B ⥤ C)
    [p.IsContinuous JA JB] [q.IsContinuous JB JC]
    [PreservesFiniteLimits (sheafPullback p (Type u) JA JB)]
    [PreservesFiniteColimits (sheafPullback p (Type u) JA JB)]
    [PreservesFiniteLimits (sheafPullback q (Type u) JB JC)]
    [PreservesFiniteColimits (sheafPullback q (Type u) JB JC)] :
    have : (p ⋙ q).IsContinuous JA JC := Functor.isContinuous_comp p q JA JB JC
    PreservesFiniteLimits (sheafPullback (p ⋙ q) (Type u) JA JC) ∧
    PreservesFiniteColimits (sheafPullback (p ⋙ q) (Type u) JA JC) := by
  have : (p ⋙ q).IsContinuous JA JC := Functor.isContinuous_comp p q JA JB JC
  let a := (sheafAdjunctionContinuous p (Type u) JA JB).comp
    (sheafAdjunctionContinuous q (Type u) JB JC)
  let b := a.ofNatIsoRight (p.sheafPushforwardContinuousComp q (Type u) JA JB JC)
  let t := b.leftAdjointUniq (sheafAdjunctionContinuous (p ⋙ q) (Type u) JA JC)
  have : PreservesFiniteLimits
      (sheafPullback p (Type u) JA JB ⋙ sheafPullback q (Type u) JB JC) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits
      (sheafPullback p (Type u) JA JB ⋙ sheafPullback q (Type u) JB JC) :=
    comp_preservesFiniteColimits _ _
  exact ⟨preservesFiniteLimits_of_natIso t, preservesFiniteColimits_of_natIso t⟩

/-- Evaluation and a strict section give exact sheaf pullbacks for the finite precoverage.
Source: Stacks Sites 00WW, 00WX, Situation 0A34. Proof: both equivalences preserve covers
and all pullbacks, so the finite covering criterion proves continuity in both directions.
Their comparison with inverse functors supplies a unit and counit, and the continuous
sheaf equivalence result gives exactness.
(blueprint: lem-weil-pbc-site-system-finite-sheaf-transport) -/
theorem finiteEquivalencePrecoverage_sheaf_equivalence
    {A B : Type u} [SmallCategory A] [SmallCategory B]
    (p : A ⥤ B) [p.IsEquivalence] (P : Precoverage B)
    [P.HasIsos] [P.IsStableUnderFiniteComposition] [P.IsStableUnderFiniteBaseChange]
    [P.HasPullbacks] (e : B ⥤ A) [e.IsEquivalence] (hep : e ⋙ p = 𝟭 B)
    (hfinite : ∀ (X : B) (R : Presieve X), R ∈ P X → Finite R.uncurry) :
    ∃ (_ : p.IsContinuous (finiteEquivalencePrecoverage p P).toGrothendieck
        P.toGrothendieck),
      ∃ (_ : e.IsContinuous P.toGrothendieck
          (finiteEquivalencePrecoverage p P).toGrothendieck),
        (PreservesFiniteLimits (sheafPullback p (Type u)
          (finiteEquivalencePrecoverage p P).toGrothendieck P.toGrothendieck) ∧
        PreservesFiniteColimits (sheafPullback p (Type u)
          (finiteEquivalencePrecoverage p P).toGrothendieck P.toGrothendieck)) ∧
        (PreservesFiniteLimits (sheafPullback e (Type u) P.toGrothendieck
          (finiteEquivalencePrecoverage p P).toGrothendieck) ∧
        PreservesFiniteColimits (sheafPullback e (Type u) P.toGrothendieck
          (finiteEquivalencePrecoverage p P).toGrothendieck)) := by
  let Q := finiteEquivalencePrecoverage p P
  have hp : p.IsContinuous Q.toGrothendieck P.toGrothendieck :=
    continuous_of_finite_pullbacks p Q P (finiteEquivalencePrecoverage_finite p P)
      (fun _ _ hR => hR.2) (by intros; infer_instance)
  have he : e.IsContinuous P.toGrothendieck Q.toGrothendieck :=
    continuous_of_finite_pullbacks e P Q hfinite
      (fun X R hR => (finiteEquivalencePrecoverage_inclusion p P e hep hfinite X R).mp hR)
      (by intros; infer_instance)
  let a : p ≅ e.inv := p.leftUnitor.symm ≪≫
    Functor.isoWhiskerRight e.asEquivalence.counitIso.symm p ≪≫
    Functor.associator e.inv e p ≪≫ Functor.isoWhiskerLeft e.inv (eqToIso hep) ≪≫
    e.inv.rightUnitor
  let eta : 𝟭 A ≅ p ⋙ e :=
    (Functor.isoWhiskerRight a e ≪≫ e.asEquivalence.counitIso).symm
  exact ⟨hp, he,
    continuous_equivalence_pullback_exact Q.toGrothendieck P.toGrothendieck
      p e eta (eqToIso hep),
    continuous_equivalence_pullback_exact P.toGrothendieck Q.toGrothendieck
      e p (eqToIso hep).symm eta.symm⟩

/-- Transport exact sheaf pullbacks along a comparison with a composite.
Source: Stacks Sites 03CB, 00WW and 00WX. Proof: first compose p and U, and then e.
Compose their adjunctions and identify pushforwards using the composition isomorphism.
The comparison theta identifies the pushforward of T with that of the composite;
uniqueness of left adjoints transfers finite-limit and finite-colimit preservation.
(blueprint: lem-weil-pbc-site-system-finite-sheaf-transport) -/
theorem continuous_transport_pullback_exact
    {A B C D : Type u}
    [SmallCategory A] [SmallCategory B] [SmallCategory C] [SmallCategory D]
    (JA : GrothendieckTopology A) (JB : GrothendieckTopology B)
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (p : A ⥤ C) (U : C ⥤ D) (e : D ⥤ B) (T : A ⥤ B)
    [p.IsContinuous JA JC] [U.IsContinuous JC JD] [e.IsContinuous JD JB]
    [T.IsContinuous JA JB]
    [PreservesFiniteLimits (sheafPullback p (Type u) JA JC)]
    [PreservesFiniteColimits (sheafPullback p (Type u) JA JC)]
    [PreservesFiniteLimits (sheafPullback U (Type u) JC JD)]
    [PreservesFiniteColimits (sheafPullback U (Type u) JC JD)]
    [PreservesFiniteLimits (sheafPullback e (Type u) JD JB)]
    [PreservesFiniteColimits (sheafPullback e (Type u) JD JB)]
    (theta : T ≅ (p ⋙ U) ⋙ e) :
    PreservesFiniteLimits (sheafPullback T (Type u) JA JB) ∧
    PreservesFiniteColimits (sheafPullback T (Type u) JA JB) := by
  have : (p ⋙ U).IsContinuous JA JD := Functor.isContinuous_comp p U JA JC JD
  obtain ⟨hpulim, hpucolim⟩ := continuous_composite_pullback_exact JA JC JD p U
  have : ((p ⋙ U) ⋙ e).IsContinuous JA JB :=
    Functor.isContinuous_comp (p ⋙ U) e JA JD JB
  obtain ⟨hwlim, hwcolim⟩ := continuous_composite_pullback_exact JA JD JB (p ⋙ U) e
  let d := Functor.sheafPushforwardContinuousIso theta (Type u) JA JB
  let a := ((sheafAdjunctionContinuous T (Type u) JA JB).ofNatIsoRight d).leftAdjointUniq
    (sheafAdjunctionContinuous ((p ⋙ U) ⋙ e) (Type u) JA JB)
  exact ⟨preservesFiniteLimits_of_natIso a.symm,
    preservesFiniteColimits_of_natIso a.symm⟩

end CategoryTheory

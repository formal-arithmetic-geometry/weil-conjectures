/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.OpenSourceComposition
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.EtaleSumRightAdjointCoherenceSupplement
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion

/-! # Unbounded compact-support exchange under an isomorphic Cartesian apex

Source: Stacks Project, More on Etale Cohomology, Tags 0F7I--0F7L,
`lemma-shriek-well-defined`, `lemma-shriek-composition`, `lemma-base-change-shriek`
(blueprint: lem-pur-unbounded-exceptional-exchange-apex-pasting).

The auxiliary comparison uses the specified compact-support compositor and the actual
extension/restriction counit for the open isomorphism. All functors act on ordinary
unbounded derived categories of constant-coefficient module sheaves.
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical compact-support comparison for changing the source by an isomorphism.
It is the inverse compact-support compositor, the open-immersion identification for `e`,
and the invertible extension/restriction counit, with the functor associators restored.
Thus its normalization is fixed before stating the exchange identity.
Source: Stacks Tags 0F7I--0F7K, source-open composition and canonical comparisons
(blueprint: lem-pur-unbounded-exceptional-exchange-apex-pasting). -/
noncomputable def unboundedEtaleApexSupportIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z P T : Scheme.{u}} (e : Z ≅ P) (r : P ⟶ T)
    [HasCompactification r] [HasCompactification (e.hom ≫ r)]
    [QuasiCompact (e.hom ≫ r)] :
    (upperStar (ModuleCat.{u + 1} A) e.hom).mapDerivedCategory ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e.hom ≫ r) ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) r :=
  Functor.isoWhiskerLeft (upperStar (ModuleCat.{u + 1} A) e.hom).mapDerivedCategory
      (unboundedEtaleLowerShriekCompIso A e.hom r).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (upperStar (ModuleCat.{u + 1} A) e.hom).mapDerivedCategory
          (rightDerivedLowerShriekIsoOfIsOpenImmersion A e.hom) ≪≫
        asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e.hom).counit)
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) r) ≪≫
    Functor.leftUnitor _

private lemma open_source_mate
    (F : CompactSupportFormalism.{_, _, u})
    {W X Y : Scheme.{u}} (e : W ⟶ X) (i : X ⟶ Y)
    [IsOpenImmersion e] [IsOpenImmersion i]
    (w : e ≫ i = (e ≫ i) ≫ 𝟙 Y) (K : F.obj X) :
    (F.baseChange e (e ≫ i) i (𝟙 Y) w).app K ≫
        (F.pbId Y).hom.app ((F.sh i).obj K) =
      (F.shComp' e i (e ≫ i) rfl).hom.app ((F.pb e).obj K) ≫
        (F.sh i).map ((F.shAdj e).counit.app K) := by
  -- Compare adjuncts using the actual units of the open adjunctions.
  apply ((F.shAdj (e ≫ i)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hb := unit_mateEquiv_symm (F.shAdj i) (F.shAdj (e ≫ i))
    (TwoSquare.mk _ _ _ _ (F.sqIso e (e ≫ i) i (𝟙 Y) w).hom) K
  change (F.pb e).map ((F.shAdj i).unit.app K) ≫
      (F.sqIso e (e ≫ i) i (𝟙 Y) w).hom.app ((F.sh i).obj K) =
    (F.shAdj (e ≫ i)).unit.app ((F.pb e).obj K) ≫
      (F.pb (e ≫ i)).map ((F.baseChange e (e ≫ i) i (𝟙 Y) w).app K) at hb
  rw [← Category.assoc, ← hb]
  have hc := unit_conjugateEquiv_symm
    ((F.shAdj e).comp (F.shAdj i)) (F.shAdj (e ≫ i))
    (F.pbComp' e i (e ≫ i) rfl).inv ((F.pb e).obj K)
  change _ = (F.shAdj (e ≫ i)).unit.app ((F.pb e).obj K) ≫
    (F.pb (e ≫ i)).map
      ((F.shComp' e i (e ≫ i) rfl).hom.app ((F.pb e).obj K)) at hc
  rw [← Category.assoc, ← hc]
  rw [F.sqIso_eq _ _ _ _ w (e ≫ i) rfl (Category.comp_id _)]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    F.pbComp'_id_right_hom_app, Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  simp only [CategoryTheory.Functor.map_id]
  simp only [Adjunction.comp_unit_app, Category.assoc]
  rw [← (F.pbComp' e i (e ≫ i) rfl).inv.naturality]
  simp only [Functor.comp_map]
  rw [← Functor.map_comp_assoc]
  rw [(F.shAdj i).unit_naturality]
  rw [Functor.map_comp]
  simp only [Functor.comp_obj, Functor.id_obj, Category.assoc, Category.comp_id,
    (F.shAdj e).right_triangle_components_assoc]

private lemma source_model_exchange
    (F : CompactSupportFormalism.{_, _, u}) [F.HasBaseChange]
    {W X Y : Scheme.{u}} {f : X ⟶ Y} (e : W ≅ X) (c : Compactification f)
    (hi : IsPullback e.hom (c.precomp e.hom).i c.i (𝟙 c.Z))
    (hp : IsPullback (𝟙 c.Z) c.g c.g (𝟙 Y)) (K : F.obj X) :
    (F.shriekBaseChange c (c.precomp e.hom) (𝟙 c.Z) hi hp).natTrans.app K ≫
        (F.pf c.g).map
          ((F.shComp' e.hom c.i (e.hom ≫ c.i) rfl).hom.app ((F.pb e.hom).obj K) ≫
            (F.sh c.i).map ((F.shAdj e.hom).counit.app K)) =
      (F.pbId Y).hom.app ((F.shriek c).obj K) := by
  have := CompactSupportFormalism.HasBaseChange.isIso_baseChange (F := F) hi
  dsimp only [Compactification.precomp] at *
  have hb := open_source_mate F e.hom c.i hi.w K
  have hb' : inv ((F.baseChange e.hom (e.hom ≫ c.i) c.i (𝟙 c.Z) hi.w).app K) ≫
      (F.shComp' e.hom c.i (e.hom ≫ c.i) rfl).hom.app ((F.pb e.hom).obj K) ≫
        (F.sh c.i).map ((F.shAdj e.hom).counit.app K) =
      (F.pbId c.Z).hom.app ((F.sh c.i).obj K) := by
    rw [← hb, IsIso.inv_hom_id_assoc]
  dsimp only [CompactSupportFormalism.shriekBaseChange]
  rw [ExchangeFormalism.shriekBaseChange_app]
  rw [F.pfBaseChange_id_horiz]
  simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.mk,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Category.id_comp,
    Category.assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  simp only [Functor.comp_obj, Functor.id_obj] at hb' ⊢
  rw [hb', Iso.inv_hom_id_app]
  simp
  rfl

private lemma apex_support_model
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z P T : Scheme.{u}} [IsNoetherian Z] [IsNoetherian P] [IsNoetherian T]
    (e : Z ≅ P) (r : P ⟶ T)
    [IsSeparated r] [LocallyOfFiniteType r] [QuasiCompact r]
    [HasCompactification r] [HasCompactification (e.hom ≫ r)]
    [QuasiCompact (e.hom ≫ r)] (c : Compactification r)
    (K : DerivedCategoryModule A P) :
    (unboundedEtaleApexSupportIso A e r).hom.app K =
      (rightDerivedLowerShriekIso A (c.precomp e.hom)).inv.app
          (((upperStar (ModuleCat.{u + 1} A) e.hom).mapDerivedCategory).obj K) ≫
        (rightDerivedLowerStar (ModuleCat.{u + 1} A) c.g).map
          ((mapDerivedCategoryOpenImmersionLowerShriekComp
              (ModuleCat.{u + 1} A) e.hom c.i).hom.app
            (((upperStar (ModuleCat.{u + 1} A) e.hom).mapDerivedCategory).obj K) ≫
            ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory).map
              ((derivedOpenImmersionLowerShriekUpperStarAdjunction
                (ModuleCat.{u + 1} A) e.hom).counit.app K)) ≫
        (rightDerivedLowerShriekIso A c).hom.app K := by
  have h := congrArg (fun t ↦ t.inv)
    (unboundedEtaleLowerShriekCompIso_open_source A e.hom r c)
  have hk := congr_app h
    (((upperStar (ModuleCat.{u + 1} A) e.hom).mapDerivedCategory).obj K)
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app] at hk
  dsimp only [Compactification.precomp] at hk ⊢
  dsimp only [unboundedEtaleApexSupportIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, asIso_hom,
    CategoryTheory.Functor.map_comp, Category.id_comp, Category.assoc]
  rw [← Category.assoc, hk]
  simp only [Category.assoc]
  erw [← (rightDerivedLowerShriekIso A c).hom.naturality_assoc]
  simp only [Functor.comp_obj, Functor.id_obj, Category.comp_id]
  rfl

private lemma apex_source_exchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z P T : Scheme.{u}} [IsNoetherian Z] [IsNoetherian P] [IsNoetherian T]
    (e : Z ≅ P) (r : P ⟶ T)
    [IsSeparated r] [LocallyOfFiniteType r] [QuasiCompact r]
    [HasCompactification r] [HasCompactification (e.hom ≫ r)]
    [QuasiCompact (e.hom ≫ r)]
    (sq : IsPullback e.hom (e.hom ≫ r) r (𝟙 T)) :
    unboundedEtaleCompactSupportBaseChange A sq ≫
        (unboundedEtaleApexSupportIso A e r).hom =
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) r)
        (unboundedEtaleUpperStarIdIso A T).hom ≫ (Functor.rightUnitor _).hom := by
  let F := unboundedFormalism A
  have : F.HasBaseChange := unbounded_has_base_change A
  have : F.HasProperExchange := unbounded_has_proper_exchange A
  let c := HasCompactification.compactification r
  have hi : IsPullback e.hom (c.precomp e.hom).i c.i (𝟙 c.Z) := by
    change IsPullback e.hom (e.hom ≫ c.i) c.i (𝟙 c.Z)
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hp : IsPullback (𝟙 c.Z) c.g c.g (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have he := congrArg TwoSquare.natTrans
    (chosenBaseChange_arbitrary F sq c (c.precomp e.hom) (𝟙 c.Z) hi hp)
  rw [F.shriekIso_refl] at he
  simp only [F, unbounded_chosen_base_change, unbounded_shriek_iso] at he
  rw [← rightDerivedLowerShriekIso] at he
  have hc : (rightDerivedLowerShriekIso A c).hom = 𝟙 _ := by
    rw [rightDerivedLowerShriekIso, ← unbounded_shriek_iso]
    exact congrArg Iso.hom (F.shriekIso_refl c)
  ext K
  have hk := congr_app he K
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.mk,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id] at hk
  rw [NatTrans.comp_app, hk, apex_support_model A e r c K]
  have hm := source_model_exchange F e c hi hp K
  simp only [F, unbounded_sh_comp, mapDerivedCategoryOpenImmersionLowerShriekCongr,
    Iso.refl_trans] at hm
  dsimp only [unboundedFormalism, Compactification.precomp,
    CompactSupportFormalism.shriek, ExchangeFormalism.shriek,
    derivedOpenImmersionLowerShriekUpperStarAdjunction,
    Functor.comp_obj, Functor.id_obj] at hk hm ⊢
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  erw [Category.id_comp]
  erw [reassoc_of% hm]
  rw [hc]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app]
  rfl

/-- The arbitrary-apex exchange is the pasted left-adjoint square, using the canonical
inverse-image compositor and the canonically normalized compact-support source comparison.
All Cartesian witnesses and all chosen compactifications are allowed, including the
identity isomorphism, empty schemes, and the zero coefficient ring.
Source: Stacks Tags 0F7I--0F7L, `lemma-base-change-shriek` and canonical comparisons
(blueprint: lem-pur-unbounded-exceptional-exchange-apex-pasting).

Proof plan from the node:
1. Choose a compactification of `f`. The base-changed opens for the two apices satisfy
   identical projection equations after composing with `e`; pullback uniqueness identifies
   them. Their proper factors and proper exchanges coincide. Cartesian witness proofs
   introduce no further choice (pur713-def-base-changed-compactification).
2. Compare the open extensions by uniqueness of left adjoints, using the inverse-image
   equivalence of `e`. The comparison preserves the actual units: the unit for the realized
   open, followed by restriction of the comparison, is the pullback of the old unit
   (lem-weil-pbc-conjugate-iso-unit-equation).
3. The normalized open-base-change mate gives both adjuncts. Inverse-image square pasting
   and exact derived transformation pasting identify the realized adjunct with the old one
   preceded by the compositor. Unit naturality and injectivity of the adjunction bijection
   yield the corresponding open-exchange equation. The open and etale sum adjunctions
   agree together with their units (lem-cbc-open-extension-zero-etale-adjunction-agreement).
4. Invert that open equation, apply the unchanged proper direct image, and precede it by
   the unchanged proper exchange. This proves the formula for the two computational models.
5. The source-open composition normalization identifies the comparison of those models
   with `unboundedEtaleApexSupportIso`: the open compositor is unit-preserving, and its
   inverse followed by the isomorphism counit is the unique comparison from step 2
   (lem-amb-compact-support-open-source-composition, lem-cbc-extension-zero-composition).
6. Insert the model-to-chosen comparisons. Their naturality at the inverse compositor
   cancels the intermediate comparisons and gives the displayed natural-transformation
   identity, with the associators restored.
7. Refinement independence and the cocycle law give the same identity for every fixed
   compactification. Projection uniqueness removes witness choices. For identity `e`,
   retain the canonical inverse-image unit constraints; the two unit factors cancel.
   None of the argument requires a nonempty scheme or a nonzero ring.
-/
theorem unboundedEtaleCompactSupportExchange_apex_pasting
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y T P Z : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian T]
    [IsNoetherian P] [IsNoetherian Z]
    {f : X ⟶ Y} {v : T ⟶ Y} {p : P ⟶ X} {r : P ⟶ T}
    [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    [IsSeparated r] [QuasiCompact r] [HasCompactification r]
    (q : ChosenCartesianSquare p r f v) (e : Z ≅ P)
    [IsSeparated (e.hom ≫ r)] [QuasiCompact (e.hom ≫ r)]
    [HasCompactification (e.hom ≫ r)]
    (q_e : IsPullback (e.hom ≫ p) (e.hom ≫ r) f v) :
    unboundedEtaleCompactSupportBaseChange A q_e =
      unboundedEtaleCompactSupportBaseChange A
          (IsPullback.of_iso_pullback q.toCommSq q.isoPullback q.hom_fst q.hom_snd) ≫
        Functor.whiskerLeft (upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategory
          (unboundedEtaleApexSupportIso A e r).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (unboundedEtaleUpperStarCompIso A e.hom p).inv
          (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (e.hom ≫ r)) := by
  have : LocallyOfFiniteType f := by
    rw [(HasCompactification.compactification f).comm]
    infer_instance
  have : LocallyOfFiniteType r := by
    rw [(HasCompactification.compactification r).comm]
    infer_instance
  let sq := IsPullback.of_iso_pullback q.toCommSq q.isoPullback q.hom_fst q.hom_snd
  have se : IsPullback e.hom (e.hom ≫ r) r (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have se' := apex_source_exchange A e r se
  have se'' : unboundedEtaleCompactSupportBaseChange A se =
      Functor.whiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) r)
        (unboundedEtaleUpperStarIdIso A T).hom ≫ (Functor.rightUnitor _).hom ≫
          (unboundedEtaleApexSupportIso A e r).inv := by
    ext K
    apply (cancel_mono ((unboundedEtaleApexSupportIso A e r).hom.app K)).mp
    have hk := congr_app se' K
    simpa only [NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id] using hk
  have sq3 : IsPullback (e.hom ≫ p) (e.hom ≫ r) f ((𝟙 T) ≫ v) := by
    simpa only [Category.id_comp] using q_e
  have h := unboundedEtaleCompactSupport_baseChange_comp A sq se sq3
  ext K
  have hk := congr_app h K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at hk ⊢
  rw [se''] at hk
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Category.assoc] at hk
  dsimp only [Functor.comp_obj, Functor.id_obj] at hk ⊢
  erw [(unboundedEtaleUpperStarIdIso A T).hom.naturality_assoc] at hk
  let M := (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj K
  let U (d : T ⟶ Y) :=
    ((upperStar (ModuleCat.{u + 1} A) d).mapDerivedCategory).obj M
  have ht (d : T ⟶ Y) (hd : d = v)
      (s : IsPullback (e.hom ≫ p) (e.hom ≫ r) f d) :
      (unboundedEtaleCompactSupportBaseChange A s).app K =
        eqToHom (congrArg U hd) ≫
          (unboundedEtaleCompactSupportBaseChange A q_e).app K := by
    subst d
    simp
  -- The outer square has bottom id ≫ v; retain its transport until cancellation.
  have hv := exact_pb_comp_congr A (𝟙 T) v (𝟙 T ≫ v) v rfl
    (Category.id_comp v).symm M
  have hu := congr_app (exact_pb_id_left A v) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at hu
  erw [hv] at hk
  erw [Category.assoc] at hk
  erw [reassoc_of% hu] at hk
  simp only [Category.id_comp, Functor.id_map] at hk
  rw [ht _ (Category.id_comp v) sq3] at hk
  apply (cancel_epi (eqToHom (congrArg U (Category.id_comp v)))).mp
  simpa only [Category.assoc, sq] using hk

end AlgebraicGeometry.Etale

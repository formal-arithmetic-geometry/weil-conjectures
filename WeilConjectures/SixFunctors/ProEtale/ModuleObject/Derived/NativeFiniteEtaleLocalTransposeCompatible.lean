/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeFiniteEtaleTracePairingLocal
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleSheetSumCompatibility
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteEtaleSplitHomDescent
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap

/-! # Compatibility of the constructed finite-etale sheet transposes

The explicit sheet transposes of `nativeFiniteEtaleLocalTranspose` are characterized by the
finite sum identity `nativeFiniteEtaleLocalTranspose_reconstruct`. This characterization is
stable under pullback of splitting charts and under reindexing of the sheets, so the
transposes on two charts agree on every common refinement of two of their sheets.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStar lowerStar upperStarComp upperStarLowerStarAdjunction

/-- A finite splitting chart pulls back to a splitting along any map into its base. -/
theorem FiniteEtaleModuleChart.pullback_splits {X U : Scheme.{u}} {p : U ⟶ X}
    (c : FiniteEtaleModuleChart p) {Z : Scheme.{u}} (a : Z ⟶ c.base) (k : Z ⟶ X)
    (hk : a ≫ c.map = k) :
    Nonempty (IsColimit (Cofan.mk (pullback p k)
      (fun j ↦ pullback.lift (a ≫ c.sheet j) (𝟙 Z)
        (by simp only [Category.assoc, c.over, Category.id_comp, hk])))) :=
  splitting_pullback p c.map a k hk c.degree c.sheet c.over c.splits.some

/-- Two sheets of a splitting chart which agree after composing with a map from a nonempty
scheme are equal, because the sheets are disjoint summands of the pullback. -/
theorem FiniteEtaleModuleChart.eq_of_comp_sheet_eq {X U : Scheme.{u}} {p : U ⟶ X}
    (c : FiniteEtaleModuleChart p) {V : Scheme.{u}} (v : V) (m : V ⟶ c.base)
    {i j : Fin c.degree} (h : m ≫ c.sheet i = m ≫ c.sheet j) : i = j := by
  by_contra hij
  let hc := c.splits.some
  let e := hc.coconePointUniqueUpToIso (colimit.isColimit
    (Discrete.functor fun _ : Fin c.degree ↦ c.base))
  have hι (l : Fin c.degree) : pullback.lift (c.sheet l) (𝟙 c.base)
      (by simpa using c.over l) ≫ e.hom = Sigma.ι (fun _ : Fin c.degree ↦ c.base) l :=
    hc.comp_coconePointUniqueUpToIso_hom _ ⟨l⟩
  have hm : m ≫ Sigma.ι (fun _ : Fin c.degree ↦ c.base) i =
      m ≫ Sigma.ι (fun _ : Fin c.degree ↦ c.base) j := by
    rw [← hι, ← hι, ← Category.assoc, ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · simpa using h
    · simp
  exact (isEmpty_of_commSq_sigmaι_of_ne ⟨hm⟩ hij).false v

/-- Every point of the source of a finite etale map lies on a sheet of an etale splitting
chart. -/
theorem FiniteEtaleModuleChart.exists_sheet_apply_eq {X U : Scheme.{u}} (p : U ⟶ X)
    [IsFinite p] [Etale p] (x : U) :
    ∃ (c : FiniteEtaleModuleChart p) (j : Fin c.degree) (y : c.base),
      Etale c.map ∧ c.sheet j y = x := by
  obtain ⟨c, y, hc, hy⟩ := exists_split_chart p (p x)
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := c.map) x y hy.symm
  let hcol := c.splits.some
  let e := hcol.coconePointUniqueUpToIso (colimit.isColimit
    (Discrete.functor fun _ : Fin c.degree ↦ c.base))
  obtain ⟨j, y', hy'⟩ := (sigmaOpenCover fun _ : Fin c.degree ↦ c.base).exists_eq (e.hom w)
  have hι : pullback.lift (c.sheet j) (𝟙 c.base) (by simpa using c.over j) ≫ e.hom =
      Sigma.ι (fun _ : Fin c.degree ↦ c.base) j :=
    hcol.comp_coconePointUniqueUpToIso_hom _ ⟨j⟩
  have hl : pullback.lift (c.sheet j) (𝟙 c.base) (by simpa using c.over j) y' = w := by
    apply (ConcreteCategory.bijective_of_isIso e.hom.base).1
    rw [← hy', sigmaOpenCover_f, ← hι, Scheme.Hom.comp_apply]
    rfl
  refine ⟨c, j, y', hc, ?_⟩
  rw [← hw, ← hl, ← Scheme.Hom.comp_apply, pullback.lift_fst]

@[reassoc]
private theorem pi_row_entry
    {C : Type*} [Category C] [Preadditive C] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → C) [HasProduct M] {P : C} (v : ∀ i, M i ⟶ P) (i : ι) :
    Pi.ι M i ≫ (∑ j, Pi.π M j ≫ v j) = v i := by
  rw [Preadditive.comp_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    rw [← Category.assoc, Pi.ι_π_of_ne M hj.symm, zero_comp]
  · simp

/-- The sheet transposes reconstruct the pulled back arrow as a finite sum of sheet terms.
(blueprint: new-det-sp-native-finite-etale-trace-pairing-local). -/
theorem nativeFiniteEtaleLocalTranspose_sum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (c : FiniteEtaleModuleChart p)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : (lowerStar Λ p).obj M ⟶ P) :
    ∑ j, nativeFiniteEtaleSheetProjection Λ p c M j ≫
        nativeFiniteEtaleLocalTranspose Λ p c M P h j ≫
        (finiteEtaleTraceSheetComparison Λ p c.map (c.sheet j) (c.over j)).inv.app P =
      (upperStar Λ c.map).map h := by
  have hr := nativeFiniteEtaleLocalTranspose_reconstruct Λ p c M P h
  rw [Preadditive.comp_sum] at hr
  simpa only [Pi.lift_π_assoc] using hr

/-- Pulling back one conjugated sheet term along a map into the base of the chart.
(blueprint: new-det-sp-native-finite-etale-local-transpose-gluing). -/
private theorem pulled_sheet_term
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y Z : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) (a : Z ⟶ Y)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (x : (upperStar Λ t).obj M ⟶ (upperStar Λ t).obj ((upperStar Λ p).obj P)) :
    ((finiteEtaleTraceSheetComparison Λ p (a ≫ g) (a ≫ t)
          (by simp only [Category.assoc, w])).hom.app ((lowerStar Λ p).obj M) ≫
        (upperStar Λ (a ≫ t)).map ((upperStarLowerStarAdjunction Λ p).counit.app M)) ≫
      ((upperStarComp Λ a t).hom.app M ≫ (upperStar Λ a).map x ≫
        (upperStarComp Λ a t).inv.app ((upperStar Λ p).obj P)) ≫
      (finiteEtaleTraceSheetComparison Λ p (a ≫ g) (a ≫ t)
          (by simp only [Category.assoc, w])).inv.app P =
    (upperStarComp Λ a g).hom.app ((lowerStar Λ p).obj M) ≫
      (upperStar Λ a).map
        (((finiteEtaleTraceSheetComparison Λ p g t w).hom.app ((lowerStar Λ p).obj M) ≫
          (upperStar Λ t).map ((upperStarLowerStarAdjunction Λ p).counit.app M)) ≫ x ≫
          (finiteEtaleTraceSheetComparison Λ p g t w).inv.app P) ≫
      (upperStarComp Λ a g).inv.app P := by
  let C := finiteEtaleTraceSheetComparison Λ p g t w
  let D := finiteEtaleTraceSheetComparison Λ p (a ≫ g) (a ≫ t)
    (by simp only [Category.assoc, w])
  have h₁ := sheet_comparison_pullback Λ p g t w a ((lowerStar Λ p).obj M)
  have hP : (upperStarComp Λ a t).inv.app ((upperStar Λ p).obj P) ≫ D.inv.app P =
      (upperStar Λ a).map (C.inv.app P) ≫ (upperStarComp Λ a g).inv.app P := by
    have h₂ := sheet_comparison_pullback Λ p g t w a P
    have e := congrArg Iso.inv (Iso.ext (α := (upperStarComp Λ a g).app P ≪≫
      (upperStar Λ a).mapIso (C.app P)) (β := D.app P ≪≫ (upperStarComp Λ a t).app
        ((upperStar Λ p).obj P)) h₂)
    simpa only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv] using e.symm
  have hn := (upperStarComp Λ a t).hom.naturality ((upperStarLowerStarAdjunction Λ p).counit.app M)
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, hP, ← reassoc_of% h₁]

/-- The finite sum of the pulled back sheet transposes reconstructs the pulled back arrow.
(blueprint: new-det-sp-native-finite-etale-local-transpose-gluing). -/
theorem nativeFiniteEtaleLocalTranspose_pullback_sum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (c : FiniteEtaleModuleChart p)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : (lowerStar Λ p).obj M ⟶ P) {Z : Scheme.{u}} (a : Z ⟶ c.base) :
    ∑ i, ((finiteEtaleTraceSheetComparison Λ p (a ≫ c.map) (a ≫ c.sheet i)
          (by simp only [Category.assoc, c.over])).hom.app ((lowerStar Λ p).obj M) ≫
        (upperStar Λ (a ≫ c.sheet i)).map ((upperStarLowerStarAdjunction Λ p).counit.app M)) ≫
      ((upperStarComp Λ a (c.sheet i)).hom.app M ≫
        (upperStar Λ a).map (nativeFiniteEtaleLocalTranspose Λ p c M P h i) ≫
        (upperStarComp Λ a (c.sheet i)).inv.app ((upperStar Λ p).obj P)) ≫
      (finiteEtaleTraceSheetComparison Λ p (a ≫ c.map) (a ≫ c.sheet i)
          (by simp only [Category.assoc, c.over])).inv.app P =
      (upperStar Λ (a ≫ c.map)).map h := by
  have hsum := nativeFiniteEtaleLocalTranspose_sum Λ p c M P h
  simp only [nativeFiniteEtaleSheetProjection_eq] at hsum
  calc
    _ = ∑ i, (upperStarComp Λ a c.map).hom.app ((lowerStar Λ p).obj M) ≫
          (upperStar Λ a).map
            (((finiteEtaleTraceSheetComparison Λ p c.map (c.sheet i) (c.over i)).hom.app
                ((lowerStar Λ p).obj M) ≫
              (upperStar Λ (c.sheet i)).map ((upperStarLowerStarAdjunction Λ p).counit.app M)) ≫
              nativeFiniteEtaleLocalTranspose Λ p c M P h i ≫
              (finiteEtaleTraceSheetComparison Λ p c.map (c.sheet i) (c.over i)).inv.app P) ≫
          (upperStarComp Λ a c.map).inv.app P :=
      Finset.sum_congr rfl fun i _ ↦ pulled_sheet_term Λ p c.map (c.sheet i) (c.over i) a
        M P (nativeFiniteEtaleLocalTranspose Λ p c M P h i)
    _ = (upperStarComp Λ a c.map).hom.app ((lowerStar Λ p).obj M) ≫
          (upperStar Λ a).map ((upperStar Λ c.map).map h) ≫
          (upperStarComp Λ a c.map).inv.app P := by
      rw [← hsum]
      simp only [Functor.map_sum, Preadditive.comp_sum, Preadditive.sum_comp]
    _ = _ := by
      have hn := (upperStarComp Λ a c.map).hom.naturality h
      simp only [Functor.comp_map] at hn
      rw [← reassoc_of% hn, Iso.hom_inv_id_app, Category.comp_id]

/-- The row of a family of sheet maps on a finite family of sections `s` of `p` over `k`:
the sum of the sheet maps composed with the canonical sheet projections. -/
def nativeFiniteEtaleSheetRow
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {Z : Scheme.{u}} (k : Z ⟶ X) {n : ℕ} (s : Fin n → (Z ⟶ U)) (w : ∀ i, s i ≫ p = k)
    (τ : ∀ i, (upperStar Λ (s i)).obj M ⟶ (upperStar Λ (s i)).obj ((upperStar Λ p).obj P)) :
    (upperStar Λ k).obj ((lowerStar Λ p).obj M) ⟶ (upperStar Λ k).obj P :=
  ∑ i, ((finiteEtaleTraceSheetComparison Λ p k (s i) (w i)).hom.app ((lowerStar Λ p).obj M) ≫
      (upperStar Λ (s i)).map ((upperStarLowerStarAdjunction Λ p).counit.app M)) ≫
    τ i ≫ (finiteEtaleTraceSheetComparison Λ p k (s i) (w i)).inv.app P

/-- On a finite splitting, a family of sheet maps is determined by its row. -/
theorem nativeFiniteEtaleSheetRow_injective
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    {Z : Scheme.{u}} (k : Z ⟶ X) [WeaklyEtale k] {n : ℕ} (s : Fin n → (Z ⟶ U))
    (w : ∀ i, s i ≫ p = k)
    (hc : Nonempty (IsColimit (Cofan.mk (pullback p k)
      (fun j ↦ pullback.lift (s j) (𝟙 Z) (by simpa using w j)))))
    (τ τ' : ∀ i, (upperStar Λ (s i)).obj M ⟶ (upperStar Λ (s i)).obj ((upperStar Λ p).obj P))
    (hτ : nativeFiniteEtaleSheetRow Λ p M P k s w τ = nativeFiniteEtaleSheetRow Λ p M P k s w τ') :
    τ = τ' := by
  classical
  have hiso := splitProEtaleModuleProductMap_isIso Λ p k n s w hc M
  have hq : IsIso (Pi.lift fun j ↦
      (finiteEtaleTraceSheetComparison Λ p k (s j) (w j)).hom.app ((lowerStar Λ p).obj M) ≫
        (upperStar Λ (s j)).map ((upperStarLowerStarAdjunction Λ p).counit.app M)) := by
    have e : (fun j ↦
        (finiteEtaleTraceSheetComparison Λ p k (s j) (w j)).hom.app ((lowerStar Λ p).obj M) ≫
          (upperStar Λ (s j)).map ((upperStarLowerStarAdjunction Λ p).counit.app M)) =
        (fun j ↦ ((eqToIso (congrArg (upperStar Λ) (w j))).symm ≪≫
            upperStarComp Λ (s j) p).hom.app ((lowerStar Λ p).obj M) ≫
          (upperStar Λ (s j)).map ((upperStarLowerStarAdjunction Λ p).counit.app M)) :=
      funext fun j ↦ congrArg (fun e : upperStar Λ k ≅ upperStar Λ p ⋙ upperStar Λ (s j) ↦
        e.hom.app ((lowerStar Λ p).obj M) ≫
          (upperStar Λ (s j)).map ((upperStarLowerStarAdjunction Λ p).counit.app M))
        (finiteEtaleTraceSheetComparison_eq Λ p k (s j) (w j))
    rw [e]
    exact hiso
  have hrow (σ : ∀ i, (upperStar Λ (s i)).obj M ⟶
      (upperStar Λ (s i)).obj ((upperStar Λ p).obj P)) :
      nativeFiniteEtaleSheetRow Λ p M P k s w σ =
        Pi.lift (fun j ↦
          (finiteEtaleTraceSheetComparison Λ p k (s j) (w j)).hom.app ((lowerStar Λ p).obj M) ≫
            (upperStar Λ (s j)).map ((upperStarLowerStarAdjunction Λ p).counit.app M)) ≫
          ∑ i, Pi.π _ i ≫ σ i ≫
            (finiteEtaleTraceSheetComparison Λ p k (s i) (w i)).inv.app P := by
    rw [nativeFiniteEtaleSheetRow, Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Pi.lift_π_assoc]
  rw [hrow, hrow] at hτ
  have hτ' := (cancel_epi _).mp hτ
  funext i
  have hi := congrArg (fun z ↦ Pi.ι _ i ≫ z ≫
    (finiteEtaleTraceSheetComparison Λ p k (s i) (w i)).hom.app P) hτ'
  simpa only [pi_row_entry_assoc, Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj,
    Category.comp_id] using hi

/-- Replacing a sheet by an equal map in one term of a row. -/
private theorem sheet_term_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}} (p : U ⟶ X)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (k : Z ⟶ X) (t t' : Z ⟶ U) (ht : t = t') (w : t ≫ p = k) (w' : t' ≫ p = k)
    (x : (upperStar Λ t').obj M ⟶ (upperStar Λ t').obj ((upperStar Λ p).obj P)) :
    ((finiteEtaleTraceSheetComparison Λ p k t w).hom.app ((lowerStar Λ p).obj M) ≫
        (upperStar Λ t).map ((upperStarLowerStarAdjunction Λ p).counit.app M)) ≫
      (eqToHom (congrArg (fun t ↦ (upperStar Λ t).obj M) ht) ≫ x ≫
        eqToHom (congrArg (fun t ↦ (upperStar Λ t).obj ((upperStar Λ p).obj P)) ht.symm)) ≫
      (finiteEtaleTraceSheetComparison Λ p k t w).inv.app P =
    ((finiteEtaleTraceSheetComparison Λ p k t' w').hom.app ((lowerStar Λ p).obj M) ≫
        (upperStar Λ t').map ((upperStarLowerStarAdjunction Λ p).counit.app M)) ≫
      x ≫ (finiteEtaleTraceSheetComparison Λ p k t' w').inv.app P := by
  subst ht
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Replacing the structure map by an equal map in one term of a row. -/
private theorem sheet_term_transport_map
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Z : Scheme.{u}} (p : U ⟶ X)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (k k' : Z ⟶ X) (hk : k = k') (t : Z ⟶ U) (w : t ≫ p = k) (w' : t ≫ p = k')
    (x : (upperStar Λ t).obj M ⟶ (upperStar Λ t).obj ((upperStar Λ p).obj P)) :
    ((finiteEtaleTraceSheetComparison Λ p k t w).hom.app ((lowerStar Λ p).obj M) ≫
        (upperStar Λ t).map ((upperStarLowerStarAdjunction Λ p).counit.app M)) ≫
      x ≫ (finiteEtaleTraceSheetComparison Λ p k t w).inv.app P =
    eqToHom (congrArg (fun k ↦ (upperStar Λ k).obj ((lowerStar Λ p).obj M)) hk) ≫
      (((finiteEtaleTraceSheetComparison Λ p k' t w').hom.app ((lowerStar Λ p).obj M) ≫
          (upperStar Λ t).map ((upperStarLowerStarAdjunction Λ p).counit.app M)) ≫
        x ≫ (finiteEtaleTraceSheetComparison Λ p k' t w').inv.app P) ≫
      eqToHom (congrArg (fun k ↦ (upperStar Λ k).obj P) hk.symm) := by
  subst hk
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Replacing the map by an equal map in a pulled back arrow. -/
private theorem upperStar_map_transport
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Z : Scheme.{u}} (k k' : Z ⟶ X) (hk : k = k')
    {N P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)} (h : N ⟶ P) :
    eqToHom (congrArg (fun k ↦ (upperStar Λ k).obj N) hk) ≫ (upperStar Λ k').map h ≫
        eqToHom (congrArg (fun k ↦ (upperStar Λ k).obj P) hk.symm) =
      (upperStar Λ k).map h := by
  subst hk
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Conjugating by an `eqToIso` followed by an isomorphism, componentwise. -/
private theorem eqToIso_trans_conj_app {C D : Type*} [Category C] [Category D] {F G H : C ⥤ D}
    (hFG : F = G) (c : G ≅ H) (A B : C) (x : H.obj A ⟶ H.obj B) :
    (eqToIso hFG ≪≫ c).hom.app A ≫ x ≫ (eqToIso hFG ≪≫ c).inv.app B =
      eqToHom (congrArg (fun F : C ⥤ D ↦ F.obj A) hFG) ≫ (c.hom.app A ≫ x ≫ c.inv.app B) ≫
        eqToHom (congrArg (fun F : C ⥤ D ↦ F.obj B) hFG.symm) := by
  subst hFG
  simp

/-- The composition-comparison conjugate along an equation `k = a ≫ t`, written with
`eqToHom`. -/
private theorem upperStarComp_eqToIso_conj
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Y Z : Scheme.{u}} (t : Y ⟶ U) (a : Z ⟶ Y) (k : Z ⟶ U)
    (hk : k = a ≫ t) {A B : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)}
    (x : (upperStar Λ t).obj A ⟶ (upperStar Λ t).obj B) :
    ((eqToIso (congrArg (upperStar Λ) hk)) ≪≫ upperStarComp Λ a t).hom.app A ≫
        (upperStar Λ a).map x ≫
        ((eqToIso (congrArg (upperStar Λ) hk)) ≪≫ upperStarComp Λ a t).inv.app B =
      eqToHom (congrArg (fun t ↦ (upperStar Λ t).obj A) hk) ≫
        ((upperStarComp Λ a t).hom.app A ≫ (upperStar Λ a).map x ≫
          (upperStarComp Λ a t).inv.app B) ≫
        eqToHom (congrArg (fun t ↦ (upperStar Λ t).obj B) hk.symm) :=
  eqToIso_trans_conj_app (congrArg (upperStar Λ) hk) (upperStarComp Λ a t) A B
    ((upperStar Λ a).map x)

/-- Conjugating a family of composition isomorphisms by `eqToHom`s along an equation of
indices. -/
private theorem comp_iso_conj_eqToHom {I C D E : Type*} [Category C] [Category D] [Category E]
    (F : I → C ⥤ D) (G : D ⥤ E) (Φ : I → C ⥤ E) (comp : ∀ i, Φ i ≅ F i ⋙ G) {k t : I}
    (hk : k = t) (A B : C) (y : (F t).obj A ⟶ (F t).obj B) (hA : (F k).obj A = (F t).obj A)
    (hB : (F t).obj B = (F k).obj B) :
    (comp k).hom.app A ≫ G.map (eqToHom hA ≫ y ≫ eqToHom hB) ≫ (comp k).inv.app B =
      eqToHom (congrArg (fun i ↦ (Φ i).obj A) hk) ≫
        ((comp t).hom.app A ≫ G.map y ≫ (comp t).inv.app B) ≫
        eqToHom (congrArg (fun i ↦ (Φ i).obj B) hk.symm) := by
  subst hk
  simp

/-- Pulling back a map conjugated by `eqToHom` along an equation of maps. -/
private theorem upperStarComp_conj_eqToHom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Y Z V : Scheme.{u}} (o : V ⟶ Z) {k t : Z ⟶ Y} (hk : k = t)
    {A B : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)}
    (y : (upperStar Λ t).obj A ⟶ (upperStar Λ t).obj B)
    (hA : (upperStar Λ k).obj A = (upperStar Λ t).obj A)
    (hB : (upperStar Λ t).obj B = (upperStar Λ k).obj B) :
    (upperStarComp Λ o k).hom.app A ≫ (upperStar Λ o).map (eqToHom hA ≫ y ≫ eqToHom hB) ≫
        (upperStarComp Λ o k).inv.app B =
      eqToHom (congrArg (fun t ↦ (upperStar Λ (o ≫ t)).obj A) hk) ≫
        ((upperStarComp Λ o t).hom.app A ≫ (upperStar Λ o).map y ≫
          (upperStarComp Λ o t).inv.app B) ≫
        eqToHom (congrArg (fun t ↦ (upperStar Λ (o ≫ t)).obj B) hk.symm) :=
  comp_iso_conj_eqToHom (fun t : Z ⟶ Y ↦ upperStar Λ t) (upperStar Λ o)
    (fun t ↦ upperStar Λ (o ≫ t)) (fun t ↦ upperStarComp Λ o t) hk A B y hA hB

/-- Solve an equation between two `eqToHom` conjugates. -/
private theorem eqToHom_conj_eq {C : Type*} [Category C] {A A' A'' B B' B'' : C}
    (γ : A = A') (δ : B' = B) (γ' : A = A'') (δ' : B'' = B) {X : A' ⟶ B'} {Y : A'' ⟶ B''}
    (h : eqToHom γ ≫ X ≫ eqToHom δ = eqToHom γ' ≫ Y ≫ eqToHom δ') :
    X = eqToHom (γ.symm.trans γ') ≫ Y ≫ eqToHom (δ'.trans δ.symm) := by
  subst γ γ' δ δ'
  simpa using h

/-- **Pulled back sheet transposes under a reindexing of sheets.** If the pullbacks along
`a` and `b` of two splitting charts have the same sheets up to a bijection `e`, then the pulled
back sheet transposes agree up to `e`.
(blueprint: new-det-sp-native-finite-etale-local-transpose-gluing). -/
theorem nativeFiniteEtaleLocalTranspose_pullback_reindex
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (c₁ c₂ : FiniteEtaleModuleChart p)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : (lowerStar Λ p).obj M ⟶ P) {V : Scheme.{u}} (a : V ⟶ c₁.base) (b : V ⟶ c₂.base)
    [WeaklyEtale (a ≫ c₁.map)] (e : Fin c₁.degree ≃ Fin c₂.degree)
    (he : ∀ i, a ≫ c₁.sheet i = b ≫ c₂.sheet (e i)) (hmap : a ≫ c₁.map = b ≫ c₂.map)
    (i : Fin c₁.degree) :
    (upperStarComp Λ a (c₁.sheet i)).hom.app M ≫
        (upperStar Λ a).map (nativeFiniteEtaleLocalTranspose Λ p c₁ M P h i) ≫
        (upperStarComp Λ a (c₁.sheet i)).inv.app ((upperStar Λ p).obj P) =
      eqToHom (congrArg (fun t ↦ (upperStar Λ t).obj M) (he i)) ≫
        ((upperStarComp Λ b (c₂.sheet (e i))).hom.app M ≫
          (upperStar Λ b).map (nativeFiniteEtaleLocalTranspose Λ p c₂ M P h (e i)) ≫
          (upperStarComp Λ b (c₂.sheet (e i))).inv.app ((upperStar Λ p).obj P)) ≫
        eqToHom (congrArg (fun t ↦ (upperStar Λ t).obj ((upperStar Λ p).obj P)) (he i).symm) := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Fin c₁.degree → (V ⟶ U), ∀ i, s i = a ≫ c₁.sheet i :=
    ⟨fun i ↦ a ≫ c₁.sheet i, fun _ ↦ rfl⟩
  have w (i : Fin c₁.degree) : s i ≫ p = a ≫ c₁.map := by
    rw [hs, Category.assoc, c₁.over]
  have hc : Nonempty (IsColimit (Cofan.mk (pullback p (a ≫ c₁.map))
      (fun j ↦ pullback.lift (s j) (𝟙 V) (by simpa using w j)))) := by
    have hfun : s = fun i ↦ a ≫ c₁.sheet i := funext hs
    subst hfun
    exact c₁.pullback_splits a (a ≫ c₁.map) rfl
  have r₁ : nativeFiniteEtaleSheetRow Λ p M P (a ≫ c₁.map) s w (fun i ↦
      eqToHom (congrArg (fun t ↦ (upperStar Λ t).obj M) (hs i)) ≫
        ((upperStarComp Λ a (c₁.sheet i)).hom.app M ≫
          (upperStar Λ a).map (nativeFiniteEtaleLocalTranspose Λ p c₁ M P h i) ≫
          (upperStarComp Λ a (c₁.sheet i)).inv.app ((upperStar Λ p).obj P)) ≫
        eqToHom (congrArg (fun t ↦ (upperStar Λ t).obj ((upperStar Λ p).obj P)) (hs i).symm)) =
      (upperStar Λ (a ≫ c₁.map)).map h := by
    rw [nativeFiniteEtaleSheetRow, ← nativeFiniteEtaleLocalTranspose_pullback_sum Λ p c₁ M P h a]
    exact Finset.sum_congr rfl fun i _ ↦ sheet_term_transport Λ p M P (a ≫ c₁.map) (s i)
      (a ≫ c₁.sheet i) (hs i) (w i) (by simp only [Category.assoc, c₁.over]) _
  have r₂ : nativeFiniteEtaleSheetRow Λ p M P (a ≫ c₁.map) s w (fun i ↦
      eqToHom (congrArg (fun t ↦ (upperStar Λ t).obj M) ((hs i).trans (he i))) ≫
        ((upperStarComp Λ b (c₂.sheet (e i))).hom.app M ≫
          (upperStar Λ b).map (nativeFiniteEtaleLocalTranspose Λ p c₂ M P h (e i)) ≫
          (upperStarComp Λ b (c₂.sheet (e i))).inv.app ((upperStar Λ p).obj P)) ≫
        eqToHom (congrArg (fun t ↦ (upperStar Λ t).obj ((upperStar Λ p).obj P))
          ((hs i).trans (he i)).symm)) =
      (upperStar Λ (a ≫ c₁.map)).map h := by
    rw [nativeFiniteEtaleSheetRow]
    refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ (sheet_term_transport Λ p M P (a ≫ c₁.map)
      (s i) (b ≫ c₂.sheet (e i)) ((hs i).trans (he i)) (w i)
      (by rw [Category.assoc, c₂.over, hmap]) _).trans
      (sheet_term_transport_map Λ p M P (a ≫ c₁.map) (b ≫ c₂.map) hmap
        (b ≫ c₂.sheet (e i)) (by rw [Category.assoc, c₂.over, hmap])
        (by simp only [Category.assoc, c₂.over]) _)) ?_
    refine Eq.trans (Equiv.sum_comp e (fun j ↦
      eqToHom (congrArg (fun k ↦ (upperStar Λ k).obj ((lowerStar Λ p).obj M)) hmap) ≫
        (((finiteEtaleTraceSheetComparison Λ p (b ≫ c₂.map) (b ≫ c₂.sheet j)
              (by simp only [Category.assoc, c₂.over])).hom.app ((lowerStar Λ p).obj M) ≫
            (upperStar Λ (b ≫ c₂.sheet j)).map
              ((upperStarLowerStarAdjunction Λ p).counit.app M)) ≫
          ((upperStarComp Λ b (c₂.sheet j)).hom.app M ≫
            (upperStar Λ b).map (nativeFiniteEtaleLocalTranspose Λ p c₂ M P h j) ≫
            (upperStarComp Λ b (c₂.sheet j)).inv.app ((upperStar Λ p).obj P)) ≫
          (finiteEtaleTraceSheetComparison Λ p (b ≫ c₂.map) (b ≫ c₂.sheet j)
              (by simp only [Category.assoc, c₂.over])).inv.app P) ≫
        eqToHom (congrArg (fun k ↦ (upperStar Λ k).obj P) hmap.symm))) ?_
    rw [← Preadditive.comp_sum, ← Preadditive.sum_comp,
      nativeFiniteEtaleLocalTranspose_pullback_sum Λ p c₂ M P h b]
    exact upperStar_map_transport Λ (a ≫ c₁.map) (b ≫ c₂.map) hmap h
  have hτ := congrFun (nativeFiniteEtaleSheetRow_injective Λ p M P (a ≫ c₁.map) s w hc _ _
    (r₁.trans r₂.symm)) i
  exact eqToHom_conj_eq _ _ _ _ hτ

/-- Associativity of the conjugation by composition isomorphisms, for abstract functors. -/
private theorem comp_iso_assoc_conj {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂]
    [Category C₃] [Category C₄] (Ft : C₁ ⥤ C₂) (Fa : C₂ ⥤ C₃) (Fo : C₃ ⥤ C₄) (Fat : C₁ ⥤ C₃)
    (Foa : C₂ ⥤ C₄) (Fo_at Foa_t : C₁ ⥤ C₄) (μat : Fat ≅ Ft ⋙ Fa) (μo_at : Fo_at ≅ Fat ⋙ Fo)
    (μoa_t : Foa_t ≅ Ft ⋙ Foa) (μoa : Foa ≅ Fa ⋙ Fo) (κ : Foa_t ≅ Fo_at)
    (hco : ∀ A, μoa_t.hom.app A ≫ μoa.hom.app (Ft.obj A) =
      κ.hom.app A ≫ μo_at.hom.app A ≫ Fo.map (μat.hom.app A))
    (A B : C₁) (x : Ft.obj A ⟶ Ft.obj B) :
    μo_at.hom.app A ≫ Fo.map (μat.hom.app A ≫ Fa.map x ≫ μat.inv.app B) ≫ μo_at.inv.app B =
      κ.inv.app A ≫ (μoa_t.hom.app A ≫ Foa.map x ≫ μoa_t.inv.app B) ≫ κ.hom.app B := by
  have hA : μo_at.hom.app A ≫ Fo.map (μat.hom.app A) =
      κ.inv.app A ≫ μoa_t.hom.app A ≫ μoa.hom.app (Ft.obj A) := by
    rw [hco A, Iso.inv_hom_id_app_assoc]
  have hB' : μo_at.hom.app B ≫ Fo.map (μat.hom.app B) =
      κ.inv.app B ≫ μoa_t.hom.app B ≫ μoa.hom.app (Ft.obj B) := by
    rw [hco B, Iso.inv_hom_id_app_assoc]
  have hB : Fo.map (μat.inv.app B) ≫ μo_at.inv.app B =
      μoa.inv.app (Ft.obj B) ≫ μoa_t.inv.app B ≫ κ.hom.app B := by
    rw [← cancel_epi (μo_at.hom.app B ≫ Fo.map (μat.hom.app B))]
    conv_rhs => rw [hB']
    simp only [Category.assoc, ← Fo.map_comp_assoc, Iso.hom_inv_id_app, Fo.map_id,
      Category.id_comp, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
  have hn := μoa.hom.naturality x
  simp only [Functor.comp_map] at hn
  rw [Fo.map_comp, Fo.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hA, hB, ← reassoc_of% hn, Iso.hom_inv_id_app_assoc]

/-- A component of an `eqToIso` of functors is an `eqToHom`. -/
private theorem eqToIso_hom_app_eq {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F = G) (A : C) :
    (eqToIso e).hom.app A = eqToHom (congrArg (fun F : C ⥤ D ↦ F.obj A) e) := by
  subst e
  rfl

/-- A component of an `eqToIso` of functors is an `eqToHom`. -/
private theorem eqToIso_inv_app_eq {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (e : F = G) (A : C) :
    (eqToIso e).inv.app A = eqToHom (congrArg (fun F : C ⥤ D ↦ F.obj A) e.symm) := by
  subst e
  rfl

/-- Pulling back a conjugated pulled back map along a further map is the conjugated pullback
along the composite. -/
theorem upperStarComp_conj_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {U Y Z V : Scheme.{u}} (o : V ⟶ Z) (a : Z ⟶ Y) (t : Y ⟶ U)
    {A B : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U)}
    (x : (upperStar Λ t).obj A ⟶ (upperStar Λ t).obj B) :
    (upperStarComp Λ o (a ≫ t)).hom.app A ≫
        (upperStar Λ o).map ((upperStarComp Λ a t).hom.app A ≫ (upperStar Λ a).map x ≫
          (upperStarComp Λ a t).inv.app B) ≫
        (upperStarComp Λ o (a ≫ t)).inv.app B =
      eqToHom (congrArg (fun t ↦ (upperStar Λ t).obj A) (Category.assoc o a t).symm) ≫
        ((upperStarComp Λ (o ≫ a) t).hom.app A ≫ (upperStar Λ (o ≫ a)).map x ≫
          (upperStarComp Λ (o ≫ a) t).inv.app B) ≫
        eqToHom (congrArg (fun t ↦ (upperStar Λ t).obj B) (Category.assoc o a t)) := by
  refine (comp_iso_assoc_conj (upperStar Λ t) (upperStar Λ a) (upperStar Λ o)
    (upperStar Λ (a ≫ t)) (upperStar Λ (o ≫ a)) (upperStar Λ (o ≫ (a ≫ t)))
    (upperStar Λ ((o ≫ a) ≫ t)) (upperStarComp Λ a t) (upperStarComp Λ o (a ≫ t))
    (upperStarComp Λ (o ≫ a) t) (upperStarComp Λ o a)
    (eqToIso (congrArg (upperStar Λ) (Category.assoc o a t)))
    (upperStarComp_hom_app_comp_upperStarComp_hom_app Λ o a t) A B x).trans ?_
  rw [eqToIso_hom_app_eq, eqToIso_inv_app_eq]

/-- **Compatibility of the sheet transposes.** On a weakly etale scheme mapping to two sheets
of two splitting charts, compatibly over `U`, the pullbacks of the two sheet transposes agree.
(blueprint: new-det-sp-native-finite-etale-local-transpose-gluing).

Proof. Locally on the common scheme the two pulled back splittings differ by a bijection of
the sheets, which sends the first chosen sheet to the second by disjointness of the sheets.
There the pulled back transposes are determined by their finite row sums, which are both the
pulled back arrow. -/
theorem nativeFiniteEtaleLocalTranspose_compatible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (c₁ c₂ : FiniteEtaleModuleChart p)
    (M : Mod (Sheaf (ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))
    (P : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (h : (lowerStar Λ p).obj M ⟶ P) (j₁ : Fin c₁.degree) (j₂ : Fin c₂.degree)
    (Z : Scheme.{u}) (a : Z ⟶ c₁.base) (b : Z ⟶ c₂.base) [WeaklyEtale a] [WeaklyEtale b]
    (k : Z ⟶ U) (ha : k = a ≫ c₁.sheet j₁) (hb : k = b ≫ c₂.sheet j₂) :
    ((eqToIso (congrArg (upperStar Λ) ha)) ≪≫ upperStarComp Λ a (c₁.sheet j₁)).hom.app M ≫
        (upperStar Λ a).map (nativeFiniteEtaleLocalTranspose Λ p c₁ M P h j₁) ≫
        ((eqToIso (congrArg (upperStar Λ) ha)) ≪≫ upperStarComp Λ a (c₁.sheet j₁)).inv.app
          ((upperStar Λ p).obj P) =
      ((eqToIso (congrArg (upperStar Λ) hb)) ≪≫ upperStarComp Λ b (c₂.sheet j₂)).hom.app M ≫
        (upperStar Λ b).map (nativeFiniteEtaleLocalTranspose Λ p c₂ M P h j₂) ≫
        ((eqToIso (congrArg (upperStar Λ) hb)) ≪≫ upperStarComp Λ b (c₂.sheet j₂)).inv.app
          ((upperStar Λ p).obj P) := by
  classical
  have w : a ≫ c₁.map = b ≫ c₂.map := by
    rw [← c₁.over j₁, ← c₂.over j₂, ← Category.assoc, ← Category.assoc, ← ha, ← hb]
  refine (upperStarComp_eqToIso_conj Λ (c₁.sheet j₁) a k ha _).trans (Eq.trans ?_
    (upperStarComp_eqToIso_conj Λ (c₂.sheet j₂) b k hb _).symm)
  choose O hz e he using refined_sheets_locally_permute p c₁ c₂ Z a b w
  apply module_hom_ext_open Λ _ _ O hz
  intro z
  apply (cancel_epi ((upperStarComp Λ (O z).ι k).hom.app M)).mp
  apply (cancel_mono ((upperStarComp Λ (O z).ι k).inv.app ((upperStar Λ p).obj P))).mp
  rw [Category.assoc ((upperStarComp Λ (O z).ι k).hom.app M),
    Category.assoc ((upperStarComp Λ (O z).ι k).hom.app M)]
  rw [upperStarComp_conj_eqToHom Λ (O z).ι ha, upperStarComp_conj_eqToHom Λ (O z).ι hb,
    upperStarComp_conj_comp, upperStarComp_conj_comp]
  have hej : e z j₁ = j₂ := by
    refine c₂.eq_of_comp_sheet_eq (⟨z, hz z⟩ : (O z)) ((O z).ι ≫ b) ?_
    rw [Category.assoc, Category.assoc, ← he z j₁, ← ha, ← hb]
  subst hej
  rw [nativeFiniteEtaleLocalTranspose_pullback_reindex Λ p c₁ c₂ M P h ((O z).ι ≫ a)
    ((O z).ι ≫ b) (e z) (fun i ↦ by simpa only [Category.assoc] using he z i)
    (by rw [Category.assoc, Category.assoc, w]) j₁]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing

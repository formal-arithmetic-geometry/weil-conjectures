/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedLisseDualityDefs
import WeilConjectures.DeligneLaumon.CondensedLisseOpenLineCoherence
import WeilConjectures.DeligneLaumon.CondensedLisseOpenGeometry

/-! # Conjugating coherent Tate restriction by smooth purity -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedLisseDual
variable (ell : ℕ) [Fact ell.Prime] (c : PurityTransport.Coefficient ell)

private theorem precomp_heq {C : Type*} [Category* C] {X Y Z Z' : C}
    (hz : Z = Z') (f : X ⟶ Y) (g : Y ⟶ Z) (g' : Y ⟶ Z') (h : HEq g g') :
    HEq (f ≫ g) (f ≫ g') := by
  cases hz
  exact (congrArg (fun v ↦ f ≫ v) (eq_of_heq h)).heq

/-- Smooth purity transports the coherent normalized Tate maps to dualizing objects.
Source: Step 2, open compatibility of the orientation
(blueprint: lem-per-condensed-lisse-open-dualizing).

Proof: define the open comparison as pullback of purity on the target, the
coherent line comparison, then inverse purity on the source. Postcomposition
with purity on the source cancels its inverse and proves normalization.
For two opens expand both composites. Functoriality cancels the middle purity
and inverse purity. Naturality of the pullback compositor moves the remaining
target-purity morphism across that compositor, and the line composition equation
finishes. The proof makes no dimension or nonemptiness assumption of its own.
-/
theorem open_dualizing_exists {k : Type u} [Field k] (hEll : IsUnit (ell : k))
    (A : ∀ T : Space k, AdjointData ell c T) (p : PurityComparisons ell c A) :
    ∃ e : OpenDualizingComparisons ell c A,
      OpenNormalized ell c A p e ∧ OpenComposition ell c A e := by
  classical
  obtain ⟨rho, hn⟩ := open_line_normalized_exists ell c k hEll
  have hc := open_line_coherence ell c k hEll rho hn
  let e : OpenDualizingComparisons ell c A := fun V T j _ hj ↦
    (pull ell c j).mapIso (p T) ≪≫ rho V T j hj ≪≫ (p V).symm
  refine ⟨e, ?_, ?_⟩
  · intro V T j hj hbase q hd
    let : IsOpenImmersion j := hj
    have h := hn V T j hbase q hd
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact precomp_heq
      (congrArg (fun d : Fin 2 ↦ c.derivedLine ell V.scheme d.val) hd)
      ((pull ell c j).map (p T).hom) _ _ h
  · intro W V T i j hi hj hbasei hbasej hbaseij
    let : IsOpenImmersion i := hi
    let : IsOpenImmersion j := hj
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    simp only [Functor.map_comp, Category.assoc]
    rw [← (pull ell c i).map_comp_assoc (p V).inv (p V).hom,
      Iso.inv_hom_id, (pull ell c i).map_id, Category.id_comp]
    have hp := (pullComp ell c i j).hom.naturality (p T).hom
    dsimp only [Functor.comp_map] at hp
    have hc' := hc W V T i j hbasei hbasej hbaseij
    calc
      _ = (pull ell c (i ≫ j)).map (p T).hom ≫
          ((pullComp ell c i j).hom.app (c.derivedLine ell T.scheme T.dim.val) ≫
            (pull ell c i).map (rho V T j hbasej).hom ≫ (rho W V i hbasei).hom) ≫
          (p W).inv := by
        simpa only [Category.assoc] using congrArg
          (fun f ↦ f ≫ (pull ell c i).map (rho V T j hbasej).hom ≫
            (rho W V i hbasei).hom ≫ (p W).inv) hp.symm
      _ = _ := by rw [hc']

end AlgebraicGeometry.ProEtale.CondensedLisseDual

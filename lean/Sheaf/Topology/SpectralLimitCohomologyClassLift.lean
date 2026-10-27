/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Sheaf.Topology.SpectralLimitCohomologyMap

import Sheaf.Topology.SpectralLimitAcyclicReplacement
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Sheaf.Topology.SpectralLimitUnitGeneration
import Sheaf.Topology.AbelianLargeCompactOpenColimit
import Sheaf.Topology.SpectralLimitCohomologyDegreeZero

/-! # ClassLift

Source: Stacks Project, Cohomology of Sheaves, Tag 0A37, lemma-colimit.
(blueprint: lem-weil-pbc-spectral-limit-cohomology-class-lift)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.Functor.sheafPullbackConstruction
namespace TopCat.Sheaf

private theorem eval₀_surjective {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u}]
    [HasExt.{u} (CategoryTheory.Sheaf J AddCommGrpCat.{u})]
    (A : CategoryTheory.Sheaf J AddCommGrpCat.{u}) (V : C) :
    Function.Surjective (CategoryTheory.Sheaf.objectCohomologyEval₀
      J V A) := by
  let W := yoneda.obj V ⋙ AddCommGrpCat.free
  let e : (W ⟶ A.obj) ≃ A.obj.obj (op V) :=
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans yonedaEquiv
  intro s
  let φ := ((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv W A).symm
    (e.symm s)
  refine ⟨CategoryTheory.Abelian.Ext.addEquiv₀.symm φ, ?_⟩
  change (((CategoryTheory.Abelian.Ext.addEquiv₀
    (CategoryTheory.Abelian.Ext.addEquiv₀.symm φ)).hom.app (op V)).hom
      (((toSheafify J W).app (op V)).hom (FreeAbelianGroup.of (𝟙 V)))) = s
  rw [AddEquiv.apply_symm_apply]
  have he : e (((sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv W A) φ) = s := by
    dsimp only [φ]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact he

attribute [local irreducible] CategoryTheory.Sheaf.cohomologyPresheafFunctor

/-- Every class of the limit sheaf is the canonical image of a class at a stage.
This is the generation half of continuity and asserts no detection of relations.

Proof: induct on the degree simultaneously for all compatible systems. In degree
zero use the spectral-limit sections comparison over the terminal compact open;
upper-tail inclusion is cofinal. For the successor step embed the system in the
compatible products of pushforwards of injectives from Tag 0A37 and form its
cokernel system. Exact inverse image and exact filtered sheaf colimits give the
short exact sequence on the limit. Every finite compact-open cover descends to a
stage. Sections comparison identifies its Cech complex for the limit of the
injectives with the filtered colimit of the stage Cech complexes: each degree has
finitely many factors. Injective Cech exactness and exact filtered colimits,
followed by the Cech criterion, make the middle limit sheaf positively acyclic.
Thus the target connecting map onto the successor cohomology is surjective.
Lift a class through that connecting map, then apply the lower-degree generation
assertion to the quotient system. The normalized pullback boundary identity and
coefficient naturality identify its stage boundary with the original class.

The compatible embedding used above is explicit: choose monomorphisms
F_k → A_k into injectives, and put G_i = ∏_{k≥i} (f_ik)_* A_k.
The k-component of F_i → G_i is α_ik followed by the pushed-forward embedding.
Its i-component is the chosen monomorphism, so it is monic. The transition from
i to j discards the coordinates with k not ≥ j and uses f_ik = f_ij f_jk on
the retained coordinates. The cocycle equations for α give compatibility of
these embeddings. Continuous direct image preserves injectives because inverse
image is exact, and products of injectives are injective. Cokernels give the
quotient system; exact inverse image and exact filtered colimits of sheaves give
the short exact sequence on X. To justify the asserted positive acyclicity,
compact opens pulled back from stages form a basis closed under intersections.
Every finite compact-open covering descends, with its covering equality, to one
stage. On this cover, sections comparison identifies each term and differential
of the limit Čech complex with the filtered colimit of the stage complexes.
Only finitely many factors occur in any fixed degree, so common upper indices
represent all their sections and detect their relations. Injective Čech
exactness and exact filtered colimits give positive Čech acyclicity. The basis
Čech criterion then gives positive sheaf-cohomology acyclicity on X.

Source: Stacks Project, Cohomology of Sheaves, Tag 0A37, lemma-colimit.
(blueprint: lem-weil-pbc-spectral-limit-cohomology-class-lift) -/
theorem spectralLimit_cohomology_class_lift
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I → TopCat.{u}) [∀ i : I, SpectralSpace (S i)]
    (f : ∀ (i j : I), i ≤ j → (S j ⟶ S i))
    (hf : ∀ (i j : I) (h : i ≤ j), IsSpectralMap (f i j h))
    (hfid : ∀ i : I, f i i le_rfl = 𝟙 (S i))
    (hfcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k),
      f j k hjk ≫ f i j hij = f i k (hij.trans hjk))
    (X : TopCat.{u}) [SpectralSpace X] (p : ∀ i : I, X ⟶ S i)
    (hpcomp : ∀ (i j : I) (h : i ≤ j), p j ≫ f i j h = p i)
    (hlimit : ∀ a : ∀ i : I, S i,
      (∀ (i j : I) (h : i ≤ j), f i j h (a j) = a i) →
      ∃! x : X, ∀ i : I, p i x = a i)
    (htop : X.str = ⨅ i : I, TopologicalSpace.induced (p i) (S i).str)
    (F : ∀ i : I, (S i).Sheaf AddCommGrpCat.{u})
    (α : ∀ (i j : I) (h : i ≤ j),
      F i ⟶ (pushforward AddCommGrpCat.{u} (f i j h)).obj (F j))
    (hαid : ∀ (i : I) (U : Opens (S i)) (s : (F i).obj.obj (op U)),
      HEq ((α i i le_rfl).hom.app (op U) s) s)
    (hαcomp : ∀ (i j k : I) (hij : i ≤ j) (hjk : j ≤ k)
      (U : Opens (S i)) (s : (F i).obj.obj (op U)),
      HEq ((α i k (hij.trans hjk)).hom.app (op U) s)
        ((α j k hjk).hom.app (op ((Opens.map (f i j hij)).obj U))
          ((α i j hij).hom.app (op U) s)))
    (P : I ⥤ X.Sheaf AddCommGrpCat.{u}) [HasColimit P]
    (eP : ∀ i : I, P.obj i ≅
      (sheafPullback (Opens.map (p i)) AddCommGrpCat.{u}
        (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).obj (F i))
    (hP : ∀ (i j : I) (h : i ≤ j) (U : Opens (S i)) (s : (F i).obj.obj (op U)),
      HEq (((eP i).inv ≫ P.map (homOfLE h) ≫ (eP j).hom).hom.app
          (op ((Opens.map (p i)).obj U))
        (((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
          (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).unit.app
            (F i)).hom.app (op U) s))
        (((sheafAdjunctionContinuous (Opens.map (p j)) AddCommGrpCat.{u}
          (Opens.grothendieckTopology (S j)) (Opens.grothendieckTopology X)).unit.app
            (F j)).hom.app (op ((Opens.map (f i j h)).obj U))
              ((α i j h).hom.app (op U) s)))
    (cp : ∀ i : I, SiteCohomologyFamily (Opens.grothendieckTopology (S i))
      (Opens.grothendieckTopology X) (Opens.map (p i)))
    (hcp : ∀ i : I, @SiteCohomologyFamily.IsPullback _ _ _ _
      (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)
        (Opens.map (p i)) inferInstance
        (@Adjunction.left_adjoint_additive _ _ _ _ _ _ _ _
          (sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
            (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X))
          (Functor.additive_of_preserves_binary_products _))
        inferInstance inferInstance (cp i))
    (q : ℕ) (y : CategoryTheory.Sheaf.H' (colimit P) q ⊤) :
    ∃ (i : I) (x : CategoryTheory.Sheaf.H' (F i) q ⊤),
      (spectralLimitCohomologyMap (p i) (cp i)
      ((sheafAdjunctionContinuous (Opens.map (p i)) AddCommGrpCat.{u}
        (Opens.grothendieckTopology (S i)) (Opens.grothendieckTopology X)).homEquiv
          (F i) (colimit P) ((eP i).inv ≫ colimit.ι P i)) q).hom x = y := by
  classical
  induction q generalizing F α P with
  | zero =>
      let E := (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)
      have : PreservesColimit P E :=
        TopCat.abelianCompactOpen_preservesDirectedColimits.{u, u} X
          (fun W hW x hx ↦ by
            obtain ⟨T, ⟨hTo, hTc⟩, hxT, hTW⟩ :=
              PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open hx hW
            exact ⟨T, hTo, hTc, hxT, hTW⟩)
          (fun W T hW hT hWc hTc ↦ hWc.inter_of_isOpen hTc hW hT) I P ⊤
          (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X)))
      let ev := CategoryTheory.Sheaf.objectCohomologyEval₀ (Opens.grothendieckTopology X) ⊤
        (colimit P)
      obtain ⟨j, s, hs⟩ := Concrete.isColimit_exists_rep (P ⋙ E)
        (isColimitOfPreserves E (colimit.isColimit P)) (ev y)
      change (colimit.ι P j).hom.app (op ⊤) s = ev y at hs
      have hgmap : ∀ (j k : I) (h : j ≤ k) (U : Opens (S j))
          (s : (F j).obj.obj (op U)),
          HEq ((P.map (homOfLE h) ≫ (eP k).hom).hom.app
              (op ((Opens.map (p j)).obj U))
            ((eP j).inv.hom.app (op ((Opens.map (p j)).obj U))
              (((sheafAdjunctionContinuous (Opens.map (p j)) AddCommGrpCat.{u}
                (Opens.grothendieckTopology (S j)) (Opens.grothendieckTopology X)).unit.app
                  (F j)).hom.app (op U) s)))
            (((sheafAdjunctionContinuous (Opens.map (p k)) AddCommGrpCat.{u}
              (Opens.grothendieckTopology (S k)) (Opens.grothendieckTopology X)).unit.app
                (F k)).hom.app (op ((Opens.map (f j k h)).obj U))
                  ((α j k h).hom.app (op U) s)) := by
        intro j k h U s
        exact hP j k h U s
      have hg := spectralLimit_unit_generation.{u, u} S f hf hfid hfcomp X p hpcomp hlimit htop
        F α hαid (fun j k l hjk hkl U s ↦ (hαcomp j k l hjk hkl U s).symm)
        P eP hgmap j ⊤
          (by simpa using (isCompact_univ : IsCompact (Set.univ : Set (S j))))
      simp only [Opens.map_top] at hg
      let η (k : I) :=
        (((sheafAdjunctionContinuous (Opens.map (p k)) AddCommGrpCat.{u}
          (Opens.grothendieckTopology (S k)) (Opens.grothendieckTopology X)).unit.app
            (F k)).hom.app (op ⊤)) ≫ (eP k).inv.hom.app (op ⊤)
      obtain ⟨k, hjk, t, ht⟩ := hg (fun k _ ↦ η k) (fun _ _ _ ↦ HEq.rfl) j le_rfl s
      have hw := ConcreteCategory.congr_hom
        (congrArg (fun a ↦ a.hom.app (op ⊤)) (colimit.w P (homOfLE hjk))) s
      have ht' := congrArg ((colimit.ι P k).hom.app (op ⊤)) ht
      have hsection : (colimit.ι P k).hom.app (op ⊤) (η k t) = ev y :=
        ht'.symm.trans (hw.trans hs)
      obtain ⟨x, hx⟩ := eval₀_surjective (Opens.grothendieckTopology (S k)) (F k) ⊤ t
      refine ⟨k, x, ?_⟩
      apply CategoryTheory.Sheaf.objectCohomologyEval₀_injective
        (Opens.grothendieckTopology X) ⊤ (colimit P)
      have hz := spectralLimitCohomologyMap_eval₀ (p k) (cp k)
        (fun A x ↦ (hcp k).2.2 ⊤ A x)
        ((sheafAdjunctionContinuous (Opens.map (p k)) AddCommGrpCat.{u}
          (Opens.grothendieckTopology (S k)) (Opens.grothendieckTopology X)).homEquiv
            (F k) (colimit P) ((eP k).inv ≫ colimit.ι P k)) x
      rw [hx] at hz
      have heval : HEq ((colimit.ι P k).hom.app (op ⊤) (η k t))
          (((sheafAdjunctionContinuous (Opens.map (p k)) AddCommGrpCat.{u}
            (Opens.grothendieckTopology (S k)) (Opens.grothendieckTopology X)).homEquiv
              (F k) (colimit P) ((eP k).inv ≫ colimit.ι P k)).hom.app (op ⊤) t) := by
        rfl
      exact eq_of_heq (hz.trans (heval.symm.trans (heq_of_eq hsection)))
  | succ n ih =>
      obtain ⟨Q, β, hβid, hβcomp, R, hcolR, eR, hR, d, D, hD, hstage⟩ :=
        spectralLimit_acyclic_replacement S f hf hfid hfcomp X p hpcomp hlimit htop
          F α hαid hαcomp P eP hP
      have := hcolR
      obtain ⟨z, hz⟩ := hD n y
      obtain ⟨i, x, hx⟩ := ih Q β hβid hβcomp R eR hR z
      refine ⟨i, d i n x, ?_⟩
      exact (hstage i (cp i) (hcp i) n x).trans ((congrArg (D n) hx).trans hz)

end TopCat.Sheaf

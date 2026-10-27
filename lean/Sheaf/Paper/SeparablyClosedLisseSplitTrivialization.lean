/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.ProEtale.StrictlyHenselianRetraction
import Sheaf.AlgebraicGeometry.ProEtale.WContractibleClopenPartition
public import Mathlib.Order.CompletePartialOrder

/-! # Split lisse trivializations at a separably closed point

Source: Bhatt--Scholze, Section 2.4, Lemma 2.4.8 and Example 7.3.5;
Stacks Project, Tags 0982, 098F, 03EH and 04IX
(blueprint: lem-sfb-separably-closed-lisse-split-trivialization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Restrict a slice isomorphism using a compatible arrow from every object. -/
private noncomputable def restrictSliceIso
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} R}
    (U : C) (b : ∀ V : C, V ⟶ U)
    (hb : ∀ {V V' : C} (f : V ⟶ V'), f ≫ b V' = b V)
    (t : M.over U ≅ N.over U) : M ≅ N := by
  let p : M.val ≅ N.val := PresheafOfModules.isoMk
    (fun Z ↦ (SheafOfModules.evaluation _ (op (Over.mk (b Z.unop)))).mapIso t)
    (by
      intro V V' f
      let h : Over.mk (b V'.unop) ⟶ Over.mk (b V.unop) :=
        Over.homMk f.unop (hb f.unop)
      ext x
      exact PresheafOfModules.naturality_apply t.hom.val h.op x)
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso p

/-- Every supplied slice trivialization of a lisse module at a separably closed point
can be restricted along a section of one of its covering arrows. The resulting global
internal-module isomorphism has exactly the specified sectionwise components.
There is no condition on the condensed coefficients beyond commutativity, and rank zero
is included. The restricted finite free module is the finite sum of the restricted
regular module, using the canonical finite-biproduct identification.

Source: Bhatt--Scholze, Lemma 2.4.8 and Example 7.3.5; Stacks Project, Tags 0982,
098F, 03EH and 04IX (blueprint: lem-sfb-separably-closed-lisse-split-trivialization).

Proof:
1. The spectrum of the field has one point and one maximal ideal, zero. Its closed
   points and connected-component space are singletons, hence the spectrum is w-local
   and its component space is extremally disconnected. The pair with the zero ideal
   is henselian: for every finite algebra the reduction by zero is the identity, so
   idempotents lift uniquely. Its residue field and sole maximal localization are the
   original separably closed field. Thus it is w-contractible by
   def-weil-pbc-henselian-terminology and det-pe-wlocal-strict-contractible.
2. Apply det-pe-wcb-clopen-partition to the given cover. A nonempty piece of its finite
   clopen partition of the one-point scheme must be the whole scheme. The map of this
   piece into its chosen covering member is the section s; its composite with the
   covering arrow is the identity. All maps over X are arrows of the small site.
3. Under def-weil-pbc-internal-abelian-sheaf-module-equivalence, evaluate tau and its
   inverse on (V, v followed by s). Naturality follows from associativity of composition;
   the rings and their actions are unchanged by def-pur-localized-ringed-site.
   The components are linear, natural and mutually inverse. The equivalence gives the
   global internal-module isomorphism phi. Its components are the displayed ones.
   Finite sums are finite products and glue coordinatewise; for rank zero their tuples
   are empty. No topology or completeness on the coefficient ring enters the argument.
-/
theorem separablyClosed_lisse_split_trivialization
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (L : Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
      (condensedRingObj Λ.X (Spec (.of Ω))))
    (hL : IsLisseCoefficientModule Λ.X L)
    (I : Type v) (U : I → (Spec (.of Ω)).ProEt)
    (a : ∀ i : I, U i ⟶ Scheme.ProEt.mk (𝟙 (Spec (.of Ω))))
    (hcover : Presieve.ofArrows U a ∈
      Scheme.ProEt.precoverage (Spec (.of Ω)) (Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))))
    (n : I → ℕ)
    (τ : ∀ i : I,
      ((sectionModuleEquivalence (Scheme.ProEt.topology (Spec (.of Ω)))
        (condensedRingObj Λ.X (Spec (.of Ω)))).functor.obj L).over (U i) ≅
      ((sectionModuleEquivalence (Scheme.ProEt.topology (Spec (.of Ω)))
        (condensedRingObj Λ.X (Spec (.of Ω)))).functor.obj
          (Mod.finiteFree (condensedRingObj Λ.X (Spec (.of Ω))) (n i))).over (U i)) :
    ∃ (i : I) (s : Scheme.ProEt.mk (𝟙 (Spec (.of Ω))) ⟶ U i),
      s ≫ a i = 𝟙 _ ∧
      ∃ φ : L ≅ Mod.finiteFree (condensedRingObj Λ.X (Spec (.of Ω))) (n i),
        ∀ (V : (Spec (.of Ω)).ProEt)
          (v : V ⟶ Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))),
          (((sectionModuleEquivalence (Scheme.ProEt.topology (Spec (.of Ω)))
            (condensedRingObj Λ.X (Spec (.of Ω)))).functor.map φ.hom).val.app (op V)).hom =
            ((τ i).hom.val.app (op (Over.mk (v ≫ s)))).hom := by
  classical
  have _hL := hL
  have : IsSepClosed (IsLocalRing.ResidueField Ω) :=
    IsSepClosed.of_ringEquiv (RingEquiv.ofBijective (IsLocalRing.residue Ω)
      ⟨(IsLocalRing.residue Ω).injective, IsLocalRing.residue_surjective⟩)
  have : IsStrictlyHenselianLocalRing Ω := ⟨inferInstance⟩
  have : IsWContractibleRing Ω := IsStrictlyHenselianLocalRing.isWContractibleRing Ω
  obtain ⟨m, W, _, _, _, htop, j, g, hg⟩ :=
    Scheme.proetale_wContractible_clopen_partition (Spec (.of Ω)) Ω (𝟙 _) I U a hcover
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show IsLocalRing.closedPoint Ω ∈ iSup W by rw [htop]; trivial)
  have hW : W k = ⊤ := by
    apply top_unique
    intro x _
    exact Subsingleton.elim (IsLocalRing.closedPoint Ω) x ▸ hk
  let e : Spec (.of Ω) ≅ (W k).toScheme :=
    (Scheme.topIso _).symm ≪≫ (Scheme.isoOfEq _ hW).symm
  have he : e.hom ≫ (W k).ι = 𝟙 _ := by
    dsimp only [e]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [Scheme.isoOfEq_inv_ι]
    exact (Scheme.topIso _).inv_hom_id
  let s : Scheme.ProEt.mk (𝟙 (Spec (.of Ω))) ⟶ U (j k) :=
    MorphismProperty.Over.homMk (e.hom ≫ g k) (by
      change (e.hom ≫ g k) ≫ (U (j k)).hom = 𝟙 _
      have ha : (a (j k)).left = (U (j k)).hom := by
        have h := MorphismProperty.Over.w (a (j k))
        change (a (j k)).left ≫ 𝟙 _ = _ at h
        simpa only [Category.comp_id] using h
      rw [← ha, Category.assoc, hg, he]) trivial
  refine ⟨j k, s, ?_, ?_⟩
  · apply MorphismProperty.Over.Hom.ext
    change (e.hom ≫ g k) ≫ (a (j k)).left = 𝟙 _
    rw [Category.assoc, hg, he]
  · let E := sectionModuleEquivalence (Scheme.ProEt.topology (Spec (.of Ω)))
      (condensedRingObj Λ.X (Spec (.of Ω)))
    let c (V : (Spec (.of Ω)).ProEt) :
        V ⟶ Scheme.ProEt.mk (𝟙 (Spec (.of Ω))) :=
      MorphismProperty.Over.homMk V.hom (by
        change V.hom ≫ 𝟙 _ = V.hom
        exact Category.comp_id _) trivial
    have hc (V : (Spec (.of Ω)).ProEt)
        (v : V ⟶ Scheme.ProEt.mk (𝟙 (Spec (.of Ω)))) : v = c V := by
      apply MorphismProperty.Over.Hom.ext
      have h := MorphismProperty.Over.w v
      change v.left ≫ 𝟙 _ = V.hom at h
      exact (Category.comp_id _).symm.trans h
    let b (V : (Spec (.of Ω)).ProEt) := c V ≫ s
    have hb {V V' : (Spec (.of Ω)).ProEt} (f : V ⟶ V') : f ≫ b V' = b V := by
      dsimp only [b]
      rw [← Category.assoc, hc V (f ≫ c V')]
    let q : E.functor.obj L ≅
        E.functor.obj (Mod.finiteFree (condensedRingObj Λ.X (Spec (.of Ω))) (n (j k))) :=
      restrictSliceIso (U (j k)) b (fun f ↦ hb f) (τ (j k))
    refine ⟨E.functor.preimageIso q, ?_⟩
    intro V v
    change ((E.functor.map (E.functor.preimage q.hom)).val.app (op V)).hom = _
    have hp := E.functor.map_preimage q.hom
    calc
      _ = (q.hom.val.app (op V)).hom :=
        congrArg (fun f ↦ (f.val.app (op V)).hom) hp
      _ = ((τ (j k)).hom.val.app (op (Over.mk (v ≫ s)))).hom := by
        rw [hc V v]
        rfl

end AlgebraicGeometry.ProEtale

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q86 and A4
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Bidual
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Locally finite-free evaluation and biduality on ringed sites

Source: blueprint `lem-sf-hom-finite-projective.proof.md`, first and last sentences;
Stacks Project, Modules on Sites, Section 04TT and Tag 0E8H; Sites, Tag 04TQ
(blueprint: lem-sf-locally-free-sheaf-evaluation-biduality).

The evaluation and internal Hom are the existing slice-Hom constructions. The only
additional data are their composite restriction identification and names for the
basis vectors and coordinate functionals of a chosen local trivialization.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}

/-- The restriction identification for internal Hom, written componentwise to avoid
transporting the entire presheaf along a definitional equality.
Source: Stacks Project, Tag 0E8H
(blueprint: lem-sf-locally-free-sheaf-evaluation-biduality). -/
noncomputable def evaluationOverHomIso
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    (M N : CategoryTheory.ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) (U : C) :
    (homObj (R := R) M N).over U ≅
      homObj (R := R.over U) (M.over U) (N.over U) :=
  (fullyFaithfulForget _).preimageIso <| PresheafOfModules.isoMk (fun W ↦ {
    hom := ConcreteCategory.ofHom {
      toFun := PresheafOfModules.restrictOverHomObjFwd (R := R.obj) (M := M.val)
        (N := N.val) U W.unop
      map_add' φ ψ := by
        refine PresheafOfModules.hom_ext
          (M₁ := (PresheafOfModules.restrictOver (R.over U).obj W.unop).obj (M.over U).val)
          (M₂ := (PresheafOfModules.restrictOver (R.over U).obj W.unop).obj (N.over U).val)
          fun V ↦ ?_
        ext x
        rfl
      map_smul' a φ := by
        refine PresheafOfModules.hom_ext
          (M₁ := (PresheafOfModules.restrictOver (R.over U).obj W.unop).obj (M.over U).val)
          (M₂ := (PresheafOfModules.restrictOver (R.over U).obj W.unop).obj (N.over U).val)
          fun V ↦ ?_
        ext x
        rfl }
    inv := ConcreteCategory.ofHom {
      toFun := PresheafOfModules.restrictOverHomObjBwd (R := R.obj) (M := M.val)
        (N := N.val) U W.unop
      map_add' φ ψ := by
        refine PresheafOfModules.hom_ext
          (M₁ := (PresheafOfModules.restrictOver R.obj W.unop.left).obj M.val)
          (M₂ := (PresheafOfModules.restrictOver R.obj W.unop.left).obj N.val)
          fun V ↦ ?_
        ext x
        rfl
      map_smul' a φ := by
        refine PresheafOfModules.hom_ext
          (M₁ := (PresheafOfModules.restrictOver R.obj W.unop.left).obj M.val)
          (M₂ := (PresheafOfModules.restrictOver R.obj W.unop.left).obj N.val)
          fun V ↦ ?_
        ext x
        rfl }
    hom_inv_id := by
      ext φ : 2
      exact PresheafOfModules.restrictOverHomObjBwd_fwd W.unop φ
    inv_hom_id := by
      ext φ : 2
      exact PresheafOfModules.restrictOverHomObjFwd_bwd W.unop φ })
    (fun {_ _} f ↦ by
      ext φ
      apply PresheafOfModules.hom_ext
      intro W
      ext x
      rfl)

/-- The canonical restriction identification for the double dual, obtained by applying
`evaluationOverHomIso` twice, with the restricted coefficients.
Source: Stacks Project, Tag 0E8H
(blueprint: lem-sf-locally-free-sheaf-evaluation-biduality). -/
noncomputable def bidualOverIso
    (M : CategoryTheory.ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) (U : C) :
    (homObj (R := R) (homObj (R := R) M (unit _)) (unit _)).over U ≅
      homObj (R := R.over U) (homObj (R := R.over U) (M.over U) (unit _)) (unit _) :=
  evaluationOverHomIso (R := R) (homObj (R := R) M (unit _)) (unit _) U ≪≫
    ((homFunctor (R.over U)).flip.obj (unit _)).mapIso
      (evaluationOverHomIso (R := R) M (unit _) U).symm.op

/-- The basis vector of a chosen finite-free trivialization, evaluated at the identity
of the slice. Source: blueprint `lem-sf-hom-finite-projective.proof.md`, first sentence
(blueprint: lem-sf-locally-free-sheaf-evaluation-biduality). -/
noncomputable def localBasisSection
    {M : CategoryTheory.ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)} {U : C} {r : ℕ}
    (e : M.over U ≅ free (ULift.{u} (Fin r))) (j : ULift.{u} (Fin r)) :
    M.val.obj (op U) :=
  (ιFree j ≫ e.inv).val.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U))

/-- The coordinate functional of a chosen finite-free trivialization, as a section
of the slice-Hom dual. Source: blueprint `lem-sf-hom-finite-projective.proof.md`,
first sentence (blueprint: lem-sf-locally-free-sheaf-evaluation-biduality). -/
noncomputable def localCoordinateFunctional
    {M : CategoryTheory.ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)} {U : C} {r : ℕ}
    (e : M.over U ≅ free (ULift.{u} (Fin r))) (j : ULift.{u} (Fin r)) :
    (homObj (R := R) M (unit _)).val.obj (op U) :=
  toRestrictOverHom (R := R) (e.hom ≫ freeπ j)

section Helpers
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

private noncomputable def finiteFreeDualIso
    (M : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    {I : Type u} [Fintype I] (b : M ≅ free I) : homObj (R := R) M (unit _) ≅ free I :=
  ((homFunctor R).flip.obj (unit _)).mapIso b.symm.op ≪≫ homObjFreeUnitIso I

private theorem finiteFreeDualIso_projection
    (M : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    {I : Type u} [Fintype I] [DecidableEq I] (b : M ≅ free I) (j : I) :
    (finiteFreeDualIso M b).hom ≫ freeπ j =
      homObjMap (R := R) (ιFree j ≫ b.inv) (𝟙 (unit _)) ≫
        (homObjUnitIso (R := R) (unit _)).hom := by
  classical
  have hp : (biproduct.isoCoproduct (fun _ : I ↦ unit
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))).hom ≫ freeπ j =
      biproduct.π (fun _ : I ↦ unit
        ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) j := by
    apply biproduct.hom_ext'
    intro l
    simp [biproduct.isoCoproduct_hom, biproduct.ι_π, freeπ]
  dsimp only [finiteFreeDualIso, homObjFreeUnitIso, Iso.trans_hom]
  rw [Category.assoc, Category.assoc, hp]
  simp [homObjFreeIso, Functor.opMapBiproductIso,
    biproduct.uniqueUpToIso, Functor.opMapBicone, ιFree]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem localBasisSection_restrict
    {M : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)}
    {U : C} {r : ℕ} (b : M.over U ≅ free (ULift.{u} (Fin r)))
    (j : ULift.{u} (Fin r)) (V : Over U) :
    (ιFree j ≫ b.inv).val.app (op V) (1 : R.obj.obj (op V.left)) =
      M.val.map V.hom.op (localBasisSection (R := R) b j) := by
  have h := PresheafOfModules.naturality_apply (ιFree j ≫ b.inv).val
    (Over.homMk V.hom (Category.comp_id _) : V ⟶ Over.mk (𝟙 U)).op
    (1 : R.obj.obj (op U))
  change (ιFree j ≫ b.inv).val.app (op V) (R.obj.map V.hom.op 1) = _ at h
  rw [map_one] at h
  exact h

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
private theorem localBasisSection_span
    {M : SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)}
    {U : C} {r : ℕ} (b : M.over U ≅ free (ULift.{u} (Fin r)))
    (V : Over U) (x : M.val.obj (op V.left)) :
    x = ∑ j : ULift.{u} (Fin r), (b.hom ≫ freeπ j).val.app (op V) x •
      M.val.map V.hom.op (localBasisSection (R := R) b j) := by
  classical
  have ht : ∑ j : ULift.{u} (Fin r),
      (b.hom ≫ freeπ j) ≫ (ιFree j ≫ b.inv) = 𝟙 _ := by
    calc
      _ = b.hom ≫ (∑ j : ULift.{u} (Fin r), freeπ j ≫ ιFree j) ≫ b.inv := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      _ = 𝟙 _ := by rw [sum_freeπ_ιFree, Category.id_comp, b.hom_inv_id]
  have hx := congrArg (fun f ↦ f.val.app (op V) x) ht
  rw [sum_val_app_apply] at hx
  refine hx.symm.trans (Finset.sum_congr rfl fun j _ ↦ ?_)
  change (ιFree j ≫ b.inv).val.app (op V) ((b.hom ≫ freeπ j).val.app (op V) x) = _
  rw [← localBasisSection_restrict (R := R) b j V]
  simpa only [smul_eq_mul, mul_one] using
    ((ιFree j ≫ b.inv).val.app (op V)).hom.map_smul
      ((b.hom ≫ freeπ j).val.app (op V) x) (1 : R.obj.obj (op V.left))

end Helpers

/-- Ordinary locally finite-free biduality, with evaluation, restriction, naturality,
dual coordinates and the inverse formula, allowing a different finite rank on each slice.

Source: blueprint `lem-sf-hom-finite-projective.proof.md`, first and last sentences;
Stacks Project, Modules on Sites, Section 04TT and Tag 0E8H; Sites, Tag 04TQ
(blueprint: lem-sf-locally-free-sheaf-evaluation-biduality).

Proof plan:
1. By def-pur-sheaf-hom and def-pur-localized-ringed-site, relocalization identifies
   the two slice-Hom constructions by sending a local morphism to itself. Apply this
   twice for the double dual; successive restrictions have the same components.
2. Evaluation sends x and a local functional lambda to lambda(x restricted).
   Linearity and naturality of lambda give a module-sheaf map. The same computation
   gives compatibility with restriction and naturality for every map M to N.
3. On each chosen finite-free slice, a functional is uniquely determined by its values
   on the basis vectors. Conversely a tuple defines the functional by the finite sum
   of coordinate functionals. These mutually inverse linear maps commute with restriction.
4. For a bidual section eta the sum of eta(e_j^*) times e_j is inverse to evaluation.
   Expand each functional in the dual basis and use commutativity and naturality.
   Both compositions are identities; for rank zero these are empty sums.
5. The slice inverses glue by lem-sfb-sheaf-cover-local-isomorphism applied to the
   underlying abelian sheaves. The inverse is linear by injectivity of evaluation.
   Uniqueness of inverses identifies its restrictions with the displayed finite sums.
   Only individual finite ranks are used, with no uniform bound or site points.
-/
theorem locallyFreeEvaluationBiduality
    (M : CategoryTheory.ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
    {I : Type u} (U : I → C) (hU : J.CoversTop U) (r : I → ℕ)
    (e : ∀ i, M.over (U i) ≅ free (ULift.{u} (Fin (r i)))) :
    (∀ (T : C) (x : M.val.obj (op T)) (V : Over T)
      (φ : (homObj (R := R) M (unit _)).val.obj (op V.left)),
      ((bidual (R := R) M).val.app (op T) x).app (op V) φ =
        φ.app (op (Over.mk (𝟙 V.left))) (M.val.map V.hom.op x)) ∧
    (∀ T : C, (bidual (R := R) M).over T ≫ (bidualOverIso (R := R) M T).hom =
      bidual (R := R.over T) (M.over T)) ∧
    (∀ (N : CategoryTheory.ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)) (f : M ⟶ N),
      bidual (R := R) M ≫ homObjMap (R := R) (homObjMap (R := R) f (𝟙 _)) (𝟙 _) =
        f ≫ bidual (R := R) N) ∧
    (∃ s : homObj (R := R) (homObj (R := R) M (unit _)) (unit _) ⟶ M,
      bidual (R := R) M ≫ s = 𝟙 M ∧ s ≫ bidual (R := R) M = 𝟙 _ ∧
      ∀ (i : I) (b : M.over (U i) ≅ free (ULift.{u} (Fin (r i)))),
      (∃ d : (homObj (R := R) M (unit _)).over (U i) ≅ free (ULift.{u} (Fin (r i))),
        ∀ (V : Over (U i)) (φ : (homObj (R := R) M (unit _)).val.obj (op V.left))
          (j : ULift.{u} (Fin (r i))),
          freeSectionsLinearEquiv (ULift.{u} (Fin (r i))) (op V)
            (d.hom.val.app (op V) φ) j =
          φ.app (op (Over.mk (𝟙 V.left)))
            (M.val.map V.hom.op (localBasisSection (R := R) b j))) ∧
      (∀ (V : Over (U i))
        (η : (homObj (R := R) (homObj (R := R) M (unit _)) (unit _)).val.obj (op V.left)),
        s.val.app (op V.left) η =
          ∑ j : ULift.{u} (Fin (r i)),
            η.app (op (Over.mk (𝟙 V.left)))
              ((homObj (R := R) M (unit _)).val.map V.hom.op
                (localCoordinateFunctional (R := R) b j)) •
                M.val.map V.hom.op (localBasisSection (R := R) b j))) := by
  classical
  have : J.HasSheafCompose (forget₂ CommRingCat RingCat.{u}) := inferInstance
  have : HasSheafify J AddCommGrpCat.{u} := inferInstance
  have : J.WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  have : ∀ X, HasSheafify (J.over X) AddCommGrpCat.{u} := fun X ↦ inferInstance
  have : ∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u} := fun X ↦ inferInstance
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro T x V φ
    rfl
  · intro T
    ext1
    ext X x : 3
    apply PresheafOfModules.hom_ext
    intro W
    ext φ
    exact congrArg (fun ψ ↦ ψ.app (op (Over.mk (𝟙 W.unop.left)))
      (M.val.map W.unop.hom.left.op x))
      (PresheafOfModules.restrictOverHomObjFwd_bwd
        (R := R.obj) (M := M.val) (N := (unit
          ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R)).val)
        W.unop.left φ)
  · intro N f
    exact (bidual_naturality f).symm
  · have : M.IsFiniteLocallyFree :=
      isFiniteLocallyFree_of_exists_over_iso_free (M := M) U hU
        (fun i ↦ ULift.{u} (Fin (r i))) (fun i ↦ ⟨e i⟩)
    have : IsIso (bidual (R := R) M) := isIso_bidual (R := R) M
    refine ⟨inv (bidual (R := R) M), IsIso.hom_inv_id _, IsIso.inv_hom_id _, ?_⟩
    intro i b
    constructor
    · let d := evaluationOverHomIso (R := R) M (unit _) (U i) ≪≫
        finiteFreeDualIso (R := R.over (U i)) (M.over (U i)) b
      refine ⟨d, ?_⟩
      intro V φ j
      have hp := finiteFreeDualIso_projection (R := R.over (U i)) (M.over (U i)) b j
      have hv := congrArg (fun f ↦ f.val.app (op V)
        ((evaluationOverHomIso (R := R) M (unit _) (U i)).hom.val.app (op V) φ)) hp
      rw [← localBasisSection_restrict (R := R) b j V]
      change _ = φ.app (op (Over.mk (𝟙 V.left)))
        ((ιFree j ≫ b.inv).val.app (op V) (1 : R.obj.obj (op V.left))) at hv
      exact hv
    · intro V η
      rcases V with ⟨Z, ⟨⟨⟩⟩, g⟩
      let V : Over (U i) := Over.mk g
      let x := (inv (bidual (R := R) M)).val.app (op V.left) η
      have hx : (bidual (R := R) M).val.app (op V.left) x = η :=
        congrArg (fun f ↦ f.val.app (op V.left) η) (IsIso.inv_hom_id (bidual (R := R) M))
      refine (localBasisSection_span (R := R) b V x).trans ?_
      apply Finset.sum_congr rfl
      intro j hj
      congr 1
      have hc := congrArg (fun φ ↦ φ.app (op (Over.mk (𝟙 V.left)))
        ((homObj (R := R) M (unit _)).val.map V.hom.op
          (localCoordinateFunctional (R := R) b j))) hx
      change ((homObj (R := R) M (unit _)).val.map V.hom.op
        (localCoordinateFunctional (R := R) b j)).app (op (Over.mk (𝟙 V.left)))
          (M.val.map (𝟙 V.left).op x) = _ at hc
      have hm : M.val.map (𝟙 V.left).op x = x := by
        exact M.val.map_id_apply' x
      rw [hm] at hc
      change (b.hom ≫ freeπ j).val.app (op (Over.mk (𝟙 V.left ≫ V.hom))) x = _ at hc
      have he := PresheafOfModules.restrictOver_hom_app_congr
        (R := R.obj) (M := M.val)
          (N := PresheafOfModules.unit (R.obj ⋙ forget₂ CommRingCat RingCat.{u}))
        (toRestrictOverHom (R := R) (M := M) (N := unit
          ((sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R))
          (b.hom ≫ freeπ j)) (Category.id_comp V.hom) x
      exact he.symm.trans hc

end SheafOfModules

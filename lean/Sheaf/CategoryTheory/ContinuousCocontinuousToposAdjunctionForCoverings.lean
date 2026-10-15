/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous

/-!
# The topos adjunction of a continuous cocontinuous site functor

Source: Stacks Project, Sites, Section 00XF and Tags 00XH, 00XK, 00XL, 00XO, 00XR
(blueprint: lem-weil-pbc-continuous-cocontinuous-topos-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private theorem continuous_of_coverings
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D) (hJ : J.IsSiteForCoverings)
    (f : C ⥤ D)
    (hcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map f ∈ K (f.obj X))
    (hpullback : ∀ (X Y Z : C) (S : Presieve X), S ∈ J X →
      ∀ (a : Y ⟶ X) (b : Z ⟶ X), S a → PreservesLimit (cospan a b) f) :
    f.IsContinuous J.toGrothendieck K.toGrothendieck := by
  let : J.HasPullbacks := ⟨by
    intro X Y R b hR
    obtain ⟨I, U, a, rfl⟩ := R.exists_eq_ofArrows
    obtain ⟨P, p, q, hpb, hp⟩ := hJ.2.2 I Y U a hR X b
    exact ⟨by
      rintro Z a ⟨i⟩
      exact (hpb i).flip.hasPullback⟩⟩
  refine ⟨fun G ↦ ?_⟩
  rw [J.isSheaf_toGrothendieck_iff]
  intro X Y b R hR
  obtain ⟨I, U, a, rfl⟩ := R.exists_eq_ofArrows
  obtain ⟨P, p, q, hpb, hp⟩ := hJ.2.2 I X U a hR Y b
  rw [← Sieve.ofArrows, ← Sieve.ofArrows_eq_pullback_of_isPullback a hpb,
    Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate]
  let : (Presieve.ofArrows P p).HasPairwisePullbacks := J.hasPairwisePullbacks_of_mem hp
  let : f.PreservesPairwisePullbacks (Presieve.ofArrows P p) :=
    ⟨fun A B a b ha hb ↦ hpullback Y A B _ hp a b ha⟩
  apply (Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks f G.obj _).2
  exact ((isSheaf_iff_isSheaf_of_type _ _).1 G.property).isSheafFor_of_mem_precoverage
    (hcover _ _ hp)

private def compatibleFamilyEquiv
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    (f : C ⥤ D) (F : Cᵒᵖ ⥤ Type u) (V : D) :
    (f.op ⋙ yoneda.obj V ⟶ F) ≃
      {s : ∀ (A : C), (f.obj A ⟶ V) → F.obj (op A) //
        ∀ (A B : C) (a : B ⟶ A) (ψ : f.obj A ⟶ V),
          F.map a.op (s A ψ) = s B (f.map a ≫ ψ)} where
  toFun α := ⟨fun A ψ ↦ α.app (op A) ψ, by
    intro A B a ψ
    exact (α.naturality_apply a.op ψ).symm⟩
  invFun s :=
    { app := fun A ↦ ↾(s.val A.unop)
      naturality := by
        intro A B a
        ext ψ
        exact (s.property A.unop B.unop a.unop ψ).symm }
  left_inv α := by ext A ψ; rfl
  right_inv s := rfl

private noncomputable def ranFamilyEquiv
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    (f : C ⥤ D) (F : Cᵒᵖ ⥤ Type u) (V : D) :
    (f.op.ran.obj F).obj (op V) ≃
      {s : ∀ (A : C), (f.obj A ⟶ V) → F.obj (op A) //
        ∀ (A B : C) (a : B ⟶ A) (ψ : f.obj A ⟶ V),
          F.map a.op (s A ψ) = s B (f.map a ≫ ψ)} :=
  yonedaEquiv.symm.trans
    (((f.op.ranAdjunction (Type u)).homEquiv (yoneda.obj V) F).symm.trans
      (compatibleFamilyEquiv f F V))

private theorem ranFamilyEquiv_apply
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    (f : C ⥤ D) (F : Cᵒᵖ ⥤ Type u) (V : D)
    (s : (f.op.ran.obj F).obj (op V)) (A : C) (ψ : f.obj A ⟶ V) :
    (ranFamilyEquiv f F V s).val A ψ =
      (f.op.ranCounit.app F).app (op A) ((f.op.ran.obj F).map ψ.op s) := by
  change ((((f.op.ranAdjunction (Type u)).homEquiv (yoneda.obj V) F).symm
    (yonedaEquiv.symm s)).app (op A)) ψ = _
  rw [Adjunction.homEquiv_counit, Functor.ranAdjunction_counit]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Source: Stacks Project, Sites, Section 00XF and Tags 00XH, 00XK, 00XL, 00XO, 00XR
(blueprint: lem-weil-pbc-continuous-cocontinuous-topos-adjunction).

`L` is identified naturally with precomposition. The existing cocontinuous pushforward
is identified sectionwise with exactly the subtype of compatible families in the node.
The two naturality equations give its restriction maps and its action on sheaf maps.
The last two equations specify the counit and unit under these identifications.
The sites use `IsSiteForCoverings`, allowing finite covers and requiring only covering
pullbacks. Composition is by distinct arrows, as in `Pretopology.transitive`.
An adjunction with `PreservesFiniteLimits L` is the node's morphism of topoi; no local
fullness, local faithfulness, or cover-density is imposed.

Proof:
1. Continuity makes precomposition a sheaf, by
   lem-weil-pbc-site-continuous-pushforward-sheaf, and hence defines `L` on objects
   and natural transformations.
2. At `V`, form the subset of the product of `F(A)` indexed by `(A, u(A) ⟶ V)`
   satisfying the displayed compatibility. Restriction substitutes `ψ ≫ h` and
   sheaf maps act componentwise. The indexing set may be empty.
3. To prove separatedness, pull a target cover back along each `ψ` and use
   cocontinuity to refine it by images of a source cover. Equality on that cover
   implies equality in `F(A)` by the sheaf condition.
4. For gluing, choose such lifts and glue the corresponding sections of `F`.
   On overlaps their images in the target have equal composite to `V`, hence
   factor through the target overlap. The matching condition gives equality.
5. Two choices of lifts have a common refinement by source fibre products;
   the same overlap argument and separatedness show that the glued section
   is independent of the choice.
6. Pulling these lifted covers back along `B ⟶ A` proves compatibility of the
   glued coordinates. Identity covers show that the resulting family restricts
   to the prescribed matching families. This proves that `R F` is a sheaf.
7. Transpose `α : L G ⟶ F` by sending `t` to the family `α_A(G(ψ)(t))`.
   The inverse evaluates at `(A, id)`. Naturality and compatibility prove that
   these are inverse, bifunctorial hom-set bijections (00XH).
8. Transpose identities to obtain the displayed unit and counit. Evaluating
   at identity arrows proves one triangle; substitution of indices followed
   by evaluation proves the other.
9. Limits of sheaves of sets are sectionwise, by
   lem-weil-pbc-site-sheaf-sets-limits-sectionwise. Precomposition therefore
   preserves finite limits, including the terminal object.
10. These functors give the morphism of topoi associated to cocontinuity (00XO).
    Its usual sheafified inverse image is canonically `L`: the universal
    property in def-weil-pbc-sheafification makes sheafification of an already
    sheaf presheaf canonically the identity, compatibly with unit and counit. -/
theorem continuousCocontinuous_toposAdjunctionForCoverings
    {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    (hJ : J.IsSiteForCoverings) (hK : K.IsSiteForCoverings)
    (f : C ⥤ D)
    (hcover : ∀ (X : C) (S : Presieve X), S ∈ J X → S.map f ∈ K (f.obj X))
    (hpullback : ∀ (X Y Z : C) (S : Presieve X), S ∈ J X →
      ∀ (a : Y ⟶ X) (b : Z ⟶ X), S a → PreservesLimit (cospan a b) f)
    [f.IsCocontinuous J.toGrothendieck K.toGrothendieck] :
    ∃ (L : Sheaf K.toGrothendieck (Type u) ⥤ Sheaf J.toGrothendieck (Type u))
      (eL : L ⋙ sheafToPresheaf J.toGrothendieck (Type u) ≅
        sheafToPresheaf K.toGrothendieck (Type u) ⋙
          (Functor.whiskeringLeft _ _ (Type u)).obj f.op)
      (adj : L ⊣ f.sheafPushforwardCocontinuous (Type u)
        J.toGrothendieck K.toGrothendieck),
      PreservesFiniteLimits L ∧
      ∃ e : ∀ (F : Sheaf J.toGrothendieck (Type u)) (V : D),
        ((f.sheafPushforwardCocontinuous (Type u)
          J.toGrothendieck K.toGrothendieck).obj F).obj.obj (op V) ≃
          {s : ∀ (A : C), (f.obj A ⟶ V) → F.obj.obj (op A) //
            ∀ (A B : C) (a : B ⟶ A) (ψ : f.obj A ⟶ V),
              F.obj.map a.op (s A ψ) = s B (f.map a ≫ ψ)},
        (∀ (F : Sheaf J.toGrothendieck (Type u)) (V V' : D) (h : V' ⟶ V)
          (s : ((f.sheafPushforwardCocontinuous (Type u)
            J.toGrothendieck K.toGrothendieck).obj F).obj.obj (op V))
          (A : C) (ψ : f.obj A ⟶ V'),
          (e F V' (((f.sheafPushforwardCocontinuous (Type u)
            J.toGrothendieck K.toGrothendieck).obj F).obj.map h.op s)).val A ψ =
              (e F V s).val A (ψ ≫ h)) ∧
        (∀ (F F' : Sheaf J.toGrothendieck (Type u)) (α : F ⟶ F') (V : D)
          (s : ((f.sheafPushforwardCocontinuous (Type u)
            J.toGrothendieck K.toGrothendieck).obj F).obj.obj (op V))
          (A : C) (ψ : f.obj A ⟶ V),
          (e F' V (((f.sheafPushforwardCocontinuous (Type u)
            J.toGrothendieck K.toGrothendieck).map α).hom.app (op V) s)).val A ψ =
              α.hom.app (op A) ((e F V s).val A ψ)) ∧
        (∀ (F : Sheaf J.toGrothendieck (Type u)) (U : C)
          (s : ((f.sheafPushforwardCocontinuous (Type u)
            J.toGrothendieck K.toGrothendieck).obj F).obj.obj (op (f.obj U))),
          (adj.counit.app F).hom.app (op U)
            (((eL.inv.app _).app (op U)) s) = (e F (f.obj U) s).val U (𝟙 _)) ∧
        (∀ (G : Sheaf K.toGrothendieck (Type u)) (V : D) (t : G.obj.obj (op V))
          (A : C) (ψ : f.obj A ⟶ V),
          (eL.hom.app G).app (op A)
            ((e (L.obj G) V ((adj.unit.app G).hom.app (op V) t)).val A ψ) =
              G.obj.map ψ.op t) := by
  obtain ⟨_, _, _⟩ := hK
  let := continuous_of_coverings J K hJ f hcover hpullback
  refine ⟨f.sheafPushforwardContinuous (Type u) J.toGrothendieck K.toGrothendieck,
    f.sheafPushforwardContinuousCompSheafToPresheafIso _ _ _,
    f.sheafAdjunctionCocontinuous _ _ _, inferInstance, ?_⟩
  refine ⟨fun F V ↦ ranFamilyEquiv f F.obj V, ?_, ?_, ?_, ?_⟩
  · intro F V V' h s A ψ
    change (f.op.ran.obj F.obj).obj (op V) at s
    change (ranFamilyEquiv f F.obj V' ((f.op.ran.obj F.obj).map h.op s)).val A ψ =
      (ranFamilyEquiv f F.obj V s).val A (ψ ≫ h)
    rw [ranFamilyEquiv_apply, ranFamilyEquiv_apply]
    simp only [← Functor.map_comp_apply, ← op_comp]
  · intro F F' α V s A ψ
    change (f.op.ran.obj F.obj).obj (op V) at s
    change (ranFamilyEquiv f F'.obj V ((f.op.ran.map α.hom).app (op V) s)).val A ψ =
      α.hom.app (op A) ((ranFamilyEquiv f F.obj V s).val A ψ)
    rw [ranFamilyEquiv_apply, ranFamilyEquiv_apply]
    rw [← (f.op.ran.map α.hom).naturality_apply ψ.op s]
    exact congrArg (fun k ↦ k ((f.op.ran.obj F.obj).map ψ.op s))
      (congr_app (f.op.ranCounit.naturality α.hom) (op A))
  · intro F U s
    change (f.op.ran.obj F.obj).obj (op (f.obj U)) at s
    change ((f.sheafAdjunctionCocontinuous (Type u) J.toGrothendieck
      K.toGrothendieck).counit.app F).hom.app (op U) s =
        (ranFamilyEquiv f F.obj (f.obj U) s).val U (𝟙 _)
    rw [f.sheafAdjunctionCocontinuous_counit_app_hom, ranFamilyEquiv_apply]
    simp only [Functor.ranAdjunction_counit, op_id, Functor.map_id, types_id_apply]
    rfl
  · intro G V t A ψ
    change (ranFamilyEquiv f (f.op ⋙ G.obj) V
      (((f.sheafAdjunctionCocontinuous (Type u) J.toGrothendieck
        K.toGrothendieck).unit.app G).hom.app (op V) t)).val A ψ = G.obj.map ψ.op t
    rw [f.sheafAdjunctionCocontinuous_unit_app_hom, ranFamilyEquiv_apply]
    erw [← ((f.op.ranAdjunction (Type u)).unit.app G.obj).naturality_apply ψ.op t]
    exact congrArg (fun k ↦ k (G.obj.map ψ.op t))
      (f.op.ranCounit_app_app_ranAdjunction_unit_app_app G.obj (op A))

end CategoryTheory

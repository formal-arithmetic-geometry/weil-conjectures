/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Lifting an equivalence of set sheaves to complete category-valued sheaves

Source: Stacks Project, Sites, Tag 00VR (`definition-sheaf`) and the preceding Hom-test
discussion; the equivalence assertion is the agent generalization proved by small pointwise
right Kan extension in the DAG, rather than a theorem of Tag 00VR
(blueprint: lem-trf-complete-valued-sheaf-equivalence-lift).
-/

@[expose] public section

set_option autoImplicit false

universe v w

open CategoryTheory.Limits

namespace CategoryTheory.Functor

open Opposite

section SetComparison

variable {C D : Type v} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [K.Subcanonical] (U : C ⥤ D) [U.IsContinuous J K]
    [(U.sheafPushforwardContinuous (Type v) J K).IsEquivalence]

include J in
private theorem set_unit_isIso (G : Sheaf K (Type v)) :
    IsIso ((U.op.ranAdjunction (Type v)).unit.app G.obj) := by
  classical
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  rw [isIso_iff_bijective]
  let R := U.sheafPushforwardContinuous (Type v) J K
  let h := U.op.ranAdjunction (Type v)
  let e₁ : (yoneda.obj X.unop ⟶ G.obj) ≃
      (U.op ⋙ yoneda.obj X.unop ⟶ U.op ⋙ G.obj) :=
    (Sheaf.homEquiv (X := K.yoneda.obj X.unop) (Y := G)).symm.trans
      ((FullyFaithful.ofFullyFaithful R).homEquiv.trans Sheaf.homEquiv)
  let e₂ := (h.homEquiv (yoneda.obj X.unop) (U.op ⋙ G.obj))
  let e : G.obj.obj X ≃ (U.op.ran.obj (U.op ⋙ G.obj)).obj X :=
    yonedaEquiv.symm.trans (e₁.trans (e₂.trans yonedaEquiv))
  change Function.Bijective (fun x ↦ ((h.unit.app G.obj).app X) x)
  rw [show (fun x ↦ ((h.unit.app G.obj).app X) x) = e from by
    funext x
    change ((h.unit.app G.obj).app X) x =
      yonedaEquiv (h.homEquiv _ _ (whiskerLeft U.op (yonedaEquiv.symm x)))
    rw [Adjunction.homEquiv_apply]
    have hn := h.unit.naturality (yonedaEquiv.symm x)
    change yonedaEquiv.symm x ≫ h.unit.app G.obj =
      h.unit.app (yoneda.obj X.unop) ≫
        U.op.ran.map (whiskerLeft U.op (yonedaEquiv.symm x)) at hn
    rw [← hn, yonedaEquiv_comp]
    congr 1
    exact yonedaEquiv.apply_symm_apply x |>.symm]
  exact e.bijective


include J K in
private theorem set_ran_isSheaf (F : Sheaf J (Type v)) :
    Presheaf.IsSheaf K (U.op.ran.obj F.obj) := by
  classical
  let R := U.sheafPushforwardContinuous (Type v) J K
  let G := R.objPreimage F
  let e : U.op ⋙ G.obj ≅ F.obj :=
    (sheafToPresheaf J (Type v)).mapIso (R.objObjPreimageIso F)
  have : IsIso ((U.op.ranAdjunction (Type v)).unit.app G.obj) :=
    set_unit_isIso J K U G
  exact (Presheaf.isSheaf_of_iso_iff
    (asIso ((U.op.ranAdjunction (Type v)).unit.app G.obj) ≪≫ U.op.ran.mapIso e)).mp G.property

include J K in
private theorem set_counit_isIso (F : Sheaf J (Type v)) :
    IsIso ((U.op.ranAdjunction (Type v)).counit.app F.obj) := by
  classical
  let R := U.sheafPushforwardContinuous (Type v) J K
  let G := R.objPreimage F
  let e : U.op ⋙ G.obj ≅ F.obj :=
    (sheafToPresheaf J (Type v)).mapIso (R.objObjPreimageIso F)
  let h := U.op.ranAdjunction (Type v)
  have : IsIso (h.unit.app G.obj) := set_unit_isIso J K U G
  have : IsIso (h.counit.app (U.op ⋙ G.obj)) :=
    isIso_of_hom_comp_eq_id _ (h.left_triangle_components G.obj)
  exact (NatTrans.isIso_app_iff_of_iso h.counit e).mp inferInstance

end SetComparison

section Coefficients

variable {C D : Type v} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [K.Subcanonical] (U : C ⥤ D) [U.IsContinuous J K]
    [(U.sheafPushforwardContinuous (Type v) J K).IsEquivalence]
    (A : Type w) [Category.{v} A] [HasLimitsOfSize.{v, v} A]

include J in
private theorem coefficient_ran_isSheaf (F : Sheaf J A) :
    Presheaf.IsSheaf K (U.op.ran.obj F.obj) := by
  intro a
  rw [← isSheaf_iff_isSheaf_of_type]
  let H := coyoneda.obj (op a)
  let e := H.rightKanExtensionCompIsoOfPreserves F.obj U.op
  apply (Presheaf.isSheaf_of_iso_iff e).mpr
  exact set_ran_isSheaf J K U (sheafOver F a)

include J K in
private theorem coefficient_counit_isIso (F : Sheaf J A) :
    IsIso ((U.op.ranAdjunction A).counit.app F.obj) := by
  rw [ranAdjunction_counit, NatTrans.isIso_iff_isIso_app]
  intro X
  apply isIso_of_yoneda_map_bijective
  intro a
  let H := coyoneda.obj (op a)
  have : IsIso ((U.op.ranAdjunction (Type v)).counit.app (F.obj ⋙ H)) :=
    set_counit_isIso J K U (sheafOver F a)
  have hs' : IsIso ((U.op.rightKanExtensionCounit (F.obj ⋙ H)).app X) := by
    change IsIso (((U.op.ranAdjunction (Type v)).counit.app (F.obj ⋙ H)).app X)
    infer_instance
  have he := H.rightKanExtensionCompIsoOfPreserves_hom_fac_app F.obj U.op X
  have : IsIso (H.map ((U.op.rightKanExtensionCounit F.obj).app X)) := by
    rw [← he]
    infer_instance
  exact (isIso_iff_bijective (H.map ((U.op.rightKanExtensionCounit F.obj).app X))).mp this

include J K in
omit [K.Subcanonical] [HasLimitsOfSize.{v, v} A] in
private theorem coefficient_reflectsIsomorphisms :
    (U.sheafPushforwardContinuous A J K).ReflectsIsomorphisms := by
  constructor
  intro F G f hf
  have hpres : IsIso ((sheafToPresheaf K A).map f) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    apply isIso_of_yoneda_map_bijective
    intro a
    let H := coyoneda.obj (op a)
    let t := (sheafCompose K H).map f
    have ht : IsIso ((U.sheafPushforwardContinuous (Type v) J K).map t) := by
      have : IsIso (whiskerLeft U.op f.hom) :=
        (sheafToPresheaf J A).map_isIso
          ((U.sheafPushforwardContinuous A J K).map f)
      have : IsIso ((sheafToPresheaf J (Type v)).map
          ((U.sheafPushforwardContinuous (Type v) J K).map t)) := by
        change IsIso (whiskerRight (whiskerLeft U.op f.hom) H)
        exact ((whiskeringRight Cᵒᵖ A (Type v)).obj H).map_isIso _
      exact isIso_of_reflects_iso _ (sheafToPresheaf J (Type v))
    have ht' : IsIso t :=
      isIso_of_reflects_iso t (U.sheafPushforwardContinuous (Type v) J K)
    have hcomp : IsIso (whiskerRight f.hom H) :=
      (sheafToPresheaf K (Type v)).map_isIso t
    have hx : IsIso (H.map (f.hom.app X)) :=
      inferInstanceAs (IsIso ((whiskerRight f.hom H).app X))
    exact (isIso_iff_bijective _).mp hx
  let := hpres
  exact isIso_of_reflects_iso f (sheafToPresheaf K A)

end Coefficients

/-- Restriction along a finite-limit- and cover-preserving functor of small subcanonical sites
is an equivalence for sheaves valued in any complete locally small category if it is an
equivalence for sheaves of sets. Here `Presheaf.IsSheaf` is precisely the Hom-test definition.

Source: Stacks Project, Sites, Tag 00VR (`definition-sheaf`) and the preceding Hom-test;
agent generalization by the following small pointwise right Kan argument
(blueprint: lem-trf-complete-valued-sheaf-equivalence-lift).

Proof:
1. Put `L = U.op`. For `d` in `D`, the category `(d ↓ L)` in `Dᵒᵖ` is
   `(U ↓ d)ᵒᵖ`, with pairs `(c, α : U(c) ⟶ d)`. Both its objects and its arrows are
   `v`-small. The lemma `lem-trf-small-pointwise-right-kan-adjunction`
   (`Functor.ranAdjunction` and `Functor.ranObjObjIsoLimit`) constructs the pointwise right
   Kan functors `T_A`, `T_set` and adjunctions `P ⊣ T`, with
   `T(F)(d) = lim_(c,α) F(c)`. Only these small comma-category limits are used.
2. Choose a quasi-inverse `E` of restriction on set sheaves. For a set sheaf `F` on `C`,
   subcanonicity and Yoneda (`lem-galois-yoneda-hom-bijection`, `yonedaEquiv`) identify
   `E(F)(d)` with `Nat(h_d, E(F))`, then full faithfulness and `R_set E(F) ≅ F` identify
   this with `Nat(R_set h_d, F)`. Such a transformation is a family `x_(c,α)` in `F(c)`
   satisfying `F(g)(x_(c,α)) = x_(c', U(g) ≫ α)` for `g : c' ⟶ c`, using Lean
   composition order.
   These are exactly the compatible families for the limit in step 1, including an empty
   comma category. Reindexing `α` and applying maps of `F` makes the identification natural
   in both arguments. Thus `E(F) ≅ T_set(F)`, so `T_set(F)` is a sheaf.
3. Restriction preserves `A`-sheaves because each Hom-test is the restriction of a set
   sheaf. Conversely, `lem-trf-hom-right-kan-comparison`
   (`Functor.ranCompIsoOfPreserves`, using `coyoneda_preservesLimits`) identifies
   `Hom(a, T_A(F)(-))` with `T_set(Hom(a, F(-)))`. Step 2 and the Hom-test show that
   `T_A(F)` is a sheaf. Both presheaf adjunctions therefore restrict to sheaves with the
   same units and counits.
4. The set-valued unit is invertible by the Yoneda bijections in step 2. The triangle
   identity gives an invertible counit on restrictions; essential surjectivity transports
   this to every set sheaf on `C`. The counit equation in
   `lem-trf-hom-right-kan-comparison` identifies its `A`-valued counterpart after applying
   `Hom(a,-)` with the composite of this set counit and the Hom/Kan comparison. Both are
   bijections. The criterion `lem-coef-joyal-homset-iso-detection`
   (`isIso_of_yoneda_map_bijective`) makes each component of the `A`-counit invertible;
   the inverses form a natural inverse.
5. Restriction on `A`-sheaves reflects isomorphisms: for every `a`, restriction of the
   Hom-test of a morphism is the Hom-test of its restriction. The set equivalence reflects
   isomorphisms, so the original Hom-test is invertible. Hom-detection objectwise makes
   the original morphism invertible.
6. The triangle identity says that the restricted unit is inverse to the invertible
   counit. Step 5 makes the unit itself invertible. The unit and counit thus exhibit
   `T_A` as a quasi-inverse of the actual restriction functor in the conclusion. -/
theorem isEquivalence_sheafPushforwardContinuous_of_types
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    [HasFiniteLimits C] [HasFiniteLimits D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [J.Subcanonical] [K.Subcanonical]
    (U : C ⥤ D) [PreservesFiniteLimits U] (hU : CoverPreserving J K U)
    (A : Type w) [Category.{v} A] [HasLimitsOfSize.{v, v} A]
    (hset : (@Functor.sheafPushforwardContinuous C _ D _ U (Type v) _ J K
      ((@Functor.isContinuous_iff_coverPreserving C _ D _ U J K
        (flat_of_preservesFiniteLimits U)).mpr hU)).IsEquivalence) :
    (@Functor.sheafPushforwardContinuous C _ D _ U A _ J K
      ((@Functor.isContinuous_iff_coverPreserving C _ D _ U J K
        (flat_of_preservesFiniteLimits U)).mpr hU)).IsEquivalence := by
  classical
  let : U.IsContinuous J K :=
    (@Functor.isContinuous_iff_coverPreserving C _ D _ U J K
      (flat_of_preservesFiniteLimits U)).mpr hU
  let : (U.sheafPushforwardContinuous (Type v) J K).IsEquivalence := hset
  let R := U.sheafPushforwardContinuous A J K
  let T : Sheaf J A ⥤ Sheaf K A := ObjectProperty.lift _
    (sheafToPresheaf J A ⋙ U.op.ran) (coefficient_ran_isSheaf J K U A)
  let e0 : sheafToPresheaf J A ⋙ U.op.ran ≅ T ⋙ sheafToPresheaf K A := Iso.refl _
  let adj : R ⊣ T := (U.op.ranAdjunction A).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
    (U.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm e0
  have hc (F : Sheaf J A) : IsIso (adj.counit.app F) := by
    have hpres : IsIso ((sheafToPresheaf J A).map (adj.counit.app F)) := by
      have he := (U.op.ranAdjunction A).map_restrictFullyFaithful_counit_app
        (fullyFaithfulSheafToPresheaf K A) (fullyFaithfulSheafToPresheaf J A)
        (U.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm
        e0 F
      change IsIso ((sheafToPresheaf J A).map (adj.counit.app F))
      rw [he]
      have h1 : IsIso ((U.sheafPushforwardContinuousCompSheafToPresheafIso A J K).symm.inv.app
          (T.obj F)) := by infer_instance
      have h2 : IsIso (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj U.op).map
          (e0.inv.app F)) := by
        apply Functor.map_isIso
      have h3 : IsIso ((U.op.ranAdjunction A).counit.app
          ((sheafToPresheaf J A).obj F)) := by
        exact coefficient_counit_isIso J K U A F
      infer_instance
    let := hpres
    exact isIso_of_reflects_iso _ (sheafToPresheaf J A)
  have : IsIso adj.counit := NatIso.isIso_of_isIso_app _
  have : R.ReflectsIsomorphisms := coefficient_reflectsIsomorphisms J K U A
  have hu (F : Sheaf K A) : IsIso (adj.unit.app F) := by
    have hmap : IsIso (R.map (adj.unit.app F)) := by
      exact isIso_of_comp_hom_eq_id _ (adj.left_triangle_components F)
    let := hmap
    exact isIso_of_reflects_iso _ R
  have : IsIso adj.unit := NatIso.isIso_of_isIso_app _
  exact adj.toEquivalence.isEquivalence_functor

end CategoryTheory.Functor

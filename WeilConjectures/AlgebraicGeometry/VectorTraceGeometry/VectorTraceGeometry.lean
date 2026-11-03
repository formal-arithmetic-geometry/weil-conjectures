/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityDirectSum
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.AlgebraicGeometry.AffineAlgebraLocalMaps
import WeilConjectures.CategoryTheory.CommAlgebraSheafModule

/-! # Canonical maps of symmetric-algebra vector bundles

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: def-pur-vector-trace-geometry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
namespace VectorTraceGeometry

/-- Binary biproducts induced by the existing finite module biproducts.
Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry). -/
instance moduleBinaryBiproducts (S : Scheme.{u}) : HasBinaryBiproducts S.Modules :=
  hasBinaryBiproducts_of_finite_biproducts S.Modules

/-- The usual module direct sum, with the base category fixed before elaborating either summand.
Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry). -/
abbrev sum (S : Scheme.{u}) (F G : S.Modules) : S.Modules := F ⊞ G

/-- The degree-one function on the symmetric-algebra total space.
Source: blueprint paragraph 2, symmetric-algebra coordinates
(blueprint: def-pur-vector-trace-geometry). -/
def generator (S : Scheme.{u}) [IsNoetherian S] (r : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] (U : S.Opens) (x : F.val.obj (op U)) :
    Γ(VectorBundleZeroSection.scheme S r F, (VectorBundleZeroSection.π S r F) ⁻¹ᵁ U) :=
  (VectorBundleZeroSection.algebraIso S r F).hom.right.hom.app (op U)
    ((SymmetricAlgebraSheaf.inclusion F).val.app (op U) x)

/-- A map of total spaces is the relative-Spec map of the given linear map precisely
when it has the indicated effect on every degree-one section. This fixes its data.
Source: blueprint paragraph 2, symmetric-algebra universal property
(blueprint: def-pur-vector-trace-geometry). -/
structure MapSpec {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (r s : ℕ) (F : S.Modules) (G : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (a : F ⟶ (Scheme.Modules.pushforward f).obj G)
    (v : VectorBundleZeroSection.scheme T s G ⟶ VectorBundleZeroSection.scheme S r F) :
    Prop where
  /-- The structural square commutes.
  Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry). -/
  comm : v ≫ VectorBundleZeroSection.π S r F = VectorBundleZeroSection.π T s G ≫ f
  /-- Pullback takes each generator to the generator of its prescribed linear image.
  Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry). -/
  generators : ∀ (U : S.Opens) (x : F.val.obj (op U)),
    v.appLE ((VectorBundleZeroSection.π S r F) ⁻¹ᵁ U)
        ((VectorBundleZeroSection.π T s G) ⁻¹ᵁ (f ⁻¹ᵁ U))
        (by rw [← Scheme.Hom.comp_preimage, ← comm, Scheme.Hom.comp_preimage])
        (generator S r F U x) =
      generator T s G (f ⁻¹ᵁ U) (a.val.app (op U) x)

private abbrev structureAlgebra {S X : Scheme.{u}} (f : X ⟶ S) : S.CommAlgebraSheaf :=
  Under.mk (⟨f.c⟩ : S.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj X.sheaf)

private theorem affine_over_ext {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [IsAffineHom g] (h h' : X ⟶ Y) (w : h ≫ g = f) (w' : h' ≫ g = f)
    (he : ∀ U : S.affineOpens,
      h.appLE (g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
        (by rw [← w, Scheme.Hom.comp_preimage]) =
      h'.appLE (g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
        (by rw [← w', Scheme.Hom.comp_preimage])) : h = h' := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (show f x ∈ (⊤ : S.Opens) from trivial) isOpen_univ
  refine ⟨f ⁻¹ᵁ U, hxU, ?_⟩
  have : IsAffine (g ⁻¹ᵁ U).toScheme := hU.preimage g
  have hh : h.resLE (g ⁻¹ᵁ U) (f ⁻¹ᵁ U)
      (by rw [← w, Scheme.Hom.comp_preimage]) =
    h'.resLE (g ⁻¹ᵁ U) (f ⁻¹ᵁ U)
      (by rw [← w', Scheme.Hom.comp_preimage]) := by
    apply ext_of_isAffine
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    rw [he ⟨U, hU⟩]
  simpa only [Scheme.Hom.resLE_comp_ι] using congrArg (· ≫ (g ⁻¹ᵁ U).ι) hh

private theorem exists_over_map_of_algebra {S X Y : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) [IsAffineHom g] (α : structureAlgebra g ⟶ structureAlgebra f) :
    ∃ (h : X ⟶ Y) (w : h ≫ g = f), ∀ U : S.Opens,
      h.appLE (g ⁻¹ᵁ U) (f ⁻¹ᵁ U)
        (by rw [← w, Scheme.Hom.comp_preimage]) = α.right.hom.app (op U) := by
  obtain ⟨k, hw, hc, ha⟩ := affine_algebra_local_maps f g α
  let 𝒰 := X.openCoverOfIsOpenCover (fun U : S.affineOpens ↦ f ⁻¹ᵁ U.1)
    (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top S))
  let h : X ⟶ Y := 𝒰.glueMorphisms k hc
  have hi (U : S.affineOpens) : (f ⁻¹ᵁ U.1).ι ≫ h = k U :=
    𝒰.ι_glueMorphisms k hc U
  have w : h ≫ g = f := by
    apply 𝒰.hom_ext
    intro U
    change (f ⁻¹ᵁ U.1).ι ≫ h ≫ g = (f ⁻¹ᵁ U.1).ι ≫ f
    rw [← Category.assoc, hi, hw]
  have haff (U : S.affineOpens) :
      h.appLE (g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
        (by rw [← w, Scheme.Hom.comp_preimage]) = α.right.hom.app (op U.1) := by
    have e : ⊤ ≤ k U ⁻¹ᵁ (g ⁻¹ᵁ U.1) := by
      rw [← Scheme.Hom.comp_preimage, hw, Scheme.Hom.comp_preimage]
      simp
    have ea := ha U e
    simp only [← hi U] at ea
    rw [Scheme.Hom.comp_appLE] at ea
    simp only [Scheme.Opens.ι_appLE] at ea
    apply (cancel_mono (f ⁻¹ᵁ U.1).topIso.inv).mp
    simp only [Scheme.Hom.appLE, Scheme.Opens.topIso_inv, Category.assoc,
      ← Functor.map_comp] at ea ⊢
    convert ea using 1
    congr 1
  let β : structureAlgebra g ⟶ structureAlgebra f := Under.homMk ⟨{
    app := fun V ↦ h.appLE (g ⁻¹ᵁ V.unop) (f ⁻¹ᵁ V.unop)
      (by rw [← w, Scheme.Hom.comp_preimage])
    naturality := by
      intros
      change Y.presheaf.map _ ≫ _ = _ ≫ X.presheaf.map _
      simp only [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map] }⟩ (by
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext V
        change g.app V.unop ≫ h.appLE _ _ _ = f.app V.unop
        rw [← Scheme.Hom.comp_appLE]
        rw [Scheme.Hom.appLE_congr_hom w _ _ _ le_rfl]
        simp only [Scheme.Hom.appLE_eq_app])
  have hβα : β = α := by
    apply Under.UnderMorphism.ext
    apply Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext _ _ (B := fun U : S.affineOpens ↦ U.1)
      (by simpa only [Subtype.range_coe] using S.isBasis_affineOpens)
    exact haff
  refine ⟨h, w, fun U ↦ ?_⟩
  exact congrArg (fun t ↦ t.right.hom.app (op U)) hβα

private def algebraModuleMap {S : Scheme.{u}} {A B : S.CommAlgebraSheaf}
    (a : A ⟶ B) : (A.toModule : S.Modules) ⟶ (B.toModule : S.Modules) :=
  (commAlgebraSheafModuleFunctor S.sheaf).map a

private def bundleGenerator (S : Scheme.{u}) [IsNoetherian S] (r : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] :
    F ⟶ (Scheme.Modules.pushforward (VectorBundleZeroSection.π S r F)).obj
      (SheafOfModules.unit (VectorBundleZeroSection.scheme S r F).ringCatSheaf) :=
  SymmetricAlgebraSheaf.inclusion F ≫
    algebraModuleMap (VectorBundleZeroSection.algebraIso S r F).hom

private theorem bundle_map_existsUnique {S X : Scheme.{u}} [IsNoetherian S]
    (r : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r] (ρ : X ⟶ S)
    (a : F ⟶ (Scheme.Modules.pushforward ρ).obj (SheafOfModules.unit X.ringCatSheaf)) :
    ∃! v : X ⟶ VectorBundleZeroSection.scheme S r F,
      ∃ w : v ≫ VectorBundleZeroSection.π S r F = ρ,
        ∀ (U : S.Opens) (x : F.val.obj (op U)),
          v.appLE ((VectorBundleZeroSection.π S r F) ⁻¹ᵁ U) (ρ ⁻¹ᵁ U)
            (by rw [← w, Scheme.Hom.comp_preimage]) (generator S r F U x) =
              a.val.app (op U) x := by
  let B := structureAlgebra ρ
  obtain ⟨t, ht, huniq⟩ := exists_quasiCoherentSymmetricAlgebra_core S F B a
  have : IsAffineHom (VectorBundleZeroSection.π S r F) :=
    (VectorBundleZeroSection.over S r F).property
  obtain ⟨v, hv, hs⟩ := exists_over_map_of_algebra ρ (VectorBundleZeroSection.π S r F)
    ((VectorBundleZeroSection.algebraIso S r F).inv ≫ t)
  have hvgen (U : S.Opens) (x : F.val.obj (op U)) :
      v.appLE ((VectorBundleZeroSection.π S r F) ⁻¹ᵁ U) (ρ ⁻¹ᵁ U)
        (by rw [← hv, Scheme.Hom.comp_preimage]) (generator S r F U x) =
          a.val.app (op U) x := by
    rw [hs]
    change t.right.hom.app (op U)
      ((VectorBundleZeroSection.algebraIso S r F).inv.right.hom.app (op U)
        ((VectorBundleZeroSection.algebraIso S r F).hom.right.hom.app (op U) _)) = _
    have he := congrArg (fun q ↦ q.right.hom.app (op U)
      ((SymmetricAlgebraSheaf.inclusion F).val.app (op U) x))
      (VectorBundleZeroSection.algebraIso S r F).hom_inv_id
    exact (congrArg (t.right.hom.app (op U)) he).trans (ht U x)
  refine ⟨v, ⟨hv, hvgen⟩, ?_⟩
  rintro z ⟨hz, hzgen⟩
  let β : structureAlgebra (VectorBundleZeroSection.π S r F) ⟶ B :=
    Under.homMk ⟨{
      app := fun U ↦ z.appLE ((VectorBundleZeroSection.π S r F) ⁻¹ᵁ U.unop)
        (ρ ⁻¹ᵁ U.unop) (by rw [← hz, Scheme.Hom.comp_preimage])
      naturality := by
        intros
        change (VectorBundleZeroSection.scheme S r F).presheaf.map _ ≫ _ =
          _ ≫ X.presheaf.map _
        simp only [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map] }⟩ (by
          apply Sheaf.hom_ext
          apply NatTrans.ext
          funext U
          change (VectorBundleZeroSection.π S r F).app U.unop ≫ z.appLE _ _ _ = _
          rw [← Scheme.Hom.comp_appLE]
          rw [Scheme.Hom.appLE_congr_hom hz _ _ _ le_rfl,
            Scheme.Hom.appLE_eq_app]
          rfl)
  have hβ : (VectorBundleZeroSection.algebraIso S r F).hom ≫ β = t :=
    huniq _ hzgen
  apply affine_over_ext ρ (VectorBundleZeroSection.π S r F) z v hz hv
  intro U
  rw [hs]
  have hβ' : β = (VectorBundleZeroSection.algebraIso S r F).inv ≫ t := by
    rw [← hβ, Iso.inv_hom_id_assoc]
  exact congrArg (fun q ↦ q.right.hom.app (op U.1)) hβ'

private def bundleLinear {S X : Scheme.{u}} [IsNoetherian S]
    (r : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r] (ρ : X ⟶ S)
    (v : X ⟶ VectorBundleZeroSection.scheme S r F)
    (w : v ≫ VectorBundleZeroSection.π S r F = ρ) :
    F ⟶ (Scheme.Modules.pushforward ρ).obj (SheafOfModules.unit X.ringCatSheaf) := by
  let β : structureAlgebra (VectorBundleZeroSection.π S r F) ⟶ structureAlgebra ρ :=
    Under.homMk ⟨{
      app := fun U ↦ v.appLE ((VectorBundleZeroSection.π S r F) ⁻¹ᵁ U.unop)
        (ρ ⁻¹ᵁ U.unop) (by rw [← w, Scheme.Hom.comp_preimage])
      naturality := by
        intros
        change (VectorBundleZeroSection.scheme S r F).presheaf.map _ ≫ _ =
          _ ≫ X.presheaf.map _
        simp only [Scheme.Hom.map_appLE, Scheme.Hom.appLE_map] }⟩ (by
          apply Sheaf.hom_ext
          apply NatTrans.ext
          funext U
          change (VectorBundleZeroSection.π S r F).app U.unop ≫ v.appLE _ _ _ = _
          rw [← Scheme.Hom.comp_appLE,
            Scheme.Hom.appLE_congr_hom w _ _ _ le_rfl,
            Scheme.Hom.appLE_eq_app]
          rfl)
  exact bundleGenerator S r F ≫ algebraModuleMap β

private theorem bundleLinear_congr {S X : Scheme.{u}} [IsNoetherian S]
    (r : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r] (ρ : X ⟶ S)
    (v z : X ⟶ VectorBundleZeroSection.scheme S r F)
    (hv : v ≫ VectorBundleZeroSection.π S r F = ρ)
    (hz : z ≫ VectorBundleZeroSection.π S r F = ρ) (h : v = z) :
    bundleLinear r F ρ v hv = bundleLinear r F ρ z hz := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change v.appLE _ _ _ (generator S r F U x) =
    z.appLE _ _ _ (generator S r F U x)
  exact congrArg (fun t : Γ(VectorBundleZeroSection.scheme S r F,
      (VectorBundleZeroSection.π S r F) ⁻¹ᵁ U) ⟶ Γ(X, ρ ⁻¹ᵁ U) ↦
        t (generator S r F U x))
    (Scheme.Hom.appLE_congr_hom h _ _ _ _)

private theorem bundle_hom_ext {S X : Scheme.{u}} [IsNoetherian S]
    (r : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r] (ρ : X ⟶ S)
    (v z : X ⟶ VectorBundleZeroSection.scheme S r F)
    (hv : v ≫ VectorBundleZeroSection.π S r F = ρ)
    (hz : z ≫ VectorBundleZeroSection.π S r F = ρ)
    (h : bundleLinear r F ρ v hv = bundleLinear r F ρ z hz) : v = z := by
  have H := bundle_map_existsUnique r F ρ (bundleLinear r F ρ z hz)
  apply H.unique
  · refine ⟨hv, fun U x ↦ ?_⟩
    exact congrArg (fun a ↦ a.val.app (op U) x) h
  · exact ⟨hz, fun _ _ ↦ rfl⟩

private def bundleLift {S X : Scheme.{u}} [IsNoetherian S]
    (r : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r] (ρ : X ⟶ S)
    (a : F ⟶ (Scheme.Modules.pushforward ρ).obj (SheafOfModules.unit X.ringCatSheaf)) :
    X ⟶ VectorBundleZeroSection.scheme S r F :=
  (bundle_map_existsUnique r F ρ a).exists.choose

private theorem bundleLift_comm {S X : Scheme.{u}} [IsNoetherian S]
    (r : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r] (ρ : X ⟶ S)
    (a : F ⟶ (Scheme.Modules.pushforward ρ).obj (SheafOfModules.unit X.ringCatSheaf)) :
    bundleLift r F ρ a ≫ VectorBundleZeroSection.π S r F = ρ :=
  (bundle_map_existsUnique r F ρ a).exists.choose_spec.choose

private theorem bundleLift_linear {S X : Scheme.{u}} [IsNoetherian S]
    (r : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r] (ρ : X ⟶ S)
    (a : F ⟶ (Scheme.Modules.pushforward ρ).obj (SheafOfModules.unit X.ringCatSheaf)) :
    bundleLinear r F ρ (bundleLift r F ρ a) (bundleLift_comm r F ρ a) = a := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  exact (bundle_map_existsUnique r F ρ a).exists.choose_spec.choose_spec U x

attribute [irreducible] bundleLift

/-- The generator prescription determines a unique scheme map, rather than a choice
from a nonempty family of maps.
Source: blueprint paragraph 2, relative Spec and symmetric algebras
(blueprint: def-pur-vector-trace-geometry).
Proof: adjunction turns a into a linear map on the new base. Extend uniquely by the
symmetric-algebra universal property. Relative Spec and its fully faithful algebra
comparison produce v. On each affine open its pullback on generators is the displayed
formula; these formulas glue. Uniqueness follows from generation by scalars and degree one.
-/
theorem existsUnique_map {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (r s : ℕ) (F : S.Modules) (G : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (a : F ⟶ (Scheme.Modules.pushforward f).obj G) :
    ∃! v : VectorBundleZeroSection.scheme T s G ⟶ VectorBundleZeroSection.scheme S r F,
      MapSpec f r s F G a v := by
  let ρ := VectorBundleZeroSection.π T s G
  let b := a ≫ (Scheme.Modules.pushforward f).map (bundleGenerator T s G) ≫
    (Scheme.Modules.pushforwardComp ρ f).hom.app _
  obtain ⟨v, ⟨hv, hs⟩, hu⟩ := bundle_map_existsUnique r F (ρ ≫ f) b
  refine ⟨v, ⟨hv, ?_⟩, ?_⟩
  · intro U x
    have he := hs U x
    change v.appLE _ _ _ _ = generator T s G (f ⁻¹ᵁ U) (a.val.app (op U) x) at he
    exact he
  · intro z hz
    apply hu z
    refine ⟨hz.comm, fun U x ↦ ?_⟩
    change z.appLE _ _ _ _ = generator T s G (f ⁻¹ᵁ U) (a.val.app (op U) x)
    exact hz.generators U x

/-- The canonical contravariant linear map of symmetric-algebra bundles.
Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry). -/
def map {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (r s : ℕ) (F : S.Modules) (G : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (a : F ⟶ (Scheme.Modules.pushforward f).obj G) :
    VectorBundleZeroSection.scheme T s G ⟶ VectorBundleZeroSection.scheme S r F :=
  (existsUnique_map f r s F G a).exists.choose

/-- The unique-extension definition satisfies both the structural and generator equations.
Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry).
Proof: take the specification of the unique extension in existsUnique_map. -/
theorem map_spec {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (r s : ℕ) (F : S.Modules) (G : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (a : F ⟶ (Scheme.Modules.pushforward f).obj G) :
    MapSpec f r s F G a (map f r s F G a) := by
  exact (existsUnique_map f r s F G a).exists.choose_spec

private theorem bundleLinear_comp {S T X : Scheme.{u}}
    [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (r s : ℕ) (F : S.Modules) (G : T.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s]
    (a : F ⟶ (Scheme.Modules.pushforward f).obj G)
    (v : VectorBundleZeroSection.scheme T s G ⟶ VectorBundleZeroSection.scheme S r F)
    (hv : MapSpec f r s F G a v) (ρ : X ⟶ T)
    (ℓ : X ⟶ VectorBundleZeroSection.scheme T s G)
    (hℓ : ℓ ≫ VectorBundleZeroSection.π T s G = ρ) :
    bundleLinear r F (ρ ≫ f) (ℓ ≫ v)
        (by rw [Category.assoc, hv.comm, ← Category.assoc, hℓ]) =
      a ≫ (Scheme.Modules.pushforward f).map (bundleLinear s G ρ ℓ hℓ) ≫
        (Scheme.Modules.pushforwardComp ρ f).hom.app _ := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (ℓ ≫ v).appLE _ _ _ (generator S r F U x) = _
  change _ = ℓ.appLE ((VectorBundleZeroSection.π T s G) ⁻¹ᵁ (f ⁻¹ᵁ U))
    (ρ ⁻¹ᵁ (f ⁻¹ᵁ U)) (by rw [← hℓ, Scheme.Hom.comp_preimage])
      (generator T s G (f ⁻¹ᵁ U) (a.val.app (op U) x))
  rw [← hv.generators U x, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  simp only [Scheme.Hom.comp_preimage]

/-- Transport the existing rank theorem through the canonical uniqueness of left adjoints.
Source: blueprint paragraph 2, pulled-back frames
(blueprint: def-pur-vector-trace-geometry). -/
instance tensorPullbackRank {S T : Scheme.{u}} (f : T ⟶ S) (r : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] :
    ((Scheme.Modules.tensorPullback f).obj F).IsFiniteLocallyFreeOfRank r :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f)).app F).symm

/-- The base-change map sends each generator to its image under the module pullback unit.
Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry). -/
def baseChange {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (r : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r] :
    VectorBundleZeroSection.scheme T r ((Scheme.Modules.tensorPullback f).obj F) ⟶
      VectorBundleZeroSection.scheme S r F :=
  map f r r F _ ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app F)

private theorem baseChange_lift_exists {S T X : Scheme.{u}}
    [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (r : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r]
    (v : X ⟶ VectorBundleZeroSection.scheme S r F) (ρ : X ⟶ T)
    (w : v ≫ VectorBundleZeroSection.π S r F = ρ ≫ f) :
    ∃! ℓ : X ⟶ VectorBundleZeroSection.scheme T r ((Scheme.Modules.tensorPullback f).obj F),
      ℓ ≫ baseChange f r F = v ∧
        ℓ ≫ VectorBundleZeroSection.π T r ((Scheme.Modules.tensorPullback f).obj F) = ρ := by
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)
  let H := (Scheme.Modules.pushforward ρ).obj (SheafOfModules.unit X.ringCatSheaf)
  let c : F ⟶ (Scheme.Modules.pushforward f).obj H :=
    bundleLinear r F (ρ ≫ f) v w ≫ (Scheme.Modules.pushforwardComp ρ f).inv.app _
  let d := (adj.homEquiv F H).symm c
  let ℓ := bundleLift r ((Scheme.Modules.tensorPullback f).obj F) ρ d
  have hℓ : ℓ ≫ VectorBundleZeroSection.π T r
      ((Scheme.Modules.tensorPullback f).obj F) = ρ :=
    bundleLift_comm r ((Scheme.Modules.tensorPullback f).obj F) ρ d
  have hc' : c ≫ (Scheme.Modules.pushforwardComp ρ f).hom.app
      (SheafOfModules.unit X.ringCatSheaf) = bundleLinear r F (ρ ≫ f) v w := by
    dsimp only [c]
    rw [Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  have hc : adj.unit.app F ≫ (Scheme.Modules.pushforward f).map d = c :=
    (adj.homEquiv F H).apply_symm_apply c
  have hleft : ℓ ≫ baseChange f r F = v := by
    change ℓ ≫ map f r r F _ (adj.unit.app F) = v
    apply bundle_hom_ext r F (ρ ≫ f) _ _
      (by rw [Category.assoc, (map_spec f r r F _ (adj.unit.app F)).comm,
        ← Category.assoc, hℓ]) w
    rw [bundleLinear_comp f r r F _ (adj.unit.app F) _
      (map_spec f r r F _ (adj.unit.app F)) ρ ℓ hℓ,
      bundleLift_linear, ← Category.assoc, hc]
    exact hc'
  refine ⟨ℓ, ⟨hleft, hℓ⟩, ?_⟩
  rintro z ⟨hz, hzρ⟩
  apply bundle_hom_ext r ((Scheme.Modules.tensorPullback f).obj F) ρ z ℓ hzρ hℓ
  rw [bundleLift_linear]
  apply (adj.homEquiv F H).injective
  rw [Equiv.apply_symm_apply]
  apply (cancel_mono ((Scheme.Modules.pushforwardComp ρ f).hom.app _)).mp
  rw [Adjunction.homEquiv_unit, Category.assoc]
  have he := bundleLinear_comp f r r F _ (adj.unit.app F) _
    (map_spec f r r F _ (adj.unit.app F)) ρ z hzρ
  rw [← he]
  trans bundleLinear r F (ρ ≫ f) v w
  · exact bundleLinear_congr r F (ρ ≫ f) _ v _ w hz
  · exact hc'.symm

/-- The bundle of the pulled-back module is the geometric fibre product.
Source: blueprint proof Step 3, symmetric algebra and relative Spec base change
(blueprint: def-pur-vector-trace-geometry).
Proof: maps from either symmetric algebra to an algebra are linear maps from the
pulled-back module. The adjunction identifies these universal properties, including
their generators. Apply relative_spec_base_change and identify its canonical map by
map_spec. Thus the square is Cartesian, including rank zero and the empty scheme. -/
theorem baseChange_isPullback {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T]
    (f : T ⟶ S) (r : ℕ) (F : S.Modules) [F.IsFiniteLocallyFreeOfRank r] :
    IsPullback (baseChange f r F)
      (VectorBundleZeroSection.π T r ((Scheme.Modules.tensorPullback f).obj F))
      (VectorBundleZeroSection.π S r F) f := by
  have hw := (map_spec f r r F _
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app F)).comm
  refine ⟨⟨hw⟩, ⟨?_⟩⟩
  exact PullbackCone.IsLimit.mk hw
    (fun t ↦ (baseChange_lift_exists f r F t.fst t.snd t.condition).exists.choose)
    (fun t ↦ (baseChange_lift_exists f r F t.fst t.snd t.condition).exists.choose_spec.1)
    (fun t ↦ (baseChange_lift_exists f r F t.fst t.snd t.condition).exists.choose_spec.2)
    (fun t z h₁ h₂ ↦
      (baseChange_lift_exists f r F t.fst t.snd t.condition).unique ⟨h₁, h₂⟩
        (baseChange_lift_exists f r F t.fst t.snd t.condition).exists.choose_spec)

end VectorTraceGeometry
namespace Etale
/-- Install the proved geometric properties of the existing vector-bundle construction.
Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry). -/
instance vectorTrace_affine (S : Scheme.{u}) [IsNoetherian S] (r : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] : IsAffineHom (VectorBundleZeroSection.π S r F) :=
  (vectorIntegration_geometry S r F).1

/-- Finite type of the existing bundle projection, used to form compact support.
Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry). -/
instance vectorTrace_finiteType (S : Scheme.{u}) [IsNoetherian S] (r : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] : LocallyOfFiniteType (VectorBundleZeroSection.π S r F) :=
  (vectorIntegration_geometry S r F).2.1

/-- The actual total space is Noetherian; this adds no assumption on the base.
Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry). -/
instance vectorTrace_noetherian (S : Scheme.{u}) [IsNoetherian S] (r : ℕ) (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] : IsNoetherian (VectorBundleZeroSection.scheme S r F) :=
  (vectorIntegration_geometry S r F).2.2

end Etale
namespace VectorTraceGeometry

private def restrictFrame {S : Scheme.{u}} {r : ℕ} {F : S.Modules}
    {U V : S.Opens} (h : V ≤ U)
    (e : F.restrict U.ι ≅ SheafOfModules.free (ULift.{u} (Fin r))) :
    F.restrict V.ι ≅ SheafOfModules.free (ULift.{u} (Fin r)) :=
  Scheme.Modules.restrictCompIso F U.ι (S.homOfLE h) V.ι
      (Scheme.homOfLE_ι S h) ≪≫
    (Scheme.Modules.restrictFunctor (S.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictFreeIso _ _

/-- Finite direct sums add ranks, so both canonical total spaces are available.
Source: blueprint paragraph 2, simultaneous frames
(blueprint: def-pur-vector-trace-geometry).
Proof: intersect frame covers, where the biproduct is free on Fin r disjoint-union Fin s.
The disjoint union is equivalent to Fin (r+s); local freeness descends on this cover. -/
theorem biprod_rank (S : Scheme.{u}) (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :
    (sum S F G).IsFiniteLocallyFreeOfRank (r + s) := by
  classical
  obtain ⟨I, U, hU, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := r)
  obtain ⟨J, V, hV, d⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free G (r := s)
  apply Scheme.Modules.isFiniteLocallyFreeOfRank_of_restrict_iso_free
    (sum S F G) (fun ij : I × J ↦ (U ij.1 ⊓ V ij.2).ι)
  · simp only [Scheme.Opens.opensRange_ι]
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hU.ge (Set.mem_univ x))
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
      (hV.ge (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j), hi, hj⟩
  · intro ij
    let W := U ij.1 ⊓ V ij.2
    have : (Scheme.Modules.restrictFunctor W.ι).Additive := inferInstance
    have : PreservesBinaryBiproducts (Scheme.Modules.restrictFunctor W.ι) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    refine ⟨(Scheme.Modules.restrictFunctor W.ι).mapBiprod F G ≪≫
      biprod.mapIso (restrictFrame inf_le_left (e ij.1).some)
        (restrictFrame inf_le_right (d ij.2).some) ≪≫
      biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso _ _ ≪≫
      SheafOfModules.freeFunctor.mapIso ?_⟩
    exact ((Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
      ((finSumFinEquiv).trans Equiv.ulift.symm)).toIso

/-- Register precisely the rank supplied by the preceding frame calculation.
Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry). -/
instance biprodRank (S : Scheme.{u}) (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :
    (sum S F G).IsFiniteLocallyFreeOfRank (r + s) := biprod_rank S r s F G

private theorem symmetricMap_spec (S : Scheme.{u}) (F G : S.Modules) (j : G ⟶ F)
    (U : S.Opens) (x : G.val.obj (op U)) :
    (WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap S F G j).right.hom.app
        (op U) ((SymmetricAlgebraSheaf.inclusion G).val.app (op U) x) =
      (SymmetricAlgebraSheaf.inclusion F).val.app (op U) (j.val.app (op U) x) :=
  (exists_quasiCoherentSymmetricAlgebra_core S G (SymmetricAlgebraSheaf.algebra F)
    (j ≫ SymmetricAlgebraSheaf.inclusion F)).exists.choose_spec U x

private theorem symmetricMap_inverse (S : Scheme.{u}) (F G : S.Modules)
    (j : G ≅ F) :
    WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap S F G j.hom ≫
      WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap S G F j.inv = 𝟙 _ := by
  apply (exists_quasiCoherentSymmetricAlgebra_core S G
    (SymmetricAlgebraSheaf.algebra G) (SymmetricAlgebraSheaf.inclusion G)).unique
  · intro U x
    change (WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap
      S G F j.inv).right.hom.app (op U)
      ((WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap
        S F G j.hom).right.hom.app (op U) _) = _
    rw [symmetricMap_spec, symmetricMap_spec]
    have h := congrArg (fun k : G ⟶ G ↦ k.val.app (op U) x) j.hom_inv_id
    exact congrArg ((SymmetricAlgebraSheaf.inclusion G).val.app (op U)) h
  · intros
    rfl

/-- The first projection, induced by the first summand's generators.
Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry). -/
def first (S : Scheme.{u}) [IsNoetherian S] (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :
    VectorBundleZeroSection.scheme S (r + s) (sum S F G) ⟶
      VectorBundleZeroSection.scheme S r F :=
  WeilConjectures.PurityFiniteSetting.purityBundleMap S (r + s) r (sum S F G) F biprod.inl

/-- The second projection, induced by the second summand's generators.
Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry). -/
def second (S : Scheme.{u}) [IsNoetherian S] (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :
    VectorBundleZeroSection.scheme S (r + s) (sum S F G) ⟶
      VectorBundleZeroSection.scheme S s G :=
  WeilConjectures.PurityFiniteSetting.purityBundleMap S (r + s) s (sum S F G) G biprod.inr

private theorem purityBundleMap_comm (S : Scheme.{u}) [IsNoetherian S]
    (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] (j : G ⟶ F) :
    WeilConjectures.PurityFiniteSetting.purityBundleMap S r s F G j ≫
      VectorBundleZeroSection.π S s G = VectorBundleZeroSection.π S r F :=
  Over.w ((VectorBundleZeroSection.antiEquivalence S).inverse.map
    (ObjectProperty.homMk
      (X := VectorBundleZeroSection.algebraObject S s G)
      (Y := VectorBundleZeroSection.algebraObject S r F)
      (WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap S F G j))).unop.hom

private theorem purityBundleMap_generators (S : Scheme.{u}) [IsNoetherian S]
    (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] (j : G ⟶ F)
    (U : S.Opens) (x : G.val.obj (op U)) :
    (WeilConjectures.PurityFiniteSetting.purityBundleMap S r s F G j).appLE
        ((VectorBundleZeroSection.π S s G) ⁻¹ᵁ U)
        ((VectorBundleZeroSection.π S r F) ⁻¹ᵁ U)
        (by rw [← purityBundleMap_comm S r s F G j, Scheme.Hom.comp_preimage])
        (generator S s G U x) = generator S r F U (j.val.app (op U) x) := by
  let a := ObjectProperty.homMk
    (X := VectorBundleZeroSection.algebraObject S s G)
    (Y := VectorBundleZeroSection.algebraObject S r F)
    (WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap S F G j)
  have h := congrArg (fun q ↦ q.hom.right.hom.app (op U)
    ((SymmetricAlgebraSheaf.inclusion G).val.app (op U) x))
    ((VectorBundleZeroSection.antiEquivalence S).counitIso.inv.naturality a)
  change (VectorBundleZeroSection.algebraIso S r F).hom.right.hom.app (op U)
      ((WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap
        S F G j).right.hom.app (op U)
        ((SymmetricAlgebraSheaf.inclusion G).val.app (op U) x)) = _ at h
  rw [symmetricMap_spec] at h
  exact h.symm

private theorem bundleLinear_purityBundleMap {S X : Scheme.{u}} [IsNoetherian S]
    (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] (j : G ⟶ F)
    (ρ : X ⟶ S) (ℓ : X ⟶ VectorBundleZeroSection.scheme S r F)
    (hℓ : ℓ ≫ VectorBundleZeroSection.π S r F = ρ) :
    bundleLinear s G ρ
        (ℓ ≫ WeilConjectures.PurityFiniteSetting.purityBundleMap S r s F G j)
        (by rw [Category.assoc, purityBundleMap_comm, hℓ]) =
      j ≫ bundleLinear r F ρ ℓ hℓ := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (ℓ ≫ WeilConjectures.PurityFiniteSetting.purityBundleMap S r s F G j).appLE
    _ _ _ (generator S s G U x) =
    ℓ.appLE _ _ _ (generator S r F U (j.val.app (op U) x))
  rw [← purityBundleMap_generators S r s F G j U x,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

private theorem sum_isPullback (S : Scheme.{u}) [IsNoetherian S]
    (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :
    IsPullback (first S r s F G) (second S r s F G)
      (VectorBundleZeroSection.π S r F) (VectorBundleZeroSection.π S s G) := by
  have hw : first S r s F G ≫ VectorBundleZeroSection.π S r F =
      second S r s F G ≫ VectorBundleZeroSection.π S s G := by
    dsimp only [first, second]
    rw [purityBundleMap_comm, purityBundleMap_comm]
  have hex (t : PullbackCone (VectorBundleZeroSection.π S r F)
      (VectorBundleZeroSection.π S s G)) :
      ∃! ℓ : t.pt ⟶ VectorBundleZeroSection.scheme S (r + s) (sum S F G),
        ℓ ≫ first S r s F G = t.fst ∧ ℓ ≫ second S r s F G = t.snd := by
    let ρ := t.fst ≫ VectorBundleZeroSection.π S r F
    let a := bundleLinear r F ρ t.fst rfl
    let b := bundleLinear s G ρ t.snd t.condition.symm
    let c : sum S F G ⟶ _ := biprod.desc a b
    let ℓ := bundleLift (r + s) (sum S F G) ρ c
    have hℓ := bundleLift_comm (r + s) (sum S F G) ρ c
    have hl : ℓ ≫ first S r s F G = t.fst := by
      change ℓ ≫ WeilConjectures.PurityFiniteSetting.purityBundleMap
        S (r + s) r (sum S F G) F biprod.inl = t.fst
      apply bundle_hom_ext r F ρ _ _
        (by rw [Category.assoc, purityBundleMap_comm, hℓ]) rfl
      rw [bundleLinear_purityBundleMap (r + s) r (sum S F G) F biprod.inl ρ ℓ hℓ,
        bundleLift_linear]
      exact biprod.inl_desc a b
    have hr : ℓ ≫ second S r s F G = t.snd := by
      change ℓ ≫ WeilConjectures.PurityFiniteSetting.purityBundleMap
        S (r + s) s (sum S F G) G biprod.inr = t.snd
      apply bundle_hom_ext s G ρ _ _
        (by rw [Category.assoc, purityBundleMap_comm, hℓ]) t.condition.symm
      rw [bundleLinear_purityBundleMap (r + s) s (sum S F G) G biprod.inr ρ ℓ hℓ,
        bundleLift_linear]
      exact biprod.inr_desc a b
    refine ⟨ℓ, ⟨hl, hr⟩, ?_⟩
    rintro z ⟨hzl, hzr⟩
    dsimp only [first, second] at hzl hzr
    have hz : z ≫ VectorBundleZeroSection.π S (r + s) (sum S F G) = ρ := by
      rw [← purityBundleMap_comm S (r + s) r _ F biprod.inl,
        ← Category.assoc, hzl]
    apply bundle_hom_ext (r + s) (sum S F G) ρ z ℓ hz hℓ
    rw [bundleLift_linear]
    apply biprod.hom_ext'
    · rw [← bundleLinear_purityBundleMap (r + s) r _ F biprod.inl ρ z hz]
      exact (bundleLinear_congr r F ρ _ t.fst _ rfl hzl).trans
        (biprod.inl_desc a b).symm
    · rw [← bundleLinear_purityBundleMap (r + s) s _ G biprod.inr ρ z hz]
      exact (bundleLinear_congr s G ρ _ t.snd _ t.condition.symm hzr).trans
        (biprod.inr_desc a b).symm
  exact ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw
    (fun t ↦ (hex t).exists.choose)
    (fun t ↦ (hex t).exists.choose_spec.1)
    (fun t ↦ (hex t).exists.choose_spec.2)
    (fun t z h₁ h₂ ↦ (hex t).unique ⟨h₁, h₂⟩ (hex t).exists.choose_spec)⟩⟩

/-- The direct-sum total space is the product, and therefore the bundle of p^*F over E(G).
Both projections are prescribed on generators, determining this isomorphism uniquely.
Source: blueprint paragraph 2, direct sums (blueprint: def-pur-vector-trace-geometry).
Proof: the symmetric algebra on a biproduct is the coproduct of the symmetric algebras,
by its universal property on generators. Relative Spec gives the product, and relative
Spec base change identifies that product with the bundle of the pulled-back module.
The two projection equations characterize the resulting product isomorphism uniquely. -/
theorem existsUnique_sumIso (S : Scheme.{u}) [IsNoetherian S] (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :
    ∃! e : VectorBundleZeroSection.scheme
        (VectorBundleZeroSection.scheme S s G) r
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F) ≅
        VectorBundleZeroSection.scheme S (r + s) (sum S F G),
      e.hom ≫ first S r s F G = baseChange (VectorBundleZeroSection.π S s G) r F ∧
      e.hom ≫ second S r s F G = VectorBundleZeroSection.π
        (VectorBundleZeroSection.scheme S s G) r
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F) := by
  let p := baseChange_isPullback (VectorBundleZeroSection.π S s G) r F
  let q := sum_isPullback S r s F G
  let e := p.isoPullback ≪≫ q.isoPullback.symm
  have he₁ : e.hom ≫ first S r s F G =
      baseChange (VectorBundleZeroSection.π S s G) r F := by
    simp [e, Category.assoc]
  have he₂ : e.hom ≫ second S r s F G =
      VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S s G) r
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F) := by
    simp [e, Category.assoc]
  refine ⟨e, ⟨he₁, he₂⟩, ?_⟩
  intro d hd
  apply Iso.ext
  apply q.hom_ext <;> simp only [hd.1, hd.2, he₁, he₂]

/-- The unique product isomorphism, in the direction from the pulled-back bundle.
Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry). -/
def sumIso (S : Scheme.{u}) [IsNoetherian S] (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :
    VectorBundleZeroSection.scheme (VectorBundleZeroSection.scheme S s G) r
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F) ≅
      VectorBundleZeroSection.scheme S (r + s) (sum S F G) :=
  (existsUnique_sumIso S r s F G).exists.choose

/-- The sum isomorphism lies over S, and hence gives an identity-base Cartesian square.
Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry).
Proof: apply the projection equations defining sumIso, then the structural equation of
second. The top and bottom horizontal arrows are isomorphisms, so the square is Cartesian. -/
theorem sumIso_isPullback (S : Scheme.{u}) [IsNoetherian S] (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :
    IsPullback (sumIso S r s F G).hom
      (VectorBundleZeroSection.π (VectorBundleZeroSection.scheme S s G) r
        ((Scheme.Modules.tensorPullback (VectorBundleZeroSection.π S s G)).obj F) ≫
        VectorBundleZeroSection.π S s G)
      (VectorBundleZeroSection.π S (r + s) (sum S F G)) (𝟙 S) := by
  apply IsPullback.of_horiz_isIso
  constructor
  rw [Category.comp_id]
  have hs := (existsUnique_sumIso S r s F G).exists.choose_spec.2
  rw [← hs, Category.assoc]
  congr 1
  exact Over.w ((VectorBundleZeroSection.antiEquivalence S).inverse.map
    (ObjectProperty.homMk
      (X := VectorBundleZeroSection.algebraObject S s G)
      (Y := VectorBundleZeroSection.algebraObject S (r + s) (sum S F G))
      (WeilConjectures.PurityFiniteSetting.puritySymmetricAlgebraMap
        S (sum S F G) G biprod.inr))).unop.hom |>.symm

/-- Exchange of the two ordered blocks is the symmetric-algebra coordinate permutation.
Source: blueprint paragraph 2 (blueprint: def-pur-vector-trace-geometry). -/
def swap (S : Scheme.{u}) [IsNoetherian S] (r s : ℕ) (F G : S.Modules)
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank s] :
    VectorBundleZeroSection.scheme S (r + s) (sum S F G) ⟶
      VectorBundleZeroSection.scheme S (s + r) (sum S G F) :=
  WeilConjectures.PurityFiniteSetting.purityBundleMap S (r + s) (s + r)
    (sum S F G) (sum S G F) (biprod.braiding G F).hom

/-- The rank-zero bundle projection is an isomorphism, including on the empty scheme.
Source: blueprint paragraph 2, rank zero (blueprint: def-pur-vector-trace-geometry).
Proof: the rank-zero module is zero on every frame, hence is zero. Its symmetric algebra
is O_S by the generator universal property. Relative Spec identifies the projection with
Spec_S O_S, whose augmentation is its inverse. -/
theorem zero_isIso (S : Scheme.{u}) [IsNoetherian S] (F : S.Modules)
    [F.IsFiniteLocallyFreeOfRank 0] : IsIso (VectorBundleZeroSection.π S 0 F) := by
  obtain ⟨I, U, hU, e⟩ :=
    Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free F (r := 0)
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) U hU
  intro i
  have := (VectorBundleZeroSection.trivializationMap_spec S 0 F (U i) (e i).some).1
  rw [← (VectorBundleZeroSection.trivializationMap_spec S 0 F (U i) (e i).some).2.1]
  infer_instance

end VectorTraceGeometry
end AlgebraicGeometry

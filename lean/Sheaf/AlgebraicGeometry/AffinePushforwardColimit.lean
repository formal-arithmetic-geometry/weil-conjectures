/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.Modules.HomOfBasis
import WeilConjectures.CategoryTheory.SheafAlgebrasDirectedColimit
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraColimit
import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections

/-! # Affine pushforward and tensor modules commute with directed limits

Source: Stacks Project, Limits, Tags 01Z0 and 01YX
(blueprint: lem-sc-valuation-limit-affine-pushforward-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

set_option hygiene false in
local notation "𝒪⁎" f:max => Under.mk (⟨(f).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (f).base).obj (Scheme.sheaf _))

set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem algebra_comp_app {S : Scheme.{u}}
    {A B C : S.CommAlgebraSheaf} (f : A ⟶ B) (g : B ⟶ C) (V : S.Opensᵒᵖ) :
    (f ≫ g).right.hom.app V = f.right.hom.app V ≫ g.right.hom.app V := rfl

-- Prove the transport with abstract categories, avoiding concrete sheaf-category reduction.
set_option backward.isDefEq.respectTransparency true in
private theorem transport_module_colimit
    {J C E : Type*} [Category J] [Category C] [Category E]
    (A : J ⥤ C) (M : C ⥤ E) (c : Cocone A)
    (hc : IsColimit (M.mapCocone c)) (B : J ⥤ E) (b : Cocone B)
    (hB : ∀ j, B.obj j = M.obj (A.obj j)) (hp : b.pt = M.obj c.pt)
    (hm : ∀ {j k} (f : j ⟶ k),
      eqToHom (hB j).symm ≫ B.map f ≫ eqToHom (hB k) = M.map (A.map f))
    (hl : ∀ j, eqToHom (hB j).symm ≫ b.ι.app j ≫ eqToHom hp = M.map (c.ι.app j)) :
    Nonempty (IsColimit b) := by
  let eB : B ≅ A ⋙ M := NatIso.ofComponents (fun j ↦ eqToIso (hB j)) (by
    intro j k f
    change B.map f ≫ eqToHom (hB k) = eqToHom (hB j) ≫ M.map (A.map f)
    rw [← hm]
    simp)
  let b' := (Cocone.precompose eB.hom).obj (M.mapCocone c)
  have hb' : IsColimit b' := (IsColimit.precomposeHomEquiv eB _).symm hc
  refine ⟨IsColimit.ofIsoColimit hb' ?_⟩
  refine Cocone.ext (eqToIso hp.symm) ?_
  intro j
  change (eqToHom (hB j) ≫ M.map (c.ι.app j)) ≫ eqToHom hp.symm = b.ι.app j
  rw [← hl]
  simp

set_option linter.style.haveILetI false in
-- Inline these section actions: keeping them as local lets makes dependent reduction expensive.
private theorem projection_map {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)
    (G : X.Modules) (η : F ⟶ (pushforward f).obj G) :
    ∃ q : F ⊗ Scheme.CommAlgebraSheaf.toModule (𝒪⁎ f) ⟶
        (pushforward f).obj G,
      ∀ (U : Y.Opens) (t : Γ(F, U)) (a : Γ(X, f ⁻¹ᵁ U)),
        q.app U (tmulSection t a) =
          a • (@id Γ(G, f ⁻¹ᵁ U) (η.app U t)) := by
  classical
  let A := Scheme.CommAlgebraSheaf.toModule (𝒪⁎ f)
  let H := (pushforward f).obj G
  -- Pin the section actions instead of unfolding the pushforward to synthesize them.
  letI (U : Y.Opens) : Module Γ(Y, U) Γ(A, U) := (A.val.obj (op U)).isModule
  letI (U : Y.Opens) : Module Γ(Y, U) Γ(H, U) := (H.val.obj (op U)).isModule
  let β (U : Y.Opens) : Γ(F, U) →ₗ[Γ(Y, U)] Γ(A, U) →ₗ[Γ(Y, U)] Γ(H, U) :=
    LinearMap.mk₂ _ (fun t a ↦ (@id Γ(X, f ⁻¹ᵁ U) a) •
        (@id Γ(G, f ⁻¹ᵁ U) (η.app U t)))
      (by
        intro t t' a
        change (@id Γ(X, f ⁻¹ᵁ U) a) •
            (@id Γ(G, f ⁻¹ᵁ U) (η.app U (t + t'))) =
          (@id Γ(X, f ⁻¹ᵁ U) a) •
              (@id Γ(G, f ⁻¹ᵁ U) (η.app U t)) +
            (@id Γ(X, f ⁻¹ᵁ U) a) •
              (@id Γ(G, f ⁻¹ᵁ U) (η.app U t'))
        have h := (η.app U).hom.map_add t t'
        change (@id Γ(G, f ⁻¹ᵁ U) (η.app U (t + t'))) =
          (@id Γ(G, f ⁻¹ᵁ U) (η.app U t)) +
            (@id Γ(G, f ⁻¹ᵁ U) (η.app U t')) at h
        rw [h]
        exact smul_add _ _ _)
      (by
        intro r t a
        rw [Hom.app_smul]
        change (@id Γ(X, f ⁻¹ᵁ U) a) • ((f.app U).hom r •
            (@id Γ(G, f ⁻¹ᵁ U) (η.app U t))) =
          (f.app U).hom r • ((@id Γ(X, f ⁻¹ᵁ U) a) •
            (@id Γ(G, f ⁻¹ᵁ U) (η.app U t)))
        exact smul_comm (M := Γ(X, f ⁻¹ᵁ U))
          (N := Γ(X, f ⁻¹ᵁ U)) _ _ _)
      (by
        intro t a b
        change ((@id Γ(X, f ⁻¹ᵁ U) a) + (@id Γ(X, f ⁻¹ᵁ U) b)) •
          (@id Γ(G, f ⁻¹ᵁ U) (η.app U t)) = _
        exact add_smul _ _ _)
      (by
        intro r t a
        change ((f.app U).hom r * (@id Γ(X, f ⁻¹ᵁ U) a)) •
            (@id Γ(G, f ⁻¹ᵁ U) (η.app U t)) =
          (f.app U).hom r • ((@id Γ(X, f ⁻¹ᵁ U) a) •
            (@id Γ(G, f ⁻¹ᵁ U) (η.app U t)))
        exact mul_smul _ _ _)
  let p : F.val ⊗ A.val ⟶ H.val :=
    { app := fun U ↦ ModuleCat.ofHom (X := (F.val ⊗ A.val).obj U)
        (Y := H.val.obj U) (TensorProduct.lift (β U.unop))
      naturality := by
        intro U V h
        ext z
        change TensorProduct.lift (β V.unop) ((F.val ⊗ A.val).map h z) =
          H.val.map h (TensorProduct.lift (β U.unop) z)
        induction z using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul t a =>
          change (@id Γ(X, f ⁻¹ᵁ V.unop) (A.val.map h a)) •
              (@id Γ(G, f ⁻¹ᵁ V.unop)
                (η.val.app V (F.val.map h t))) =
            (G).val.map
              ((TopologicalSpace.Opens.map f.base).op.map h) ((@id Γ(X, f ⁻¹ᵁ U.unop) a) •
                (@id Γ(G, f ⁻¹ᵁ U.unop) (η.val.app U t)))
          rw [PresheafOfModules.map_smul]
          congr 1
          exact PresheafOfModules.naturality_apply η.val h t
        | add z w hz hw => simp only [map_add, hz, hw] }
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  let q := (adj.homEquiv (F.val ⊗ A.val) H).symm p
  refine ⟨(SheafOfModules.tensorObjIsoSheafification F A).hom ≫ q, ?_⟩
  intro U t a
  have h := (adj.homEquiv (F.val ⊗ A.val) H).apply_symm_apply p
  rw [Adjunction.homEquiv_unit] at h
  have hv := congrArg (fun k ↦ k.app (op U) (t ⊗ₜ[Γ(Y, U)] a)) h
  change q.val.app (op U) ((SheafOfModules.tensorObjIsoSheafification F A).hom.val.app
    (op U) ((SheafOfModules.tensorObjIsoSheafification F A).inv.val.app (op U)
      ((adj.unit.app (F.val ⊗ A.val)).app (op U) (t ⊗ₜ[Γ(Y, U)] a)))) = _
  have hi := congrArg (fun k ↦ k.val.app (op U)
    ((adj.unit.app (F.val ⊗ A.val)).app (op U) (t ⊗ₜ[Γ(Y, U)] a)))
    (SheafOfModules.tensorObjIsoSheafification F A).inv_hom_id
  change (SheafOfModules.tensorObjIsoSheafification F A).hom.val.app (op U)
    ((SheafOfModules.tensorObjIsoSheafification F A).inv.val.app (op U) _) = _ at hi
  rw [hi]
  change q.val.app (op U) ((adj.unit.app (F.val ⊗ A.val)).app (op U)
    (t ⊗ₜ[Γ(Y, U)] a)) = _ at hv
  exact hv

attribute [local irreducible] AlgebraicGeometry.Scheme.Modules.tmulSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsMap
  AlgebraicGeometry.Scheme.Modules.tensorPullbackObj

private theorem underlying_colimit {X : Scheme.{u}}
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (A : J ⥤ X.CommAlgebraSheaf) (c : Cocone A) (hc : IsColimit c) :
    Nonempty (IsColimit ((commAlgebraSheafModuleFunctor X.sheaf).mapCocone c)) := by
  classical
  let P := A ⋙ Under.forget X.sheaf ⋙
    sheafToPresheaf (_root_.Opens.grothendieckTopology X) CommRingCat
  let p := colimit.cocone P
  have hp (U : X.Opens) : Nonempty (IsColimit
      (((evaluation X.Opensᵒᵖ CommRingCat).obj (op U)).mapCocone p)) :=
    ⟨isColimitOfPreserves _ (colimit.isColimit P)⟩
  obtain ⟨σP, σ, ι, _, _, _, hcol, hmod⟩ :=
    sheafAlgebras_directed_colimit X X.sheaf J A p hp
  have : PreservesColimit A (commAlgebraSheafModuleFunctor X.sheaf) :=
    preservesColimit_of_preserves_colimit_cocone hcol.some hmod.some
  exact ⟨isColimitOfPreserves _ hc⟩

private theorem projection_iso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (F : Y.Modules) [F.IsQuasicoherent] :
    ∃ e : F ⊗ Scheme.CommAlgebraSheaf.toModule (𝒪⁎ f) ≅
        (pushforward f).obj ((tensorPullback f).obj F),
      ∀ (U : Y.Opens) (t : Γ(F, U)) (a : Γ(X, f ⁻¹ᵁ U)),
        e.hom.app U (tmulSection t a) =
          a • (@id Γ((tensorPullback f).obj F, f ⁻¹ᵁ U)
            (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F).app U t)) := by
  classical
  obtain ⟨q, hq⟩ := projection_map f F ((tensorPullback f).obj F)
    ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F)
  have hA : (Scheme.CommAlgebraSheaf.toModule (𝒪⁎ f)).IsQuasicoherent :=
    (affine_morphism_relative_spec Y).1 f inferInstance
  have hbij (U : Y.affineOpens) : Function.Bijective (q.app U.1) := by
    let V : X.affineOpens := ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩
    let : Algebra Γ(Y, U.1) Γ(X, V.1) := (f.appLE U.1 V.1 le_rfl).hom.toAlgebra
    obtain ⟨c, hc, _, hct, _⟩ := exists_tensorPullback_affine_sections f U V le_rfl
    have ht := (quasiCoherent_tensor_product_affine_sections F
      (Scheme.CommAlgebraSheaf.toModule (𝒪⁎ f))).2 U.1 U.2
    let eA : Γ(Scheme.CommAlgebraSheaf.toModule (𝒪⁎ f), U.1) ≃ₗ[Γ(Y, U.1)]
        Γ(X, V.1) :=
      { toFun := fun a ↦ a
        invFun := fun a ↦ a
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro r a
          change (f.app U.1).hom r * (@id Γ(X, V.1) a) =
            (f.appLE U.1 V.1 le_rfl).hom r * (@id Γ(X, V.1) a)
          congr 1
          simp [Scheme.Hom.appLE, V] }
    let eT := TensorProduct.congr (LinearEquiv.refl Γ(Y, U.1) Γ(F, U.1)) eA
    let eH : Γ((tensorPullback f).obj F, V.1) ≃+
        Γ((pushforward f).obj ((tensorPullback f).obj F), U.1) :=
      { toFun := fun a ↦ a
        invFun := fun a ↦ a
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl }
    have he : ∀ z, q.app U.1 (tensorSectionsMap F
        (Scheme.CommAlgebraSheaf.toModule (𝒪⁎ f)) U.1 z) = eH (c F inferInstance (eT z)) := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul t a =>
        rw [tensorSectionsMap_tmul, hq]
        change _ = eH (c F inferInstance (t ⊗ₜ[Γ(Y, U.1)] eA a))
        rw [hct]
        change _ = (@id Γ(X, f ⁻¹ᵁ U.1) a) •
          ((tensorPullback f).obj F).presheaf.map (𝟙 _) _
        change (@id Γ(X, f ⁻¹ᵁ U.1) a) •
            (@id Γ((tensorPullback f).obj F, f ⁻¹ᵁ U.1)
              (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F).app U.1 t)) = _
        rw [CategoryTheory.Functor.map_id]
        rfl
      | add z w hz hw =>
        simp only [map_add]
        exact congrArg₂ (· + ·) hz hw
    have hh : Function.Bijective ((q.app U.1) ∘ tensorSectionsMap F
        (Scheme.CommAlgebraSheaf.toModule (𝒪⁎ f)) U.1) := by
      have heq : (q.app U.1) ∘ tensorSectionsMap F
          (Scheme.CommAlgebraSheaf.toModule (𝒪⁎ f)) U.1 =
          eH ∘ (c F inferInstance) ∘ eT := funext he
      rw [heq]
      exact eH.bijective.comp ((hc F inferInstance).comp eT.bijective)
    exact (Function.Bijective.of_comp_iff _ ht).mp hh
  have : IsIso q := isIso_of_bijective_app_of_basis
    (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using Y.isBasis_affineOpens)
    q hbij
  exact ⟨asIso q, hq⟩

private theorem projection_iso_algebra {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (F : Y.Modules) [F.IsQuasicoherent] (A : Y.CommAlgebraSheaf)
    (α : A ≅ 𝒪⁎ f) :
    ∃ e : F ⊗ A.toModule ≅ (pushforward f).obj ((tensorPullback f).obj F),
      ∀ (U : Y.Opens) (t : Γ(F, U)) (a : A.right.obj.obj (op U)),
        e.hom.app U (tmulSection t a) =
          (@id Γ(X, f ⁻¹ᵁ U) (α.hom.right.hom.app (op U) a)) •
            (@id Γ((tensorPullback f).obj F, f ⁻¹ᵁ U)
              (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F).app U t)) := by
  obtain ⟨e, he⟩ := projection_iso f F
  let M := commAlgebraSheafModuleFunctor Y.sheaf
  refine ⟨(tensorLeft F).mapIso (M.mapIso α) ≪≫ e, ?_⟩
  intro U t a
  change e.hom.app U ((F ◁ M.map α.hom).app U (tmulSection t a)) = _
  rw [whiskerLeft_app_tmulSection, he]
  rfl

private theorem projection_iso_eq {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (F : Y.Modules) [F.IsQuasicoherent] (A : Y.CommAlgebraSheaf) (hA : A = 𝒪⁎ f) :
    ∃ e : F ⊗ A.toModule ≅ (pushforward f).obj ((tensorPullback f).obj F),
      ∀ (U : Y.Opens) (t : Γ(F, U)) (a : A.right.obj.obj (op U)),
        e.hom.app U (tmulSection t a) =
          ((eqToHom (by rw [hA]; rfl : A.right.obj.obj (op U) =
            Γ(X, f ⁻¹ᵁ U))) a) •
            (@id Γ((tensorPullback f).obj F, f ⁻¹ᵁ U)
              (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app F).app U t)) := by
  subst A
  exact projection_iso f F

private theorem conjugate_tmul {S : Scheme.{u}} (F M N H K : S.Modules)
    (e : F ⊗ M ≅ H) (d : F ⊗ N ≅ K) (f : M ⟶ N)
    (U : S.Opens) (t : Γ(F, U)) (a : Γ(M, U)) :
    (e.inv ≫ (F ◁ f) ≫ d.hom).app U (e.hom.app U (tmulSection t a)) =
      d.hom.app U (tmulSection t (f.app U a)) := by
  simp only [Hom.comp_app, ConcreteCategory.comp_apply]
  rw [inv_app_hom_app_apply_of_iso, whiskerLeft_app_tmulSection]

set_option maxHeartbeats 1000000 in
-- The cone, equivalence and transported cocones require dependent categorical elaboration.
/-- The algebra colimit describes the relative spectrum of the limit, the affine projection
formula is canonical, and tensoring its underlying cocone with a fixed module is a colimit.
All algebra and module diagram maps are specified on sections, including the colimit legs.
Source: Stacks Project, Limits, Tags 01Z0 and 01YX
(blueprint: lem-sc-valuation-limit-affine-pushforward-colimit).

Proof: (1) Restrict to the cofinal tail above `i₀` and view its limiting cone in
schemes affine over the fixed stage. The relative-spectrum anti-equivalence turns this
into a colimit of quasi-coherent algebras. The quasi-coherent-algebra colimit theorem
shows that its inclusion in all algebra sheaves preserves this colimit. The object and
section formulas of the equivalence identify its diagram with `A`; uniqueness of colimits
gives `α` with the stated formula for its legs. Mathlib gives affineness of the limit
projection, hence also the affine-chart isomorphisms.
(2) Sheafify the bilinear section map `t, a ↦ a • η(t)`. On an affine open, the existing
pullback-section and tensor-section comparisons prove bijectivity. The affine-basis
criterion gives the projection isomorphism, and its construction gives the pure-tensor
formula on every open. Transport it along `hA` or `α`.
(3) The general sheaf-algebra directed-colimit theorem gives the underlying module
colimit. The section hypotheses identify its diagram and cocone with `B` and `b`.
The algebra isomorphism transports quasi-coherence from the affine pushforward to the
vertex. The sheaf tensor–Hom adjunction shows that `tensorLeft F` preserves this colimit.
(4) Cancel the inverse of each projection isomorphism against its hom, compute tensoring
on pure sections, and substitute `hBm` or `hbm` and the target projection formula. -/
theorem affine_pushforward_colimit
    (I : Type u) [Preorder I] [IsDirected I (· ≤ ·)] (i₀ : I)
    (D : Iᵒᵖ ⥤ Scheme.{u}) (s : Cone D) (hs : IsLimit s)
    [∀ i : I, CompactSpace (D.obj (op i))]
    [∀ i : I, QuasiSeparatedSpace (D.obj (op i))]
    (haff : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f.op))
    (gᵢ : ∀ i : {i : I // i₀ ≤ i}, D.obj (op i.val) ⟶ D.obj (op i₀))
    (hgᵢ : ∀ i, gᵢ i = D.map (homOfLE i.property).op)
    (F : (D.obj (op i₀)).Modules) [F.IsQuasicoherent]
    (A : {i : I // i₀ ≤ i} ⥤ (D.obj (op i₀)).CommAlgebraSheaf)
    (hA : ∀ i, A.obj i = 𝒪⁎ (gᵢ i))
    (hAm : ∀ {i j : {i : I // i₀ ≤ i}} (f : i ⟶ j) (U : (D.obj (op i₀)).Opens),
      (A.map f).right.hom.app (op U) =
        eqToHom (by rw [hA i]; rfl) ≫
          (D.map (homOfLE (x := i.val) (y := j.val) (leOfHom f)).op).appLE
            ((gᵢ i) ⁻¹ᵁ U) ((gᵢ j) ⁻¹ᵁ U)
            (by rw [hgᵢ i, hgᵢ j, ← Scheme.Hom.comp_preimage, ← D.map_comp]; rfl) ≫
          eqToHom (by rw [hA j]; rfl))
    (c : Cocone A) (hc : IsColimit c)
    (B : {i : I // i₀ ≤ i} ⥤ (D.obj (op i₀)).Modules)
    (hB : ∀ i, B.obj i = (A.obj i).toModule)
    (hBm : ∀ {i j : {i : I // i₀ ≤ i}} (f : i ⟶ j) (U : (D.obj (op i₀)).Opens)
        (a : (A.obj i).right.obj.obj (op U)),
      ((eqToHom (hB i).symm ≫ B.map f ≫ eqToHom (hB j)).val.app (op U)) a =
        (A.map f).right.hom.app (op U) a)
    (b : Cocone B) (hbp : b.pt = c.pt.toModule)
    (hbm : ∀ (i) (U : (D.obj (op i₀)).Opens)
        (a : (A.obj i).right.obj.obj (op U)),
      ((eqToHom (hB i).symm ≫ b.ι.app i ≫ eqToHom hbp).val.app (op U)) a =
        (c.ι.app i).right.hom.app (op U) a) :
    c.pt.toModule.IsQuasicoherent ∧
    (∀ i, (A.obj i).toModule.IsQuasicoherent) ∧
    IsAffineHom (s.π.app (op i₀)) ∧
    ∃ α : c.pt ≅ 𝒪⁎ (s.π.app (op i₀)),
      (∀ (i) (U : (D.obj (op i₀)).Opens),
        (c.ι.app i ≫ α.hom).right.hom.app (op U) =
          eqToHom (by rw [hA i]; rfl) ≫
            (s.π.app (op i.val)).appLE ((gᵢ i) ⁻¹ᵁ U)
              ((s.π.app (op i₀)) ⁻¹ᵁ U)
              (by rw [hgᵢ i, ← Scheme.Hom.comp_preimage,
                s.w (homOfLE i.property).op])) ∧
      (∀ (U : (D.obj (op i₀)).Opens), IsAffineOpen U →
        IsIso (((s.π.app (op i₀)) ⁻¹ᵁ U).toSpecΓ ≫
          Spec.map (α.hom.right.hom.app (op U)))) ∧
      ∃ (eᵢ : ∀ i, F ⊗ (A.obj i).toModule ≅
          (pushforward (gᵢ i)).obj ((tensorPullback (gᵢ i)).obj F))
        (e : F ⊗ c.pt.toModule ≅
          (pushforward (s.π.app (op i₀))).obj
            ((tensorPullback (s.π.app (op i₀))).obj F)),
        (∀ (i) (U : (D.obj (op i₀)).Opens) (t : Γ(F, U))
            (a : (A.obj i).right.obj.obj (op U)),
          (eᵢ i).hom.app U (tmulSection t a) =
            ((eqToHom (by rw [hA i]; rfl : (A.obj i).right.obj.obj (op U) =
              Γ(D.obj (op i.val), (gᵢ i) ⁻¹ᵁ U))) a) •
              (@id Γ((tensorPullback (gᵢ i)).obj F, (gᵢ i) ⁻¹ᵁ U)
                (((Classical.choose (exists_tensorPullbackAdjunction (gᵢ i))).unit.app F).app
                  U t))) ∧
        (∀ (U : (D.obj (op i₀)).Opens) (t : Γ(F, U))
            (a : c.pt.right.obj.obj (op U)),
          e.hom.app U (tmulSection t a) =
            (@id Γ(s.pt, (s.π.app (op i₀)) ⁻¹ᵁ U) (α.hom.right.hom.app (op U) a)) •
              (@id Γ((tensorPullback (s.π.app (op i₀))).obj F, (s.π.app (op i₀)) ⁻¹ᵁ U)
                (((Classical.choose
                  (exists_tensorPullbackAdjunction (s.π.app (op i₀)))).unit.app F).app U t))) ∧
        (∀ {i j : {i : I // i₀ ≤ i}} (f : i ⟶ j)
            (U : (D.obj (op i₀)).Opens) (t : Γ(F, U))
            (a : (A.obj i).right.obj.obj (op U)),
          ((eᵢ i).inv ≫
            (F ◁ (eqToHom (hB i).symm ≫ B.map f ≫ eqToHom (hB j))) ≫
            (eᵢ j).hom).app U ((eᵢ i).hom.app U (tmulSection t a)) =
              ((eqToHom (by rw [hA j]; rfl : (A.obj j).right.obj.obj (op U) =
                  Γ(D.obj (op j.val), (gᵢ j) ⁻¹ᵁ U)))
                ((A.map f).right.hom.app (op U) a)) •
                (@id Γ((tensorPullback (gᵢ j)).obj F, (gᵢ j) ⁻¹ᵁ U)
                  (((Classical.choose (exists_tensorPullbackAdjunction (gᵢ j))).unit.app F).app
                    U t))) ∧
        (∀ (i) (U : (D.obj (op i₀)).Opens) (t : Γ(F, U))
            (a : (A.obj i).right.obj.obj (op U)),
          ((eᵢ i).inv ≫
            (F ◁ (eqToHom (hB i).symm ≫ b.ι.app i ≫ eqToHom hbp)) ≫
            e.hom).app U ((eᵢ i).hom.app U (tmulSection t a)) =
              (@id Γ(s.pt, (s.π.app (op i₀)) ⁻¹ᵁ U)
                  ((c.ι.app i ≫ α.hom).right.hom.app (op U) a)) •
                (@id Γ((tensorPullback (s.π.app (op i₀))).obj F, (s.π.app (op i₀)) ⁻¹ᵁ U)
                  (((Classical.choose
                    (exists_tensorPullbackAdjunction (s.π.app (op i₀)))).unit.app F).app U t))) ∧
        Nonempty (IsColimit b) ∧
        Nonempty (IsColimit ((tensorLeft F).mapCocone b)) := by
  classical
  let J := {i : I // i₀ ≤ i}
  let : Nonempty I := ⟨i₀⟩
  let : Nonempty J := ⟨⟨i₀, le_rfl⟩⟩
  let : IsDirected J (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  let {i j : Iᵒᵖ} (f : i ⟶ j) : IsAffineHom (D.map f) := haff f.unop
  let hg : IsAffineHom (s.π.app (op i₀)) := isAffineHom_π_app D s hs _
  have hgi (j : J) : IsAffineHom (gᵢ j) := by
    rw [hgᵢ j]
    exact haff _
  have hqc (j : J) : (A.obj j).toModule.IsQuasicoherent := by
    rw [hA j]
    exact (affine_morphism_relative_spec (D.obj (op i₀))).1 (gᵢ j) (hgi j)
  let t : J ⥤ I := (show Monotone (fun j : J ↦ j.val) from fun _ _ h ↦ h).functor
  let : t.op.Initial := Functor.initial_of_exists_of_isCofiltered t.op
    (fun i ↦ by
      obtain ⟨j, h₀, hi⟩ := exists_ge_ge i₀ i.unop
      exact ⟨op ⟨j, h₀⟩, ⟨(homOfLE hi).op⟩⟩)
    (fun {_ _} f g ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
  let S := D.obj (op i₀)
  -- Bind the general transport theorem with a type indexed by the section expression.
  have hsections {C C' : S.CommAlgebraSheaf} (h : C = C') (U : S.Opensᵒᵖ) :
      (eqToHom h).right.hom.app U = eqToHom (by cases h; rfl) :=
    eqToHom_map (Under.forget S.sheaf ⋙
      sheafToPresheaf (_root_.Opens.grothendieckTopology S) CommRingCat ⋙
      (evaluation S.Opensᵒᵖ CommRingCat).obj U) h
  let P : ObjectProperty S.CommAlgebraSheaf := fun C ↦ C.toModule.IsQuasicoherent
  let Q : ObjectProperty (Over S) := fun Y ↦ IsAffineHom Y.hom
  let L : Jᵒᵖ ⥤ Q.FullSubcategory :=
    { obj := fun j ↦ ⟨Over.mk (gᵢ j.unop), hgi j.unop⟩
      map := fun {j k} f ↦ ⟨Over.homMk (D.map (t.op.map f)) (by
        change D.map (t.op.map f) ≫ gᵢ k.unop = gᵢ j.unop
        rw [hgᵢ, hgᵢ]
        exact (D.map_comp _ _).symm.trans (congrArg D.map (Subsingleton.elim _ _))
        )⟩
      map_id := by
        intro j
        apply InducedCategory.hom_ext
        apply Over.OverMorphism.ext
        change D.map (t.op.map (𝟙 j)) = 𝟙 _
        rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
      map_comp := by
        intro j k l f g
        apply InducedCategory.hom_ext
        apply Over.OverMorphism.ext
        change D.map (t.op.map (f ≫ g)) = D.map (t.op.map f) ≫ D.map (t.op.map g)
        rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] }
  let l : Cone L :=
    { pt := ⟨Over.mk (s.π.app (op i₀)), hg⟩
      π :=
        { app := fun j ↦ ⟨Over.homMk (s.π.app (op j.unop.val)) (by
            change s.π.app (op j.unop.val) ≫ gᵢ j.unop = _
            rw [hgᵢ, s.w]
            rfl)⟩
          naturality := by
            intro j k f
            apply InducedCategory.hom_ext
            apply Over.OverMorphism.ext
            exact (s.w (t.op.map f)).symm } }
  let : IsConnected Jᵒᵖ := IsCofiltered.isConnected Jᵒᵖ
  have hl : IsLimit l := by
    apply isLimitOfReflects Q.ι
    apply isLimitOfReflects (Over.forget S)
    exact (Functor.Initial.isLimitWhiskerEquiv t.op s).symm hs
  obtain ⟨_, E, hobj, _, hmap, _⟩ := affine_morphism_relative_spec S
  let G := L.rightOp ⋙ E.functor
  let d := E.functor.mapCocone (coconeRightOpOfCone l)
  have hd : IsColimit d :=
    isColimitOfPreserves E.functor (isColimitCoconeRightOpOfCone L hl)
  obtain ⟨a, ⟨ha⟩, hqa, _⟩ := Scheme.quasiCoherentAlgebra_colimit S J
    (G ⋙ P.ι) (fun j ↦ (G.obj j).property)
  let : HasColimit (G ⋙ P.ι) := ⟨⟨a, ha⟩⟩
  let : CreatesColimit G P.ι := createsColimitFullSubcategoryInclusion' G ha hqa
  have hd' : IsColimit (P.ι.mapCocone d) := isColimitOfPreserves P.ι hd
  let eA : A ≅ G ⋙ P.ι := NatIso.ofComponents
    (fun j ↦ eqToIso (hA j) ≪≫ (eqToIso (hobj (L.obj (op j)))).symm) (by
      intro j k f
      apply Under.UnderMorphism.ext
      apply CategoryTheory.Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      change (A.map f).right.hom.app U ≫
          ((eqToHom (hA k) ≫ eqToHom (hobj (L.obj (op k))).symm).right.hom.app U) =
        ((eqToHom (hA j) ≫ eqToHom (hobj (L.obj (op j))).symm).right.hom.app U) ≫
          (E.functor.map (L.map f.op).op).hom.right.hom.app U
      simp only [algebra_comp_app, hsections]
      erw [hAm f U.unop]
      erw [hmap (L.obj (op k)) (L.obj (op j)) (L.map f.op) U.unop]
      simp only [Category.assoc, eqToHom_trans]
      simp only [← Category.assoc, eqToHom_trans]
      rfl)
  let dA := (Cocone.precompose eA.hom).obj (P.ι.mapCocone d)
  have hdA : IsColimit dA := (IsColimit.precomposeHomEquiv eA _).symm hd'
  let α : c.pt ≅ 𝒪⁎ (s.π.app (op i₀)) :=
    hc.coconePointUniqueUpToIso hdA ≪≫ eqToIso (hobj l.pt)
  have hα (j : J) (U : S.Opens) :
      (c.ι.app j ≫ α.hom).right.hom.app (op U) =
        eqToHom (by rw [hA j]; rfl) ≫
          (s.π.app (op j.val)).appLE ((gᵢ j) ⁻¹ᵁ U)
            ((s.π.app (op i₀)) ⁻¹ᵁ U)
            (by rw [hgᵢ j, ← Scheme.Hom.comp_preimage,
              s.w (homOfLE j.property).op]) := by
    change (c.ι.app j ≫ (hc.coconePointUniqueUpToIso hdA).hom ≫
      eqToHom (hobj l.pt)).right.hom.app (op U) = _
    rw [← Category.assoc, hc.comp_coconePointUniqueUpToIso_hom]
    change (((eqToHom (hA j) ≫ eqToHom (hobj (L.obj (op j))).symm) ≫
      (E.functor.map (l.π.app (op j)).op).hom) ≫
      eqToHom (hobj l.pt)).right.hom.app (op U) = _
    simp only [algebra_comp_app]
    rw [hmap l.pt (L.obj (op j)) (l.π.app (op j)) U]
    simp only [hsections, Category.assoc, eqToHom_trans]
    simp only [← Category.assoc, eqToHom_trans]
    rfl
  let M : S.CommAlgebraSheaf ⥤ S.Modules := commAlgebraSheafModuleFunctor S.sheaf
  have hmapB {j k : J} (f : j ⟶ k) :
      eqToHom (hB j).symm ≫ B.map f ≫ eqToHom (hB k) = M.map (A.map f) := by
    apply Scheme.Modules.hom_ext
    intro U
    ext a
    exact hBm f U a
  have hlegB (j : J) :
      eqToHom (hB j).symm ≫ b.ι.app j ≫ eqToHom hbp = M.map (c.ι.app j) := by
    apply Scheme.Modules.hom_ext
    intro U
    ext a
    exact hbm j U a
  have hcM : IsColimit (M.mapCocone c) := (underlying_colimit A c hc).some
  have hb' : IsColimit b := (transport_module_colimit A M c hcM B b hB hbp
    (fun f ↦ hmapB f) hlegB).some
  have hqcG : (Scheme.CommAlgebraSheaf.toModule
      (𝒪⁎ (s.π.app (op i₀)))).IsQuasicoherent :=
    (affine_morphism_relative_spec S).1 (s.π.app (op i₀)) hg
  have hqcC : c.pt.toModule.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso (M.mapIso α).symm hqcG
  have ht : Nonempty (IsColimit ((tensorLeft F).mapCocone b)) := by
    have : PreservesColimits (tensorLeft F) :=
      (SheafOfModules.tensorHomAdjunction S.sheaf F).leftAdjoint_preservesColimits
    exact ⟨isColimitOfPreserves _ hb'⟩
  let (j : J) : IsAffineHom (gᵢ j) := hgi j
  have hi (j : J) := projection_iso_eq (gᵢ j) F (A.obj j) (hA j)
  choose eᵢ heᵢ using hi
  obtain ⟨e, he⟩ := projection_iso_algebra (s.π.app (op i₀)) F c.pt α
  refine ⟨hqcC, hqc, hg, α, hα, ?_, eᵢ, e, ?_, he, ?_, ?_, ⟨hb'⟩, ht⟩
  · intro U hU
    have : IsIso (((s.π.app (op i₀)) ⁻¹ᵁ U).toSpecΓ) :=
      (hU.preimage _).isoSpec.isIso_hom
    infer_instance
  · intro j U t a
    exact heᵢ j U t a
  · intro j k f U t a
    have hh := hBm f U a
    change (eqToHom (hB j).symm ≫ B.map f ≫ eqToHom (hB k)).app U a = _ at hh
    exact (conjugate_tmul F _ _ _ _ (eᵢ j) (eᵢ k)
      (eqToHom (hB j).symm ≫ B.map f ≫ eqToHom (hB k)) U t a).trans
      ((congrArg (fun z ↦ (eᵢ k).hom.app U (tmulSection t z)) hh).trans (by
        exact heᵢ k U t ((A.map f).right.hom.app (op U) a)))
  · intro j U t a
    have hh := hbm j U a
    change (eqToHom (hB j).symm ≫ b.ι.app j ≫ eqToHom hbp).app U a = _ at hh
    exact (conjugate_tmul F _ _ _ _ (eᵢ j) e
      (eqToHom (hB j).symm ≫ b.ι.app j ≫ eqToHom hbp) U t a).trans
      ((congrArg (fun z ↦ e.hom.app U (tmulSection t z)) hh).trans
        (by
          have hj := he U t ((c.ι.app j).right.hom.app (op U) a)
          convert hj using 1
          rfl))

end AlgebraicGeometry

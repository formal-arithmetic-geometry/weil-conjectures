/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BertiniLocalFirstJets
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks

import Sheaf.AlgebraicGeometry.RelativeDifferentialsStalk
import Sheaf.AlgebraicGeometry.SourceFibreDifferentialFunctionals
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! Auxiliary comparison and injectivity statements for source-fibre differentials.

Source: Stacks Project, Morphisms, lemma-base-change-differentials (Tag 01V0),
lemma-smooth-omega-finite-locally-free (Tag 02G1), and Sheaves, Tag 0098.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry

private theorem exists_linearMap_of_germs
    {X : Scheme.{u}} (x : X) (M : X.Modules)
    {N : Type u} [AddCommGroup N] [Module (X.presheaf.stalk x) N]
    (q : ∀ (W : X.Opens), x ∈ W → Γ(M, W) →+ N)
    (hq : ∀ (W V : X.Opens) (hx : x ∈ W) (hV : V ≤ W) (hv : x ∈ V)
      (m : Γ(M, W)), q V hv (M.presheaf.map (homOfLE hV).op m) = q W hx m)
    (hs : ∀ (W : X.Opens) (hx : x ∈ W) (r : Γ(X, W)) (m : Γ(M, W)),
      q W hx (r • m) = X.presheaf.germ W x hx r • q W hx m) :
    ∃ L : M.presheaf.stalk x →ₗ[X.presheaf.stalk x] N,
      ∀ (W : X.Opens) (hx : x ∈ W) (m : Γ(M, W)),
        L (M.presheaf.germ W x hx m) = q W hx m := by
  let a : M.presheaf.stalk x →+ N :=
    ConcreteCategory.hom (colimit.desc ((TopologicalSpace.OpenNhds.inclusion x).op ⋙
      M.presheaf)
      { pt := AddCommGrpCat.of N
        ι :=
          { app W := AddCommGrpCat.ofHom (q W.unop.1 W.unop.2)
            naturality W V i := by
              ext m
              exact hq _ _ W.unop.2 i.unop.le V.unop.2 m } })
  have ha (W : X.Opens) (hx : x ∈ W) (m : Γ(M, W)) :
      a (M.presheaf.germ W x hx m) = q W hx m := by
    dsimp only [a, TopCat.Presheaf.germ]
    erw [colimit.ι_desc_apply]
    rfl
  refine ⟨Scheme.Modules.stalkLinearMapMk a ?_, ha⟩
  intro W hx r m
  rw [ha, ha]
  exact hs W hx r m

private theorem residue_point_appLE {X T : Scheme.{u}} (x : X)
    (h : T ⟶ Spec (X.residueField x)) (W : X.Opens) (hx : x ∈ W)
    (hV : (⊤ : T.Opens) ≤ (h ≫ X.fromSpecResidueField x) ⁻¹ᵁ W) :
    (h ≫ X.fromSpecResidueField x).appLE W ⊤ hV =
      X.presheaf.germ W x hx ≫ X.residue x ≫
        (Scheme.ΓSpecIso (X.residueField x)).inv ≫ h.appTop := by
  change ((h ≫ Spec.map (X.residue x)) ≫ X.fromSpecStalk x).appLE W ⊤ hV = _
  rw [Scheme.Hom.comp_appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc]
  rw [Scheme.Hom.map_appLE]
  rw [show (h ≫ Spec.map (X.residue x)).appLE ⊤ ⊤ (by simp) =
      (h ≫ Spec.map (X.residue x)).appTop by simp [Scheme.Hom.appLE]]
  rw [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc]

private theorem exists_restricted_stalk_to_sections
    {X Y T : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (x : X)
    (h : T ⟶ Spec (X.residueField x)) (r : T ⟶ Y)
    (hr : r = h ≫ X.fromSpecResidueField x ≫ j)
    (M : Y.Modules) (N : T.Modules)
    (φ : M ⟶ (Scheme.Modules.pushforward r).obj N)
    (σ : X.presheaf.stalk x →+* Γ(T, ⊤))
    (hσ : σ = (((X.residue x) ≫
      (Scheme.ΓSpecIso (X.residueField x)).inv ≫ h.appTop)).hom) :
    letI : Module (X.presheaf.stalk x) Γ(N, ⊤) := Module.compHom _ σ
    ∃ L : (M.restrict j).presheaf.stalk x →ₗ[X.presheaf.stalk x] Γ(N, ⊤),
      ∀ (W : X.Opens) (hx : x ∈ W) (m : Γ(M.restrict j, W))
        (hW : (⊤ : T.Opens) ≤ r ⁻¹ᵁ (j ''ᵁ W)),
        L ((M.restrict j).presheaf.germ W x hx m) =
          N.presheaf.map (homOfLE hW).op (φ.app (j ''ᵁ W) m) := by
  let : Module (X.presheaf.stalk x) Γ(N, ⊤) := Module.compHom _ σ
  change ∃ L : (M.restrict j).presheaf.stalk x →ₗ[X.presheaf.stalk x] Γ(N, ⊤), _
  have hW (W : X.Opens) (hx : x ∈ W) :
      (⊤ : T.Opens) ≤ r ⁻¹ᵁ (j ''ᵁ W) := by
    intro t _
    change r t ∈ j ''ᵁ W
    rw [hr]
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using
      (show j x ∈ j ''ᵁ W by simpa using hx)
  let q (W : X.Opens) (hx : x ∈ W) : Γ(M.restrict j, W) →+ Γ(N, ⊤) :=
    (N.presheaf.map (homOfLE (hW W hx)).op).hom.comp (φ.app (j ''ᵁ W)).hom
  have hq (W V : X.Opens) (hx : x ∈ W) (hV : V ≤ W) (hv : x ∈ V)
      (m : Γ(M.restrict j, W)) :
      q V hv ((M.restrict j).presheaf.map (homOfLE hV).op m) = q W hx m := by
    let m' : Γ(M, j ''ᵁ W) := m
    change N.presheaf.map _ (φ.app (j ''ᵁ V) (M.presheaf.map _ m')) = _
    have hn := ConcreteCategory.congr_hom
      (φ.mapPresheaf.naturality (homOfLE (j.image_mono hV)).op) m'
    change φ.app _ (M.presheaf.map _ m') = N.presheaf.map _ (φ.app _ m') at hn
    erw [hn]
    rw [← ConcreteCategory.comp_apply, ← N.presheaf.map_comp]
    rfl
  have hs (W : X.Opens) (hx : x ∈ W) (a : Γ(X, W)) (m : Γ(M.restrict j, W)) :
      q W hx (a • m) = X.presheaf.germ W x hx a • q W hx m := by
    let m' : Γ(M, j ''ᵁ W) := m
    change N.presheaf.map _ (φ.app _ ((j.appIso W).inv a • m')) = _
    rw [Scheme.Modules.Hom.app_smul]
    change N.presheaf.map _ (r.app _ ((j.appIso W).inv a) •
      (show Γ(N, r ⁻¹ᵁ (j ''ᵁ W)) from φ.app _ m')) = _
    rw [Scheme.Modules.map_smul]
    change r.appLE (j ''ᵁ W) ⊤ (hW W hx) ((j.appIso W).inv a) • (_ : Γ(N, ⊤)) =
      σ (X.presheaf.germ W x hx a) • (_ : Γ(N, ⊤))
    have he : (j.appIso W).inv ≫ r.appLE (j ''ᵁ W) ⊤ (hW W hx) =
        X.presheaf.germ W x hx ≫ X.residue x ≫
          (Scheme.ΓSpecIso (X.residueField x)).inv ≫ h.appTop := by
      subst r
      have hp : (⊤ : T.Opens) ≤ (h ≫ X.fromSpecResidueField x) ⁻¹ᵁ W := by
        intro t _
        change (h ≫ X.fromSpecResidueField x) t ∈ W
        simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using hx
      have hc := Scheme.Hom.appLE_comp_appLE (h ≫ X.fromSpecResidueField x) j
        (j ''ᵁ W) W ⊤ (by simp) hp
      have hc' : j.appLE (j ''ᵁ W) W (by simp) ≫
          (h ≫ X.fromSpecResidueField x).appLE W ⊤ hp =
          (h ≫ X.fromSpecResidueField x ≫ j).appLE (j ''ᵁ W) ⊤ (hW W hx) := by
        simpa only [Category.assoc] using hc
      rw [← hc', ← Category.assoc, Scheme.Hom.appIso_inv_appLE]
      simpa using residue_point_appLE x h W hx hp
    rw [← CommRingCat.comp_apply, he, hσ]
    rfl
  obtain ⟨L, hL⟩ := exists_linearMap_of_germs x (M.restrict j) q hq hs
  exact ⟨L, fun W hx m _ ↦ hL W hx m⟩

private theorem exists_source_differential_pushforward
    {S Y B : Scheme.{u}} (f : Y ⟶ S) (c : B ⟶ S) :
    ∃ τ : f.relativeDifferentials ⟶
        (Scheme.Modules.pushforward (pullback.snd c f)).obj
          (pullback.fst c f).relativeDifferentials,
      ∀ (W : Y.Opens) (a : Γ(Y, W)),
        τ.app W (f.relativeDifferentialsDerivation.d (X := Opposite.op W) a) =
          (pullback.fst c f).relativeDifferentialsDerivation.d
            (X := Opposite.op ((pullback.snd c f) ⁻¹ᵁ W))
            ((pullback.snd c f).app W a) := by
  let p := pullback.snd c f
  let q := pullback.fst c f
  let δ : ((Scheme.Modules.pushforward p).obj q.relativeDifferentials).val.Derivation'
      f.pullbackPresheafToPresheaf :=
    f.derivationMk
      (fun {W} ↦ q.relativeDifferentialsDerivation.d.comp
        (p.app W.unop).hom.toAddMonoidHom)
      (by
        intro W a b
        change q.relativeDifferentialsDerivation.d (p.app W.unop (a * b)) = _
        rw [map_mul, PresheafOfModules.Derivation.d_mul]
        rfl)
      (by
        intro W V i a
        change q.relativeDifferentialsDerivation.d (p.app V.unop (Y.presheaf.map i a)) = _
        rw [← CommRingCat.comp_apply, p.naturality i]
        exact q.relativeDifferentialsDerivation.d_map _ _)
      (by
        intro V a
        change q.relativeDifferentialsDerivation.d
          (p.app (f ⁻¹ᵁ V) (f.app V a)) = 0
        have hw := Scheme.Hom.congr_app (pullback.condition (f := c) (g := f)).symm V
        have hv := congrArg (fun k ↦ k a) hw
        change (p ≫ f).app V a = _ at hv
        change q.relativeDifferentialsDerivation.d ((p ≫ f).app V a) = 0
        rw [hv]
        erw [q.relativeDifferentialsDerivation.d_map]
        change q.relativeDifferentials.val.map _
          (q.relativeDifferentialsDerivation.d (q.app _ (c.app V a))) = 0
        erw [q.relativeDifferentialsDerivation.d_app_app, map_zero])
  refine ⟨(f.relativeDifferentialsHomEquiv _).symm δ, ?_⟩
  intro W a
  exact (f.relativeDifferentialsHomEquiv_symm_app_d δ a).trans rfl

/-- The differential comparison exists with the required pure-tensor formula; injectivity
is handled separately by `source_fibre_differential_injective_of_formula`.

Source: Stacks Project, Morphisms, lemma-base-change-differentials (Tag 01V0),
lemma-smooth-omega-finite-locally-free (Tag 02G1), and Sheaves, Tag 0098.
(blueprint: lem-zl-source-fibre-differential-formula).

Proof: Compose the universal derivation with the source projection and the normalized
pullback unit along g. This gives a map from Omega_f to the pushforward of g^*Omega_p.
Every neighbourhood of z in U pulls back to all of T by hg, so the maps on sections of
Omega_f restricted to U descend through the stalk colimit. The residue-field-point
formula and h_alpha make this map linear over O_U,z acting through K and A.
Compose with the stalk of Omega_(U/k) -> Omega_(Y/k)|_U, and extend scalars first to K
and then to A. The tensor-Hom adjunction gives D. The open-restriction differential
formula, naturality and the normalized unit give exactly the displayed pure-tensor
formula. This construction requires no finite basis or finite local freeness.
-/
theorem exists_source_fibre_differential_formula
    {k : Type u} [Field k] {Y B T : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [Smooth f] (c : B ⟶ Spec (.of k))
    (U : Y.Opens) (z : U)
    (h : T ⟶ Spec ((U : Scheme).residueField z)) (g : T ⟶ pullback c f)
    (hg : g ≫ pullback.snd c f = h ≫ (U : Scheme).fromSpecResidueField z ≫ U.ι)
    (α : (U : Scheme).residueField z →+* Γ(T, ⊤))
    (hα : α = ((Scheme.ΓSpecIso ((U : Scheme).residueField z)).inv ≫ h.appTop).hom) :
    let K := (U : Scheme).residueField z
    let A := Γ(T, ⊤)
    letI : Algebra K A := α.toAlgebra
    ∃ D : (A ⊗[K] bertiniCotangentFibre f U z) →ₗ[A]
        Γ((Scheme.Modules.tensorPullback g).obj (pullback.fst c f).relativeDifferentials, ⊤),
      ∀ (W : Y.Opens) (hz : U.ι z ∈ W)
        (hV : (⊤ : T.Opens) ≤ g ⁻¹ᵁ ((pullback.snd c f) ⁻¹ᵁ W))
        (a : Γ(Y, W)) (b : A),
        D (b ⊗ₜ[K] (bertiniLocalFirstJet f U z W hz a).2) =
          b • ((Scheme.Modules.tensorPullback g).obj
            (pullback.fst c f).relativeDifferentials).presheaf.map (homOfLE hV).op
              (Scheme.Modules.tensorPullbackSection g (pullback.fst c f).relativeDifferentials
                ((pullback.snd c f) ⁻¹ᵁ W)
                ((pullback.fst c f).relativeDifferentialsDerivation.d
                  (X := Opposite.op ((pullback.snd c f) ⁻¹ᵁ W))
                  ((pullback.snd c f).app W a))) := by
  classical
  dsimp only
  let X : Scheme := U
  let R := X.presheaf.stalk z
  let K := X.residueField z
  let A := Γ(T, ⊤)
  let : Algebra K A := α.toAlgebra
  let ρ : R →+* K := ((𝟙 X : X ⟶ X).stalkMap z ≫ X.residue z).hom
  let : Algebra R K := ρ.toAlgebra
  let σ : R →+* A := α.comp ρ
  let N := (Scheme.Modules.tensorPullback g).obj (pullback.fst c f).relativeDifferentials
  let : Module K Γ(N, ⊤) := Module.compHom _ α
  let : Module R Γ(N, ⊤) := Module.compHom _ σ
  let : IsScalarTower K A Γ(N, ⊤) :=
    ⟨fun a b m ↦ mul_smul (α a) b m⟩
  let : IsScalarTower R K Γ(N, ⊤) :=
    ⟨fun a b m ↦ by
      change α (ρ a * b) • m = α (ρ a) • (α b • m)
      rw [map_mul, mul_smul]⟩
  obtain ⟨τ, hτ⟩ := exists_source_differential_pushforward f c
  obtain ⟨adj, hadj, _⟩ := Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction g
  let φ : f.relativeDifferentials ⟶
      (Scheme.Modules.pushforward (g ≫ pullback.snd c f)).obj N :=
    τ ≫ (Scheme.Modules.pushforward (pullback.snd c f)).map
      (adj.unit.app (pullback.fst c f).relativeDifferentials) ≫
        (Scheme.Modules.pushforwardComp g (pullback.snd c f)).hom.app N
  have hφ (W : Y.Opens) (a : Γ(Y, W)) :
      φ.app W (f.relativeDifferentialsDerivation.d (X := Opposite.op W) a) =
        Scheme.Modules.tensorPullbackSection g (pullback.fst c f).relativeDifferentials
          ((pullback.snd c f) ⁻¹ᵁ W)
          ((pullback.fst c f).relativeDifferentialsDerivation.d
            (X := Opposite.op ((pullback.snd c f) ⁻¹ᵁ W))
            ((pullback.snd c f).app W a)) := by
    change (adj.unit.app _).app _ (τ.app W _) = _
    rw [hτ, hadj]
    rfl
  have hσ : σ = (X.residue z ≫ (Scheme.ΓSpecIso K).inv ≫ h.appTop).hom := by
    dsimp only [σ, ρ]
    rw [Scheme.Hom.stalkMap_id]
    change α.comp (X.residue z).hom = _
    exact congrArg (fun β : K →+* A ↦ β.comp (X.residue z).hom) hα
  obtain ⟨L, hL⟩ := exists_restricted_stalk_to_sections U.ι z h
    (g ≫ pullback.snd c f) hg f.relativeDifferentials N φ σ hσ
  let ψ := f.relativeDifferentialsToRestrict U.ι
  let L₀ := L.comp (ψ.stalkLinearMap z)
  have hstalk (W : Y.Opens) (hz : U.ι z ∈ W)
      (hV : (⊤ : T.Opens) ≤ g ⁻¹ᵁ ((pullback.snd c f) ⁻¹ᵁ W)) (a : Γ(Y, W)) :
      L₀ ((U.ι ≫ f).relativeDifferentials.presheaf.germ (U.ι ⁻¹ᵁ W) z hz
        ((U.ι ≫ f).relativeDifferentialsDerivation.d (U.ι.app W a))) =
        N.presheaf.map (homOfLE hV).op
          (φ.app W (f.relativeDifferentialsDerivation.d (X := Opposite.op W) a)) := by
    dsimp only [L₀, LinearMap.comp_apply]
    erw [Scheme.Modules.Hom.stalkLinearMap_germ]
    have hW : (⊤ : T.Opens) ≤
        (g ≫ pullback.snd c f) ⁻¹ᵁ (U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) := by
      intro t _
      change (g ≫ pullback.snd c f) t ∈ U.ι ''ᵁ (U.ι ⁻¹ᵁ W)
      rw [hg]
      simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using
        (show U.ι z ∈ U.ι ''ᵁ (U.ι ⁻¹ᵁ W) from ⟨z, hz, rfl⟩)
    rw [hL _ hz _ hW]
    have hψ : ψ.app (U.ι ⁻¹ᵁ W)
        ((U.ι ≫ f).relativeDifferentialsDerivation.d (U.ι.app W a)) =
        f.relativeDifferentialsDerivation.d
          ((U.ι.appIso (U.ι ⁻¹ᵁ W)).inv (U.ι.app W a)) :=
      f.relativeDifferentialsToRestrict_app_d U.ι
        (W := Opposite.op (U.ι ⁻¹ᵁ W)) (U.ι.app W a)
    rw [hψ]
    have ha := ConcreteCategory.congr_hom (U.ι.app_appIso_inv W) a
    change (U.ι.appIso (U.ι ⁻¹ᵁ W)).inv (U.ι.app W a) = Y.presheaf.map _ a at ha
    let i : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) ⟶ W :=
      homOfLE (Set.image_preimage_subset U.ι W.1)
    have hd : f.relativeDifferentialsDerivation.d
        (Y.presheaf.map i.op a) =
        f.relativeDifferentials.presheaf.map i.op
          (f.relativeDifferentialsDerivation.d (X := Opposite.op W) a) :=
      f.relativeDifferentialsDerivation.d_map i.op a
    rw [ha]
    erw [hd]
    have hn := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op)
      (f.relativeDifferentialsDerivation.d (X := Opposite.op W) a)
    change φ.app _ (f.relativeDifferentials.presheaf.map _ _) =
      N.presheaf.map _ (φ.app W _) at hn
    erw [hn]
    have hc : N.presheaf.map
        ((TopologicalSpace.Opens.map (g ≫ pullback.snd c f).base).op.map i.op) ≫
        N.presheaf.map (homOfLE hW).op = N.presheaf.map (homOfLE hV).op := by
      rw [← N.presheaf.map_comp]
      rfl
    exact ConcreteCategory.congr_hom hc _
  let D : (A ⊗[K] bertiniCotangentFibre f U z) →ₗ[A] Γ(N, ⊤) :=
    (L₀.liftBaseChange K).liftBaseChange A
  refine ⟨D, ?_⟩
  intro W hz hV a b
  change b • ((1 : K) • L₀
    ((U.ι ≫ f).relativeDifferentials.presheaf.germ (U.ι ⁻¹ᵁ W) z hz
      ((U.ι ≫ f).relativeDifferentialsDerivation.d (U.ι.app W a)))) =
    b • N.presheaf.map (homOfLE hV).op _
  rw [one_smul, hstalk W hz hV a, hφ]

private theorem span_source_local_differentials
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (U : Y.Opens) (z : U) :
    Submodule.span ((U : Scheme).residueField z)
      (Set.range fun i : (Σ W : Y.Opens, {_a : Γ(Y, W) // U.ι z ∈ W}) ↦
        (bertiniLocalFirstJet f U z i.1 i.2.2 i.2.1).2) = ⊤ := by
  classical
  let X : Scheme := U
  let R := X.presheaf.stalk z
  let K := X.residueField z
  let F := U.ι ≫ f
  let : Algebra R K := ((𝟙 X : X ⟶ X).stalkMap z ≫ X.residue z).hom.toAlgebra
  let : Algebra ((Spec (.of k)).presheaf.stalk (F z)) R :=
    (F.stalkMap z).hom.toAlgebra
  let I := Σ W : Y.Opens, {_a : Γ(Y, W) // U.ι z ∈ W}
  let v : I → bertiniCotangentFibre f U z := fun i ↦
    (bertiniLocalFirstJet f U z i.1 i.2.2 i.2.1).2
  let P := Submodule.span K (Set.range v)
  obtain ⟨e, he, _⟩ := Scheme.Hom.existsUnique_relativeDifferentialsStalkEquiv F z
  let E : bertiniCotangentFibre f U z ≃ₗ[K]
      K ⊗[R] CommRingCat.KaehlerDifferential (F.stalkMap z) := e.baseChange R K
  let Q := P.map E.toLinearMap
  have hD (r : R) :
      (1 : K) ⊗ₜ[R] CommRingCat.KaehlerDifferential.d (f := F.stalkMap z) r ∈ Q := by
    obtain ⟨r', hr'⟩ := (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap z)).2 r
    obtain ⟨W, hz, a, rfl⟩ := Y.presheaf.exists_germ_eq r'
    have hr : X.presheaf.germ (U.ι ⁻¹ᵁ W) z hz (U.ι.app W a) = r := by
      rw [← Scheme.Hom.germ_stalkMap_apply]
      exact hr'
    refine ⟨v ⟨W, a, hz⟩, Submodule.subset_span ⟨⟨W, a, hz⟩, rfl⟩, ?_⟩
    change (1 : K) ⊗ₜ[R] e
      (F.relativeDifferentials.presheaf.germ (U.ι ⁻¹ᵁ W) z hz
        (F.relativeDifferentialsDerivation.d (U.ι.app W a))) = _
    rw [he, hr]
  have hall (m : CommRingCat.KaehlerDifferential (F.stalkMap z)) :
      (1 : K) ⊗ₜ[R] m ∈ Q := by
    have hm : m ∈ Submodule.span R
        (Set.range (CommRingCat.KaehlerDifferential.d (f := F.stalkMap z))) := by
      change m ∈ Submodule.span R (Set.range
        (KaehlerDifferential.D ((Spec (.of k)).presheaf.stalk (F z)) R))
      rw [KaehlerDifferential.span_range_derivation]
      exact Submodule.mem_top
    induction hm using Submodule.span_induction with
    | mem m hm => obtain ⟨r, rfl⟩ := hm; exact hD r
    | zero => simpa only [TensorProduct.tmul_zero] using Q.zero_mem
    | add a b ha hb ha' hb' =>
      simpa only [TensorProduct.tmul_add] using Q.add_mem ha' hb'
    | smul a b hb hb' =>
      rw [TensorProduct.tmul_smul]
      exact (Q.restrictScalars R).smul_mem a hb'
  have hQ : Q = ⊤ := by
    apply top_unique
    intro t ht
    clear ht
    induction t using TensorProduct.induction_on with
    | zero => exact Q.zero_mem
    | tmul a m =>
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using Q.smul_mem a (hall m)
    | add a b ha hb => exact Q.add_mem ha hb
  exact (Submodule.map_eq_top_iff (e := E)).mp hQ

private theorem tensor_eq_zero_of_all_coefficients
    {K A M : Type u} [Field K] [CommRing A] [Algebra K A]
    [AddCommGroup M] [Module K M] (t : A ⊗[K] M)
    (ht : ∀ l : M →ₗ[K] K,
      (((Algebra.linearMap K A).comp l).liftBaseChange A) t = 0) : t = 0 := by
  classical
  let b := Module.Free.chooseBasis K M
  apply (b.baseChange A).forall_coord_eq_zero_iff.mp
  intro i
  have hi : (b.baseChange A).coord i =
      ((Algebra.linearMap K A).comp (b.coord i)).liftBaseChange A := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a m
    simp only [Module.Basis.coord_apply, Module.Basis.baseChange_repr_tmul,
      LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, Algebra.linearMap_apply,
      Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  rw [hi]
  exact ht (b.coord i)

/-- A comparison map satisfying the source-fibre differential formula is injective.

Source: Stacks Project, Morphisms, lemma-base-change-differentials (Tag 01V0),
and Sheaves, Tag 0098. The proof uses the relative differential stalk comparison
and extension of individual cotangent functionals.
(blueprint: lem-zl-source-fibre-differential-injective).

Proof: Differential germs of source-local functions span the cotangent fibre: lift
stalk elements through the open immersion, use the Kaehler differential generators,
and then extend scalars to the residue field. For each linear functional l on this
fibre, extend it geometrically to L on the pulled-back differential sections.
The formula for D implies that L composed with D is the scalar extension of l,
first on the spanning differential germs and then everywhere. A tensor killed by D
is therefore killed by every scalar-extended functional. Apply this to the coordinate
functionals of any basis: the base-changed basis coordinates all vanish, so the tensor
is zero. No finite-dimensionality assumption is used in this argument.
-/
theorem source_fibre_differential_injective_of_formula
    {k : Type u} [Field k] {Y B T : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [Smooth f] (c : B ⟶ Spec (.of k))
    (U : Y.Opens) (z : U)
    (h : T ⟶ Spec ((U : Scheme).residueField z)) (g : T ⟶ pullback c f)
    (hg : g ≫ pullback.snd c f = h ≫ (U : Scheme).fromSpecResidueField z ≫ U.ι)
    (α : (U : Scheme).residueField z →+* Γ(T, ⊤))
    (hα : α = ((Scheme.ΓSpecIso ((U : Scheme).residueField z)).inv ≫ h.appTop).hom)
    (D : let K := (U : Scheme).residueField z
      let A := Γ(T, ⊤)
      letI : Algebra K A := α.toAlgebra
      (A ⊗[K] bertiniCotangentFibre f U z) →ₗ[A]
        Γ((Scheme.Modules.tensorPullback g).obj (pullback.fst c f).relativeDifferentials, ⊤))
    (hD : let K := (U : Scheme).residueField z
      let A := Γ(T, ⊤)
      letI : Algebra K A := α.toAlgebra
      ∀ (W : Y.Opens) (hz : U.ι z ∈ W)
        (hV : (⊤ : T.Opens) ≤ g ⁻¹ᵁ ((pullback.snd c f) ⁻¹ᵁ W))
        (a : Γ(Y, W)) (b : A),
        D (b ⊗ₜ[K] (bertiniLocalFirstJet f U z W hz a).2) =
          b • ((Scheme.Modules.tensorPullback g).obj
            (pullback.fst c f).relativeDifferentials).presheaf.map (homOfLE hV).op
              (Scheme.Modules.tensorPullbackSection g (pullback.fst c f).relativeDifferentials
                ((pullback.snd c f) ⁻¹ᵁ W)
                ((pullback.fst c f).relativeDifferentialsDerivation.d
                  (X := Opposite.op ((pullback.snd c f) ⁻¹ᵁ W))
                  ((pullback.snd c f).app W a)))) :
    let K := (U : Scheme).residueField z
    let A := Γ(T, ⊤)
    letI : Algebra K A := α.toAlgebra
    Function.Injective D := by
  dsimp only
  let K := (U : Scheme).residueField z
  let A := Γ(T, ⊤)
  let : Algebra K A := α.toAlgebra
  have hV (W : Y.Opens) (hz : U.ι z ∈ W) :
      (⊤ : T.Opens) ≤ g ⁻¹ᵁ ((pullback.snd c f) ⁻¹ᵁ W) := by
    intro t _
    change (g ≫ pullback.snd c f) t ∈ W
    rw [hg]
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using hz
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro t ht
  change t = 0
  apply tensor_eq_zero_of_all_coefficients
  intro l
  obtain ⟨L, hL⟩ := exists_source_fibre_differential_functional f c U z h g hg α hα l
  have hmaps : L.comp D = ((Algebra.linearMap K A).comp l).liftBaseChange A := by
    apply (LinearMap.liftBaseChangeEquiv A).symm.injective
    change _ = (LinearMap.liftBaseChangeEquiv A).symm
      ((LinearMap.liftBaseChangeEquiv A) ((Algebra.linearMap K A).comp l))
    rw [LinearEquiv.symm_apply_apply]
    apply LinearMap.ext_on_range (span_source_local_differentials f U z)
    rintro ⟨W, a, hz⟩
    simp only [LinearMap.liftBaseChangeEquiv_symm_apply, LinearMap.comp_apply]
    change L (D ((1 : A) ⊗ₜ[K] (bertiniLocalFirstJet f U z W hz a).2)) =
      α (l (bertiniLocalFirstJet f U z W hz a).2)
    rw [hD W hz (hV W hz) a 1, one_smul, hL]
  change D t = 0 at ht
  rw [← hmaps, LinearMap.comp_apply, ht, map_zero]


end AlgebraicGeometry

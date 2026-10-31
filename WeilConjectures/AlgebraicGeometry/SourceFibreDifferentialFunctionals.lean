/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BertiniLocalFirstJets
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.RelativeDifferentialSheafBaseChange
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberSections
import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk

/-! # Extending a cotangent functional over a fixed source point

Source: Stacks Project, Morphisms, Tag 01V0, base change of differentials;
Sheaves, Tag 0098, stalks of module pullback.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback
  Scheme.Hom.relativeDifferentials Scheme.Hom.relativeDifferentialsHomEquiv
  Scheme.Hom.relativeDifferentialsDerivation Scheme.Hom.pushforwardDerivation

private theorem residue_appLE {X T : Scheme.{u}} (x : X)
    (h : T ⟶ Spec (X.residueField x)) (W : X.Opens) (hx : x ∈ W)
    (hW : (⊤ : T.Opens) ≤ (h ≫ X.fromSpecResidueField x) ⁻¹ᵁ W) :
    (h ≫ X.fromSpecResidueField x).appLE W ⊤ hW =
      X.evaluation W x hx ≫ (Scheme.ΓSpecIso _).inv ≫ h.appTop := by
  have he : (X.fromSpecResidueField x).appLE W ⊤
      (X.preimage_fromSpecResidueField hx).ge =
      X.evaluation W x hx ≫ (Scheme.ΓSpecIso _).inv := by
    apply (cancel_mono (Scheme.ΓSpecIso _).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact X.fromSpecResidueField_appLE_ΓSpecIso_hom x W hx
  rw [← Category.assoc, ← he,
    ← Scheme.Hom.appLE_top_top_fiberDegree h (by simp),
    Scheme.Hom.appLE_comp_appLE]

-- Evaluation on opens containing the point, and zero on empty inverse images.
private theorem residue_functional {X T : Scheme.{u}} (x : X)
    (h : T ⟶ Spec (X.residueField x)) (M : X.Modules)
    (l : letI : Algebra (X.presheaf.stalk x) (X.residueField x) :=
        ((𝟙 X : X ⟶ X).stalkMap x ≫ X.residue x).hom.toAlgebra
      M.presheaf.stalk x →ₗ[X.presheaf.stalk x] X.residueField x) :
    ∃ φ : M ⟶ (Scheme.Modules.pushforward (h ≫ X.fromSpecResidueField x)).obj
        (SheafOfModules.unit T.ringCatSheaf),
      ∀ (W : X.Opens) (hx : x ∈ W) (m : Γ(M, W)),
        φ.app W m = T.presheaf.map (homOfLE le_top).op
          (((Scheme.ΓSpecIso _).inv ≫ h.appTop)
            (l (M.presheaf.germ W x hx m))) := by
  classical
  let : Algebra (X.presheaf.stalk x) (X.residueField x) :=
    ((𝟙 X : X ⟶ X).stalkMap x ≫ X.residue x).hom.toAlgebra
  let r := h ≫ X.fromSpecResidueField x
  let α := ((Scheme.ΓSpecIso (X.residueField x)).inv ≫ h.appTop).hom
  have hres (b : X.presheaf.stalk x) :
      ((𝟙 X : X ⟶ X).stalkMap x ≫ X.residue x) b = X.residue x b := by
    rw [Scheme.Hom.stalkMap_id]
    rfl
  have hr (t : T) : r t = x := by
    simp only [r, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have hempty (W : X.Opens) (hx : x ∉ W) : r ⁻¹ᵁ W = ⊥ := by
    ext t
    change (r t ∈ W) ↔ False
    rw [hr]
    exact iff_false_intro hx
  have hscalar (W : X.Opens) (hx : x ∈ W) (a : Γ(X, W)) :
      r.app W a = T.presheaf.map (homOfLE le_top).op
        (α (X.residue x (X.presheaf.germ W x hx a))) := by
    have hW : (⊤ : T.Opens) ≤ r ⁻¹ᵁ W := by
      intro t _
      change r t ∈ W
      rwa [hr]
    have he := residue_appLE x h W hx hW
    have he' := congrArg (fun f ↦ f ≫
      T.presheaf.map (homOfLE (le_top : r ⁻¹ᵁ W ≤ ⊤)).op) he
    rw [Scheme.Hom.appLE_map] at he'
    change r.appLE W (r ⁻¹ᵁ W) _ = _ at he'
    simpa only [Scheme.Hom.appLE_eq_app, CommRingCat.comp_apply,
      Scheme.evaluation, α, RingHom.comp_apply] using congrArg (fun f ↦ f a) he'
  let F (W : X.Opens) (m : Γ(M, W)) : Γ(T, r ⁻¹ᵁ W) :=
    if hx : x ∈ W then T.presheaf.map (homOfLE le_top).op
      (α (l (M.presheaf.germ W x hx m))) else 0
  have hF (W : X.Opens) (hx : x ∈ W) (m : Γ(M, W)) :
      F W m = T.presheaf.map (homOfLE le_top).op
        (α (l (M.presheaf.germ W x hx m))) := dif_pos hx
  let φ : M ⟶ (Scheme.Modules.pushforward r).obj
      (SheafOfModules.unit T.ringCatSheaf) :=
    ⟨PresheafOfModules.homMk
      { app := fun W ↦ AddCommGrpCat.ofHom
          { toFun := F W.unop
            map_zero' := by
              by_cases hx : x ∈ W.unop
              · simp only [hF _ hx, map_zero]
              · simp only [F, dif_neg hx]
            map_add' := by
              intro m n
              by_cases hx : x ∈ W.unop
              · simp only [hF _ hx, map_add]
              · simp only [F, dif_neg hx, add_zero] }
        naturality := by
          intro V W i
          ext m
          change Γ(M, V.unop) at m
          by_cases hx : x ∈ W.unop
          · have hxV : x ∈ V.unop := i.unop.le hx
            change F W.unop (M.presheaf.map i m) =
              T.presheaf.map ((TopologicalSpace.Opens.map r.base).map i.unop).op
                (F V.unop m)
            rw [hF _ hx, hF _ hxV]
            erw [M.presheaf.germ_res_apply' i x hx]
            have hm : T.presheaf.map (homOfLE (le_top : r ⁻¹ᵁ V.unop ≤ ⊤)).op ≫
                T.presheaf.map ((TopologicalSpace.Opens.map r.base).map i.unop).op =
                T.presheaf.map (homOfLE (le_top : r ⁻¹ᵁ W.unop ≤ ⊤)).op := by
              rw [← Functor.map_comp]
              rfl
            exact (congrArg (fun f ↦ f (α (l (M.presheaf.germ V.unop x hxV m)))) hm).symm
          · have : Subsingleton Γ(T, r ⁻¹ᵁ W.unop) := by
              rw [hempty _ hx]
              infer_instance
            exact @Subsingleton.elim Γ(T, r ⁻¹ᵁ W.unop) this _ _ }
      (by
        intro W a m
        by_cases hx : x ∈ W.unop
        · change F W.unop (a • m) = r.app W.unop a * F W.unop m
          rw [hF _ hx, hF _ hx, Scheme.Modules.germ_smul, l.map_smul]
          change T.presheaf.map (homOfLE le_top).op
              (α (((𝟙 X : X ⟶ X).stalkMap x ≫ X.residue x)
                (X.presheaf.germ W.unop x hx a) *
                l (M.presheaf.germ W.unop x hx m))) = _
          rw [hres]
          rw [map_mul, map_mul, hscalar W.unop hx a]
        · have : Subsingleton Γ(T, r ⁻¹ᵁ W.unop) := by
            rw [hempty _ hx]
            infer_instance
          exact @Subsingleton.elim Γ(T, r ⁻¹ᵁ W.unop) this _ _)⟩
  exact ⟨φ, hF⟩

private theorem adjoint_section {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (N : X.Modules) (φ : M ⟶ (Scheme.Modules.pushforward g).obj N)
    (W : Y.Opens) (V : X.Opens) (hV : V ≤ g ⁻¹ᵁ W) (m : Γ(M, W)) :
    let ψ := ((Scheme.Modules.tensorPullbackSectionAdjunction g).homEquiv M N).symm φ
    ψ.app V (((Scheme.Modules.tensorPullback g).obj M).presheaf.map (homOfLE hV).op
      (Scheme.Modules.tensorPullbackSection g M W m)) =
      N.presheaf.map (homOfLE hV).op (φ.app W m) := by
  dsimp only
  let adj := Scheme.Modules.tensorPullbackSectionAdjunction g
  let ψ := (adj.homEquiv M N).symm φ
  have hunit : (adj.unit.app M).app W m =
      Scheme.Modules.tensorPullbackSection g M W m :=
    (Classical.choose_spec
      (Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction g)).1 M W m
  have he := congrArg (fun a ↦ a.app W m) ((adj.homEquiv M N).apply_symm_apply φ)
  rw [Adjunction.homEquiv_unit] at he
  change ψ.app (g ⁻¹ᵁ W) ((adj.unit.app M).app W m) = φ.app W m at he
  rw [hunit] at he
  change ψ.app V _ = _
  exact (PresheafOfModules.naturality_apply ψ.val (homOfLE hV).op _).trans
    (congrArg (N.presheaf.map (homOfLE hV).op) he)

private theorem pushforward_congr_section {X Y : Scheme.{u}} {g g' : X ⟶ Y}
    (e : g = g') (N : X.Modules) (W : Y.Opens) (V : X.Opens)
    (hV : V ≤ g ⁻¹ᵁ W) (hV' : V ≤ g' ⁻¹ᵁ W)
    (m : Γ((Scheme.Modules.pushforward g).obj N, W)) :
    N.presheaf.map (homOfLE hV').op
      (((Scheme.Modules.pushforwardCongr e).hom.app N).app W m) =
      N.presheaf.map (homOfLE hV).op m := by
  subst g'
  change Γ(N, g ⁻¹ᵁ W) at m
  simp only [Scheme.Modules.pushforwardCongr_hom_app_app, eqToHom_refl, op_id]
  erw [CategoryTheory.Functor.map_id]
  rfl

private theorem baseChange_functional {Y B S : Scheme.{u}} (f : Y ⟶ S) (c : B ⟶ S)
    (N : (pullback f c : Scheme.{u}).Modules)
    (φ : f.relativeDifferentials ⟶
      (Scheme.Modules.pushforward (pullback.fst f c)).obj N) :
    ∃ ψ : (pullback.snd f c).relativeDifferentials ⟶ N,
      ∀ (W : Y.Opens) (a : Γ(Y, W)),
        ψ.app ((pullback.fst f c) ⁻¹ᵁ W)
          ((pullback.snd f c).relativeDifferentialsDerivation.d
            (X := op ((pullback.fst f c) ⁻¹ᵁ W)) ((pullback.fst f c).app W a)) =
          φ.app W (f.relativeDifferentialsDerivation.d (X := op W) a) := by
  obtain ⟨_, _, b, hb, _, hbi, _⟩ := f.relativeDifferentialSheaf_baseChange c
  let := hbi
  let d := ((Scheme.Modules.tensorPullbackSectionAdjunction
    (pullback.fst f c)).homEquiv _ N).symm φ
  refine ⟨inv b ≫ d, ?_⟩
  intro W a
  have he := adjoint_section (pullback.fst f c) f.relativeDifferentials N φ W
    ((pullback.fst f c) ⁻¹ᵁ W) le_rfl
      (f.relativeDifferentialsDerivation.d (X := op W) a)
  simp only [homOfLE_refl, op_id] at he
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id] at he
  change d.app _ ((inv b).app _ _) = _
  rw [← hb W a]
  have hi := congrArg (fun t ↦ t.app ((pullback.fst f c) ⁻¹ᵁ W)
    (Scheme.Modules.tensorPullbackSection (pullback.fst f c) f.relativeDifferentials W
      (f.relativeDifferentialsDerivation.d (X := op W) a))) (IsIso.hom_inv_id b)
  change (inv b).app _ (b.app _ _) = _ at hi
  rw [hi]
  exact he

-- Push the differential morphism through the symmetry of the fibre product.
private theorem transport_functional {P Q Y B T : Scheme.{u}}
    (bP : P ⟶ B) (bQ : Q ⟶ B) (a : Q ⟶ P) (hb : a ≫ bP = bQ)
    (q : P ⟶ Y) (p : Q ⟶ Y) (hp : a ≫ q = p)
    (v : T ⟶ Q) (g : T ⟶ P) (hg : v ≫ a = g) (N : T.Modules)
    (φ : bQ.relativeDifferentials ⟶ (Scheme.Modules.pushforward v).obj N) :
    ∃ ψ : bP.relativeDifferentials ⟶ (Scheme.Modules.pushforward g).obj N,
      ∀ (W : Y.Opens) (s : Γ(Y, W))
        (hV : (⊤ : T.Opens) ≤ g ⁻¹ᵁ (q ⁻¹ᵁ W))
        (hV' : (⊤ : T.Opens) ≤ v ⁻¹ᵁ (p ⁻¹ᵁ W)),
        N.presheaf.map (homOfLE hV).op
          (ψ.app (q ⁻¹ᵁ W) (bP.relativeDifferentialsDerivation.d
            (X := op (q ⁻¹ᵁ W)) (q.app W s))) =
        N.presheaf.map (homOfLE hV').op
          (φ.app (p ⁻¹ᵁ W) (bQ.relativeDifferentialsDerivation.d
            (X := op (p ⁻¹ᵁ W)) (p.app W s))) := by
  subst bQ
  subst p
  subst g
  let δ := (bP.relativeDifferentialsHomEquiv _).symm (bP.pushforwardDerivation a)
  let ψ := δ ≫ (Scheme.Modules.pushforward a).map φ ≫
    (Scheme.Modules.pushforwardComp v a).hom.app N
  refine ⟨ψ, ?_⟩
  intro W s hV hV'
  change N.presheaf.map (homOfLE hV).op
      (φ.app (a ⁻¹ᵁ (q ⁻¹ᵁ W))
        (δ.app (q ⁻¹ᵁ W) (bP.relativeDifferentialsDerivation.d (q.app W s)))) = _
  erw [bP.pushforwardDerivation_desc_app_d a]
  rfl

private theorem restrict_top {T : Scheme.{u}} (V : T.Opens)
    (hV : (⊤ : T.Opens) ≤ V) (s : Γ(T, ⊤)) :
    T.presheaf.map (homOfLE hV).op
      (T.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op s) = s := by
  have he : V = ⊤ := top_unique hV
  subst V
  simp

private theorem cotangent_functional {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (U : Y.Opens) (z : U)
    (l : bertiniCotangentFibre f U z →ₗ[(U : Scheme).residueField z]
      (U : Scheme).residueField z) :
    ∃ l' : letI : Algebra ((U : Scheme).presheaf.stalk z) ((U : Scheme).residueField z) :=
        ((𝟙 (U : Scheme) : (U : Scheme) ⟶ (U : Scheme)).stalkMap z ≫
          (U : Scheme).residue z).hom.toAlgebra
        (U.ι ≫ f).relativeDifferentials.presheaf.stalk z →ₗ[(U : Scheme).presheaf.stalk z]
          (U : Scheme).residueField z,
      ∀ (W : Y.Opens) (hz : U.ι z ∈ W) (a : Γ(Y, W)),
        l' ((U.ι ≫ f).relativeDifferentials.presheaf.germ (U.ι ⁻¹ᵁ W) z hz
          ((U.ι ≫ f).relativeDifferentialsDerivation.d
            (X := op (U.ι ⁻¹ᵁ W)) (U.ι.app W a))) =
          l (bertiniLocalFirstJet f U z W hz a).2 := by
  let : Algebra ((U : Scheme).presheaf.stalk z) ((U : Scheme).residueField z) :=
    ((𝟙 (U : Scheme) : (U : Scheme) ⟶ (U : Scheme)).stalkMap z ≫
      (U : Scheme).residue z).hom.toAlgebra
  refine ⟨(LinearMap.liftBaseChangeEquiv ((U : Scheme).residueField z)).symm l, ?_⟩
  intro W hz a
  rfl

/-- A cotangent functional extends to an ordinary linear functional on the sections
of the pulled-back relative differential sheaf. Smoothness and finite dimensionality
are not required, and no comparison map from a tensor product is assumed.

Source: Stacks Project, Morphisms, `lemma-base-change-differentials` (Tag 01V0),
and Sheaves, Tag 0098.
(blueprint: lem-zl-source-fibre-differential-functionals).

Proof: Put K = kappa_U(z), and contract l with the canonical map from the
relative differential stalk to its K-fibre. Construct a sheaf morphism from
Omega_(U/k) to the pushforward of O_T along h followed by the residue-field
point. On an open containing z, apply the stalk functional to the germ, apply
the scalar map K to Gamma(T,O_T), and restrict. On an open missing z, the
inverse image is empty, so use zero. Residue-field evaluation proves linearity;
restriction of germs proves naturality. This realizes the stalk-skyscraper
argument directly, without choosing a skyscraper or comparing pullback stalks.

Compose with the universal differential map from Y to U. The normalized
pullback adjunction and differential base-change isomorphism give a morphism
from Omega_(Y times_k B / B) to the pushforward of O_T. Transport through
pullback symmetry, apply the normalized adjunction along g, and take global
sections. The unit formula, naturality, and the base-change formula on da give
the displayed equality; h_alpha identifies the scalar map. No basis or inverse
comparison of global sections is used. Empty T and zero cotangent fibre are
included in the same construction. -/
theorem exists_source_fibre_differential_functional
    {k : Type u} [Field k] {Y B T : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) (c : B ⟶ Spec (.of k))
    (U : Y.Opens) (z : U)
    (h : T ⟶ Spec ((U : Scheme).residueField z)) (g : T ⟶ pullback c f)
    (hg : g ≫ pullback.snd c f = h ≫ (U : Scheme).fromSpecResidueField z ≫ U.ι)
    (α : (U : Scheme).residueField z →+* Γ(T, ⊤))
    (hα : α = ((Scheme.ΓSpecIso ((U : Scheme).residueField z)).inv ≫ h.appTop).hom)
    (l : bertiniCotangentFibre f U z →ₗ[(U : Scheme).residueField z]
      (U : Scheme).residueField z) :
    ∃ L : Γ((Scheme.Modules.tensorPullback g).obj
        (pullback.fst c f).relativeDifferentials, ⊤) →ₗ[Γ(T, ⊤)] Γ(T, ⊤),
      ∀ (W : Y.Opens) (hz : U.ι z ∈ W)
        (hV : (⊤ : T.Opens) ≤ g ⁻¹ᵁ ((pullback.snd c f) ⁻¹ᵁ W)) (a : Γ(Y, W)),
        L (((Scheme.Modules.tensorPullback g).obj
            (pullback.fst c f).relativeDifferentials).presheaf.map (homOfLE hV).op
              (Scheme.Modules.tensorPullbackSection g (pullback.fst c f).relativeDifferentials
                ((pullback.snd c f) ⁻¹ᵁ W)
                ((pullback.fst c f).relativeDifferentialsDerivation.d
                  (X := Opposite.op ((pullback.snd c f) ⁻¹ᵁ W))
                  ((pullback.snd c f).app W a)))) =
          α (l (bertiniLocalFirstJet f U z W hz a).2) := by
  classical
  let N : T.Modules := SheafOfModules.unit T.ringCatSheaf
  let r : T ⟶ (U : Scheme) := h ≫ (U : Scheme).fromSpecResidueField z
  let e : pullback c f ≅ pullback f c := pullbackSymmetry c f
  let v : T ⟶ pullback f c := g ≫ e.hom
  let p := pullback.fst f c
  let q := pullback.snd c f
  have hvp : v ≫ p = g ≫ q := by
    simp only [v, p, q, e, Category.assoc, pullbackSymmetry_hom_comp_fst]
  have hr : r ≫ U.ι = v ≫ p := by
    rw [hvp]
    exact hg.symm
  obtain ⟨l', hl'⟩ := cotangent_functional f U z l
  obtain ⟨φU, hφU⟩ := residue_functional (X := (U : Scheme)) (T := T)
    z h (U.ι ≫ f).relativeDifferentials l'
  let δ : f.relativeDifferentials ⟶
      (Scheme.Modules.pushforward U.ι).obj (U.ι ≫ f).relativeDifferentials :=
    (f.relativeDifferentialsHomEquiv _).symm (f.pushforwardDerivation U.ι)
  let φ₀ : f.relativeDifferentials ⟶
      (Scheme.Modules.pushforward (r ≫ U.ι)).obj N := δ ≫ (Scheme.Modules.pushforward U.ι).map φU ≫
    (Scheme.Modules.pushforwardComp r U.ι).hom.app N
  let φ₁ : f.relativeDifferentials ⟶
      (Scheme.Modules.pushforward (v ≫ p)).obj N :=
    φ₀ ≫ (Scheme.Modules.pushforwardCongr hr).hom.app N
  let φ : f.relativeDifferentials ⟶
      (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pushforward v).obj N) :=
    φ₁ ≫ (Scheme.Modules.pushforwardComp v p).inv.app N
  have hφ (W : Y.Opens) (hz : U.ι z ∈ W) (a : Γ(Y, W))
      (hV : (⊤ : T.Opens) ≤ v ⁻¹ᵁ (p ⁻¹ᵁ W)) :
      N.presheaf.map (homOfLE hV).op
        (φ.app W (f.relativeDifferentialsDerivation.d (X := op W) a)) =
        α (l (bertiniLocalFirstJet f U z W hz a).2) := by
    have hW : (⊤ : T.Opens) ≤ (r ≫ U.ι) ⁻¹ᵁ W := by
      intro t _
      change U.ι ((U : Scheme).fromSpecResidueField z (h t)) ∈ W
      rwa [Scheme.fromSpecResidueField_apply]
    change N.presheaf.map (homOfLE hV).op
      (((Scheme.Modules.pushforwardCongr hr).hom.app N).app W
        (φ₀.app W (f.relativeDifferentialsDerivation.d (X := op W) a))) = _
    refine (pushforward_congr_section hr N W ⊤ hW hV
      (φ₀.app W (f.relativeDifferentialsDerivation.d (X := op W) a))).trans ?_
    change T.presheaf.map (homOfLE hW).op
      (φU.app (U.ι ⁻¹ᵁ W)
        (δ.app W (f.relativeDifferentialsDerivation.d (X := op W) a))) = _
    erw [f.pushforwardDerivation_desc_app_d U.ι, hφU (U.ι ⁻¹ᵁ W) hz]
    erw [restrict_top, hl', hα]
  obtain ⟨φQ, hφQ⟩ := baseChange_functional f c
    ((Scheme.Modules.pushforward v).obj N) φ
  have hb : e.inv ≫ pullback.fst c f = pullback.snd f c := by
    exact pullbackSymmetry_inv_comp_fst c f
  have hp : e.inv ≫ q = p := by
    exact pullbackSymmetry_inv_comp_snd c f
  have hv : v ≫ e.inv = g := by simp [v]
  obtain ⟨φP, hφP⟩ := transport_functional (pullback.fst c f) (pullback.snd f c)
    e.inv hb q p hp v g hv N φQ
  let ψ := ((Scheme.Modules.tensorPullbackSectionAdjunction g).homEquiv _ N).symm φP
  refine ⟨(ψ.val.app (op ⊤)).hom, ?_⟩
  intro W hz hV a
  have hV' : (⊤ : T.Opens) ≤ v ⁻¹ᵁ (p ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, hvp, Scheme.Hom.comp_preimage]
    exact hV
  have ht := adjoint_section g (pullback.fst c f).relativeDifferentials N φP
    (q ⁻¹ᵁ W) ⊤ hV
      ((pullback.fst c f).relativeDifferentialsDerivation.d
        (X := op (q ⁻¹ᵁ W)) (q.app W a))
  change ψ.app ⊤ _ = _
  exact ht.trans ((hφP W a hV hV').trans (by rw [hφQ W a]; exact hφ W hz a hV'))

end AlgebraicGeometry

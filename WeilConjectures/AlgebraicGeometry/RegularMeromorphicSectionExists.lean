/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.MeromorphicModule
public import WeilConjectures.AlgebraicGeometry.NoEmbeddedPoints
import WeilConjectures.AlgebraicGeometry.MeromorphicSheafGenericProduct
import all WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor

@[expose] public section

universe v

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-!
# Existence of a regular meromorphic section

Source: Stacks Project, Divisors, Tag 02OZ (Lemma 31.5.10, case (3));
(blueprint: lem-sc-regular-meromorphic-section-exists).
-/

set_option backward.isDefEq.respectTransparency false in
private theorem unit_stalk_iso (X : Scheme.{v}) (x : X) :
    ∃ e : (unit X).presheaf.stalk x ≃ₗ[X.presheaf.stalk x] X.presheaf.stalk x,
      ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
        e ((unit X).presheaf.germ U x hx r) = X.presheaf.germ U x hx r := by
  let D := (TopologicalSpace.OpenNhds.inclusion x).op ⋙ X.presheaf
  let A := forget₂ CommRingCat.{v} RingCat.{v} ⋙
    forget₂ RingCat.{v} AddCommGrpCat.{v}
  let e : ↑(TopCat.Presheaf.stalk (C := Ab.{v})
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf x) ≃+ X.presheaf.stalk x :=
    (preservesColimitIso A D).symm.addCommGroupIsoToAddEquiv
  have hg (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) :
      e (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r := by
    change (CategoryTheory.Limits.colimit.ι (D ⋙ A)
      (Opposite.op (⟨U, hx⟩ : TopologicalSpace.OpenNhds x)) ≫
      (preservesColimitIso A D).inv) r = _
    rw [ι_preservesColimitIso_inv]
    rfl
  let f : (unit X).presheaf.stalk x →ₗ[X.presheaf.stalk x] X.presheaf.stalk x :=
    { e.toAddMonoidHom with
      map_smul' := by
        intro r m
        obtain ⟨U, hxU, r, rfl⟩ := X.presheaf.exists_germ_eq r
        obtain ⟨V, hxV, m, rfl⟩ :=
          TopCat.Presheaf.exists_germ_eq
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf m
        have hx : x ∈ U ⊓ V := ⟨hxU, hxV⟩
        rw [← X.presheaf.germ_res_apply (homOfLE inf_le_left) x hx r,
          ← TopCat.Presheaf.germ_res_apply
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf
            (homOfLE inf_le_right) x hx m,
          ← PresheafOfModules.germ_smul (R := X.presheaf)]
        let r' := X.presheaf.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op r
        let m' : Γ(X, U ⊓ V) :=
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf.map
            (homOfLE inf_le_right : U ⊓ V ⟶ V).op m
        change e (TopCat.Presheaf.germ
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf (U ⊓ V) x hx (r' * m')) =
          X.presheaf.germ (U ⊓ V) x hx r' * (e (TopCat.Presheaf.germ
            (SheafOfModules.unit X.ringCatSheaf).val.presheaf (U ⊓ V) x hx m') :
              X.presheaf.stalk x)
        rw [hg, hg]
        exact map_mul (X.presheaf.germ (U ⊓ V) x hx).hom _ _ }
  refine ⟨(LinearEquiv.ofBijective f e.bijective), ?_⟩
  exact hg

set_option backward.isDefEq.respectTransparency false in
private theorem normalized_stalk_smul {X : Scheme.{v}} {M N : X.Modules}
    (φ : M ⟶ N) (x : X) {A : Type v} [AddCommGroup A]
    [Module (X.presheaf.stalk x) A] (e : N.presheaf.stalk x ≃+ A)
    (p : M.presheaf.stalk x →ₗ[X.presheaf.stalk x] A)
    (hp : Function.Surjective p)
    (he : ∀ (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U)),
      e (N.presheaf.germ U x hx (φ.app U m)) = p (M.presheaf.germ U x hx m))
    (r : X.presheaf.stalk x) (n : N.presheaf.stalk x) :
    e (r • n) = r • e n := by
  have hc (m : M.presheaf.stalk x) : e (φ.stalkLinearMap x m) = p m := by
    obtain ⟨U, hx, m, rfl⟩ := M.presheaf.exists_germ_eq m
    rw [Hom.stalkLinearMap_germ]
    exact he U hx m
  obtain ⟨m, hm⟩ := hp (e n)
  have hn : φ.stalkLinearMap x m = n := e.injective ((hc m).trans hm)
  rw [← hn, ← (φ.stalkLinearMap x).map_smul, hc, p.map_smul, hc]

set_option backward.isDefEq.respectTransparency false in
/-- For a proper locally Noetherian finite-dimensional scheme without embedded points, every
invertible module has a regular meromorphic section. The canonical map is represented by
`meromorphicSectionMap`, and regularity means that this map is a monomorphism.
Source: Stacks Project, Divisors, Tag 02OZ (Lemma 31.5.10, case (3));
(blueprint: lem-sc-regular-meromorphic-section-exists).
Proof: choose generators at generic points using Tag 0EMH and check injectivity componentwise;
these are the two proof steps recorded in the DAG, using
lem-sc-meromorphic-sheaf-generic-product and def-sc-invertible-module. -/
theorem exists_regularMeromorphicSection
    {k : Type v} [Field k] (X : Scheme.{v})
    [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    [IsLocallyNoetherian X]
    [NoEmbeddedPoints X]
    (hfinite : topologicalKrullDim X ≠ ⊤)
    (L : X.Modules) [L.IsInvertible] :
    ∃ s : unit X ⟶ meromorphicModule X L,
      Mono (meromorphicSectionMap X L s) := by
  have _hfinite := hfinite
  classical
  have hno : ∀ x : X,
      (∃ a : X.presheaf.stalk x, IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
        (⊥ : Submodule (X.presheaf.stalk x) (X.presheaf.stalk x)).colon {a}) →
      x ∈ genericPoints X := by
    intro x hx
    apply NoEmbeddedPoints.associatedPoints_are_generic x
    change IsAssociatedPrime (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
      (X.presheaf.stalk x)
    exact isAssociatedPrime_iff.mpr ⟨inferInstance, hx⟩
  obtain ⟨eK, eL, mul, hK, hL, bK, bL, _⟩ :=
    meromorphicSheaf_generic_product hno L
  let K := meromorphicModule X (unit X)
  let N := meromorphicModule X L
  have hk (η : {x : X // x ∈ genericPoints X})
      (r : X.presheaf.stalk η.val) (a : K.presheaf.stalk η.val) :
      eK η (r • a) = r • eK η a := by
    obtain ⟨p, hp⟩ := unit_stalk_iso X η.val
    exact normalized_stalk_smul (toMeromorphicModule X (unit X)) η.val (eK η)
      p.toLinearMap p.surjective (by
        intro U hx m
        exact (hK η U hx m).trans (hp U hx m).symm) r a
  have hl (η : {x : X // x ∈ genericPoints X})
      (r : X.presheaf.stalk η.val) (a : N.presheaf.stalk η.val) :
      eL η (r • a) = r • eL η a := by
    exact normalized_stalk_smul (toMeromorphicModule X L) η.val (eL η)
      LinearMap.id Function.surjective_id (hL η) r a
  have hg (x : X) : ∃ g : L.presheaf.stalk x,
      Function.Bijective (fun r : X.presheaf.stalk x ↦ r • g) := by
    have : SheafOfModules.IsInvertible.{v, v, v} L :=
      IsInvertible.sheafOfModules_isInvertible L
    obtain ⟨U, hx, _, g, hg⟩ := exists_isFreeGenerator L (x := x) (W := ⊤) trivial
    exact ⟨L.presheaf.germ U.1 x hx g, Scheme.Modules.stalk_generator_bijective hg x hx⟩
  choose g hg using hg
  let qK (U : X.Opens) (a : Γ(K, U)) :
      (η : {x : X // x ∈ genericPoints X ∧ x ∈ U}) → X.presheaf.stalk η.val :=
    fun η ↦ eK ⟨η.val, η.property.1⟩ (K.presheaf.germ U η.val η.property.2 a)
  let qL (U : X.Opens) (a : Γ(N, U)) :
      (η : {x : X // x ∈ genericPoints X ∧ x ∈ U}) → L.presheaf.stalk η.val :=
    fun η ↦ eL ⟨η.val, η.property.1⟩ (N.presheaf.germ U η.val η.property.2 a)
  let E (U : X.Opens) := Equiv.ofBijective (qL U) (bL U)
  let f (U : X.Opens) (a : Γ(K, U)) : Γ(N, U) :=
    (E U).symm (fun η ↦ qK U a η • g η.val)
  have hf (U : X.Opens) (a : Γ(K, U))
      (η : {x : X // x ∈ genericPoints X ∧ x ∈ U}) :
      qL U (f U a) η = qK U a η • g η.val := by
    exact congrFun ((E U).apply_symm_apply _) η
  have hinj (U : X.Opens) : Function.Injective (f U) := by
    intro a b hab
    apply (bK U).injective
    funext η
    apply (hg η.val).injective
    change qK U a η • g η.val = qK U b η • g η.val
    rw [← hf, ← hf, hab]
  let F : K ⟶ N :=
    { val :=
        { app := fun U ↦ ModuleCat.ofHom (X := K.val.obj U) (Y := N.val.obj U)
            { toFun := f U.unop
              map_add' := by
                intro a b
                apply (bL U.unop).injective
                funext η
                change qL U.unop (f U.unop (a + b)) η =
                  qL U.unop (f U.unop a + f U.unop b) η
                rw [hf]
                have hadd (a b : Γ(N, U.unop)) :
                    qL U.unop (a + b) η = qL U.unop a η + qL U.unop b η := by
                  simp only [qL, map_add]
                rw [hadd, hf, hf]
                simp only [qK, map_add, add_smul]
              map_smul' := by
                intro r a
                let r' : Γ(X, U.unop) := r
                change f U.unop (r' • a) = r' • f U.unop a
                apply (bL U.unop).injective
                funext η
                change qL U.unop (f U.unop (r' • a)) η =
                  qL U.unop (r' • f U.unop a) η
                rw [hf]
                have hs (b : Γ(N, U.unop)) :
                    qL U.unop (r' • b) η = X.presheaf.germ U.unop η.val η.property.2 r' •
                      qL U.unop b η := by
                  simp only [qL, germ_smul, hl]
                rw [hs, hf]
                dsimp only [qK]
                rw [germ_smul K η.val η.property.2 r' a, hk]
                exact mul_smul _ _ _ }
          naturality := by
            intro U V i
            ext a
            let a' : Γ(K, U.unop) := a
            change f V.unop (K.presheaf.map i a') = N.presheaf.map i (f U.unop a')
            apply (bL V.unop).injective
            funext η
            symm
            change qL V.unop (N.presheaf.map i (f U.unop a')) η =
              qL V.unop (f V.unop (K.presheaf.map i a')) η
            rw [hf]
            dsimp only [qL, qK]
            have hN := N.presheaf.germ_res_apply i.unop η.val η.property.2 (f U.unop a')
            have hK' := K.presheaf.germ_res_apply i.unop η.val η.property.2 a'
            simp only [Quiver.Hom.op_unop] at hN hK'
            rw [hN, hK']
            exact hf U.unop a' ⟨η.val, η.property.1, i.unop.le η.property.2⟩ } }
  have hmono : Mono F := by
    constructor
    intro Z a b hab
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.Hom.ext
    funext U
    ext z
    apply hinj U.unop
    change F.val.app U (a.val.app U z) = F.val.app U (b.val.app U z)
    exact congrArg (fun t : Z ⟶ N ↦ t.val.app U z) hab
  let s : unit X ⟶ N := toMeromorphicModule X (unit X) ≫ F
  refine ⟨s, ?_⟩
  have hF : meromorphicSectionMap X L s = F := by
    apply (exists_meromorphicSectionMap X L s).unique
    · exact (exists_meromorphicSectionMap X L s).exists.choose_spec
    · rfl
  rw [hF]
  exact hmono

end AlgebraicGeometry

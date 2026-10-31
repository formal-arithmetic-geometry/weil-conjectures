/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.LineProjFractionChartData
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import Mathlib.RingTheory.LocalRing.Basic

/-! # The positive-degree generation locus -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.Modules

/-- A local free generator stays a basis on stalks, by representing germs on smaller opens. -/
private theorem lineProj_stalk_generator_bijective {Y : Scheme.{u}} {L : Y.Modules}
    {U : Y.Opens} {e : Γ(L, U)} (he : IsFreeGenerator e) (x : Y) (hx : x ∈ U) :
    Function.Bijective (fun a : Y.presheaf.stalk x ↦
      a • L.presheaf.germ U x hx e) := by
  constructor
  · intro a b hab
    obtain ⟨V, hVU, hxV, r, hr⟩ := Y.presheaf.exists_le_germ_eq a hx
    obtain ⟨W, hWU, hxW, t, ht⟩ := Y.presheaf.exists_le_germ_eq b hx
    have hge (Z : Y.Opens) (hZU : Z ≤ U) (hxZ : x ∈ Z) (c : Γ(Y, Z)) :
        L.presheaf.germ Z x hxZ (c • L.presheaf.map (homOfLE hZU).op e) =
          Y.presheaf.germ Z x hxZ c • L.presheaf.germ U x hx e := by
      rw [germ_smul L, L.presheaf.germ_res_apply]
    have hab' := hab
    dsimp only at hab'
    rw [← hr, ← ht, ← hge V hVU hxV r, ← hge W hWU hxW t] at hab'
    obtain ⟨Z, hxZ, iV, iW, hZ⟩ := L.presheaf.germ_eq x hxV hxW _ _ hab'
    rw [map_smul, map_smul, presheaf_map_map_apply, presheaf_map_map_apply] at hZ
    have hrt := ((he.map ((leOfHom iV).trans hVU)).smul_left_injective hZ)
    have hg := congrArg (Y.presheaf.germ Z x hxZ) hrt
    rw [Y.presheaf.germ_res_apply, Y.presheaf.germ_res_apply, hr, ht] at hg
    exact hg
  · intro m
    obtain ⟨V, hVU, hxV, t, ht⟩ := L.presheaf.exists_le_germ_eq m hx
    obtain ⟨a, ha⟩ := (he V hVU).2 t
    refine ⟨Y.presheaf.germ V x hxV a, ?_⟩
    rw [← ht, ← ha, germ_smul L, L.presheaf.germ_res_apply]

/-- Membership in the ambient generator open is equivalent to a local free generator.
Source: Stacks Project, Modules, Tag 01CY, locality of the generating locus.
(blueprint: lem-trf-line-proj-generation-locus). -/
theorem lineProj_mem_generator_open {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (s : Γ(M, U)) (x : X) :
    x ∈ U ⊓ U.ι ''ᵁ generatingLocus
        ((M.restrictAppIso U.ι ⊤).inv
          (M.presheaf.map (eqToHom U.ι_image_top).op s)) ↔
      ∃ (B : X.Opens) (hB : B ≤ U), x ∈ B ∧
        IsFreeGenerator (M.presheaf.map (homOfLE hB).op s) := by
  have hsec (B : U.toScheme.Opens) :
      (M.restrict U.ι).presheaf.map (homOfLE (le_top : B ≤ ⊤)).op
          ((M.restrictAppIso U.ι ⊤).inv
            (M.presheaf.map (eqToHom U.ι_image_top).op s)) =
        M.presheaf.map (homOfLE (show U.ι ''ᵁ B ≤ U by
          simpa using U.ι.image_le_opensRange B)).op s := by
    have h := ConcreteCategory.congr_hom
      (M.restrictAppIso_inv_map U.ι (homOfLE (le_top : B ≤ ⊤)).op)
      (M.presheaf.map (eqToHom U.ι_image_top).op s)
    change _ = M.presheaf.map
      (homOfLE (show U.ι ''ᵁ B ≤ U by
        simpa using U.ι.image_le_opensRange B)).op s
    simp only [ConcreteCategory.comp_apply] at h
    trans (M.restrictAppIso U.ι B).inv
      (M.presheaf.map (homOfLE (U.ι.image_mono (le_top : B ≤ ⊤))).op
        (M.presheaf.map (eqToHom U.ι_image_top).op s))
    · exact h
    change M.presheaf.map (homOfLE (U.ι.image_mono (le_top : B ≤ ⊤))).op
      (M.presheaf.map (eqToHom U.ι_image_top).op s) = _
    rw [presheaf_map_map_apply]
    rfl
  constructor
  · rintro ⟨hxU, y, hy, rfl⟩
    obtain ⟨B, hyB, hB⟩ := hy
    rw [hsec B] at hB
    exact ⟨U.ι ''ᵁ B, by simpa using U.ι.image_le_opensRange B,
      ⟨y, hyB, rfl⟩, (isFreeGenerator_restrict_iff U.ι M _).mp hB⟩
  · rintro ⟨B, hBU, hxB, he⟩
    have hxU := hBU hxB
    refine ⟨hxU, ⟨x, hxU⟩, ?_, rfl⟩
    refine ⟨U.ι ⁻¹ᵁ B, hxB, ?_⟩
    rw [hsec]
    apply (isFreeGenerator_restrict_iff U.ι M _).mpr
    have hle : U.ι ''ᵁ (U.ι ⁻¹ᵁ B) ≤ B := by
      rw [U.ι.image_preimage_eq_opensRange_inf B]
      exact inf_le_right
    simpa only [presheaf_map_homOfLE_map_homOfLE] using he.map hle

private theorem lineProj_local_generator_iff {X : Scheme.{u}} (M : X.Modules)
    [M.IsInvertible] (U : X.Opens) (s : Γ(M, U)) (x : X) (hx : x ∈ U) :
    (∃ (B : X.Opens) (hB : B ≤ U), x ∈ B ∧
      IsFreeGenerator (M.presheaf.map (homOfLE hB).op s)) ↔
      Function.Bijective (fun r : X.presheaf.stalk x ↦
        r • M.presheaf.germ U x hx s) := by
  constructor
  · rintro ⟨B, hB, hxB, he⟩
    have h := lineProj_stalk_generator_bijective he x hxB
    simpa only [M.presheaf.germ_res_apply] using h
  · intro hs
    have : SheafOfModules.IsInvertible.{u, u, u} M :=
      IsInvertible.sheafOfModules_isInvertible M
    obtain ⟨B, hxB, hBU, e, he⟩ := exists_isFreeGenerator M hx
    obtain ⟨c, hc⟩ := he.exists_smul_eq (M.presheaf.map (homOfLE hBU).op s)
    obtain ⟨r, hr⟩ := hs.2 (M.presheaf.germ B.1 x hxB e)
    have he' := lineProj_stalk_generator_bijective he x hxB
    have hgs : M.presheaf.germ U x hx s =
        X.presheaf.germ B.1 x hxB c • M.presheaf.germ B.1 x hxB e := by
      rw [← M.presheaf.germ_res_apply (homOfLE hBU) x hxB s, ← hc, germ_smul M]
    change r • M.presheaf.germ U x hx s = _ at hr
    rw [hgs, ← mul_smul] at hr
    have hu : IsUnit (X.presheaf.germ B.1 x hxB c) := by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨r, ?_⟩
      rw [mul_comm]
      apply he'.1
      simpa only [one_smul] using hr
    have hxc : x ∈ X.basicOpen c := (X.mem_basicOpen c x hxB).mpr hu
    have hle := X.basicOpen_le c
    refine ⟨X.basicOpen c, hle.trans hBU, hxc, ?_⟩
    have hu' : IsUnit (X.presheaf.map (homOfLE hle).op c) :=
      X.toRingedSpace.isUnit_res_basicOpen c
    have hres : M.presheaf.map (homOfLE (hle.trans hBU)).op s =
        hu'.unit.val • M.presheaf.map (homOfLE hle).op e := by
      rw [← presheaf_map_homOfLE_map_homOfLE hBU hle, ← hc, map_smul]
      rfl
    rw [hres]
    exact (he.map hle).units_smul _

/-- A section that freely generates near every point of an open generates on that open.
Source: Stacks Project, Modules, Tag 01CY, locality of the free-generator property.
(blueprint: lem-trf-line-proj-generation-locus). -/
theorem lineProj_open_generator {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (s : Γ(M, U))
    (G : X.Opens) (hG : G ≤ U)
    (hg : ∀ x ∈ G, ∃ (B : X.Opens) (hB : B ≤ U), x ∈ B ∧
      IsFreeGenerator (M.presheaf.map (homOfLE hB).op s)) :
    IsFreeGenerator (M.presheaf.map (homOfLE hG).op s) := by
  let S : Sieve G :=
    ⟨fun B i ↦ IsFreeGenerator
      (M.presheaf.map (homOfLE (i.le.trans hG)).op s), by
      intro B C i hi j
      simpa only [presheaf_map_homOfLE_map_homOfLE] using hi.map j.le⟩
  apply isFreeGenerator_of_mem _ (S := S)
  · intro x hx
    obtain ⟨B, hB, hxB, he⟩ := hg x hx
    refine ⟨B ⊓ G, homOfLE inf_le_right, ?_, hxB, hx⟩
    simpa only [presheaf_map_homOfLE_map_homOfLE] using
      (he.map (inf_le_left : B ⊓ G ≤ B))
  · intro B i hi
    change IsFreeGenerator
      (M.presheaf.map (homOfLE (i.le.trans hG)).op s) at hi
    change IsFreeGenerator
      (M.presheaf.map (homOfLE i.le).op
        (M.presheaf.map (homOfLE hG).op s))
    simpa only [presheaf_map_homOfLE_map_homOfLE] using hi

/-- A homogeneous image generates near a point exactly when its germ is a basis.
Source: Stacks, Modules, the open locus where a section generates an invertible module;
Constructions, Tag 01O9.
(blueprint: lem-trf-line-proj-generation-locus). -/
theorem lineProj_generator_stalk {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules) [L.IsInvertible]
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n)
    (V : T.affineOpens) (d : ℕ) (a : Γ(A.piece d, V.1)) (x : W) :
    x ∈ lineProjGeneratorOpen f A L ψ V d a ↔
      ∃ hx : x ∈ f ⁻¹ᵁ V.1,
        Function.Bijective fun r : W.presheaf.stalk x ↦
          r • (L.tensorPow d).presheaf.germ (f ⁻¹ᵁ V.1) x hx
            (lineProjImage f A L ψ V.1 d a) := by
  rw [lineProjGeneratorOpen, lineProj_mem_generator_open]
  constructor
  · rintro ⟨B, hB, hxB, he⟩
    exact ⟨hB hxB, (lineProj_local_generator_iff _ _ _ _ _).mp ⟨B, hB, hxB, he⟩⟩
  · rintro ⟨hx, hs⟩
    exact (lineProj_local_generator_iff _ _ _ _ hx).mpr hs

/-- Images of affine homogeneous sections detect stalkwise positive-degree generation.

Source: Stacks Project, Constructions, Tag 01O9, definition of U(psi) and property (2);
Schemes, Tags 01I9 and 01IA, quasi-coherent affine pullback sections.
(blueprint: lem-trf-line-proj-generation-locus).

Proof: A point of a generator open has an element of the pullback stalk whose image
is a basis. Scalar multiples of that element therefore cover the target stalk.
Conversely suppose a positive-degree stalk map is surjective. Trivialize its invertible
target near x and take a preimage of the basis germ. The tensor-pullback stalk comparison
writes that preimage as an element of O_{W,x} tensor_{O_{T,f(x)}} A_{d,f(x)}.
Tensor induction shows that if all images of pure tensors 1 tensor a have nonunit
coefficients, every image has nonunit coefficient: nonunits in a local ring are closed
under addition and multiplication by any scalar. Surjectivity gives the coefficient 1,
a contradiction. Represent the resulting stalk element a by a section on an affine
neighbourhood V of f(x). Its coefficient is a unit, so its image germ is a basis.
The local-generator criterion puts x in the corresponding generator open.
No finite generation or quasi-coherence is needed for this stalk argument.
Empty schemes and zero homogeneous pieces satisfy both implications as stated. -/
theorem lineProj_generation_locus {W T : Scheme.{u}} (f : W ⟶ T)
    (A : RelativeProjAlgebra T) (L : W.Modules) [L.IsInvertible]
    (ψ : ∀ n : ℕ, (tensorPullback f).obj (A.piece n) ⟶ L.tensorPow n) :
    ((⨆ (V : T.affineOpens) (d : ℕ) (_hd : 0 < d) (a : Γ(A.piece d, V.1)),
        lineProjGeneratorOpen f A L ψ V d a : W.Opens) : Set W) =
      {x | ∃ d : ℕ, 0 < d ∧ Function.Surjective
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (ψ d).mapPresheaf)} := by
  classical
  apply Set.ext
  intro x
  simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨V, d, hd, a, hx⟩
    obtain ⟨hxV, hs⟩ := (lineProj_generator_stalk f A L ψ V d a x).mp hx
    refine ⟨d, hd, ?_⟩
    intro t
    obtain ⟨r, hr⟩ := hs.2 t
    refine ⟨r • ((tensorPullback f).obj (A.piece d)).presheaf.germ
      (f ⁻¹ᵁ V.1) x hxV (tensorPullbackSection f (A.piece d) V.1 a), ?_⟩
    change (ψ d).stalkLinearMap x (_ • _) = _
    erw [LinearMap.map_smul, Hom.stalkLinearMap_germ]
    exact hr
  · rintro ⟨d, hd, hs⟩
    have : SheafOfModules.IsInvertible.{u, u, u} (L.tensorPow d) :=
      IsInvertible.sheafOfModules_isInvertible _
    obtain ⟨B, hxB, hB, e, he⟩ :=
      exists_isFreeGenerator (L.tensorPow d) (show x ∈ (⊤ : W.Opens) from trivial)
    let σ : W.presheaf.stalk x ≃ₗ[W.presheaf.stalk x] (L.tensorPow d).presheaf.stalk x :=
      LinearEquiv.ofBijective (LinearMap.toSpanSingleton _ _
        ((L.tensorPow d).presheaf.germ B.1 x hxB e))
          (lineProj_stalk_generator_bijective he x hxB)
    obtain ⟨δ, hδ⟩ := exists_tensorPullback_stalk_iso f x
    let F := σ.symm.toLinearMap.comp
      ((ψ d).stalkLinearMap x |>.comp (δ.inv.app (A.piece d)).hom)
    have hF : Function.Surjective F := by
      exact σ.symm.surjective.comp
        (hs.comp (ConcreteCategory.bijective_of_isIso (δ.inv.app (A.piece d))).2)
    by_contra hn
    have hnu (V : T.affineOpens) (hxV : f x ∈ V.1) (a : Γ(A.piece d, V.1)) :
        ¬ IsUnit (σ.symm ((L.tensorPow d).presheaf.germ (f ⁻¹ᵁ V.1) x hxV
          (lineProjImage f A L ψ V.1 d a))) := by
      intro hu
      apply hn
      refine ⟨V, d, hd, a, (lineProj_generator_stalk f A L ψ V d a x).mpr
        ⟨hxV, ?_⟩⟩
      have hm := IsUnit.isUnit_iff_mulRight_bijective.mp hu
      have heq : (fun r : W.presheaf.stalk x ↦
          r • (L.tensorPow d).presheaf.germ (f ⁻¹ᵁ V.1) x hxV
            (lineProjImage f A L ψ V.1 d a)) =
          σ ∘ (fun r ↦ r * σ.symm ((L.tensorPow d).presheaf.germ
            (f ⁻¹ᵁ V.1) x hxV (lineProjImage f A L ψ V.1 d a))) := by
        funext r
        rw [Function.comp_apply, ← smul_eq_mul, σ.map_smul, σ.apply_symm_apply]
      rw [heq]
      exact σ.bijective.comp hm
    have hnon (t : (ModuleCat.extendScalars (f.stalkMap x).hom).obj
        ((RingedSpace.moduleStalkFunctor T.toRingedSpace (f x)).obj (A.piece d))) :
        F t ∈ nonunits (W.presheaf.stalk x) := by
      induction t using TensorProduct.induction_on with
      | zero => simpa only [map_zero] using (show (0 : W.presheaf.stalk x) ∈
          nonunits (W.presheaf.stalk x) from zero_mem_nonunits.mpr zero_ne_one)
      | tmul r m =>
        change W.presheaf.stalk x at r
        obtain ⟨U, hxU, a, rfl⟩ := (A.piece d).presheaf.exists_germ_eq m
        obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
        let b := (A.piece d).presheaf.map (homOfLE hVU).op a
        have hnorm : F ((1 : W.presheaf.stalk x) ⊗ₜ[_, (f.stalkMap x).hom]
            ((A.piece d).presheaf.germ U (f x) hxU a)) =
            σ.symm ((L.tensorPow d).presheaf.germ (f ⁻¹ᵁ V) x hxV
              (lineProjImage f A L ψ V d b)) := by
          have hp := hδ (A.piece d) V hxV b
          rw [(Classical.choose_spec (exists_tensorPullbackAdjunction f))] at hp
          have hh := congrArg (δ.inv.app (A.piece d)) hp
          rw [← ConcreteCategory.comp_apply, δ.hom_inv_id_app,
            ConcreteCategory.id_apply] at hh
          dsimp only [F, LinearMap.comp_apply, LinearEquiv.coe_coe]
          rw [← (A.piece d).presheaf.germ_res_apply (homOfLE hVU) (f x) hxV a,
            ]
          change σ.symm ((ψ d).stalkLinearMap x
            ((δ.inv.app (A.piece d))
              ((1 : W.presheaf.stalk x) ⊗ₜ[_, (f.stalkMap x).hom]
                (A.piece d).presheaf.germ V (f x) hxV b))) = _
          exact (congrArg (fun z ↦ σ.symm ((ψ d).stalkLinearMap x z)) hh.symm).trans
            (congrArg σ.symm ((ψ d).stalkLinearMap_germ _ _ _))
        have ht : F (r ⊗ₜ[_, (f.stalkMap x).hom]
            ((A.piece d).presheaf.germ U (f x) hxU a)) =
            (r : W.presheaf.stalk x) * F ((1 : W.presheaf.stalk x) ⊗ₜ[_, (f.stalkMap x).hom]
              ((A.piece d).presheaf.germ U (f x) hxU a)) := by
          erw [← smul_eq_mul, ← F.map_smul, TensorProduct.smul_tmul',
            smul_eq_mul, mul_one]
        rw [ht, hnorm]
        exact fun hu ↦ hnu ⟨V, hV⟩ hxV b (isUnit_of_mul_isUnit_right hu)
      | add t t' ht ht' =>
        rw [map_add]
        exact IsLocalRing.nonunits_add ht ht'
    obtain ⟨t, ht⟩ := hF 1
    have hh := hnon t
    rw [ht] at hh
    exact hh isUnit_one

end AlgebraicGeometry.Scheme.Modules

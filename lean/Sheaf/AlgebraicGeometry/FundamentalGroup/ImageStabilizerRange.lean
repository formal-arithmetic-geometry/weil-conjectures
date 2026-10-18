/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
/-!
# Image of the finite étale fundamental-group map

Source: SGA 1, Exposé V, Proposition 6.13 and §7
(blueprint: lem-galois-pi1-finite-etale-image-stabilizer-range).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.PreGaloisCategory
namespace AlgebraicGeometry.Scheme.FiniteEtale
/-- The image of the induced fundamental-group homomorphism is the marked-point stabilizer.
Source: SGA 1, Exposé V, Proposition 6.13, pp. 114–115, and §7, p. 116
(blueprint: lem-galois-pi1-finite-etale-image-stabilizer-range).

Proof (Proposition 6.13 leaves this argument to the reader):
1. Let `P` be the cover `f` and `a` its point `s`. The diagonal section
   `X ⟶ X ×[Y] X` carries the unique point of the terminal fibre to a point over `a`.
   Naturality of the `GX` action fixes this point, and `fundamentalGroupMap_smul`
   carries this equality to `f_*(h) • a = a`. Thus the image lies in the stabilizer.
2. For `g` fixing `a` and a finite étale cover `q : Z ⟶ X`, regard `Z` as a cover
   of `Y` by composition with `f`, using composition of finite and étale morphisms.
   Its fibre over `s` identifies with the subset of its fibre over `s ≫ f` whose
   image under `q` is `a`: both descriptions are morphisms `Spec Ω ⟶ Z` whose
   composite with `q` equals `s`. Naturality along `q` shows that `g` preserves
   this subset. Its inverse fixes `a` too, so the restriction is a bijection.
3. A morphism of covers over `X` is also one over `Y`; naturality over `Y` therefore
   makes the restricted bijections a natural automorphism of `fiber s`. The
   inverse restrictions are its inverse. The equivalence `toAutMulEquiv` produces
   an element `h` of `GX` with precisely these actions.
4. Apply these restrictions to a pullback cover `R ×[Y] X`. Its projection to `R`
   is a morphism over `Y`, and the induced map on the marked subset is exactly
   `pullbackFiberIso f s`. Naturality of `g` along this projection and
   `fundamentalGroupMap_smul` show that `f_*(h)` and `g` act identically on every
   fibre of `Y`. Faithfulness (`toAut_bijective`) gives `f_*(h) = g`, proving the
   reverse inclusion. No passage to locally constant sheaves is needed. -/
theorem fundamentalGroupMap_range_eq_stabilizer_range
    {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) [IsFinite f] [Etale f]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (GX GY : Type u) [Group GX] [TopologicalSpace GX] [IsTopologicalGroup GX]
    [CompactSpace GX] [∀ Q, MulAction GX ((fiber s).obj Q)]
    [IsFundamentalGroup (fiber s) GX]
    [Group GY] [TopologicalSpace GY] [IsTopologicalGroup GY] [CompactSpace GY]
    [∀ P, MulAction GY ((fiber (s ≫ f)).obj P)]
    [IsFundamentalGroup (fiber (s ≫ f)) GY] :
    let P : Y.FiniteEtale := ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩
    let a : (fiber (s ≫ f)).obj P := fiberMk (s ≫ f) P s rfl
    let U := MulAction.stabilizer GY a
    (fundamentalGroupMap (pullbackFiberIso f s) GX GY).range = U := by
  classical
  dsimp only
  let P : Y.FiniteEtale := ⟨Etale.mk f, inferInstanceAs (IsFinite f)⟩
  let a : (fiber (s ≫ f)).obj P := fiberMk (s ≫ f) P s rfl
  let ρ := fundamentalGroupMap (pullbackFiberIso f s) GX GY
  apply le_antisymm
  · rintro g ⟨h, rfl⟩
    change ρ h • a = a
    let T : X.FiniteEtale :=
      ⟨Etale.mk (𝟙 X), inferInstanceAs (IsFinite (𝟙 X))⟩
    let b : (fiber s).obj T := fiberMk s T s (Category.comp_id s)
    let d : T ⟶ (pullback f).obj P :=
      ObjectProperty.homMk (MorphismProperty.Over.homMk
        (Limits.pullback.lift (𝟙 X) (𝟙 X) (by simp [P]))
        (Limits.pullback.lift_snd _ _ _))
    have hb : h • b = b := fiber_ext s (by
      change (h • b).left = s
      have ht := fiber_left_comp s (h • b)
      change (h • b).left ≫ 𝟙 X = s at ht
      exact (Category.comp_id (h • b).left).symm.trans ht)
    have hd : h • (fiber s).map d b = (fiber s).map d b := by
      rw [← IsNaturalSMul.naturality, hb]
    have ha : (pullbackFiberIso f s).hom.app P ((fiber s).map d b) = a := by
      apply fiber_ext
      change (s ≫ Limits.pullback.lift (𝟙 X) (𝟙 X) _) ≫
        Limits.pullback.fst f f = s
      rw [Category.assoc, Limits.pullback.lift_fst, Category.comp_id]
    rw [← ha, fundamentalGroupMap_smul, hd]
  · intro g hg
    change g • a = a at hg
    let push (Q : X.FiniteEtale) : Y.FiniteEtale := by
      have : IsFinite Q.obj.hom := Q.property
      have : Etale Q.obj.hom := Q.obj.prop
      exact ⟨Etale.mk (Q.obj.hom ≫ f), inferInstanceAs (IsFinite (Q.obj.hom ≫ f))⟩
    let incl (Q : X.FiniteEtale) (z : (fiber s).obj Q) :
        (fiber (s ≫ f)).obj (push Q) :=
      fiberMk (s ≫ f) (push Q) z.left (by
        change z.left ≫ Q.obj.hom ≫ f = s ≫ f
        rw [← Category.assoc, fiber_left_comp])
    have incl_inj (Q : X.FiniteEtale) : Function.Injective (incl Q) := by
      intro z w hzw
      exact fiber_ext s (congrArg (fun z ↦ z.left) hzw)
    let proj (Q : X.FiniteEtale) : push Q ⟶ P :=
      ObjectProperty.homMk (MorphismProperty.Over.homMk Q.obj.hom rfl)
    have proj_incl (Q : X.FiniteEtale) (z : (fiber s).obj Q) :
        (fiber (s ≫ f)).map (proj Q) (incl Q z) = a := by
      exact fiber_ext _ (fiber_left_comp s z)
    have preserves (k : GY) (hk : k • a = a) (Q : X.FiniteEtale)
        (z : (fiber s).obj Q) : (k • incl Q z).left ≫ Q.obj.hom = s := by
      have hn := IsNaturalSMul.naturality (F := fiber (s ≫ f)) k (proj Q) (incl Q z)
      rw [proj_incl, hk] at hn
      exact congrArg (fun z ↦ z.left) hn
    let act (k : GY) (hk : k • a = a) (Q : X.FiniteEtale)
        (z : (fiber s).obj Q) : (fiber s).obj Q :=
      fiberMk s Q (k • incl Q z).left (preserves k hk Q z)
    have incl_act (k : GY) (hk : k • a = a) (Q : X.FiniteEtale)
        (z : (fiber s).obj Q) : incl Q (act k hk Q z) = k • incl Q z :=
      fiber_ext _ rfl
    have hgi : g⁻¹ • a = a := by
      rw [inv_smul_eq_iff]
      exact hg.symm
    let e (Q : X.FiniteEtale) : (fiber s).obj Q ≅ (fiber s).obj Q :=
      FintypeCat.equivEquivIso
        { toFun := act g hg Q
          invFun := act g⁻¹ hgi Q
          left_inv := fun z ↦ incl_inj Q (by
            rw [incl_act g⁻¹ hgi, incl_act g hg, inv_smul_smul])
          right_inv := fun z ↦ incl_inj Q (by
            rw [incl_act g hg, incl_act g⁻¹ hgi, smul_inv_smul]) }
    let pushMap {Q R : X.FiniteEtale} (φ : Q ⟶ R) : push Q ⟶ push R :=
      ObjectProperty.homMk (MorphismProperty.Over.homMk φ.hom.left (by
        change φ.hom.left ≫ R.obj.hom ≫ f = Q.obj.hom ≫ f
        rw [← Category.assoc, hom_left_comp]))
    have incl_map {Q R : X.FiniteEtale} (φ : Q ⟶ R) (z : (fiber s).obj Q) :
        incl R ((fiber s).map φ z) = (fiber (s ≫ f)).map (pushMap φ) (incl Q z) :=
      fiber_ext _ rfl
    let σ : fiber s ≅ fiber s := NatIso.ofComponents e (by
      intro Q R φ
      ext z
      apply incl_inj R
      change incl R (act g hg R ((fiber s).map φ z)) =
        incl R ((fiber s).map φ (act g hg Q z))
      rw [incl_act g hg, incl_map, incl_map, incl_act g hg, IsNaturalSMul.naturality])
    obtain ⟨h, hh⟩ := (toAut_bijective (fiber s) GX).surjective σ
    have hact (Q : X.FiniteEtale) (z : (fiber s).obj Q) :
        h • z = act g hg Q z := by
      have he := congrArg (fun σ : Aut (fiber s) ↦ σ.hom.app Q z) hh
      exact he
    refine ⟨h, ?_⟩
    apply (toAut_bijective (fiber (s ≫ f)) GY).injective
    ext R z
    simp only [toAut_hom_app_apply]
    obtain ⟨w, rfl⟩ : ∃ w : (fiber s).obj ((pullback f).obj R),
        (pullbackFiberIso f s).hom.app R w = z :=
      ⟨(pullbackFiberIso f s).inv.app R z,
        ConcreteCategory.congr_hom ((pullbackFiberIso f s).inv_hom_id_app R) z⟩
    rw [fundamentalGroupMap_smul, hact]
    let π : push ((pullback f).obj R) ⟶ R :=
      ObjectProperty.homMk (MorphismProperty.Over.homMk
        (Limits.pullback.fst R.obj.hom f) (Limits.pullback.condition))
    have hπ (v : (fiber s).obj ((pullback f).obj R)) :
        (fiber (s ≫ f)).map π (incl _ v) = (pullbackFiberIso f s).hom.app R v :=
      fiber_ext _ rfl
    rw [← hπ, incl_act g hg, IsNaturalSMul.naturality, hπ]
end AlgebraicGeometry.Scheme.FiniteEtale

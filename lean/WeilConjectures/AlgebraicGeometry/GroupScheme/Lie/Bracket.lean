/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPointsEquiv
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf

/-!
# The bracket on the Lie algebra of a group scheme

The bracket of `Lie(G)` as the mixed term of the commutator of infinitesimal points, the
rescaling of infinitesimal points, and the functoriality of infinitesimal points in the group
scheme.
-/

@[expose] public section

universe u

open CategoryTheory TrivSqZeroExt
open scoped MonObj

namespace AlgebraicGeometry
section InfPoints

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

namespace GrpObj

/-! ### The bracket as the mixed term of the commutator -/

/-- The points of `G` over `S[ε][δ]` reducing to the identity both for `ε = 0` and for `δ = 0`. -/
noncomputable def mixedPoints : Subgroup (Scheme.dualNumbers₂Over S ⟶ G) :=
  (pointsPrecomp G (Scheme.dualNumbersιεOver S)).ker ⊓
    (pointsPrecomp G (Scheme.dualNumbersιδOver S)).ker

theorem mem_mixedPoints {z : Scheme.dualNumbers₂Over S ⟶ G} :
    z ∈ mixedPoints G ↔ Scheme.dualNumbersιεOver S ≫ z = 1 ∧ Scheme.dualNumbersιδOver S ≫ z = 1 :=
  Iff.rfl

/-- The map `μ : infPoints G → mixedPoints G` induced by `η ↦ εδ`. -/
noncomputable def toMixed (v : infPoints G) : mixedPoints G :=
  ⟨Scheme.dualNumbersMulOver S ≫ v.1, by
    have hv := (mem_infPoints G).1 v.2
    rw [mem_mixedPoints, Scheme.dualNumbersιεOver_comp_dualNumbersMulOver_assoc,
      Scheme.dualNumbersιδOver_comp_dualNumbersMulOver_assoc, hv, MonObj.comp_one]
    exact ⟨rfl, rfl⟩⟩

@[simp]
theorem coe_toMixed (v : infPoints G) :
    (toMixed G v : Scheme.dualNumbers₂Over S ⟶ G) = Scheme.dualNumbersMulOver S ≫ v.1 :=
  rfl

private theorem mixed_coefficients (z : mixedPoints G) (U : G.left.Opens)
    (a : Γ(G.left, U)) :
    (z.1.left.app U a).fst.snd = 0 ∧ (z.1.left.app U a).snd.fst = 0 := by
  have hz := (mem_mixedPoints G).mp z.2
  have hε := ConcreteCategory.congr_hom
    (Scheme.Hom.congr_app (congrArg Over.Hom.left hz.1) U) a
  have hδ := ConcreteCategory.congr_hom
    (Scheme.Hom.congr_app (congrArg Over.Hom.left hz.2) U) a
  constructor
  · have h := congrArg snd hε
    change (z.1.left.app U a).fst.snd =
      (DualNumber.mapRingHom (S.presheaf.map _).hom (inl _)).snd at h
    simpa using h
  · have h := congrArg snd hδ
    change (DualNumber.mapRingHom (fstHom Γ(S, z.1.left ⁻¹ᵁ U) Γ(S, z.1.left ⁻¹ᵁ U)
        Γ(S, z.1.left ⁻¹ᵁ U)).toRingHom (z.1.left.app U a)).snd =
      (DualNumber.mapRingHom (S.presheaf.map _).hom (inl _)).snd at h
    simpa using h

private def extractMixed {A R : Type*} [CommRing A] [CommRing R]
    (f : A →+* DualNumber (DualNumber R))
    (hf : ∀ a, (f a).fst.snd = 0 ∧ (f a).snd.fst = 0) : A →+* DualNumber R where
  toFun a := inl (f a).fst.fst + inr (f a).snd.snd
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp only [map_mul, snd_mul, fst_mul, fst_add, snd_add, fst_inl, snd_inl,
        fst_inr, snd_inr, add_zero, zero_add, smul_eq_mul, op_smul_eq_mul,
        (hf a).1, (hf a).2, (hf b).1, (hf b).2, mul_zero]

private noncomputable def mixedRingHom (z : mixedPoints G) (U : G.left.Opens) :
    Γ(G.left, U) →+* DualNumber Γ(S, z.1.left ⁻¹ᵁ U) :=
  extractMixed (z.1.left.app U).hom (mixed_coefficients G z U)

set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def mixedHom (z : mixedPoints G) :
    S.dualNumbers.toPresheafedSpace ⟶ G.left.toPresheafedSpace where
  base := z.1.left.base
  c :=
    { app U := CommRingCat.ofHom (mixedRingHom G z U.unop)
      naturality U V i := by
        ext a
        have h := ConcreteCategory.congr_hom (z.1.left.c.naturality i) a
        change (z.1.left.app V.unop).hom (G.left.presheaf.map i a) =
          DualNumber.mapRingHom (DualNumber.mapRingHom (S.presheaf.map _).hom)
            ((z.1.left.app U.unop).hom a) at h
        change mixedRingHom G z V.unop (G.left.presheaf.map i a) =
          DualNumber.mapRingHom (S.presheaf.map _).hom (mixedRingHom G z U.unop a)
        ext
        · simp only [mixedRingHom, extractMixed, RingHom.coe_mk, MonoidHom.coe_mk,
            OneHom.coe_mk, fst_add, fst_inl, fst_inr, add_zero,
            DualNumber.fst_mapRingHom]
          have hx := congrArg
            (fun x : DualNumber (DualNumber Γ(S, z.1.left ⁻¹ᵁ V.unop)) ↦ x.fst.fst) h
          simp only [DualNumber.mapRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
            OneHom.coe_mk, fst_add, fst_inl, fst_inr, add_zero] at hx
          convert hx using 1 <;> rfl
        · simp only [mixedRingHom, extractMixed, RingHom.coe_mk, MonoidHom.coe_mk,
            OneHom.coe_mk, snd_add, snd_inl, snd_inr, zero_add,
            DualNumber.snd_mapRingHom]
          have hx := congrArg
            (fun x : DualNumber (DualNumber Γ(S, z.1.left ⁻¹ᵁ V.unop)) ↦ x.snd.snd) h
          simp only [DualNumber.mapRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
            OneHom.coe_mk, snd_add, snd_inl, snd_inr, zero_add] at hx
          convert hx using 1 <;> rfl }

private theorem mul_comp_mixedHom (z : mixedPoints G) :
    S.dualNumbersMul.toPshHom ≫ mixedHom G z = z.1.left.toPshHom := by
  refine PresheafedSpace.ext _ _ rfl ?_
  ext U a
  simp only [Functor.comp_obj, Functor.op_obj, eqToHom_refl, Functor.whiskerRight_id',
    TopCat.Presheaf.comp_app, TopCat.Presheaf.pushforward_obj_obj, NatTrans.id_app,
    Category.comp_id]
  change DualNumber.mulRingHom (mixedRingHom G z U a) = z.1.left.app U a
  have h := mixed_coefficients G z U a
  ext <;> simp [mixedRingHom, extractMixed, h.1, h.2] <;> rfl

private noncomputable def mixedPoint (z : mixedPoints G) : S.dualNumbers ⟶ G.left where
  toHom := mixedHom G z
  prop y := by
    have h := PresheafedSpace.stalkMap.comp S.dualNumbersMul.toPshHom (mixedHom G z) y
    rw [PresheafedSpace.stalkMap.congr_hom _ _ (mul_comp_mixedHom G z),
      eqToHom_refl, Category.id_comp] at h
    have := z.1.left.prop y
    rw [h, CommRingCat.hom_comp] at this
    exact @isLocalHom_of_comp _ _ _ _ _ _ _ _ this

private theorem mul_comp_mixedPoint (z : mixedPoints G) :
    S.dualNumbersMul ≫ mixedPoint G z = z.1.left :=
  Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' (mul_comp_mixedHom G z))

private theorem mul_precomp_injective {Y : Scheme.{u}}
    {f g : S.dualNumbers ⟶ Y}
    (h : S.dualNumbersMul ≫ f = S.dualNumbersMul ≫ g) : f = g := by
  have hb : f.base = g.base := congrArg (fun k : S.dualNumbers.dualNumbers ⟶ Y ↦ k.base) h
  apply Scheme.Hom.ext hb
  intro U
  ext a
  have hh := ConcreteCategory.congr_hom (Scheme.Hom.congr_app h.symm U) a
  change DualNumber.mulRingHom (g.app U a) =
    DualNumber.mapRingHom (DualNumber.mapRingHom (S.presheaf.map _).hom)
      (DualNumber.mulRingHom (f.app U a)) at hh
  have hfst := congrArg
    (fun x : DualNumber (DualNumber Γ(S, g ⁻¹ᵁ U)) ↦ x.fst.fst) hh
  have hsnd := congrArg
    (fun x : DualNumber (DualNumber Γ(S, g ⁻¹ᵁ U)) ↦ x.snd.snd) hh
  change DualNumber.mapRingHom (S.presheaf.map _).hom (f.app U a) = g.app U a
  ext
  · simpa only [DualNumber.fst_mulRingHom, fst_inl, DualNumber.fst_mapRingHom] using
      hfst.symm
  · simpa only [DualNumber.snd_mulRingHom, snd_inr, DualNumber.snd_mapRingHom] using
      hsnd.symm

/-- `η ↦ εδ` identifies the infinitesimal points with the points over `S[ε][δ]` trivial for
`ε = 0` and for `δ = 0`: such a point has `z^♯(a) = e^♯(a) + εδ d(a)` for a derivation `d`. -/
theorem toMixed_bijective : Function.Bijective (toMixed G) := by
  constructor
  · intro v w h
    apply Subtype.ext
    apply Over.OverMorphism.ext
    apply mul_precomp_injective
    exact congrArg (fun z : mixedPoints G ↦ z.1.left) h
  · intro z
    have hp : mixedPoint G z ≫ G.hom = S.dualNumbersProj := by
      apply mul_precomp_injective
      rw [← Category.assoc, mul_comp_mixedPoint, Over.w,
        Scheme.dualNumbersMul_comp_proj]
      rfl
    let v : Scheme.dualNumbersOver S ⟶ G := Over.homMk (mixedPoint G z) hp
    have hv : v ∈ infPoints G := by
      rw [mem_infPoints]
      apply Over.OverMorphism.ext
      change S.dualNumbersι ≫ mixedPoint G z = unitSection G
      have hz := congrArg Over.Hom.left ((mem_mixedPoints G).mp z.2).1
      have he : S.dualNumbersProj ≫ S.dualNumbersι ≫ mixedPoint G z =
          S.dualNumbersProj ≫ unitSection G := by
        rw [← Category.assoc, ← Scheme.dualNumbersι_comp_dualNumbersMul, Category.assoc,
          mul_comp_mixedPoint]
        simpa [Scheme.dualNumbersιεOver, Hom.one_def, Over.comp_left,
          Over.toUnit_left, unitSection] using hz
      have h := congrArg (fun k ↦ S.dualNumbersι ≫ k) he
      simpa only [← Category.assoc, Scheme.dualNumbersι_comp_proj, Category.id_comp] using h
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    apply Over.OverMorphism.ext
    exact mul_comp_mixedPoint G z

/-- The infinitesimal points are the mixed points, through `η ↦ εδ`. -/
noncomputable def mixedEquiv : infPoints G ≃ mixedPoints G :=
  Equiv.ofBijective _ (toMixed_bijective G)

/-- The point `v_ε : S[ε][δ] ⟶ G` of an infinitesimal point `v`, through the projection
forgetting `δ`. -/
noncomputable def toε (v : infPoints G) : Scheme.dualNumbers₂Over S ⟶ G :=
  Scheme.dualNumbersProjεOver S ≫ v.1

/-- The point `v_δ : S[ε][δ] ⟶ G` of an infinitesimal point `v`, through the projection
forgetting `ε`. -/
noncomputable def toδ (v : infPoints G) : Scheme.dualNumbers₂Over S ⟶ G :=
  Scheme.dualNumbersProjδOver S ≫ v.1

/-- The commutator `v_ε w_δ v_ε⁻¹ w_δ⁻¹` of two infinitesimal points reduces to the identity both
for `ε = 0` and for `δ = 0`. -/
theorem commutator_mem_mixedPoints (v w : infPoints G) :
    toε G v * toδ G w * (toε G v)⁻¹ * (toδ G w)⁻¹ ∈ mixedPoints G := by
  have hεδ : Scheme.dualNumbersιεOver S ≫ Scheme.dualNumbersProjδOver S =
      CartesianMonoidalCategory.toUnit (Scheme.dualNumbersOver S) ≫
        Scheme.dualNumbersιOver S := by
    ext1
    simp [Scheme.dualNumbersιεOver, Scheme.dualNumbersProjδOver,
      Scheme.dualNumbersιOver, Over.toUnit_left]
  have hδε : Scheme.dualNumbersιδOver S ≫ Scheme.dualNumbersProjεOver S =
      CartesianMonoidalCategory.toUnit (Scheme.dualNumbersOver S) ≫
        Scheme.dualNumbersιOver S := by
    ext1
    simp [Scheme.dualNumbersιδOver, Scheme.dualNumbersProjεOver,
      Scheme.dualNumbersιOver, Over.toUnit_left]
  have hw : Scheme.dualNumbersιεOver S ≫ toδ G w = 1 := by
    rw [toδ, ← Category.assoc, hεδ, Category.assoc, (mem_infPoints G).mp w.2,
      MonObj.comp_one]
  have hv : Scheme.dualNumbersιδOver S ≫ toε G v = 1 := by
    rw [toε, ← Category.assoc, hδε, Category.assoc, (mem_infPoints G).mp v.2,
      MonObj.comp_one]
  rw [mem_mixedPoints]
  simp [MonObj.comp_mul, GrpObj.comp_inv, hw, hv]

/-- The bracket of two infinitesimal points: the mixed term `εδ` of their group commutator
`v_ε w_δ v_ε⁻¹ w_δ⁻¹` over `S[ε][δ]`. It is the restriction to the identity of the commutator
`[ṽ, w̃]` of the left-invariant vector fields extending `v` and `w`. (blueprint: `sk-d-tangent`) -/
noncomputable def infBracket (v w : infPoints G) : infPoints G :=
  (mixedEquiv G).symm ⟨_, commutator_mem_mixedPoints G v w⟩

private theorem toMixed_infBracket (v w : infPoints G) :
    (toMixed G (infBracket G v w) : Scheme.dualNumbers₂Over S ⟶ G) =
      toε G v * toδ G w * (toε G v)⁻¹ * (toδ G w)⁻¹ := by
  exact congrArg Subtype.val ((mixedEquiv G).apply_symm_apply
    ⟨_, commutator_mem_mixedPoints G v w⟩)

/-- The Lie bracket on `Lie(G)`, transported from the infinitesimal points. -/
noncomputable instance : Bracket (Lie G) (Lie G) where
  bracket x y := lieEquiv G (infBracket G ((lieEquiv G).symm x) ((lieEquiv G).symm y))

theorem lie_def (x y : Lie G) :
    ⁅x, y⁆ = lieEquiv G (infBracket G ((lieEquiv G).symm x) ((lieEquiv G).symm y)) :=
  rfl

/-- `Lie(G)` is a Lie ring: the bracket is biadditive, alternating and satisfies the Jacobi
identity, as the commutator of derivations of `𝒪_G`. (blueprint: `sk-d-tangent`) -/
noncomputable instance : LieRing (Lie G) where
  add_lie := by sorry
  lie_add := by sorry
  lie_self := by sorry
  leibniz_lie := by sorry

/-- `Lie(G)` is a Lie algebra over `Γ(S, 𝒪_S)`. (blueprint: `sk-d-tangent`) -/
noncomputable instance : LieAlgebra Γ(S, ⊤) (Lie G) where
  lie_smul := by sorry

/-! ### Rescaling infinitesimal points -/

omit [GrpObj G] in
/-- Multiplying the morphism attached to a derivation by a global function `r` multiplies the
derivation by `r`. -/
theorem homOfDerivation_comp_unitSmul (g : S ⟶ G.left)
    (D : ((Scheme.Modules.pushforward g).obj (Scheme.Modules.unitModule S)).val.Derivation'
      G.hom.pullbackPresheafHom) (r : Γ(S, ⊤)) :
    homOfDerivation G g D ≫ Scheme.Modules.unitSmul r = homOfDerivation G g
      (D.postcomp ((Scheme.Modules.pushforward g).map (Scheme.Modules.unitSmul r)).val) := by
  rw [homOfDerivation, homOfDerivation, ← Adjunction.homEquiv_naturality_right_symm,
    ← PresheafOfModules.Derivation.Universal.desc_comp]
  exact congrArg _ (PresheafOfModules.sheafificationHomEquiv_symm_comp _ _ _).symm

theorem dualNumbersScaleOver_comp_mem_infPoints (r : Γ(S, ⊤))
    {v : Scheme.dualNumbersOver S ⟶ G} (hv : v ∈ infPoints G) :
    Scheme.dualNumbersScaleOver S r ≫ v ∈ infPoints G := by
  rw [mem_infPoints] at hv ⊢
  rw [Scheme.dualNumbersιOver_comp_scaleOver_assoc, hv]

/-- The rescaling `v ↦ v(rε)` of an infinitesimal point by a global function `r`. It is the
multiplication by `r` on the Lie algebra (`toLie_infPointsScale`). -/
noncomputable def infPointsScale (r : Γ(S, ⊤)) (v : infPoints G) : infPoints G :=
  ⟨Scheme.dualNumbersScaleOver S r ≫ v.1, dualNumbersScaleOver_comp_mem_infPoints G r v.2⟩

theorem toLie_infPointsScale (r : Γ(S, ⊤)) (v : infPoints G) :
    toLie G (infPointsScale G r v) = r • toLie G v := by
  rw [Scheme.Modules.homUnit_smul_def, toLie, toLie, Category.assoc, omegaHom_eq_homOfDerivation,
    omegaHom_eq_homOfDerivation, homOfDerivation_comp_unitSmul]
  refine pullbackCongr_inv_comp_homOfDerivation G _ _ _ _ fun {V} a ↦ heq_of_eq ?_
  rw [PresheafOfModules.Derivation.postcomp_d_apply]
  change (DualNumber.scale _ (v.1.left.app V.unop a)).snd =
    (v.1.left.app V.unop a).snd * S.presheaf.map (homOfLE le_top).op r
  rw [DualNumber.snd_scale, mul_comm]
  rfl

theorem lieEquiv_symm_smul (r : Γ(S, ⊤)) (x : Lie G) :
    (lieEquiv G).symm (r • x) = infPointsScale G r ((lieEquiv G).symm x) := by
  rw [Equiv.symm_apply_eq]
  change _ = toLie G _
  rw [toLie_infPointsScale]
  exact congrArg (r • ·) ((lieEquiv G).apply_symm_apply x).symm

/-! ### Functoriality -/

variable {G} {H : Over S} [GrpObj H]

theorem comp_mem_infPoints (f : G ⟶ H) [IsMonHom f] {v : Scheme.dualNumbersOver S ⟶ G}
    (hv : v ∈ infPoints G) : v ≫ f ∈ infPoints H := by
  rw [mem_infPoints] at hv ⊢
  rw [← Category.assoc, hv, MonObj.one_comp]

/-- A homomorphism of group schemes `f : G ⟶ H` maps infinitesimal points to infinitesimal
points: `v ↦ v ≫ f`. -/
noncomputable def infPointsMap (f : G ⟶ H) [IsMonHom f] : infPoints G →* infPoints H :=
  ((IsMonHom.monoidHom f _).comp (infPoints G).subtype).codRestrict (infPoints H)
    fun v ↦ comp_mem_infPoints f v.2

@[simp]
theorem coe_infPointsMap_apply (f : G ⟶ H) [IsMonHom f] (v : infPoints G) :
    (infPointsMap f v : Scheme.dualNumbersOver S ⟶ H) = (v : Scheme.dualNumbersOver S ⟶ G) ≫ f :=
  rfl

/-- A homomorphism of group schemes preserves brackets of infinitesimal points: it preserves
group commutators and commutes with `η ↦ εδ`. -/
theorem infPointsMap_infBracket (f : G ⟶ H) [IsMonHom f] (v w : infPoints G) :
    infPointsMap f (infBracket G v w) = infBracket H (infPointsMap f v) (infPointsMap f w) := by
  apply (toMixed_bijective H).injective
  apply Subtype.ext
  rw [toMixed_infBracket]
  change Scheme.dualNumbersMulOver S ≫
    ((infBracket G v w : Scheme.dualNumbersOver S ⟶ G) ≫ f) = _
  rw [← Category.assoc, ← coe_toMixed, toMixed_infBracket]
  simp only [MonObj.mul_comp, GrpObj.inv_comp, toε, toδ,
    coe_infPointsMap_apply, Category.assoc]

/-- Let `f : G ⟶ H` be a monomorphism of group schemes, a subgroup scheme of `H`. If the
commutators of the points of `H` over `S[ε][δ]` factor through `G`, then the bracket of two
infinitesimal points of `H` comes from `G`: the commutator `v_ε w_δ v_ε⁻¹ w_δ⁻¹` is `c ≫ f` for a
point `c` of `G` over `S[ε][δ]`, which is a mixed point of `G` since `f` is a monomorphism, and
its preimage under `η ↦ εδ` is an infinitesimal point of `G` mapping to `[v, w]`.
(blueprint: `sk-i-restriction`) -/
theorem infBracket_mem_range_infPointsMap (f : G ⟶ H) [IsMonHom f] [Mono f]
    (hf : ∀ a b : Scheme.dualNumbers₂Over S ⟶ H, a * b * a⁻¹ * b⁻¹ ∈ (IsMonHom.monoidHom f _).range)
    (v w : infPoints H) : infBracket H v w ∈ (infPointsMap f).range := by
  obtain ⟨c, hc⟩ := hf (toε H v) (toδ H w)
  change c ≫ f = _ at hc
  have hcomm := (mem_mixedPoints H).mp (commutator_mem_mixedPoints H v w)
  have hcm : c ∈ mixedPoints G := by
    rw [mem_mixedPoints]
    constructor
    · apply (cancel_mono f).mp
      rw [Category.assoc, hc, hcomm.1, MonObj.one_comp]
    · apply (cancel_mono f).mp
      rw [Category.assoc, hc, hcomm.2, MonObj.one_comp]
  let t := (mixedEquiv G).symm ⟨c, hcm⟩
  refine ⟨t, ?_⟩
  apply (toMixed_bijective H).injective
  apply Subtype.ext
  rw [toMixed_infBracket]
  change Scheme.dualNumbersMulOver S ≫ (t.1 ≫ f) = _
  rw [← Category.assoc]
  have ht : Scheme.dualNumbersMulOver S ≫ t.1 = c :=
    congrArg Subtype.val ((mixedEquiv G).apply_symm_apply ⟨c, hcm⟩)
  rw [ht, hc]

end GrpObj

end InfPoints

end AlgebraicGeometry

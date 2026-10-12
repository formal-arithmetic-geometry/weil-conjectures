/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Lie.Basic
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.InfPointsEquiv
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Sheaf.AlgebraicGeometry.GroupScheme.MixedCoefficientDerivation

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

/-- `η ↦ εδ` identifies the infinitesimal points with the points over `S[ε][δ]` trivial for
`ε = 0` and for `δ = 0`: such a point has `z^♯(a) = e^♯(a) + εδ d(a)` for a derivation `d`. -/
theorem toMixed_bijective : Function.Bijective (toMixed G) := by
  refine ⟨?_, ?_⟩
  · intro v w h
    apply Subtype.ext
    apply Over.OverMorphism.ext
    have h' := congrArg (fun x : mixedPoints G ↦ x.val.left) h
    change S.dualNumbersMul ≫ v.val.left = S.dualNumbersMul ≫ w.val.left at h'
    have hb : v.val.left.base = w.val.left.base := congrArg (fun f ↦ f.base) h'
    refine Scheme.Hom.ext hb fun U ↦ ?_
    have hc := Scheme.Hom.congr_app h'.symm U
    ext a : 2
    have ha := ConcreteCategory.congr_hom hc a
    simp only [Scheme.Hom.comp_app, CommRingCat.comp_apply] at ha
    let i : w.val.left ⁻¹ᵁ U ⟶ v.val.left ⁻¹ᵁ U :=
      eqToHom (congrArg (fun f ↦ (TopologicalSpace.Opens.map f).obj U) hb.symm)
    change DualNumber.mulRingHom (w.val.left.app U a) =
      DualNumber.mapRingHom (DualNumber.mapRingHom (S.presheaf.map i.op).hom)
        (DualNumber.mulRingHom (v.val.left.app U a)) at ha
    change DualNumber.mapRingHom (S.presheaf.map i.op).hom (v.val.left.app U a) =
      w.val.left.app U a
    apply TrivSqZeroExt.ext
    · simpa using (congrArg (fun x ↦ x.fst.fst) ha).symm
    · simpa using (congrArg (fun x ↦ x.snd.snd) ha).symm
  · intro z
    obtain ⟨D, hD⟩ := exists_mixedCoefficientDerivation G z.val
      ((mem_mixedPoints G).mp z.property).1 ((mem_mixedPoints G).mp z.property).2
    let g := S.dualNumbersι ≫ S.dualNumbers.dualNumbersι ≫ z.val.left
    have hg : g = unitSection G := by
      have h := congrArg (fun f ↦ f.left) ((mem_mixedPoints G).mp z.property).1
      have h' := congrArg (fun f ↦ S.dualNumbersι ≫ f) h
      simpa [g, ← Category.assoc, Scheme.dualNumbersιεOver, Hom.one_def,
        Over.toUnit_left, unitSection] using h'
    let v : Scheme.dualNumbersOver S ⟶ G :=
      Over.homMk (pointOfDerivation G g D)
        (pointOfDerivation_comp_hom G g D (hg ▸ unitSection_comp_hom G))
    have hv : v ∈ infPoints G := by
      rw [mem_infPoints]
      apply Over.OverMorphism.ext
      exact (ι_comp_pointOfDerivation G g D).trans (hg.trans (one_left G).symm)
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    apply Over.OverMorphism.ext
    change S.dualNumbersMul ≫ pointOfDerivation G g D = z.val.left
    refine Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext'
      (PresheafedSpace.ext _ _ rfl ?_))
    ext U a
    simp only [Functor.comp_obj, Functor.op_obj, eqToHom_refl, Functor.whiskerRight_id',
      TopCat.Presheaf.comp_app, TopCat.Presheaf.pushforward_obj_obj, NatTrans.id_app,
      Category.comp_id]
    change DualNumber.mulRingHom (pointOfDerivationRingHom G g D U a) = z.val.left.app U a
    have hε := congrArg (fun f ↦ f.left) ((mem_mixedPoints G).mp z.property).1
    have hδ := congrArg (fun f ↦ f.left) ((mem_mixedPoints G).mp z.property).2
    have he := ConcreteCategory.congr_hom (Scheme.Hom.congr_app hε U) a
    have hd := ConcreteCategory.congr_hom (Scheme.Hom.congr_app hδ U) a
    have he' := congrArg snd he
    have hd' := congrArg snd hd
    simp only [Over.comp_left, Scheme.Hom.comp_app, CommRingCat.comp_apply] at he' hd'
    simp only [Hom.one_def, Over.comp_left, Over.toUnit_left,
      Scheme.Hom.comp_app, CommRingCat.comp_apply] at he' hd'
    change (z.val.left.app U a).fst.snd = _ at he'
    change (DualNumber.mapRingHom
      (fstHom Γ(S, z.val.left ⁻¹ᵁ U) Γ(S, z.val.left ⁻¹ᵁ U)
        Γ(S, z.val.left ⁻¹ᵁ U)).toRingHom (z.val.left.app U a)).snd = _ at hd'
    rw [DualNumber.snd_mapRingHom] at hd'
    let ie : z.val.left ⁻¹ᵁ U ⟶ unitSection G ⁻¹ᵁ U :=
      eqToHom (congrArg (fun f ↦ (TopologicalSpace.Opens.map f).obj U)
        (congrArg (fun f ↦ f.base) hε))
    change (z.val.left.app U a).fst.snd =
      (DualNumber.mapRingHom (S.presheaf.map ie.op).hom
        (inl ((unitSection G).app U a))).snd at he'
    change (z.val.left.app U a).snd.fst =
      (DualNumber.mapRingHom (S.presheaf.map ie.op).hom
        (inl ((unitSection G).app U a))).snd at hd'
    simp only [DualNumber.snd_mapRingHom, snd_inl, map_zero] at he' hd'
    apply TrivSqZeroExt.ext
    · apply TrivSqZeroExt.ext
      · simp only [DualNumber.fst_mulRingHom, fst_inl, pointOfDerivationRingHom,
          RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, fst_add, fst_inr, add_zero]
        rfl
      · simpa [pointOfDerivationRingHom] using he'.symm
    · apply TrivSqZeroExt.ext
      · simpa [pointOfDerivationRingHom] using hd'.symm
      · simp only [DualNumber.snd_mulRingHom, snd_inr, pointOfDerivationRingHom,
          RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, snd_add, snd_inl, zero_add]
        exact hD a

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
  have hε : Scheme.dualNumbersιεOver S ≫ Scheme.dualNumbersProjδOver S =
      CartesianMonoidalCategory.toUnit (Scheme.dualNumbersOver S) ≫
        Scheme.dualNumbersιOver S := by
    ext1
    simp [Scheme.dualNumbersιεOver, Scheme.dualNumbersProjδOver,
      Scheme.dualNumbersιOver, Over.toUnit_left]
  have hδ : Scheme.dualNumbersιδOver S ≫ Scheme.dualNumbersProjεOver S =
      CartesianMonoidalCategory.toUnit (Scheme.dualNumbersOver S) ≫
        Scheme.dualNumbersιOver S := by
    ext1
    simp [Scheme.dualNumbersιδOver, Scheme.dualNumbersProjεOver,
      Scheme.dualNumbersιOver, Over.toUnit_left]
  have hw : Scheme.dualNumbersιεOver S ≫ toδ G w = 1 := by
    rw [toδ, ← Category.assoc, hε, Category.assoc, (mem_infPoints G).1 w.2,
      MonObj.comp_one]
  have hv : Scheme.dualNumbersιδOver S ≫ toε G v = 1 := by
    rw [toε, ← Category.assoc, hδ, Category.assoc, (mem_infPoints G).1 v.2,
      MonObj.comp_one]
  rw [mem_mixedPoints]
  simp only [MonObj.comp_mul, GrpObj.comp_inv, hw, hv, one_mul, mul_one,
    inv_one, mul_inv_cancel, and_self]

/-- The bracket of two infinitesimal points: the mixed term `εδ` of their group commutator
`v_ε w_δ v_ε⁻¹ w_δ⁻¹` over `S[ε][δ]`. It is the restriction to the identity of the commutator
`[ṽ, w̃]` of the left-invariant vector fields extending `v` and `w`. (blueprint: `sk-d-tangent`) -/
noncomputable def infBracket (v w : infPoints G) : infPoints G :=
  (mixedEquiv G).symm ⟨_, commutator_mem_mixedPoints G v w⟩

private theorem mixedEquiv_infBracket (v w : infPoints G) :
    (mixedEquiv G) (infBracket G v w) =
      ⟨_, commutator_mem_mixedPoints G v w⟩ :=
  (mixedEquiv G).apply_symm_apply _

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
  apply (mixedEquiv H).injective
  rw [mixedEquiv_infBracket]
  apply Subtype.ext
  change Scheme.dualNumbersMulOver S ≫ ((infBracket G v w).1 ≫ f) = _
  rw [← Category.assoc]
  have h := congrArg Subtype.val (mixedEquiv_infBracket G v w)
  change Scheme.dualNumbersMulOver S ≫ (infBracket G v w).1 = _ at h
  rw [h]
  simp only [toε, toδ, coe_infPointsMap_apply, Category.assoc,
    MonObj.mul_comp, GrpObj.inv_comp]

/-- Let `f : G ⟶ H` be a monomorphism of group schemes, a subgroup scheme of `H`. If the
commutators of the points of `H` over `S[ε][δ]` factor through `G`, then the bracket of two
infinitesimal points of `H` comes from `G`: the commutator `v_ε w_δ v_ε⁻¹ w_δ⁻¹` is `c ≫ f` for a
point `c` of `G` over `S[ε][δ]`, which is a mixed point of `G` since `f` is a monomorphism, and
its preimage under `η ↦ εδ` is an infinitesimal point of `G` mapping to `[v, w]`.
(blueprint: `sk-i-restriction`) -/
theorem infBracket_mem_range_infPointsMap (f : G ⟶ H) [IsMonHom f] [Mono f]
    (hf : ∀ a b : Scheme.dualNumbers₂Over S ⟶ H, a * b * a⁻¹ * b⁻¹ ∈ (IsMonHom.monoidHom f _).range)
    (v w : infPoints H) : infBracket H v w ∈ (infPointsMap f).range := by
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 (hf (toε H v) (toδ H w))
  change c ≫ f = _ at hc
  have hm : c ∈ mixedPoints G := by
    have h := (mem_mixedPoints H).1 (commutator_mem_mixedPoints H v w)
    rw [mem_mixedPoints]
    constructor
    · apply (cancel_mono f).1
      rw [Category.assoc, hc, h.1, MonObj.one_comp]
    · apply (cancel_mono f).1
      rw [Category.assoc, hc, h.2, MonObj.one_comp]
  let z : mixedPoints G := ⟨c, hm⟩
  refine MonoidHom.mem_range.2 ⟨(mixedEquiv G).symm z, ?_⟩
  apply (mixedEquiv H).injective
  rw [mixedEquiv_infBracket]
  apply Subtype.ext
  change Scheme.dualNumbersMulOver S ≫ (((mixedEquiv G).symm z).1 ≫ f) = _
  rw [← Category.assoc]
  have hz := congrArg Subtype.val ((mixedEquiv G).apply_symm_apply z)
  change Scheme.dualNumbersMulOver S ≫ ((mixedEquiv G).symm z).1 = c at hz
  rw [hz, hc]

end GrpObj

end InfPoints

end AlgebraicGeometry

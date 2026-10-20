/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C5
-/
module

public import Sheaf.Paper.IntegralHeartLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ClosedTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod

/-!
# The derived dual of the residue coefficient sheaf

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-integral-heart,
the final two sentences of the integral-heart-dualizable proof.
(blueprint: lem-integral-heart-residue-dual)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
open MonObj MonoidalClosed CategoryTheory.Pretriangulated

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]
private theorem unit_pre (f : End (𝟙_ (DerivedCategory A))) :
    MonoidalClosed.id (𝟙_ _) ≫ (pre f).app (𝟙_ _) =
      f ≫ MonoidalClosed.id (𝟙_ _) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_natural_left, MonoidalClosed.id_eq, uncurry_curry]
  rw [rightUnitor_naturality, ← unitors_equal, leftUnitor_naturality]

private theorem unit_cone_dual {K : DerivedCategory A} (f : End (𝟙_ (DerivedCategory A)))
    (g : 𝟙_ (DerivedCategory A) ⟶ K) (δ : K ⟶ (𝟙_ (DerivedCategory A))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g δ ∈ distTriang (DerivedCategory A)) :
    Nonempty ((ihom K).obj (𝟙_ _) ≅ K⟦(-1 : ℤ)⟧) := by
  obtain ⟨h, hh⟩ := DerivedCategory.exists_distinguished_ihom_pre
    (Triangle.mk f g δ) hT (𝟙_ _)
  let T := Triangle.mk ((pre g).app (𝟙_ _)) ((pre f).app (𝟙_ _)) h
  have : IsIso (MonoidalClosed.id (𝟙_ (DerivedCategory A))) := by
    rw [MonoidalClosed.id_eq, ← unitors_equal]
    refine ⟨(λ_ _).inv ≫ (ihom.ev (𝟙_ (DerivedCategory A))).app _, ?_, ?_⟩
    · rw [leftUnitor_inv_naturality_assoc, ← uncurry_eq, uncurry_curry]
      exact (λ_ _).inv_hom_id
    · rw [← curry_natural_left, leftUnitor_naturality, Iso.hom_inv_id_assoc,
        ← uncurry_id_eq_ev, curry_uncurry]
  let eU := asIso (MonoidalClosed.id (𝟙_ (DerivedCategory A)))
  let e := isoTriangleOfIso₁₂ (Triangle.mk f g δ) T.rotate hT
    (rot_of_distTriang T hh) eU eU (unit_pre f).symm
  let eK : K ≅ ((ihom K).obj (𝟙_ _))⟦(1 : ℤ)⟧ := Triangle.π₃.mapIso e
  exact ⟨((shiftFunctorCompIsoId (DerivedCategory A) (1 : ℤ) (-1) (by omega)).app
      ((ihom K).obj (𝟙_ _))).symm ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso eK.symm⟩

private theorem shortExact_units_dual {S : ShortComplex A} (hS : S.ShortExact)
    (e₁ : S.X₁ ≅ 𝟙_ A) (e₂ : S.X₂ ≅ 𝟙_ A) :
    Nonempty ((ihom ((DerivedCategory.singleFunctor A 0).obj S.X₃)).obj (𝟙_ _) ≅
      ((DerivedCategory.singleFunctor A 0).obj S.X₃)⟦(-1 : ℤ)⟧) := by
  let H := DerivedCategory.singleFunctor A 0
  let e₁' := H.mapIso e₁ ≪≫ DerivedCategory.singleFunctorObjUnitIso A
  let e₂' := H.mapIso e₂ ≪≫ DerivedCategory.singleFunctorObjUnitIso A
  let K := H.obj S.X₃
  let f := e₁'.inv ≫ H.map S.f ≫ e₂'.hom
  let g := e₂'.inv ≫ H.map S.g
  let δ := hS.singleδ ≫ e₁'.hom⟦(1 : ℤ)⟧'
  have ht : Triangle.mk f g δ ∈ distTriang _ := by
    apply isomorphic_distinguished _ hS.singleTriangle_distinguished
    refine Triangle.isoMk _ _ e₁'.symm e₂'.symm (Iso.refl K) ?_ ?_ ?_
    · change f ≫ e₂'.inv = e₁'.inv ≫ H.map S.f
      simp only [f, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · change g ≫ 𝟙 K = e₂'.inv ≫ H.map S.g
      exact Category.comp_id _
    · change δ ≫ e₁'.inv⟦(1 : ℤ)⟧' = 𝟙 K ≫ hS.singleδ
      dsimp only [δ]
      rw [Category.assoc, ← Functor.map_comp, e₁'.hom_inv_id]
      rw [(shiftFunctor (DerivedCategory A) (1 : ℤ)).map_id]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
  exact unit_cone_dual f g δ ht

namespace AlgebraicGeometry.ProEtale

private def pointMultiplier (O : Type) [CommRing O] [TopologicalSpace O]
    [IsTopologicalRing O] (a : O) :
    End (Mod.regular (Profinite.continuousMapRingObj.{u} O)) := by
  let R := Profinite.continuousMapRingObj.{u} O
  let J := coherentTopology Profinite.{u}
  let h : R ⟶ R := ⟨{
    app := fun S ↦ AddCommGrpCat.ofHom {
      toFun f := ULift.up (f.down * ContinuousMap.const S.unop a)
      map_zero' := by apply ULift.ext; exact zero_mul _
      map_add' f g := by apply ULift.ext; exact add_mul _ _ _ }
    naturality := by intros; rfl }⟩
  refine Mod.homMk h ?_
  let F := sheafToPresheaf J Ab.{u + 1}
  let : MonObj R.obj := (Profinite.continuousMapRingSheaf.{u} O).obj.monObjCompForget₂
  have hp : μ[R.obj] ≫ h.hom = R.obj ◁ h.hom ≫ μ[R.obj] := by
    ext S : 2
    apply AddCommGrpCat.hom_ext_toIntLinearMap
    apply TensorProduct.ext'
    intro f g
    apply ULift.ext
    ext x
    exact mul_assoc _ _ _
  apply Sheaf.tensor_hom_ext
  change Functor.LaxMonoidal.μ F R R ≫ F.map (μ[R] ≫ h) =
    Functor.LaxMonoidal.μ F R R ≫ F.map (R ◁ h ≫ μ[R])
  rw [F.map_comp, F.map_comp, ← Category.assoc, Sheaf.μ_comp_map_mul]
  rw [← Category.assoc, ← Functor.LaxMonoidal.μ_natural_right,
    Category.assoc, Sheaf.μ_comp_map_mul]
  exact hp

private theorem coefficientUniformizer_ne_zero (ℓ : ℕ) [Fact ℓ.Prime] (E : Type)
    [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    Padic.coefficientExtensionUniformizer ℓ E ≠ 0 := by
  let h := (Padic.extension_integers_dvr ℓ E
    (Padic.coefficientExtensionAbsoluteValue ℓ E)
    (spectralNorm_extends (K := Padic ℓ) (L := E))).choose_spec.choose_spec
  have hm : Padic.coefficientExtensionMaximalIdeal ℓ E ≠ ⊥ :=
    h.2.2.2.2.2.2.2.2.2.1
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer ℓ E} :
      Set (Padic.coefficientExtensionIntegers ℓ E)) =
        Padic.coefficientExtensionMaximalIdeal ℓ E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  intro h0
  apply hm
  rw [← hgen, h0, Ideal.span_singleton_eq_bot]

private theorem principal_discrete (ℓ : ℕ) [Fact ℓ.Prime] (E : Type)
    [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]
    (a : Padic.coefficientExtensionIntegers ℓ E) (ha : a ≠ 0) :
    letI := spectralNorm.normedField (Padic ℓ) E
    DiscreteTopology (Padic.coefficientExtensionIntegers ℓ E ⧸ Ideal.span {a}) := by
  let := spectralNorm.normedField (Padic ℓ) E
  let A := Padic.coefficientExtensionIntegers ℓ E
  let I : Ideal A := Ideal.span {a}
  have hmem (x : E) : x ∈ A ↔ ‖x‖ ≤ 1 :=
    (Padic.extension_integers_dvr ℓ E (Padic.coefficientExtensionAbsoluteValue ℓ E)
      (spectralNorm_extends (K := Padic ℓ) (L := E))).choose_spec.choose_spec.1 x
  have ha' : (a : E) ≠ 0 := fun h ↦ ha (Subtype.ext h)
  have hopen : IsOpen (I : Set A) := by
    apply I.toAddSubgroup.isOpen_of_mem_nhds (g := 0)
    have ho : IsOpen ((fun x : A ↦ (x : E)) ⁻¹' Metric.ball 0 ‖(a : E)‖) :=
      Metric.isOpen_ball.preimage continuous_subtype_val
    apply Filter.mem_of_superset (ho.mem_nhds (by
      change dist (0 : E) 0 < ‖(a : E)‖
      simpa only [dist_self] using norm_pos_iff.mpr ha'))
    intro x hx
    have hx' : ‖(x : E)‖ < ‖(a : E)‖ := by
      change dist (x : E) 0 < ‖(a : E)‖ at hx
      simpa only [dist_zero_right] using hx
    have hdiv : (x : E) / a ∈ A := (hmem _).2 (by
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr ha')).2 hx'.le)
    change x ∈ Ideal.span {a}
    rw [Ideal.mem_span_singleton]
    refine ⟨⟨(x : E) / a, hdiv⟩, ?_⟩
    apply Subtype.ext
    exact (mul_div_cancel₀ _ ha').symm
  exact QuotientAddGroup.discreteTopology hopen

private theorem small_residue_sequence (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v)
    [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    ∃ (d : End (Mod.regular (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E)))
      (q : Mod.regular (SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E) ⟶
        SmallAdicCompletion.Coefficients.quotientModule ℓ E 1)
      (h : d ≫ q = 0), (ShortComplex.mk d q h).ShortExact := by
  classical
  let F := SmallAdicCompletion.Coefficients.field ℓ E
  let A := SmallAdicCompletion.Coefficients.integers ℓ E
  let a := Padic.coefficientExtensionUniformizer ℓ F
  have ha : a ≠ 0 := coefficientUniformizer_ne_zero ℓ F
  let J := coherentTopology Profinite.{u}
  let R := SmallAdicCompletion.Coefficients.integerRing.{u} ℓ E
  let d : End (Mod.regular R) := pointMultiplier A a
  let q := SmallAdicCompletion.quotientUnit.{u} ℓ E 0
  have hw : d ≫ q = 0 := by
    apply Mod.hom_ext
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply ConcreteCategory.hom_ext
    intro f
    apply ULift.ext
    ext x
    change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ F 1) (f.down x * a) = 0
    rw [map_mul]
    have hz : Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ F 1) a = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      change a ∈ (Ideal.span {a}) ^ 1
      simp only [pow_one]
      exact Ideal.subset_span (Set.mem_singleton a)
    rw [hz, mul_zero]
  let S := ShortComplex.mk d q hw
  have hsec (U : Profinite.{u}ᵒᵖ) :
      ((S.map (Mod.forget R)).map
        (sheafToPresheaf J Ab.{u + 1} ⋙ (evaluation _ _).obj U)).ShortExact := by
    let T := (S.map (Mod.forget R)).map
      (sheafToPresheaf J Ab.{u + 1} ⋙ (evaluation _ _).obj U)
    have hm : Mono T.f := by
      rw [AddCommGrpCat.mono_iff_injective]
      intro x y hxy
      apply ULift.ext
      ext t
      have he := congrArg (fun z : ULift.{u + 1} C(U.unop, A) ↦ z.down t) hxy
      change x.down t * a = y.down t * a at he
      exact congrArg Subtype.val ((mul_left_injective₀ ha) he)
    have he : Epi T.g := by
      rw [AddCommGrpCat.epi_iff_surjective]
      let : DiscreteTopology (Padic.coefficientExtensionRing ℓ F 1) := by
        change DiscreteTopology (A ⧸ (Ideal.span {a}) ^ 1)
        rw [pow_one]
        exact principal_discrete ℓ F a ha
      intro y
      let σ : Padic.coefficientExtensionRing ℓ F 1 → A := Quotient.out
      have hσ : Continuous σ := continuous_of_discreteTopology
      refine ⟨ULift.up (⟨fun x ↦ σ (y.down x), hσ.comp y.down.continuous⟩ : C(U.unop, A)), ?_⟩
      apply ULift.ext
      ext x
      exact Quotient.out_eq (y.down x)
    have hex : T.Exact := by
      rw [ShortComplex.ab_exact_iff]
      intro x hx
      have ha' : (a : F) ≠ 0 := fun h ↦ ha (Subtype.ext h)
      have hdiv (t : U.unop) : (x.down t : F) / a ∈ A := by
        have ht := congrArg
          (fun z : ULift.{u + 1} C(U.unop, Padic.coefficientExtensionRing ℓ F 1) ↦ z.down t) hx
        change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal ℓ F 1) (x.down t) = 0 at ht
        have ht' : x.down t ∈ Ideal.span {a} := by
          simpa only [Padic.coefficientExtensionIdeal, pow_one] using
            Ideal.Quotient.eq_zero_iff_mem.mp ht
        obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ht'
        have hb' := congrArg Subtype.val hb
        change (x.down t : F) = (a : F) * b at hb'
        rw [hb', mul_div_cancel_left₀ _ ha']
        exact b.property
      let g : C(U.unop, A) := ⟨fun t ↦ ⟨(x.down t : F) / a, hdiv t⟩,
        ((continuous_subtype_val.comp x.down.continuous).div_const (a : F)).subtype_mk _⟩
      refine ⟨ULift.up g, ?_⟩
      apply ULift.ext
      ext t
      change ((x.down t : F) / a) * a = (x.down t : F)
      exact div_mul_cancel₀ _ ha'
    exact ShortComplex.ShortExact.mk' hex hm he
  have hT : ((S.map (Mod.forget R)).map (sheafToPresheaf J Ab.{u + 1})).ShortExact := by
    let T := (S.map (Mod.forget R)).map (sheafToPresheaf J Ab.{u + 1})
    have : Mono T.f := by
      rw [NatTrans.mono_iff_mono_app]
      exact fun U ↦ (hsec U).mono_f
    have : Epi T.g := by
      rw [NatTrans.epi_iff_epi_app]
      exact fun U ↦ (hsec U).epi_g
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    rw [ShortComplex.exact_iff_evaluation]
    exact fun U ↦ (hsec U).exact
  have hT' := hT.map_of_exact (presheafToSheaf J Ab.{u + 1})
  have hs : (S.map (Mod.forget R)).ShortExact := ShortComplex.shortExact_of_iso
    (ShortComplex.mapNatIso (S.map (Mod.forget R)) (sheafificationNatIso J Ab.{u + 1})).symm hT'
  have hm : Mono d := (Mod.forget R).mono_of_mono_map hs.mono_f
  have he : Epi q := (Mod.forget R).epi_of_epi_map hs.epi_g
  exact ⟨d, q, hw, ⟨(Mod.forget R).reflects_exact_of_faithful S hs.exact⟩⟩


/-- The residue coefficient sheaf has derived dual in degree one.

Source: integral-heart-dualizable, final two sentences; Stacks Project, Tags 08JI
and 0FPU; the coefficient sequence is DerivedNakayamaResolution at n=1.
(blueprint: lem-integral-heart-residue-dual)

Proof: specialize the coefficient short exact sequence to the canonical small
presentation of E and n=1. The finiteModule with index zero is this positive-level-one
quotient. Its resolution has two completed units, in degrees -1 and 0, and differential
multiplication by the uniformizer. The bounded-free internal-Hom model identifies its
derived dual with the two units in degrees 0 and 1, with differential minus that
multiplication. Multiplication is injective by the original short exact sequence.
Its negative has the same image, hence cokernel the residue module. The quotient map
from degree one to the residue module, with zero in other degrees, is a chain map
and induces isomorphisms on every cohomology sheaf. Localization therefore gives the
stated isomorphism. With the cohomological shift convention, the target is the
residue module in degree one, namely its degree-zero complex shifted by -1. -/
theorem integralHeart_residue_dual
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type v) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (X : Scheme.{u}) :
    Nonempty
      ((((CondensedRing.derivedHom (SmallAdicCompletion.Coefficients.integerRing ℓ E)
          X).obj (op ((DerivedCategory.singleFunctor _ 0).obj
            (SmallAdicCompletion.finiteModule ℓ E X 0)))).obj
              (𝟙_ (integralHeartDerivedCategory.{u} ℓ E X))) ≅
        ((DerivedCategory.singleFunctor _ 0).obj
          (SmallAdicCompletion.finiteModule ℓ E X 0))⟦(-1 : ℤ)⟧) := by
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar
    infer_instance
  have : PreservesFiniteColimits pointUpperStar.{u} := by
    have : PreservesColimitsOfSize.{0, 0} pointUpperStar :=
      pointUpperStarLowerStarAdjunction.leftAdjoint_preservesColimits
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    dsimp [upperStarFromPoint]
    infer_instance
  have : PreservesFiniteColimits (upperStarFromPoint X) := by
    dsimp [upperStarFromPoint]
    infer_instance
  have : (upperStarFromPoint X).Additive := leftExactFunctor_le_additiveFunctor _ _ _ (by
    rw [leftExactFunctor_iff]
    infer_instance)
  obtain ⟨d, q, w, hS⟩ := small_residue_sequence.{u} ℓ E
  let S := ShortComplex.mk d q w
  have hSX := hS.map_of_exact (SmallAdicCompletion.Coefficients.pullback ℓ E X)
  let SX := S.map (SmallAdicCompletion.Coefficients.pullback ℓ E X)
  change Nonempty ((ihom ((DerivedCategory.singleFunctor _ 0).obj SX.X₃)).obj
    (𝟙_ _) ≅ ((DerivedCategory.singleFunctor _ 0).obj SX.X₃)⟦(-1 : ℤ)⟧)
  exact shortExact_units_dual (S := SX) hSX
    (SmallAdicCompletion.Coefficients.regularPullbackIso ℓ E X)
    (SmallAdicCompletion.Coefficients.regularPullbackIso ℓ E X)

end AlgebraicGeometry.ProEtale

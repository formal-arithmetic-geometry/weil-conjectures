/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Topology.ProfiniteSectionsFiniteQuotient
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Homeomorph.Lemmas
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Finite integral coefficients have a condensed finite free resolution

Source: blueprint main-20261015, scalar-six direct-image proof, paragraph
"Finite free and finitely presented coefficient extensions", second bullet
(blueprint: lem-sfb-finite-integral-condensed-resolution).

The conclusion is packaged transparently so that the arithmetic theorem can install the
recorded valuation topology and the discrete topology explicitly. The two free condensed
modules are the continuous-section modules of the coordinate modules O^r. The component
formulas specify their arrows by postcomposition, rather than by arbitrary exact arrows.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Padic

/-- The conclusion of the finite integral condensed resolution assertion, with specified
coefficient topologies and scalar homomorphism. The free module is presented in coordinates:
its sections over S are C(S,O^r), naturally the finite direct sum of r copies of C(S,O).
The pointwise scalar action is the recorded restriction of the regular module.

Source: blueprint scalar-six direct-image proof, finite coefficients bullet
(blueprint: lem-sfb-finite-integral-condensed-resolution). -/
def FiniteIntegralCondensedResolution
    (O A : Type u) [CommRing O] [CommRing A]
    [TopologicalSpace O] [TopologicalSpace A] [IsTopologicalRing O] [IsTopologicalRing A]
    (a : O →+* A) (ha : Continuous a) : Prop :=
  letI := a.toAlgebra
  letI := continuousSMul_of_algebraMap O A ha
  letI : HasFiniteBiproducts
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousCoefficientRingObj O)) := .of_hasFiniteProducts
  ∃ (r : ℕ) (q : (Fin r → O) →L[O] A) (φ : (Fin r → O) →L[O] (Fin r → O)),
    Function.Surjective q ∧ Function.Injective φ ∧
    Function.Exact φ q ∧
    (∃ M : Matrix (Fin r) (Fin r) O, ∀ x : Fin r → O, φ x = M.mulVec x) ∧
    (∃ e : (Fin r → O) ≃ₜ LinearMap.ker q.toLinearMap,
      ∀ x : Fin r → O, (e x).val = φ x) ∧
    (∀ S : Profinite.{u},
      Function.Injective (ContinuousLinearMap.compLeftContinuous O S φ) ∧
      Function.Exact (ContinuousLinearMap.compLeftContinuous O S φ)
        (ContinuousLinearMap.compLeftContinuous O S q) ∧
      Function.Surjective (ContinuousLinearMap.compLeftContinuous O S q)) ∧
    Nonempty (Profinite.continuousSectionsModule O (Fin r → O) ≅
      biproduct (fun _i : Fin r ↦ Mod.regular (Profinite.continuousCoefficientRingObj O))) ∧
    (∃ (F : Profinite.continuousSectionsModule O (Fin r → O) ⟶
          Profinite.continuousSectionsModule O (Fin r → O))
       (G : Profinite.continuousSectionsModule O (Fin r → O) ⟶
          Profinite.continuousSectionsModule O A)
       (h : F ≫ G = 0),
      (∀ (S : Profinite.{u}) (f : ULift.{u + 1} C(S, Fin r → O)) (s : S),
        ((F.hom.hom.app (op S)) f).down s = φ (f.down s)) ∧
      (∀ (S : Profinite.{u}) (f : ULift.{u + 1} C(S, Fin r → O)) (s : S),
        ((G.hom.hom.app (op S)) f).down s = q (f.down s)) ∧
      (ShortComplex.mk F G h).ShortExact)

/-- The recorded integer-ring topology is a topological ring structure. This is only the
existing subring topological-ring instance for the spectral norm, with its topology exposed.

Source: blueprint scalar-six direct-image proof, valuation topology on O_E
(blueprint: lem-sfb-finite-integral-condensed-resolution). -/
noncomputable abbrev finiteIntegralIntegersTopologicalRing
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] :
    @IsTopologicalRing (coefficientExtensionIntegers l E)
      (coefficientExtensionIntegersTopology l E) inferInstance := by
  let := spectralNorm.normedField (Padic l) E
  exact inferInstanceAs (IsTopologicalRing (coefficientExtensionIntegers l E))

private def sectionsLinear
    {A T U : Type u} [CommRing A] [CommRing T] [CommRing U]
    [TopologicalSpace A] [TopologicalSpace T] [TopologicalSpace U]
    [IsTopologicalRing A] [IsTopologicalRing T] [IsTopologicalRing U]
    [Algebra A T] [Algebra A U] [ContinuousSMul A T] [ContinuousSMul A U]
    (f : T →L[A] U) (S : Profinite.{u}) :
    C(S, T) →ₗ[C(S, A)] C(S, U) where
  toFun a := (⟨fun x ↦ f x, f.continuous⟩ : C(T, U)).comp a
  map_add' a b := by ext s; exact map_add f _ _
  map_smul' a b := by ext s; exact f.map_smul (a s) (b s)

private noncomputable def sectionsMap
    {A T U : Type u} [CommRing A] [CommRing T] [CommRing U]
    [TopologicalSpace A] [TopologicalSpace T] [TopologicalSpace U]
    [IsTopologicalRing A] [IsTopologicalRing T] [IsTopologicalRing U]
    [Algebra A T] [Algebra A U] [ContinuousSMul A T] [ContinuousSMul A U]
    (f : T →L[A] U) :
    Profinite.continuousSectionsModule A T ⟶ Profinite.continuousSectionsModule A U := by
  letI : MonObj (Profinite.continuousCoefficientRingObj T).obj :=
    (Profinite.continuousCoefficientRingSheaf T).obj.monObjCompForget₂
  letI : MonObj (Profinite.continuousCoefficientRingObj U).obj :=
    (Profinite.continuousCoefficientRingSheaf U).obj.monObjCompForget₂
  let k : Profinite.continuousCoefficientRingObj T ⟶ Profinite.continuousCoefficientRingObj U :=
    ⟨{ app S := AddCommGrpCat.ofHom
         { toFun a := ULift.up ((sectionsLinear f S.unop) a.down)
           map_zero' := congrArg ULift.up (map_zero (sectionsLinear f S.unop))
           map_add' a b := congrArg ULift.up (map_add (sectionsLinear f S.unop) _ _) }
       naturality _ _ _ := by
         ext a
         apply ULift.ext
         ext s
         rfl }⟩
  refine Mod.homMk k ?_
  let aT : Profinite.continuousCoefficientRingObj A ⟶ Profinite.continuousCoefficientRingObj T :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMapOfUniverse.{u, u} (algebraMap A T)
        (continuous_algebraMap A T) :
        Profinite.continuousCoefficientRingSheaf A ⟶ Profinite.continuousCoefficientRingSheaf T)
  let aU : Profinite.continuousCoefficientRingObj A ⟶ Profinite.continuousCoefficientRingObj U :=
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      (Profinite.continuousMapRingSheafMapOfUniverse.{u, u} (algebraMap A U)
        (continuous_algebraMap A U) :
        Profinite.continuousCoefficientRingSheaf A ⟶ Profinite.continuousCoefficientRingSheaf U)
  change (MonoidalCategory.whiskerRight aT _ ≫ MonObj.mul) ≫ k =
    MonoidalCategory.whiskerLeft _ k ≫
      (MonoidalCategory.whiskerRight aU _ ≫ MonObj.mul)
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc,
    ← Functor.LaxMonoidal.μ_natural_right_assoc,
    ← Functor.LaxMonoidal.μ_natural_left_assoc]
  have hT := Sheaf.μ_comp_map_mul (Profinite.continuousCoefficientRingObj T)
  have hU := Sheaf.μ_comp_map_mul (Profinite.continuousCoefficientRingObj U)
  simp only [reassoc_of% hT, hU]
  ext S : 2
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  intro a b
  change (k.hom.app S)
      ((MonObj.mul : MonoidalCategory.tensorObj (Profinite.continuousCoefficientRingObj T).obj
        (Profinite.continuousCoefficientRingObj T).obj ⟶ _).app S
          ((aT.hom.app S) a ⊗ₜ[ℤ] b)) =
    (MonObj.mul : MonoidalCategory.tensorObj (Profinite.continuousCoefficientRingObj U).obj
      (Profinite.continuousCoefficientRingObj U).obj ⟶ _).app S
        ((aU.hom.app S) a ⊗ₜ[ℤ] (k.hom.app S) b)
  apply ULift.ext
  ext s
  change f (algebraMap A T (a.down s) * b.down s) =
    algebraMap A U (a.down s) * f (b.down s)
  simpa only [Algebra.smul_def] using f.map_smul (a.down s) (b.down s)

/-- Finite discrete integral coefficient algebras have a two-term finite free resolution
that is exact on continuous functions from every profinite set and as condensed modules.

Source: blueprint main-20261015, scalar-six direct-image proof, paragraph
"Finite free and finitely presented coefficient extensions", second bullet
(blueprint: lem-sfb-finite-integral-condensed-resolution).

Proof plan:
1. If A is the zero ring, take r=0 and the unique maps. This also works for empty S.
2. Otherwise enumerate A and define q(x)=sum_i a(x_i)b_i. The coordinate vectors show
   surjectivity. Finite sums of continuous maps show continuity. Give K=ker q its
   subspace topology.
3. N! annihilates every element of the additive group of A, where N=|A|. Its image c
   in O is nonzero because O lies in the characteristic-zero field E. Hence c O^r ≤ K.
4. By lem-weil-l-adic-extension-integers-dvr, O is a domain and PID. Apply
   lem-sc-dvr-saturation-line-smith-normal-form to K ≤ O^r to obtain ambient basis u_i
   and kernel basis v_i=d_i u_i with distinct ambient indices and nonzero d_i.
5. There are r kernel basis vectors: otherwise c times an unused ambient basis vector
   belongs to K, contradicting its nonzero coordinate. Let φ have columns v_i.
   It is injective with image K, is a matrix over O, and is continuous.
6. The ambient basis change and its inverse are continuous matrices. On K the inverse
   of φ has coordinates (P⁻¹ y)_i/d_i in E, with values in O. Division by each fixed
   nonzero d_i is continuous. The subspace and product topologies make this inverse
   continuous, giving the required homeomorphism onto K.
7. On C(S,-), injectivity is pointwise. A section killed by q factors continuously
   through K; compose with the inverse in step 6 to obtain its unique preimage.
8. Choose a preimage in O^r for each element of A. A continuous S→A has finite clopen
   fibres; taking the chosen constant preimage on each fibre gives a continuous lift.
9. Coordinate projections and assembly identify C(S,O^r) with C(S,O)^r, naturally in S
   and linearly over C(S,O). The coordinate inclusions and projections make these the
   finite direct sums of the regular condensed O-module. The target is the recorded
   continuous A-valued coefficient sheaf with the action through a.
10. Postcomposition commutes with restrictions and scalar actions, giving F and G.
    Step 7 gives the kernel universal property sectionwise. For a map killing F,
    factor through G by choosing lifts as in step 8; differences are in the image of F,
    so the factor is well defined, linear and natural. Sectionwise surjectivity gives
    uniqueness. Thus the condensed sequence is short exact.
-/
theorem finite_integral_condensed_resolution
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (A : Type u) [CommRing A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    (a : coefficientExtensionIntegers l E →+* A)
    (ha : @Continuous _ _ (coefficientExtensionIntegersTopology l E) inferInstance a) :
    @FiniteIntegralCondensedResolution (coefficientExtensionIntegers l E) A
      inferInstance inferInstance (coefficientExtensionIntegersTopology l E) inferInstance
      (finiteIntegralIntegersTopologicalRing l E) inferInstance a ha := by
  classical
  let O := coefficientExtensionIntegers l E
  let : TopologicalSpace O := coefficientExtensionIntegersTopology l E
  let : IsTopologicalRing O := finiteIntegralIntegersTopologicalRing l E
  let : Algebra O A := a.toAlgebra
  let : ContinuousSMul O A := continuousSMul_of_algebraMap O A ha
  let := Fintype.ofFinite A
  let : CharZero E := charZero_of_injective_algebraMap (algebraMap (Padic l) E).injective
  let : CharZero O := inferInstance
  let : IsPrincipalIdealRing O :=
    (extension_integers_dvr l E (coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec.2.2.2.2.2.2.2.2.1
  have ht := coefficientExtension_integers_profinite_tower.{u, u} l E
  let : CompactSpace O := ht.2.1
  let : T2Space O := ht.2.2.1
  let r := Fintype.card A
  let b : Fin r → A := (Fintype.equivFin A).symm
  let q₀ : (Fin r → O) →ₗ[O] A := (Pi.basisFun O (Fin r)).constr O b
  let q : (Fin r → O) →L[O] A := ⟨q₀, q₀.continuous_on_pi⟩
  have hq : Function.Surjective q := by
    intro y
    refine ⟨(Pi.basisFun O (Fin r)) ((Fintype.equivFin A) y), ?_⟩
    change q₀ ((Pi.basisFun O (Fin r)) ((Fintype.equivFin A) y)) = y
    simp [q₀, b]
  let K := LinearMap.ker q₀
  let c : O := (Fintype.card A : ℕ)
  have hc : c ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := A))
  have hcA : ∀ y : A, c • y = 0 := by
    intro y
    change a (Fintype.card A : O) * y = 0
    simp only [map_natCast, ← nsmul_eq_mul]
    exact card_nsmul_eq_zero
  have hcK (x : Fin r → O) : c • x ∈ K := by
    change q₀ (c • x) = 0
    rw [map_smul, hcA]
  obtain ⟨n, snf⟩ := K.smithNormalForm (Pi.basisFun O (Fin r))
  have hsur : Function.Surjective snf.f := by
    intro i
    by_contra hi
    have hz := snf.repr_eq_zero_of_notMem_range
      (⟨c • snf.bM i, hcK (snf.bM i)⟩ : K) hi
    exact hc (by simpa using hz)
  let ef : Fin n ≃ Fin r := Equiv.ofBijective snf.f ⟨snf.f.injective, hsur⟩
  let eL : (Fin r → O) ≃ₗ[O] K := (snf.bN.reindex ef).equivFun.symm
  let φ₀ : (Fin r → O) →ₗ[O] (Fin r → O) := K.subtype.comp eL.toLinearMap
  let φ : (Fin r → O) →L[O] (Fin r → O) := ⟨φ₀, φ₀.continuous_on_pi⟩
  have hφ : Function.Injective φ := Subtype.val_injective.comp eL.injective
  have hex : LinearMap.range φ.toLinearMap = LinearMap.ker q.toLinearMap := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (eL y).property
    · intro hx
      exact ⟨eL.symm ⟨x, hx⟩, congrArg Subtype.val (eL.apply_symm_apply ⟨x, hx⟩)⟩
  have hker : ∃ e : (Fin r → O) ≃ₜ LinearMap.ker q.toLinearMap,
      ∀ x, (e x).val = φ x := by
    have he : Continuous eL := φ.continuous.subtype_mk _
    exact ⟨eL.toEquiv.toHomeomorphOfContinuousClosed he he.isClosedMap, fun _ ↦ rfl⟩
  let : HasFiniteBiproducts
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (Profinite.continuousCoefficientRingObj O)) := .of_hasFiniteProducts
  obtain ⟨hsec, hcond⟩ := Profinite.continuousSections_finiteDiscrete_shortExact
    O (Fin r → O) (Fin r → O) A φ q hφ hq hex hker
  refine ⟨r, q, φ, hq, hφ, ?_, ?_, hker, ?_, ?_, hcond⟩
  · exact LinearMap.exact_iff.mpr hex.symm
  · exact ⟨LinearMap.toMatrix' φ₀, fun x ↦ (LinearMap.toMatrix'_mulVec φ₀ x).symm⟩
  · intro S
    obtain ⟨F, G, hF, hG, hi, he, hs⟩ := hsec S
    have hF' : (fun f ↦ F f) =
        fun f ↦ ContinuousLinearMap.compLeftContinuous O S φ f := by
      funext f
      apply ContinuousMap.ext
      exact hF f
    have hG' : (fun f ↦ G f) =
        fun f ↦ ContinuousLinearMap.compLeftContinuous O S q f := by
      funext f
      apply ContinuousMap.ext
      exact hG f
    change Function.Injective (fun f ↦ ContinuousLinearMap.compLeftContinuous O S φ f) ∧
      Function.Exact (fun f ↦ ContinuousLinearMap.compLeftContinuous O S φ f)
        (fun f ↦ ContinuousLinearMap.compLeftContinuous O S q f) ∧
      Function.Surjective (fun f ↦ ContinuousLinearMap.compLeftContinuous O S q f)
    rw [← hF', ← hG']
    exact ⟨hi, he, hs⟩
  · let R := Profinite.continuousCoefficientRingObj O
    have hρ : (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
            (algebraMap O O) (continuous_algebraMap O O)) = 𝟙 R := by
      ext S f
      rfl
    let eR : Profinite.continuousSectionsModule O O ≅ Mod.regular R :=
      Mod.isoMk (Iso.refl R) (by
        change (_ ≫ _) ≫ 𝟙 R = _
        rw [hρ]
        change (MonoidalCategory.whiskerRight (𝟙 R) R) ≫ MonObj.mul =
          (MonoidalCategory.whiskerLeft R (𝟙 R)) ≫ MonObj.mul
        simp only [MonoidalCategory.id_whiskerRight,
          MonoidalCategory.whiskerLeft_id, Category.id_comp])
    let π : (i : Fin r) →
        Profinite.continuousSectionsModule O (Fin r → O) ⟶ Mod.regular R :=
      fun i ↦ sectionsMap (ContinuousLinearMap.proj i) ≫ eR.hom
    let ι : (i : Fin r) →
        Mod.regular R ⟶ Profinite.continuousSectionsModule O (Fin r → O) :=
      fun i ↦ eR.inv ≫ sectionsMap
      (ContinuousLinearMap.single O (fun _ : Fin r ↦ O) i)
    let B : Bicone (fun _i : Fin r ↦ Mod.regular R) :=
      { pt := Profinite.continuousSectionsModule O (Fin r → O)
        π := π
        ι := ι
        ι_π := by
          intro i j
          apply Mod.hom_ext
          ext S f
          apply ULift.ext
          apply ContinuousMap.ext
          intro s
          change (Pi.single i (f.down s) : Fin r → O) j = _
          split_ifs with h
          · subst j; simp
          · simp [h] }
    refine ⟨biproduct.uniqueUpToIso _ (isBilimitOfTotal B ?_)⟩
    apply Mod.hom_ext
    ext S f
    apply ULift.ext
    apply ContinuousMap.ext
    intro s
    let ev : (B.pt ⟶ B.pt) →+ (Fin r → O) :=
      { toFun g := ((g.hom.hom.app S) f).down s
        map_zero' := rfl
        map_add' _ _ := rfl }
    change ev (∑ i : Fin r, B.π i ≫ B.ι i) = f.down s
    rw [map_sum]
    change (∑ i : Fin r, (Pi.single i (f.down s i) : Fin r → O)) = f.down s
    exact Finset.univ_sum_single _

end Padic

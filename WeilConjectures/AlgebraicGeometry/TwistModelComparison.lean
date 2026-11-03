/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientFreeTensorLinear

/-! # Comparison of the two coefficient Tate twist constructions

Source: latest blueprint, part-six-operations/sec-coefficients-constructible/
sec-n-coefficients/sec-pulling-back-to-a-scheme/sk-def-sp-tate-twist/_section.md,
finite, integral, rational and algebraically closed coefficient paragraphs,
and def-coefficient-twists-detailed.md in that directory
(blueprint: lem-pod-twist-model-comparison).
All comparisons below are specified by quotient maps, root maps, limit
projections, scalar-extension units and colimit inclusions. Signed comparisons
are their tensor powers and inverse Hom transposes.

The identity-coefficient specialization of `podSignedComparison` also supplies
the encoding transport in `StrictWeilCondensed.tateLine_identification`, used by
the condensed Weil Tate-twist functor (blueprint: def-wf-tate-twist). Its unit,
tensor and evaluation normalizations retain the specified signed line and Weil
map; an arbitrary isomorphism of rank-one modules would not supply that datum.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The identity-on-roots section maps commute with restriction.
Source: clause 4 (blueprint: lem-pod-twist-model-comparison).
Proof: restriction on both presentations is the same ring-map action on units.
The kernel section identification is fixed by the injective inclusion into units,
so these two restrictions agree. -/
theorem podRootSectionMap_naturality (N : ℕ) (U V : X.ProEtᵒᵖ) (f : U ⟶ V) :
    (rootsOfUnityPresheaf X N).map f ≫ podRootSectionMap X N V =
      podRootSectionMap X N U ≫ (Scheme.proEtaleRootsOfUnitySheaf X N).obj.map f := by
  have hp (W : X.ProEtᵒᵖ) (z : (rootsOfUnityPresheaf X N).obj W) :
      Scheme.proEtaleRootsOfUnitySections X N W (podRootSectionMap X N W z) = z.down :=
    (Scheme.proEtaleRootsOfUnitySections X N W).apply_symm_apply z.down
  have hs (W : X.ProEtᵒᵖ) (x : (Scheme.proEtaleRootsOfUnitySheaf X N).obj.obj W) :
      ULift.up (Additive.ofMul (Scheme.proEtaleRootsOfUnitySections X N W x).toMul.val) =
        (Scheme.proEtaleRootsOfUnityInclusion X N).hom.app W x :=
    (Scheme.existsUnique_proEtaleRootsOfUnitySections X N W).exists.choose_spec x
  ext z
  apply (Scheme.proEtaleRootsOfUnitySections X N V).injective
  change Scheme.proEtaleRootsOfUnitySections X N V
      (podRootSectionMap X N V ((rootsOfUnityPresheaf X N).map f z)) =
    Scheme.proEtaleRootsOfUnitySections X N V
      ((Scheme.proEtaleRootsOfUnitySheaf X N).obj.map f (podRootSectionMap X N U z))
  rw [hp]
  apply Additive.toMul.injective
  apply Subtype.ext
  have h := congrArg (fun b ↦ b (podRootSectionMap X N U z))
    ((Scheme.proEtaleRootsOfUnityInclusion X N).hom.naturality f)
  change (Scheme.proEtaleRootsOfUnityInclusion X N).hom.app V
      ((Scheme.proEtaleRootsOfUnitySheaf X N).obj.map f (podRootSectionMap X N U z)) =
    (Scheme.proEtaleUnitsSheaf X).obj.map f
      ((Scheme.proEtaleRootsOfUnityInclusion X N).hom.app U (podRootSectionMap X N U z)) at h
  rw [← hs V _, ← hs U _, hp] at h
  exact (congrArg (fun y ↦ y.down.toMul) h).symm

/-- The two root models identify the same roots, before imposing invertibility of ell.
Source: all finite levels (blueprint: lem-pod-twist-model-comparison).
Proof: the kernel sheaf and the sheafification of the root presheaf represent
sections of units killed by N. The section identification commutes with every
restriction; its inverse induces the inverse sheaf map by sheafification. -/
@[instance] theorem podRootMap_isIso (N : ℕ) : IsIso (podRootMap X N) := by
  let e := PurityTransport.rootComparison X N
  have he := (PurityTransport.rootComparison_existsUnique X N).exists.choose_spec
  have hmap : podRootMap X N = e.hom := by
    apply Equiv.injective
      ((sheafificationAdjunction (Scheme.ProEt.topology X) Ab.{u + 1}).homEquiv _ _)
    rw [podRootMap, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    ext U z
    apply (Scheme.proEtaleRootsOfUnitySections X N U).injective
    change (Scheme.proEtaleRootsOfUnitySections X N U)
      ((Scheme.proEtaleRootsOfUnitySections X N U).symm z.down) =
        (Scheme.proEtaleRootsOfUnitySections X N U)
          (e.hom.hom.app U ((toSheafify (Scheme.ProEt.topology X)
            (rootsOfUnityPresheaf X N)).app U z))
    rw [AddEquiv.apply_symm_apply]
    exact (he U z).symm
  rw [hmap]
  infer_instance

/-- Lifting the fixed finite field changes no coefficient or finite dimension.
Source: the fixed finite intermediate extension (blueprint: lem-pod-twist-model-comparison).
Proof: ULift.algEquiv is a Q_ell-linear equivalence; transport a finite basis along
its inverse. This supplies the scheme universe without restricting the scheme. -/
@[instance] theorem podLiftFiniteDimensional (F : PadicAlgCl.FiniteIntermediateField l) :
    FiniteDimensional ℚ_[l] (ULift.{u} F.1) := by
  exact Module.Finite.equiv (ULift.algEquiv (R := ℚ_[l]) (A := F.1)).symm.toLinearEquiv

/-- The integer-ring identification is fixed on every element of the finite field.
Source: coefficient convention, spIntegers_eq (blueprint: lem-pod-twist-model-comparison).
Proof: uniqueness of the extending absolute value identifies the lifted spectral
integer subring with the integer subring of the fixed algebraic closure. Restrict
ULift.ringEquiv to these subrings. Injectivity into F gives uniqueness. -/
theorem podIntegerEquiv_existsUnique (F : PadicAlgCl.FiniteIntermediateField l) :
    ∃! e : Padic.coefficientExtensionIntegers l (ULift.{u} F.1) ≃+*
        PadicAlgCl.integers l F.1,
      ∀ a, (e a).val = a.val.down := by
  have hm (a : ULift.{u} F.1) :
      a ∈ Padic.coefficientExtensionIntegers l (ULift.{u} F.1) ↔
        a.down ∈ (PadicAlgCl.integers l F.1).toSubring := by
    rw [← spIntegers_eq l F]
    have hLift : a ∈ Padic.coefficientExtensionIntegers l (ULift.{u} F.1) ↔
        spectralNorm ℚ_[l] (ULift.{u} F.1) a ≤ 1 :=
      (Padic.extension_integers_dvr l (ULift.{u} F.1)
        (Padic.coefficientExtensionAbsoluteValue l (ULift.{u} F.1))
        (spectralNorm_extends (K := ℚ_[l]) (L := ULift.{u} F.1))).choose_spec.choose_spec.1 a
    have hBase : a.down ∈ Padic.coefficientExtensionIntegers l F.1 ↔
        spectralNorm ℚ_[l] F.1 a.down ≤ 1 :=
      (Padic.extension_integers_dvr l F.1 (Padic.coefficientExtensionAbsoluteValue l F.1)
        (spectralNorm_extends (K := ℚ_[l]) (L := F.1))).choose_spec.choose_spec.1 a.down
    rw [hLift, hBase]
    unfold spectralNorm
    rw [← minpoly.algEquiv_eq (ULift.algEquiv (R := ℚ_[l]) (A := F.1)) a]
    rfl
  let e0 : ULift.{u} F.1 ≃+* F.1 := ULift.ringEquiv
  let e := e0.restrict (Padic.coefficientExtensionIntegers l (ULift.{u} F.1))
    (PadicAlgCl.integers l F.1).toSubring hm
  refine ⟨e, fun _ ↦ rfl, ?_⟩
  intro e' he
  apply RingEquiv.ext
  intro a
  apply Subtype.ext
  exact he a

private theorem podSpectralMetric (l : ℕ) [Fact l.Prime] (T : Type u)
    [hT : NormedField T] [NormedAlgebra ℚ_[l] T] [FiniteDimensional ℚ_[l] T] :
    (spectralNorm.normedField ℚ_[l] T).toMetricSpace = hT.toMetricSpace := by
  apply MetricSpace.ext
  apply Dist.ext
  funext a b
  rw [(spectralNorm.normedField ℚ_[l] T).dist_eq, hT.dist_eq]
  exact (NormedAlgebra.norm_eq_spectralNorm ℚ_[l] (-a + b)).symm

private theorem podContinuousRingIso_existsUnique
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {B : Type} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (e : A ≃+* B) (hc : Continuous e) (hi : Continuous e.symm) :
    ∃! i : Profinite.continuousCoefficientRingObj A ≅ Profinite.continuousMapRingObj B,
      IsMonHom i.hom ∧ ∀ (S : Profinite.{u}ᵒᵖ)
        (a : (Profinite.continuousCoefficientRingObj A).obj.obj S) (x : S.unop),
        ((i.hom.hom.app S) a).down x = e (a.down x) := by
  let j : Profinite.continuousCoefficientRingSheaf A ≅ Profinite.continuousMapRingSheaf B :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop hc).comp ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hi).comp
              ULift.ringEquiv.toRingHom))
        naturality := fun _ _ _ ↦ rfl }⟩
      hom_inv_id := by
        ext S a
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S a
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let H := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})
  refine ⟨H.mapIso j, ⟨?_, fun _ _ _ ↦ rfl⟩, ?_⟩
  · change IsMonHom (H.map j.hom)
    dsimp only [H]
    infer_instance
  · intro i hi
    apply Iso.ext
    ext S a
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    exact hi.2 S a x

/-- The rational coefficient identification is pointwise ULift.down.
Source: clause 3 (blueprint: lem-pod-twist-model-comparison).
Proof: uniqueness of the extending absolute value makes ULift.down a topological
field isomorphism. Postcomposition gives the isomorphism of continuous function
sheaves. Evaluation on all profinite points determines it uniquely. -/
theorem podRationalRingIso_existsUnique (F : PadicAlgCl.FiniteIntermediateField l) :
    ∃! e : twistRationalRing l (ULift.{u} F.1) ≅
        Profinite.continuousMapRingObj.{u} F.1,
      IsMonHom e.hom ∧ ∀ (S : Profinite.{u}ᵒᵖ)
        (s : (twistRationalRing l (ULift.{u} F.1)).obj.obj S) (x : S.unop),
        ((e.hom.hom.app S) s).down x = (s.down x).down := by
  let : NormedField (ULift.{u} F.1) :=
    { (inferInstance : NormedCommRing (ULift.{u} F.1)),
      (inferInstance : Field (ULift.{u} F.1)) with
      norm_mul a b := norm_mul a.down b.down }
  let tn : TopologicalSpace (ULift.{u} F.1) := inferInstance
  have hring : @IsTopologicalRing (ULift.{u} F.1) tn inferInstance := inferInstance
  let e : ULift.{u} F.1 ≃ₐ[ℚ_[l]] F.1 := ULift.algEquiv
  have hc : Continuous e := e.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hi : Continuous e.symm :=
    e.symm.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  let ts : TopologicalSpace (ULift.{u} F.1) :=
    (spectralNorm.normedField ℚ_[l] (ULift.{u} F.1)).toMetricSpace
      |>.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have ht : ts = tn :=
    congrArg (fun m : MetricSpace (ULift.{u} F.1) ↦
      m.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
        (podSpectralMetric l (ULift.{u} F.1))
  exact @podContinuousRingIso_existsUnique.{u}
    (ULift.{u} F.1) inferInstance ts (by rw [ht]; exact hring)
    F.1 inferInstance inferInstance inferInstance e.toRingEquiv
      (by rw [ht]; exact hc)
      (by rw [ht]; exact hi)

/-- The positive detailed coefficient quotient is finite.
Source: clause 1 (blueprint: lem-pod-twist-model-comparison).
Proof: apply finite_coefficientExtensionRing at n+1, which is positive. -/
@[instance] theorem podFiniteCoefficient_finite (F : PadicAlgCl.FiniteIntermediateField l)
    (n : ℕ) : Finite (Padic.coefficientExtensionRing l (ULift.{u} F.1) (n + 1)) := by
  exact Padic.finite_coefficientExtensionRing l (ULift.{u} F.1) (n + 1) (Nat.succ_pos n)

/-- Ell^(n+1) annihilates the chosen finite coefficient representative.
Source: clause 1 (blueprint: lem-pod-twist-model-comparison).
Proof: ell belongs to the maximal ideal (pi), so its (n+1)-st power belongs
to (pi^(n+1)). The same equation holds after ULift. -/
theorem podFiniteCoefficient_annihilated (F : PadicAlgCl.FiniteIntermediateField l)
    (n : ℕ) :
    (l ^ (n + 1) : ULift.{u + 1}
      (Padic.coefficientExtensionRing l (ULift.{u} F.1) (n + 1))) = 0 := by
  apply ULift.down_injective
  exact coefficientFiniteTwist_annihilator l (ULift.{u} F.1) n

/-- The section realization of a signed map into the recorded sketched construction.
The equivalence counit is part of the encoding identification.
Source: signed paragraph (blueprint: lem-pod-twist-model-comparison). -/
def podSignedRealization
    (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S) (m : ℤ)
    (f : coefficientSignedTwist X R L m ⟶
      (Mod.comap φ).obj (spInternalSignedTwist X S M m)) :
    (coefficientSignedTwist X R L m).X ⟶
      (SheafOfModules.toSheaf _).obj (spSignedTwist X S M m) :=
  f.hom ≫ (SheafOfModules.toSheaf _).map
    ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X) S).counitIso.app (spSignedTwist X S M m)).hom

/-- Exact normalization of all signed comparisons against spInternalSignedTwist.
Zero is the coefficient identity after scalar identification; one is the degree-one
map with the harmless source unitor. Positive degrees fix every pure tensor.
Negative degrees are the inverse transpose, characterized by evaluation.
Source: final paragraph (blueprint: lem-pod-twist-model-comparison). -/
structure PodSignedComparisonSpec
    (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ≅ S) [IsMonHom φ.hom]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)
    (e : L ≅ (Mod.comap φ.hom).obj M)
    (gamma : ∀ m : ℤ, coefficientSignedTwist X R L m ≅
      (Mod.comap φ.hom).obj (spInternalSignedTwist X S M m)) : Prop where
  zero : ∀ (U : X.ProEtᵒᵖ) (r : R.obj.obj U),
    (podSignedRealization X R S φ.hom L M 0 (gamma 0).hom).hom.app U r =
      φ.hom.hom.app U r
  one : podSignedRealization X R S φ.hom L M 1 (gamma 1).hom =
    (λ_ L).hom.hom ≫ e.hom.hom
  tensor : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (x : (coefficientTwistNat X R L (n + 1)).X.obj.obj U) (y : L.X.obj.obj U),
    (podSignedRealization X R S φ.hom L M (n + 2) (gamma (n + 2)).hom).hom.app U
      (InternalAbelianSheafModule.comparison_internalTmul (Scheme.ProEt.topology X) R
        (coefficientTwistNat X R L (n + 1)) L U x y) =
      SheafOfModules.siteSheafTensorTmul (spSignedTwist X S M (n + 1))
        ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) S).functor.obj M) U
        ((podSignedRealization X R S φ.hom L M (n + 1) (gamma (n + 1)).hom).hom.app U x)
        (e.hom.hom.hom.app U y)
  dual : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
      (d : (coefficientSignedTwist X R L (.negSucc n)).X.obj.obj U)
      (x : (coefficientTwistNat X R L (n + 1)).X.obj.obj U),
    (((podSignedRealization X R S φ.hom L M (.negSucc n)
        (gamma (.negSucc n)).hom).hom.app U d).app (op (Over.mk (𝟙 U.unop))))
      ((podSignedRealization X R S φ.hom L M (n + 1) (gamma (n + 1)).hom).hom.app U x) =
      φ.hom.hom.app U
        (((ihom.ev (coefficientTwistNat X R L (n + 1))).app (𝟙_ _)).hom.hom.app U
          (InternalAbelianSheafModule.comparison_internalTmul (Scheme.ProEt.topology X) R
            (coefficientTwistNat X R L (n + 1))
            ((ihom (coefficientTwistNat X R L (n + 1))).obj (𝟙_ _)) U x d))

/-- The specified signed maps exist uniquely, with the recorded sketched targets.
Source: final paragraph (blueprint: lem-pod-twist-model-comparison).
Proof: identify the internal relative tensor with the sheafified balanced section
tensor, and the internal unit with the section unit. The identity on sections and
on pure tensors fixes these comparisons. A coefficient-ring isomorphism gives the
same identifications after restricting scalars. In degree one use e and the unitor;
iterate the tensor pairing for positive powers. The closed adjunction identifies
internal Hom with sectionwise sheaf Hom. Send a functional to its composite with
the inverse positive comparison and the coefficient isomorphism. This is exactly
the displayed evaluation formula. Its inverse uses e inverse. Unit sections,
local tensor generators and evaluation respectively give uniqueness in every degree. -/
theorem podSignedComparison_existsUnique
    (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ≅ S) [IsMonHom φ.hom]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)
    (e : L ≅ (Mod.comap φ.hom).obj M) :
    ∃! gamma : ∀ m : ℤ, coefficientSignedTwist X R L m ≅
        (Mod.comap φ.hom).obj (spInternalSignedTwist X S M m),
      PodSignedComparisonSpec X R S φ L M e gamma := by
  sorry

/-- Gamma_m itself, selected by the complete tensor, unit and inverse-transpose normalization.
Source: final paragraph (blueprint: lem-pod-twist-model-comparison). -/
def podSignedComparison
    (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ≅ S) [IsMonHom φ.hom]
    (L : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)
    (e : L ≅ (Mod.comap φ.hom).obj M) :=
  (podSignedComparison_existsUnique X R S φ L M e).exists.choose

/-- The identity coefficient isomorphism preserves the ring operations.
Source: zero-degree convention (blueprint: lem-pod-twist-model-comparison).
Proof: the hom of Iso.refl is the identity ring morphism, preserving unit and
multiplication. This exposes that instance without unfolding coefficient objects. -/
@[instance] theorem podIdentityIso_isMonHom
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    IsMonHom (Iso.refl R).hom := by
  change IsMonHom (𝟙 R)
  infer_instance

/-- The detailed generic signed convention specializes to the published Qbar twist.
Source: detailed Qbar signed convention (blueprint: lem-pod-twist-model-comparison).
Proof: induction on the natural exponent identifies the two recursions for tensor
powers, including the unit at zero. In each negative degree both definitions are
the internal Hom from that same positive power into the unit. -/
theorem podQbarDetailedSigned_eq (m : ℤ) :
    tateTwist X l m = coefficientSignedTwist X
      (condensedRingObj (Profinite.padicAlgClRingObj l) X) (tateTwistOne X l) m := by
  have hn (n : ℕ) : tateTwistNat X l n = coefficientTwistNat X
      (condensedRingObj (Profinite.padicAlgClRingObj l) X) (tateTwistOne X l) n := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [tateTwistNat, coefficientTwistNat, ih]
  cases m with
  | ofNat n => exact hn n
  | negSucc n =>
    dsimp only [tateTwist, coefficientSignedTwist]
    rw [hn]

end AlgebraicGeometry.ProEtale

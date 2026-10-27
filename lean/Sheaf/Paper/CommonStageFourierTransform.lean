/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.Paper.WeilFourierTransform
public import WeilConjectures.FourierTransform.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
public import Sheaf.Paper.FourierAdicArtinSchreier
public import Sheaf.Paper.CommonStageWeilShriek
public import Sheaf.Paper.CompletedPullbackTensorComparison
import Sheaf.Paper.DerivedPullbackTensorIso
import Sheaf.AlgebraicGeometry.FrobeniusDetailed

/-! # Fourier transform on the recorded adic fixed-pair category

Source: Laumon, Transformation de Fourier, Definition 1.2.1.1, pp. 140--141;
blueprint main-20261015, sk-def-ft (blueprint: def-fd-transform).

The existing ordinary-etale and derived-of-Weil transforms remain public imports.
The fixed-pair version uses the actual common-stage tensor and compact support.
The shifted character kernel is first formed on the finite-field model and then
pulled to the geometric fibre. Its Weil structure is the normalized pullback
composition comparison for g followed by the model projection. Thus no independent
choice of a Frobenius automorphism or a shift comparison enters the construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
namespace WeilConjectures

variable (F : FourierSetting.{u})

/-- The coefficient prime is invertible on every finite-field model.
Source: the characteristic assumptions in sk-def-ft (blueprint: def-fd-transform).
Proof: the cardinality q=p^a fixes characteristic p on k0. Since l differs from p,
l is a unit in k0, hence in every residue-field k0-algebra of the model. -/
theorem fourierModelPrime_isUnit (X₀ : Over (Spec (.of F.field.k₀))) :
    ∀ x : X₀.left, IsUnit (F.coefficients.l : X₀.left.residueField x) := by
  classical
  let := Fintype.ofFinite F.field.k₀
  let : Fact F.field.p.Prime := ⟨F.field.prime⟩
  have : CharP F.field.k₀ F.field.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using
      F.field.card_base.trans F.field.cardinality_eq)
  have hunit : IsUnit (F.coefficients.l : F.field.k₀) :=
    (CharP.cast_ne_zero_of_ne_of_prime F.field.k₀
      (Fact.out : F.coefficients.l.Prime) F.coefficients.different.symm).isUnit
  intro x
  simpa only [map_natCast] using hunit.map
    ((Scheme.ΓSpecIso (CommRingCat.of F.field.k₀)).inv ≫ X₀.hom.appTop ≫
      X₀.left.Γevaluation x).hom

/-- The inherited residue-field unit, adding no hypothesis.
Source: sk-def-ft, coefficient convention (blueprint: def-fd-transform). -/
@[instance_reducible]
def fourierModelPrimeInvertible (X₀ : Over (Spec (.of F.field.k₀))) (x : X₀.left) :
    Invertible (F.coefficients.l : X₀.left.residueField x) :=
  (fourierModelPrime_isUnit F X₀ x).invertible

/-- Projection of the geometric fibre to its finite-field model.
Source: sk-def-ft and the fixed-pair convention (blueprint: def-fd-transform). -/
def fourierModelProjection (X₀ : Over (Spec (.of F.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (F.field.geometricFiber X₀).left ⟶ X₀.left :=
  pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (algebraMap F.field.k₀ F.field.k)))

/-- Geometric Frobenius fixes the finite-field model projection.
Source: Laumon 1.1; geometric-Frobenius convention (blueprint: def-fd-transform).
Proof: apply galoisMap_projections to the inverse q-power field automorphism.
The first pullback projection is unchanged, although the closure projection is
semilinear. This does not assert that geometric points are fixed pointwise. -/
theorem fourierModelProjection_frobenius (X₀ : Over (Spec (.of F.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] :
    (F.field.geometricFrobenius X₀).hom ≫ fourierModelProjection F X₀ =
      fourierModelProjection F X₀ := by
  let := Fintype.ofFinite F.field.k₀
  exact (F.field.galoisMap_projections X₀.hom
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic F.field.k₀ F.field.k)).1

/-- The canonical Weil pair attached to a complex defined on the finite-field model.
Its structure is the inverse normalized composition comparison followed by the
actual equality of scheme maps, not an arbitrary isomorphism.
Source: Laumon 1.1 and sk-def-ft (blueprint: def-fd-transform). -/
def fourierModelWeil (X₀ : Over (Spec (.of F.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (A : generalAlgebraicallyClosedConstructibleCategory F.coefficients.l
      F.coefficients.Qbar X₀.left) :
    sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      X₀ F.coefficients.Qbar :=
  letI := fourierModelPrimeInvertible F X₀
  letI := sfWeilPrimeInvertible F.field F.coefficients.l F.coefficients.different X₀
  IsoAlgebra.mk
    ((commonStageDerivedPullback F.coefficients.l F.coefficients.Qbar
      (fourierModelProjection F X₀)).obj A)
    ((zlPullComp F.coefficients.l F.coefficients.Qbar
        (F.field.geometricFrobenius X₀).hom (fourierModelProjection F X₀)).symm.app A ≪≫
      (eqToIso (congrArg (fun f ↦ commonStageDerivedPullback F.coefficients.l
        F.coefficients.Qbar f) (fourierModelProjection_frobenius F X₀))).app A)

/-- Tensor on the right with the carrier of a specified Weil pair.
Source: sk-def-ft, tensor factor of the transform (blueprint: def-fd-transform). -/
def fourierTensorUnderlying (X₀ : Over (Spec (.of F.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (N : sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      X₀ F.coefficients.Qbar) :
    generalAlgebraicallyClosedConstructibleCategory F.coefficients.l F.coefficients.Qbar
        (F.field.geometricFiber X₀).left ⥤
      generalAlgebraicallyClosedConstructibleCategory F.coefficients.l F.coefficients.Qbar
        (F.field.geometricFiber X₀).left :=
  letI := sfWeilPrimeInvertible F.field F.coefficients.l F.coefficients.different X₀
  (Functor.prod' (𝟭 _) ((Functor.const _).obj N.carrier)) ⋙
    commonStageDerivedTensor F.coefficients.l F.coefficients.Qbar
      (F.field.geometricFiber X₀).left

/-- The tensor Frobenius comparison, with its canonical monoidal first factor.
Source: sk-def-ft and tensor Weil structures (blueprint: def-fd-transform). -/
def fourierTensorFrobeniusComponent (X₀ : Over (Spec (.of F.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (N : sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      X₀ F.coefficients.Qbar)
    (P : generalAlgebraicallyClosedConstructibleCategory F.coefficients.l
      F.coefficients.Qbar (F.field.geometricFiber X₀).left) :
    (sfCommonStageWeilFrobeniusPullback F.field F.coefficients.l
      F.coefficients.different X₀ F.coefficients.Qbar).obj
        ((fourierTensorUnderlying F X₀ N).obj P) ≅
      (fourierTensorUnderlying F X₀ N).obj
        ((sfCommonStageWeilFrobeniusPullback F.field F.coefficients.l
          F.coefficients.different X₀ F.coefficients.Qbar).obj P) :=
  letI := sfWeilPrimeInvertible F.field F.coefficients.l F.coefficients.different X₀
  canonicalCommonStagePullbackTensor F.coefficients.l F.coefficients.Qbar
      (F.field.geometricFrobenius X₀).hom P N.carrier ≪≫
    (commonStageDerivedTensor F.coefficients.l F.coefficients.Qbar
      (F.field.geometricFiber X₀).left).mapIso (Iso.prod (Iso.refl _) N.str)

/-- Naturality of the specified tensor Frobenius comparison.
Source: sk-def-ft and the monoidal pullback comparison (blueprint: def-fd-transform).
Proof: apply naturality of canonicalCommonStagePullbackTensor to (f,id_N).
Functoriality of tensor then moves the fixed isomorphism N.str across f.
The two composites are exactly the displayed naturality equation. -/
theorem fourierTensorFrobenius_naturality (X₀ : Over (Spec (.of F.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (N : sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      X₀ F.coefficients.Qbar)
    {P Q : generalAlgebraicallyClosedConstructibleCategory F.coefficients.l
      F.coefficients.Qbar (F.field.geometricFiber X₀).left} (f : P ⟶ Q) :
    (fourierTensorUnderlying F X₀ N ⋙ sfCommonStageWeilFrobeniusPullback F.field
      F.coefficients.l F.coefficients.different X₀ F.coefficients.Qbar).map f ≫
        (fourierTensorFrobeniusComponent F X₀ N Q).hom =
      (fourierTensorFrobeniusComponent F X₀ N P).hom ≫
        (sfCommonStageWeilFrobeniusPullback F.field F.coefficients.l
          F.coefficients.different X₀ F.coefficients.Qbar ⋙
            fourierTensorUnderlying F X₀ N).map f := by
  let := sfWeilPrimeInvertible F.field F.coefficients.l F.coefficients.different X₀
  obtain ⟨e, he⟩ := (derivedPullbackTensorIso F.coefficients.l (fourierCoefficient F)
    (F.field.geometricFrobenius X₀).hom 0 F.coefficients.Qbar).2.2.2.2.2.2.2.1
  have h := e.hom.naturality (Prod.mkHom f (𝟙 N.carrier))
  change _ ≫ (e.app (Q, N.carrier)).hom = (e.app (P, N.carrier)).hom ≫ _ at h
  rw [he Q N.carrier, he P N.carrier] at h
  dsimp [fourierTensorUnderlying, fourierTensorFrobeniusComponent,
    sfCommonStageWeilFrobeniusPullback] at h ⊢
  rw [← Category.assoc, h]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 1
  congr 1
  ext <;> simp

/-- The normalized natural tensor/Frobenius isomorphism.
Source: sk-def-ft (blueprint: def-fd-transform). -/
def fourierTensorFrobenius (X₀ : Over (Spec (.of F.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (N : sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      X₀ F.coefficients.Qbar) :
    fourierTensorUnderlying F X₀ N ⋙ sfCommonStageWeilFrobeniusPullback F.field
        F.coefficients.l F.coefficients.different X₀ F.coefficients.Qbar ≅
      sfCommonStageWeilFrobeniusPullback F.field F.coefficients.l
        F.coefficients.different X₀ F.coefficients.Qbar ⋙ fourierTensorUnderlying F X₀ N :=
  NatIso.ofComponents (fourierTensorFrobeniusComponent F X₀ N)
    (fun f ↦ fourierTensorFrobenius_naturality F X₀ N f)

/-- Tensor with a Weil pair, on objects and all equivariant underlying morphisms.
Source: sk-def-ft (blueprint: def-fd-transform). -/
def fourierWeilTensorFunctor (X₀ : Over (Spec (.of F.field.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (N : sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      X₀ F.coefficients.Qbar) :
    sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
        X₀ F.coefficients.Qbar ⥤
      sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
        X₀ F.coefficients.Qbar :=
  IsoAlgebra.mapOfNatIso (fourierTensorFrobenius F X₀ N)

/-- The whole integral-transform functor on the actual fixed pairs. Its action on an
arrow is the recorded pullback, tensor with identity of the shifted kernel, and compact
support. Identities and composition are those of the three existing functors.
Source: Laumon Definition 1.2.1.1, sk-def-ft (blueprint: def-fd-transform). -/
def commonStageFourierTransformFunctor
    {V₀ V₀' W₀ : Over (Spec (.of F.field.k₀))}
    [LocallyOfFiniteType V₀.hom] [QuasiCompact V₀.hom]
    [LocallyOfFiniteType V₀'.hom] [QuasiCompact V₀'.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
    (p₁ : W₀ ⟶ V₀) (p₂ : W₀ ⟶ V₀') (c : Compactification p₂.left)
    (A : generalAlgebraicallyClosedConstructibleCategory F.coefficients.l
      F.coefficients.Qbar W₀.left) (r : ℤ) :
    sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
        V₀ F.coefficients.Qbar ⥤
      sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
        V₀' F.coefficients.Qbar :=
  IsoAlgebra.mapOfNatIso (zlFrobeniusSquare F.field F.coefficients.l
      F.coefficients.different F.coefficients.Qbar p₁) ⋙
    fourierWeilTensorFunctor F W₀
      (fourierModelWeil F W₀ ((shiftFunctor _ r).obj A)) ⋙
    zlComplexShriek F.field F.coefficients.l F.coefficients.different F.coefficients.Qbar p₂ c

/-- The canonical common-stage integral transform on Weil pairs. The kernel A is
formed on W0 over k0. Moving [r] to the kernel uses the standard signed tensor-shift
and exact compact-support shift comparisons, so its underlying object is exactly
Rp2!(p1*K tensor A)[r], up to those canonical comparisons.
Source: Laumon Definition 1.2.1.1 (blueprint: def-fd-transform). -/
def commonStageFourierTransform
    {V₀ V₀' W₀ : Over (Spec (.of F.field.k₀))}
    [LocallyOfFiniteType V₀.hom] [QuasiCompact V₀.hom]
    [LocallyOfFiniteType V₀'.hom] [QuasiCompact V₀'.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
    (p₁ : W₀ ⟶ V₀) (p₂ : W₀ ⟶ V₀') (c : Compactification p₂.left)
    (A : generalAlgebraicallyClosedConstructibleCategory F.coefficients.l
      F.coefficients.Qbar W₀.left) (r : ℤ)
    (K : sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      V₀ F.coefficients.Qbar) :
    sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      V₀' F.coefficients.Qbar :=
  (commonStageFourierTransformFunctor F p₁ p₂ c A r).obj K

/-- The standard affine-space model over the finite field, as an over-object.
Source: sk-def-ft, vector-space application (blueprint: def-fd-transform). -/
abbrev fourierAffineModel (n : Type u) : Over (Spec (.of F.field.k₀)) :=
  Over.mk (AffineSpace n (Spec (.of F.field.k₀)) ↘ Spec (.of F.field.k₀))

/-- The finite affine model is of finite type.
Source: sk-def-ft (blueprint: def-fd-transform).
Proof: affine space in finitely many variables is finite type over its base field. -/
@[instance] theorem fourierAffineModel_finiteType (n : Type u) [Finite n] :
    LocallyOfFiniteType (fourierAffineModel F n).hom := by
  dsimp [fourierAffineModel]
  infer_instance

/-- The affine model is quasi-compact over its field.
Source: sk-def-ft (blueprint: def-fd-transform).
Proof: its structure morphism is affine, hence quasi-compact. -/
@[instance] theorem fourierAffineModel_quasiCompact (n : Type u) :
    QuasiCompact (fourierAffineModel F n).hom := by
  dsimp [fourierAffineModel]
  infer_instance

/-- The affine model is separated over its field.
Source: sk-def-ft (blueprint: def-fd-transform).
Proof: affine morphisms are separated. -/
@[instance] theorem fourierAffineModel_separated (n : Type u) :
    IsSeparated (fourierAffineModel F n).hom := by
  dsimp [fourierAffineModel]
  infer_instance

/-- The product of the model with its coordinate dual, over k0.
Source: sk-def-ft, standard evaluation pairing (blueprint: def-fd-transform). -/
abbrev fourierSquareModel (n : Type u) : Over (Spec (.of F.field.k₀)) :=
  Over.mk (pullback.fst (fourierAffineModel F n).hom (fourierAffineModel F n).hom ≫
    (fourierAffineModel F n).hom)

/-- The actual product projections and structure map are finite type and quasi-compact.
Source: Laumon 1.2.1.1 (blueprint: def-fd-transform).
Proof: finite-dimensional affine space is affine and finite type over k0. The two
projections are its base changes; composition gives the product structure map. -/
theorem fourierSquareModel_geometry (n : Type u) [Finite n] :
    LocallyOfFiniteType (fourierSquareModel F n).hom ∧
      QuasiCompact (fourierSquareModel F n).hom ∧
      IsNoetherian (fourierSquareModel F n).left := by
  have hft : LocallyOfFiniteType (fourierSquareModel F n).hom := by
    dsimp [fourierSquareModel]
    infer_instance
  have hqc : QuasiCompact (fourierSquareModel F n).hom := by
    dsimp [fourierSquareModel]
    infer_instance
  let : IsLocallyNoetherian (fourierSquareModel F n).left :=
    LocallyOfFiniteType.isLocallyNoetherian (fourierSquareModel F n).hom
  let : QuasiCompact (fourierSquareModel F n).hom := hqc
  let : CompactSpace (fourierSquareModel F n).left :=
    QuasiCompact.compactSpace_of_compactSpace (fourierSquareModel F n).hom
  exact ⟨hft, hqc, ⟨⟩⟩

/-- The standard pairing scheme has characteristic p, including in rank zero.
Source: sk-def-ft, characteristic-p base (blueprint: def-fd-transform).
Proof: k0 has cardinality p^a, with a positive, hence characteristic p. Global
functions on its affine product are a nonzero k0-algebra and have characteristic p. -/
theorem fourierSquareModel_characteristic (n : Type u) :
    CharP Γ((fourierSquareModel F n).left, ⊤) F.field.p := by
  classical
  let := Fintype.ofFinite F.field.k₀
  let : Fact F.field.p.Prime := ⟨F.field.prime⟩
  have : CharP F.field.k₀ F.field.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using
      F.field.card_base.trans F.field.cardinality_eq)
  let z := AffineSpace.zeroSection n (Spec (.of F.field.k₀))
  let s : Spec (.of F.field.k₀) ⟶ (fourierSquareModel F n).left :=
    pullback.lift z z rfl
  have : Nontrivial Γ((fourierSquareModel F n).left, ⊤) := s.appTop.hom.domain_nontrivial
  exact CharP.of_ringHom_of_ne_zero
    ((Scheme.ΓSpecIso (CommRingCat.of F.field.k₀)).inv ≫
      (fourierSquareModel F n).hom.appTop).hom F.field.p F.field.prime.ne_zero

/-- The first projection, over the finite field.
Source: sk-def-ft (blueprint: def-fd-transform). -/
def fourierModelFst (n : Type u) : fourierSquareModel F n ⟶ fourierAffineModel F n :=
  Over.homMk (pullback.fst _ _) rfl

/-- The second projection, over the finite field.
Source: sk-def-ft (blueprint: def-fd-transform). -/
def fourierModelSnd (n : Type u) : fourierSquareModel F n ⟶ fourierAffineModel F n :=
  Over.homMk (pullback.snd _ _) pullback.condition.symm

/-- Fourier transform of actual common-stage Weil pairs on standard affine space.
The standard pairing identifies the dual with the same coordinate space. The prime-field
character gives psi by trace composition. This includes rank zero and all positive ranks;
on the affine line the signed shift is [1]. Compactification is an implementation choice,
and the trace identity holds for every such choice.
Source: Laumon 1.2.1.1; blueprint sk-def-ft (blueprint: def-fd-transform). -/
def affineCommonStageFourierTransform (n : Type u) [Fintype n]
    (Ψ : AddChar (ZMod F.field.p) F.coefficients.Qbar)
    (c : Compactification (fourierModelSnd F n).left)
    (K : sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      (fourierAffineModel F n) F.coefficients.Qbar) :
    sfCommonStageWeilComplex F.field F.coefficients.l F.coefficients.different
      (fourierAffineModel F n) F.coefficients.Qbar :=
  letI := (fourierSquareModel_geometry F n).1
  letI := (fourierSquareModel_geometry F n).2.1
  letI : IsNoetherian
      (pullback (fourierAffineModel F n).hom (fourierAffineModel F n).hom) :=
    (fourierSquareModel_geometry F n).2.2
  letI : CharP Γ(pullback (fourierAffineModel F n).hom (fourierAffineModel F n).hom, ⊤)
      F.field.p := fourierSquareModel_characteristic F n
  commonStageFourierTransform F (fourierModelFst F n) (fourierModelSnd F n) c
    (fourierAdicKernel F (fourierAffineModel F n).hom (fourierAffineModel F n).hom
      Ψ (AffineSpace.stdPairing n (Spec (.of F.field.k₀)))) (Fintype.card n) K

/-- The fixed base field has the stated characteristic p.
Source: sk-def-fourier-set and sk-def-char (blueprint: def-fd-transform).
Proof: k0 is a finite field of cardinality p^a, with p prime and a positive;
the unique prime dividing its cardinality is its characteristic. -/
theorem fourierBaseCharacteristic : CharP F.field.k₀ F.field.p := by
  classical
  let := Fintype.ofFinite F.field.k₀
  let : Fact F.field.p.Prime := ⟨F.field.prime⟩
  exact charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using
      F.field.card_base.trans F.field.cardinality_eq)

end WeilConjectures

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicQbarConstructibleRealization
public import WeilConjectures.SixFunctors.Supporting.GeometricCommonStageDirectImage
public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperTensorComparison
public import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
public import WeilConjectures.AlgebraicGeometry.ContinuousRational.DirectImage.RationalDirectImageRealization
public import WeilConjectures.AlgebraicGeometry.ContinuousRational.ContinuousRationalDerivedRealization
public import WeilConjectures.WeilSheaf.Ordinary.OrdinaryCompletedIntegralPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients

import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.AdicNormalizedPullbackRealization
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.AdicProperOrdinaryPushPreservation

/-! # Proper adjunction comparison for native continuous coefficients

Source: Bhatt--Scholze, Proposition 6.8.14, Remark 6.8.15 and Lemma 6.7.2;
agent assembly of the normalized common-stage comparison
(blueprint: lem-sf-adic-proper-adjunction-realization).

All functors below take values in ordinary module derived categories. The comparison
is fixed before rationalization by balanced tensor multiplication, and its direct-image
comparison is fixed by the actual adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
set_option linter.all false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper
open AdicQbarRealization
attribute [local irreducible] ContinuousRational.modulePull ContinuousRational.derivedPull
  ordinaryIntegralModulePull ordinaryIntegralDerivedPull
/-- A mate is invertible on an object once its target lies in the fully faithful
source image. This is the usual mate argument inside the full essential images. -/
private theorem mate_isIso_on_image
    {C₀ : Type*} {D₀ : Type*} {C₁ : Type*} {D₁ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    {L : C₀ ⥤ D₀} {R : D₀ ⥤ C₀} {L' : C₁ ⥤ D₁} {R' : D₁ ⥤ C₁}
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (G : C₀ ⥤ C₁) (H : D₀ ⥤ D₁)
    [G.Full] [G.Faithful] [H.Full] [H.Faithful]
    (θ : G ⋙ L' ≅ L ⋙ H) (d : D₀)
    (image : ∃ c, Nonempty (G.obj c ≅ R'.obj (H.obj d))) :
    IsIso ((mateEquiv adj adj' θ.hom).natTrans.app d) := by
  let α := (mateEquiv adj adj' θ.hom).natTrans.app d
  have h (c : C₀) : Function.Bijective (fun f : G.obj c ⟶ G.obj (R.obj d) ↦ f ≫ α) := by
    let e : (G.obj c ⟶ G.obj (R.obj d)) ≃ (G.obj c ⟶ R'.obj (H.obj d)) :=
      (Functor.FullyFaithful.ofFullyFaithful G).homEquiv.symm |>.trans
        ((adj.homEquiv c d).symm.trans
          ((Functor.FullyFaithful.ofFullyFaithful H).homEquiv.trans
            ((Iso.homCongr (θ.app c).symm (Iso.refl _)).trans
              (adj'.homEquiv (G.obj c) (H.obj d)))))
    have he (f : G.obj c ⟶ G.obj (R.obj d)) : e f = f ≫ α := by
      obtain ⟨t, rfl⟩ := G.map_surjective f
      apply (adj'.homEquiv (G.obj c) (H.obj d)).symm.injective
      dsimp only [e, Equiv.trans_apply]
      erw [Equiv.symm_apply_apply]
      simp only [Functor.FullyFaithful.homEquiv_apply,
        Functor.FullyFaithful.homEquiv_symm_apply, Functor.FullyFaithful.preimage_map,
        Adjunction.homEquiv_symm_apply]
      rw [L'.map_comp, Category.assoc]
      rw [show L'.map α ≫ adj'.counit.app (H.obj d) =
          θ.hom.app (R.obj d) ≫ H.map (adj.counit.app d) from
        mateEquiv_counit adj adj' θ.hom d]
      have ht := θ.hom.naturality t
      dsimp only [Functor.comp_map] at ht
      rw [← Category.assoc, ht]
      simp [Functor.map_comp, Category.assoc]
    simpa only [← he] using e.bijective
  obtain ⟨c, ⟨i⟩⟩ := image
  obtain ⟨t, ht⟩ := (h c).surjective i.hom
  change t ≫ α = i.hom at ht
  let β := i.inv ≫ t
  have hβα : β ≫ α = 𝟙 _ := by
    dsimp only [β]
    rw [Category.assoc, ht, i.inv_hom_id]
  have hαβ : α ≫ β = 𝟙 _ := by
    apply (h (R.obj d)).injective
    change (α ≫ β) ≫ α = (𝟙 _) ≫ α
    calc
      (α ≫ β) ≫ α = α ≫ (β ≫ α) := Category.assoc _ _ _
      _ = α := by rw [hβα]; exact Category.comp_id α
      _ = (𝟙 _) ≫ α := (Category.id_comp α).symm
  exact ⟨⟨β, hαβ, hβα⟩⟩

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (p : X ⟶ Y)
  (R : LocallyFiniteAdicRealization.Realization l X)
  (S : LocallyFiniteAdicRealization.Realization l Y)

variable [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]
attribute [local irreducible] ordinary commonStageDerivedPullback
  commonStageDerivedTensor

variable (k : Type u) [Field k] (hl : IsUnit (l : k))
  [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [p.IsOver (Spec (.of k))]

/-- The normalized proper comparison, with preservation in the full bounded
constructible subcategories and equalities of actual ambient adjunction maps.
Source: BS 6.8.14--6.8.15, 6.7.2; the eight-step assembly recorded in the DAG
(blueprint: lem-sf-adic-proper-adjunction-realization). -/
structure Comparison (A : At l X R) (C : At l Y S) where
  operations : Operations l p R S
  integral : ∀ E, IntegralComparison l p R S operations E
  tensor : TensorComparison l p R S operations A C
  a : commonStageDerivedPullback l (PadicAlgCl l) p ⋙ ordinary l X R ≅
    ordinary l Y S ⋙ ContinuousRational.derivedPull p operations.coefficient
  integral_normalization : ∀ E, IntegralAgreement l p R S operations E (integral E) a
  pull_preserves : ∀ K, boundedConstructible l Y S K → boundedConstructible l X R
    ((ContinuousRational.derivedPull p operations.coefficient).obj K)
  push_preserves : ∀ K, boundedConstructible l X R K → boundedConstructible l Y S
    ((ContinuousRational.DirectImage.derivedPush p operations.coefficient).obj K)
  sourceUnit : canonicalCommonStagePullbackTensor_unit l (PadicAlgCl l) p
  tensor_compatibility : ∀ M N,
    (ContinuousRational.derivedPull p operations.coefficient).map
        (C.tensor.hom.app (M, N)) ≫
      a.inv.app ((commonStageDerivedTensor l (PadicAlgCl l) Y).obj (M, N)) ≫
      (ordinary l X R).map (canonicalCommonStagePullbackTensor l (PadicAlgCl l) p M N).hom =
    tensor.tensor.hom.app ((ordinary l Y S).obj M, (ordinary l Y S).obj N) ≫
      A.closed.tensor.map (Prod.mkHom (a.inv.app M) (a.inv.app N)) ≫
      A.tensor.hom.app ((commonStageDerivedPullback l (PadicAlgCl l) p).obj M,
        (commonStageDerivedPullback l (PadicAlgCl l) p).obj N)
  unit_compatibility :
    (ContinuousRational.derivedPull p operations.coefficient).map C.unit.hom ≫
      a.inv.app (pullbackTensorCommonUnit l (PadicAlgCl l) Y) ≫
      (ordinary l X R).map sourceUnit.exists.choose.hom = tensor.unit.hom ≫ A.unit.hom
  b : geometricCommonStageDirectImage l (PadicAlgCl l) k hl p ⋙ ordinary l Y S ≅
    ordinary l X R ⋙ ContinuousRational.DirectImage.derivedPush p operations.coefficient
  mate : ∀ K,
    b.hom.app K = operations.adjunction.unit.app
        ((ordinary l Y S).obj
          ((geometricCommonStageDirectImage l (PadicAlgCl l) k hl p).obj K)) ≫
      (ContinuousRational.DirectImage.derivedPush p operations.coefficient).map
        (a.inv.app ((geometricCommonStageDirectImage l (PadicAlgCl l) k hl p).obj K)) ≫
      (ContinuousRational.DirectImage.derivedPush p operations.coefficient).map
        ((ordinary l X R).map
          ((geometricCommonStageAdjunction l (PadicAlgCl l) k hl p).counit.app K))
  counit : ∀ K,
    (ordinary l X R).map
        ((geometricCommonStageAdjunction l (PadicAlgCl l) k hl p).counit.app K) =
      a.hom.app ((geometricCommonStageDirectImage l (PadicAlgCl l) k hl p).obj K) ≫
        (ContinuousRational.derivedPull p operations.coefficient).map (b.hom.app K) ≫
        operations.adjunction.counit.app ((ordinary l X R).obj K)
  unit : ∀ M,
    (ordinary l Y S).map
        ((geometricCommonStageAdjunction l (PadicAlgCl l) k hl p).unit.app M) ≫
      b.hom.app ((commonStageDerivedPullback l (PadicAlgCl l) p).obj M) ≫
      (ContinuousRational.DirectImage.derivedPush p operations.coefficient).map
        (a.hom.app M) = operations.adjunction.unit.app ((ordinary l Y S).obj M)

/-- Read the comparison type at the residue-unit instances already supplied by
SpaceData. No additional hypothesis is imposed on the geometric spaces.
Source: BS 6.8.14--6.8.15
(blueprint: lem-sf-adic-proper-adjunction-realization). -/
def AtSpaces (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) (F : Family l D)
    (Z T : GeometricSpace D) (p : Z.base ⟶ T.base) : Type (u + 2) := by
  letI := (F.data Z).units
  letI := (F.data T).units
  letI := Z.separated
  letI := T.separated
  letI : Z.base.left.Over (Spec (.of D.k)) := ⟨Z.base.hom⟩
  letI : T.base.left.Over (Spec (.of D.k)) := ⟨T.base.hom⟩
  letI : LocallyOfFiniteType (Z.base.left ↘ Spec (.of D.k)) := Z.finiteType
  letI : LocallyOfFiniteType (T.base.left ↘ Spec (.of D.k)) := T.finiteType
  letI : QuasiCompact (Z.base.left ↘ Spec (.of D.k)) := Z.quasiCompact
  letI : QuasiCompact (T.base.left ↘ Spec (.of D.k)) := T.quasiCompact
  letI : p.left.IsOver (Spec (.of D.k)) := ⟨Over.w p⟩
  exact Comparison l p.left (F.data Z).realization (F.data T).realization D.k
    (finiteFieldDatumPrimeUnit D l hl) (F.data Z).tensor (F.data T).tensor

/-- Continuous-coefficient realization identifies proper inverse/direct image,
including the specified integral, tensor, unit, mate and adjunction normalizations.
Source: Bhatt--Scholze, Proposition 6.8.14 and Remark 6.8.15 (pp. 61--62),
with Lemma 6.7.2; agent-formulated consequence, as recorded in the DAG
(blueprint: lem-sf-adic-proper-adjunction-realization).
Proof: finite-type schemes over the field are Noetherian and finite dimensional,
and l is invertible. Use the coefficient-ring realization theta and its scheme-map
square: taking adjoints identifies the structural coefficient map with exactly
precomposition. The finite-integral formula identifies its realization with rho,
on objects and on fractions over every common coefficient field.
On a finite integral representative, invert the actual quotient-tower completion
unit and flatten the balanced tensors. Rational realization pullback comparison
and scalar coherence identify these maps after every coefficient inclusion, so
representatives over a common field give the well-defined natural isomorphism a.
Essential surjectivity of rho gives bounded constructible pullback preservation.
For tensor normalization retain the whole quotient tower: the ordinary/completed
pullback and tensor units have quotient coordinates in the unshifted product and
zero in the shifted product. Cochain scalar/pullback/tensor equations commute with
these actual transitions. Apply derived limit and the primitive counit comparison;
then invert completion units. This identifies the ordinary tensor and action-unit
comparisons. Monoidal scalar associativity and rho's symmetric monoidal structure
give the stated tensor and unit equations. On homogeneous sections both routes
flatten b tensor (x tensor y) to (b tensor x) tensor (1 tensor y); all coefficient
scalars have degree zero, so the signed symmetry is unchanged.
Apply the compact-support realization theorem to the compactification (id,p).
Its identity extension by zero is the identity, hence the actual ambient derived
direct image preserves the full constructible subcategory. Finite Tor amplitude
over the coefficient field imposes no further hypothesis.
Use the common-stage adjunction: its finite-stage Hom bijections are the raw
localizations of the ordinary completed bijections. Their scalar compatibility
makes them independent of both field and representative. Restrict the ambient
ordinary module adjunction to the full constructible subcategories; its maps are
unchanged. Set alpha = a.inv and define b by its right-mate formula, using these
two actual adjunctions. The mate-isomorphism lemma applies because rho_Y is an
equivalence and rho_Z is fully faithful. Finally the mate counit identity, composed
with a, gives the displayed counit equation. The mate unit identity, composed with
the right functor applied to a, gives the unit equation. Full inclusions retain
these as equalities in ordinary module derived categories. -/
theorem adic_proper_adjunction_realization (D : FiniteFieldDatum.{u}) (l : ℕ)
    [Fact l.Prime] (hl : l ≠ D.p) :
    ∃ F : Family l D, ∀ (Z T : GeometricSpace D) (p : Z.base ⟶ T.base),
      IsProper p.left → Nonempty (AtSpaces l D hl F Z T p) := by
  classical
  obtain ⟨F⟩ := adic_qbar_constructible_realization D l hl
  refine ⟨F, ?_⟩
  intro Z T p hp
  letI := (F.data Z).units
  letI := (F.data T).units
  letI := Z.separated
  letI := T.separated
  letI : Z.base.left.Over (Spec (.of D.k)) := ⟨Z.base.hom⟩
  letI : T.base.left.Over (Spec (.of D.k)) := ⟨T.base.hom⟩
  letI : LocallyOfFiniteType (Z.base.left ↘ Spec (.of D.k)) := Z.finiteType
  letI : LocallyOfFiniteType (T.base.left ↘ Spec (.of D.k)) := T.finiteType
  letI : QuasiCompact (Z.base.left ↘ Spec (.of D.k)) := Z.quasiCompact
  letI : QuasiCompact (T.base.left ↘ Spec (.of D.k)) := T.quasiCompact
  letI : p.left.IsOver (Spec (.of D.k)) := ⟨Over.w p⟩
  change Nonempty (Comparison l p.left (F.data Z).realization (F.data T).realization
    D.k (finiteFieldDatumPrimeUnit D l hl) (F.data Z).tensor (F.data T).tensor)
  obtain ⟨q⟩ := adic_normalized_pullback_realization l D hl F Z T p
  let G := ordinary l T.base.left (F.data T).realization
  let H := ordinary l Z.base.left (F.data Z).realization
  let L := commonStageDerivedPullback l (PadicAlgCl l) p.left
  let L' := ContinuousRational.derivedPull p.left q.operations.coefficient
  let R' := ContinuousRational.DirectImage.derivedPush p.left q.operations.coefficient
  let adj := geometricCommonStageAdjunction l (PadicAlgCl l) D.k
    (finiteFieldDatumPrimeUnit D l hl) p.left
  let m := (mateEquiv adj q.operations.adjunction q.a.inv).natTrans
  have push := adic_proper_ordinary_push_preservation D l hl F Z T p hp q.operations
  let : G.Full := ⟨fun {A B} ↦ ((F.data T).fully_faithful A B).2⟩
  let : G.Faithful := ⟨fun {A B} ↦ ((F.data T).fully_faithful A B).1⟩
  let : H.Full := ⟨fun {A B} ↦ ((F.data Z).fully_faithful A B).2⟩
  let : H.Faithful := ⟨fun {A B} ↦ ((F.data Z).fully_faithful A B).1⟩
  have hm (K) : IsIso (m.app K) := by
    apply mate_isIso_on_image adj q.operations.adjunction G H q.a.symm K
    apply ((F.data T).image _).mp
    apply push
    exact ((F.data Z).image _).mpr ⟨K, ⟨Iso.refl _⟩⟩
  have : IsIso m := NatIso.isIso_of_isIso_app m
  let b := asIso m
  refine ⟨{
    operations := q.operations
    integral := q.integral
    tensor := q.tensor
    a := q.a
    integral_normalization := q.integral_normalization
    pull_preserves := ?_
    push_preserves := push
    sourceUnit := q.sourceUnit
    tensor_compatibility := q.tensor_compatibility
    unit_compatibility := q.unit_compatibility
    b := b
    mate := ?_
    counit := ?_
    unit := ?_ }⟩
  · intro K hK
    obtain ⟨M, ⟨i⟩⟩ := ((F.data T).image K).mp hK
    apply ((F.data Z).image _).mpr
    exact ⟨L.obj M, ⟨q.a.app M ≪≫ L'.mapIso i⟩⟩
  · intro K
    simp [b, m, mateEquiv, Category.assoc] <;> rfl
  · intro K
    have h := mateEquiv_counit adj q.operations.adjunction q.a.inv K
    change L'.map (b.hom.app K) ≫ q.operations.adjunction.counit.app (H.obj K) =
      q.a.inv.app _ ≫ H.map (adj.counit.app K) at h
    calc
      H.map (adj.counit.app K) =
          q.a.hom.app _ ≫ (q.a.inv.app _ ≫ H.map (adj.counit.app K)) := by
            simp only [← Category.assoc, q.a.hom_inv_id_app, Category.id_comp]
      _ = _ := by rw [← h]
  · intro M
    have h := unit_mateEquiv adj q.operations.adjunction q.a.inv M
    change G.map (adj.unit.app M) ≫ b.hom.app (L.obj M) =
      q.operations.adjunction.unit.app (G.obj M) ≫ R'.map (q.a.inv.app M) at h
    rw [← Category.assoc, h, Category.assoc, ← R'.map_comp]
    rw [q.a.inv_hom_id_app]
    change q.operations.adjunction.unit.app (G.obj M) ≫
      R'.map (𝟙 (L'.obj (G.obj M))) = q.operations.adjunction.unit.app (G.obj M)
    rw [R'.map_id]
    exact Category.comp_id _

end WeilConjectures.AdicQbarRealization.Proper

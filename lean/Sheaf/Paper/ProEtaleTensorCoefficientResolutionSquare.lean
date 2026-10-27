/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.QuasiIso
import Sheaf.Paper.ProEtaleFixedTensorRepresentativeComparison
import Sheaf.Paper.ProEtaleResolutionDerivedSquare
import Sheaf.Paper.ProEtaleResolutionSigmaNaturality
import Sheaf.Paper.ProEtaleResolutionRepresentativeSquare
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # The coefficient-resolution square for pro-etale tensor pullback

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 06YU.
(blueprint: lem-sp-proetale-tensor-coefficient-resolution-square)

The ordinary comparison, localization factors and derived comparison are the published
canonical constructions. The bottom-right complex is written as the tensor with F(N[0]);
the canonical termwise single-complex identification identifies this with FP tensor FN.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The existing direct-sum total tensor, including its cochain signs.
Source: Stacks, Tag 06YM
(blueprint: lem-sp-proetale-tensor-coefficient-resolution-square). -/
abbrev proEtaleResolutionTotal (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) :=
  Functor.uncurry.obj ((proEtaleOrdinaryTensor Z R).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- The formula for alpha from a resolution and the localized tensor-resolution iso.
The inverse here is the specified inverse of Q(1 tensor q), supplied as e. This is an
actual composite, with no choice of a comparison map or of a coefficient resolution.
Source: Stacks, Tag 06YU, construction preceding definition-derived-tor
(blueprint: lem-sp-proetale-tensor-coefficient-resolution-square). -/
def proEtaleCoefficientResolutionAlpha (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}) (a : ProEtaleTensorModel Z R)
    (P M H : CochainComplex (proEtaleRingModules Z R) ℤ)
    (hP : proEtaleFlatRepresentatives Z R P) (hH : proEtaleFlatRepresentatives Z R H)
    (q : H ⟶ M)
    (e : DerivedCategory.Q.obj ((proEtaleResolutionTotal Z R).obj (P, H)) ≅
      DerivedCategory.Q.obj ((proEtaleResolutionTotal Z R).obj (P, M))) :
    DerivedCategory.Q.obj ((proEtaleResolutionTotal Z R).obj (P, M)) ⟶
      a.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj M) :=
  e.inv ≫ a.representative.hom.app (⟨P, hP⟩, ⟨H, hH⟩) ≫
    a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q))

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- Exact termwise pullback on the original small pro-etale sites.
Source: Stacks, Tag 07A4
(blueprint: lem-sp-proetale-tensor-coefficient-resolution-square). -/
abbrev proEtaleResolutionPullback :=
  (proEtaleRingModulePullback f R S c).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Sigma has the forward orientation in the coefficient-resolution square; the published
summandwise total comparison has the reverse orientation.
Source: Stacks, Tag 07A4
(blueprint: lem-sp-proetale-tensor-coefficient-resolution-square). -/
abbrev proEtaleResolutionSigma (P H : CochainComplex (proEtaleRingModules Y R) ℤ) :=
  (proEtaleTensorPullbackTotalIso f R S c P H).symm

/-- The degree-zero coefficient complex, using the existing single-complex functor.
Source: Stacks, Tag 06YU
(blueprint: lem-sp-proetale-tensor-coefficient-resolution-square). -/
abbrev proEtaleResolutionSingle (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (N : proEtaleRingModules Z R) :=
  (HomologicalComplex.single (proEtaleRingModules Z R) (ComplexShape.up ℤ) 0).obj N

/-- The arrow 1 tensor q on the existing direct-sum total tensor.
Source: Stacks, Tags 06YP and 06YU
(blueprint: lem-sp-proetale-tensor-coefficient-resolution-square). -/
abbrev proEtaleResolutionTensorMap (Z : Scheme.{u})
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (P : CochainComplex (proEtaleRingModules Z R) ℤ)
    {H M : CochainComplex (proEtaleRingModules Z R) ℤ} (q : H ⟶ M) :=
  (proEtaleResolutionTotal Z R).map (Prod.mkHom (𝟙 P) q)

/-- Resolution independence means equality of the prescribed alpha composites for every
pair of flat-term K-flat resolutions of this fixed M. It includes every inverse witness
whose forward arrow is Q(1 tensor q), so no choice of an inverse is hidden.
Source: Stacks, Tag 06YU, normalized localization construction
(blueprint: lem-sp-proetale-tensor-coefficient-resolution-square). -/
def ProEtaleCoefficientResolutionIndependent
    (Z : Scheme.{u}) (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel Z RZ)
    (P M : CochainComplex (proEtaleRingModules Z RZ) ℤ)
    (hP : proEtaleFlatRepresentatives Z RZ P) : Prop :=
  ∀ (H H' : CochainComplex (proEtaleRingModules Z RZ) ℤ)
    (hH : proEtaleFlatRepresentatives Z RZ H)
    (hH' : proEtaleFlatRepresentatives Z RZ H')
    (q : H ⟶ M) (q' : H' ⟶ M), QuasiIso q → QuasiIso q' →
    ∀ (e : DerivedCategory.Q.obj ((proEtaleResolutionTotal Z RZ).obj (P, H)) ≅
      DerivedCategory.Q.obj ((proEtaleResolutionTotal Z RZ).obj (P, M)))
    (e' : DerivedCategory.Q.obj ((proEtaleResolutionTotal Z RZ).obj (P, H')) ≅
      DerivedCategory.Q.obj ((proEtaleResolutionTotal Z RZ).obj (P, M))),
    e.hom = DerivedCategory.Q.map (proEtaleResolutionTensorMap Z RZ P q) →
    e'.hom = DerivedCategory.Q.map (proEtaleResolutionTensorMap Z RZ P q') →
    proEtaleCoefficientResolutionAlpha Z RZ a P M H hP hH q e =
      proEtaleCoefficientResolutionAlpha Z RZ a P M H' hP hH' q' e'

attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] proEtaleTensorPullbackTotal proEtaleTensorPullbackTotalIso
  proEtaleRingDerivedPullbackFactors CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.presheafToSheaf
  HomologicalComplex₂.total

private theorem resolutionTensor_quasiIso
    (Z : Scheme.{u}) (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (P : CochainComplex (proEtaleRingModules Z RZ) ℤ)
    (hP : proEtaleFlatRepresentatives Z RZ P)
    {H M : CochainComplex (proEtaleRingModules Z RZ) ℤ} (q : H ⟶ M)
    (hq : QuasiIso q) : QuasiIso (proEtaleResolutionTensorMap Z RZ P q) := by
  obtain ⟨_, ht⟩ := SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated RZ
  have hp := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP.1
  have hh := (ht P hp hP.2).1 H M q hq |>.1
  let T := (proEtaleOrdinaryTensor Z RZ).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  have he : proEtaleResolutionTensorMap Z RZ P q = (T.obj P).map q := by
    change (T.map (𝟙 P)).app H ≫ (T.obj P).map q = _
    rw [T.map_id, NatTrans.id_app, Category.id_comp]
  rw [he]
  exact hh

private theorem resolutionTotal_flat
    (Z : Scheme.{u}) (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (P H : CochainComplex (proEtaleRingModules Z RZ) ℤ)
    (hP : proEtaleFlatRepresentatives Z RZ P)
    (hH : proEtaleFlatRepresentatives Z RZ H) :
    proEtaleFlatRepresentatives Z RZ ((proEtaleResolutionTotal Z RZ).obj (P, H)) := by
  have hp := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hP.1
  have hh := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat H).2 hH.1
  have ht := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    RZ P H hp hh hP.2 hH.2
  exact ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 ht.1, ht.2.1⟩

private theorem resolutionAlpha_eq
    (Z : Scheme.{u}) (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel Z RZ)
    (P M H : CochainComplex (proEtaleRingModules Z RZ) ℤ)
    (hP : proEtaleFlatRepresentatives Z RZ P)
    (hH : proEtaleFlatRepresentatives Z RZ H) (q : H ⟶ M)
    (e : DerivedCategory.Q.obj ((proEtaleResolutionTotal Z RZ).obj (P, H)) ≅
      DerivedCategory.Q.obj ((proEtaleResolutionTotal Z RZ).obj (P, M)))
    (he : e.hom = DerivedCategory.Q.map (proEtaleResolutionTensorMap Z RZ P q))
    (d : ((Functor.const _).obj P).prod' (𝟭 _) ⋙ proEtaleResolutionTotal Z RZ ⋙
        DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ ((Functor.const _).obj (DerivedCategory.Q.obj P)).prod' (𝟭 _) ⋙
        a.tensor)
    (hd : ∀ (H : CochainComplex (proEtaleRingModules Z RZ) ℤ)
      (hH : proEtaleFlatRepresentatives Z RZ H),
      d.hom.app H = a.representative.hom.app (⟨P, hP⟩, ⟨H, hH⟩)) :
    proEtaleCoefficientResolutionAlpha Z RZ a P M H hP hH q e = d.hom.app M := by
  have hn := d.hom.naturality q
  change DerivedCategory.Q.map (proEtaleResolutionTensorMap Z RZ P q) ≫ d.hom.app M =
    d.hom.app H ≫ a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
      (DerivedCategory.Q.map q)) at hn
  unfold proEtaleCoefficientResolutionAlpha
  rw [← hd H hH, ← hn, ← he, Iso.inv_hom_id_assoc]

private theorem resolution_independent
    (Z : Scheme.{u}) (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel Z RZ)
    (P M : CochainComplex (proEtaleRingModules Z RZ) ℤ)
    (hP : proEtaleFlatRepresentatives Z RZ P) :
    ProEtaleCoefficientResolutionIndependent Z RZ a P M hP := by
  obtain ⟨d, hd⟩ := proEtale_fixed_tensor_representative_comparison Z RZ a P hP
  intro H H' hH hH' q q' _hq _hq' e e' he he'
  rw [resolutionAlpha_eq Z RZ a P M H hP hH q e he d hd,
    resolutionAlpha_eq Z RZ a P M H' hP hH' q' e' he' d hd]

private theorem resolutionAlpha_formula
    (Z : Scheme.{u}) (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel Z RZ)
    (P M H : CochainComplex (proEtaleRingModules Z RZ) ℤ)
    (hP : proEtaleFlatRepresentatives Z RZ P)
    (hH : proEtaleFlatRepresentatives Z RZ H) (q : H ⟶ M)
    (e : DerivedCategory.Q.obj ((proEtaleResolutionTotal Z RZ).obj (P, H)) ≅
      DerivedCategory.Q.obj ((proEtaleResolutionTotal Z RZ).obj (P, M))) :
    proEtaleCoefficientResolutionAlpha Z RZ a P M H hP hH q e =
      e.inv ≫ a.representative.hom.app (⟨P, hP⟩, ⟨H, hH⟩) ≫
        a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P)) (DerivedCategory.Q.map q)) := rfl

private theorem resolutionAlpha_isIso
    (Z : Scheme.{u}) (RZ : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (a : ProEtaleTensorModel Z RZ)
    (P M H : CochainComplex (proEtaleRingModules Z RZ) ℤ)
    (hP : proEtaleFlatRepresentatives Z RZ P)
    (hH : proEtaleFlatRepresentatives Z RZ H) (q : H ⟶ M) [QuasiIso q]
    (e : DerivedCategory.Q.obj ((proEtaleResolutionTotal Z RZ).obj (P, H)) ≅
      DerivedCategory.Q.obj ((proEtaleResolutionTotal Z RZ).obj (P, M))) :
    IsIso (proEtaleCoefficientResolutionAlpha Z RZ a P M H hP hH q e) := by
  exact (e.symm ≪≫ (a.representative.app (⟨P, hP⟩, ⟨H, hH⟩) ≪≫
    a.tensor.mapIso (Iso.prod (Iso.refl _) (asIso (DerivedCategory.Q.map q))))).isIso_hom

attribute [local irreducible] proEtaleCoefficientResolutionAlpha

/-- The coefficient-resolution square, its representatives, and the final derived identity.
The isomorphisms eY and eX have prescribed forward maps Q(1 tensor q), so alpha uses
exactly their canonical inverses. No resolution or comparison is chosen arbitrarily.
Source: Stacks, Tags 07A4 and 06YU
(blueprint: lem-sp-proetale-tensor-coefficient-resolution-square).
Proof:
1. Naturality of the specified inverse total-tensor comparison at (1,q) gives the
   chain square. The pro-etale descent data preserve flat-term K-flat representatives.
2. The total-tensor theorem gives flatness and K-flatness of the source and target top
   tensors. Apply preservation also to the source total tensor.
3. Tensor with a fixed flat-term K-flat complex preserves quasi-isomorphisms. Apply
   this to P,q and FP,Fq; exact pullback also preserves q and 1 tensor q. Localizing
   gives eY,eX with the prescribed forward maps.
4. The defining characterization of the canonical comparison gives the top derived
   representative square, with all flatness witnesses identified by proof irrelevance.
5. Localize tensor with fixed P, and extend its specified comparison on representatives
   using fully faithful restriction. Naturality at q identifies every alpha with its
   component at N[0]. This proves resolution independence over both sites. Each alpha
   is an isomorphism because its three factors are isomorphisms.
6. Localize the chain square. Naturality of epsilon at 1 tensor q and cancellation of
   the invertible vertical maps reduce the final equation to the top representative
   square. Naturality of epsilon at q, bifunctoriality, and naturality of tau move the
   remaining coefficient map across that square. Functoriality then gives the stated
   composite alphaY. No step assumes N flat or its ordinary tensor K-flat.
-/
theorem proEtale_tensor_coefficient_resolution_square
    (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
    (P H : CochainComplex (proEtaleRingModules Y R) ℤ)
    (N : proEtaleRingModules Y R)
    (hP : proEtaleFlatRepresentatives Y R P)
    (hH : proEtaleFlatRepresentatives Y R H)
    (q : H ⟶ proEtaleResolutionSingle Y R N) [QuasiIso q] :
    (proEtaleResolutionSigma f R S c P H).hom ≫
        proEtaleResolutionTensorMap X S ((proEtaleResolutionPullback f R S c).obj P)
          ((proEtaleResolutionPullback f R S c).map q) =
      (proEtaleResolutionPullback f R S c).map
          (proEtaleResolutionTensorMap Y R P q) ≫
        (proEtaleResolutionSigma f R S c P (proEtaleResolutionSingle Y R N)).hom ∧
    QuasiIso ((proEtaleResolutionPullback f R S c).map
      (proEtaleResolutionTensorMap Y R P q)) ∧
    QuasiIso (proEtaleResolutionTensorMap X S
      ((proEtaleResolutionPullback f R S c).obj P)
      ((proEtaleResolutionPullback f R S c).map q)) ∧
    proEtaleFlatRepresentatives Y R ((proEtaleResolutionTotal Y R).obj (P, H)) ∧
    proEtaleFlatRepresentatives X S ((proEtaleResolutionPullback f R S c).obj
      ((proEtaleResolutionTotal Y R).obj (P, H))) ∧
    ∃ (hFP : proEtaleFlatRepresentatives X S
        ((proEtaleResolutionPullback f R S c).obj P))
      (hFH : proEtaleFlatRepresentatives X S
        ((proEtaleResolutionPullback f R S c).obj H)),
      ProEtaleCoefficientResolutionIndependent Y R a P
        (proEtaleResolutionSingle Y R N) hP ∧
      ProEtaleCoefficientResolutionIndependent X S b
        ((proEtaleResolutionPullback f R S c).obj P)
        ((proEtaleResolutionPullback f R S c).obj (proEtaleResolutionSingle Y R N)) hFP ∧
      proEtaleFlatRepresentatives X S ((proEtaleResolutionTotal X S).obj
        ((proEtaleResolutionPullback f R S c).obj P,
          (proEtaleResolutionPullback f R S c).obj H)) ∧
      ((proEtaleRingDerivedPullback f R S c).map
          (a.representative.hom.app (⟨P, hP⟩, ⟨H, hH⟩)) ≫
        (proEtaleCanonicalTensorComparison f R S c a b).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj H) ≫
        b.tensor.map (Prod.mkHom
          ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
          ((proEtaleRingDerivedPullbackFactors f R S c).hom.app H)) =
      (proEtaleRingDerivedPullbackFactors f R S c).hom.app
          ((proEtaleResolutionTotal Y R).obj (P, H)) ≫
        DerivedCategory.Q.map (proEtaleResolutionSigma f R S c P H).hom ≫
        b.representative.hom.app
          (⟨(proEtaleResolutionPullback f R S c).obj P, hFP⟩,
            ⟨(proEtaleResolutionPullback f R S c).obj H, hFH⟩)) ∧
      ∃ (eY : DerivedCategory.Q.obj ((proEtaleResolutionTotal Y R).obj (P, H)) ≅
          DerivedCategory.Q.obj ((proEtaleResolutionTotal Y R).obj
            (P, proEtaleResolutionSingle Y R N)))
        (eX : DerivedCategory.Q.obj ((proEtaleResolutionTotal X S).obj
            ((proEtaleResolutionPullback f R S c).obj P,
              (proEtaleResolutionPullback f R S c).obj H)) ≅
          DerivedCategory.Q.obj ((proEtaleResolutionTotal X S).obj
            ((proEtaleResolutionPullback f R S c).obj P,
              (proEtaleResolutionPullback f R S c).obj (proEtaleResolutionSingle Y R N)))),
        eY.hom = DerivedCategory.Q.map (proEtaleResolutionTensorMap Y R P q) ∧
        eX.hom = DerivedCategory.Q.map (proEtaleResolutionTensorMap X S
          ((proEtaleResolutionPullback f R S c).obj P)
          ((proEtaleResolutionPullback f R S c).map q)) ∧
        IsIso (proEtaleCoefficientResolutionAlpha Y R a P
          (proEtaleResolutionSingle Y R N) H hP hH q eY) ∧
        IsIso (proEtaleCoefficientResolutionAlpha X S b
          ((proEtaleResolutionPullback f R S c).obj P)
          ((proEtaleResolutionPullback f R S c).obj (proEtaleResolutionSingle Y R N))
          ((proEtaleResolutionPullback f R S c).obj H) hFP hFH
          ((proEtaleResolutionPullback f R S c).map q) eX) ∧
        (proEtaleRingDerivedPullbackFactors f R S c).hom.app
            ((proEtaleResolutionTotal Y R).obj (P, proEtaleResolutionSingle Y R N)) ≫
          DerivedCategory.Q.map
            (proEtaleResolutionSigma f R S c P (proEtaleResolutionSingle Y R N)).hom ≫
          proEtaleCoefficientResolutionAlpha X S b
            ((proEtaleResolutionPullback f R S c).obj P)
            ((proEtaleResolutionPullback f R S c).obj (proEtaleResolutionSingle Y R N))
            ((proEtaleResolutionPullback f R S c).obj H) hFP hFH
            ((proEtaleResolutionPullback f R S c).map q) eX =
        (proEtaleRingDerivedPullback f R S c).map
            (proEtaleCoefficientResolutionAlpha Y R a P
              (proEtaleResolutionSingle Y R N) H hP hH q eY) ≫
          (proEtaleCanonicalTensorComparison f R S c a b).hom.app
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj (proEtaleResolutionSingle Y R N)) ≫
          b.tensor.map (Prod.mkHom
            ((proEtaleRingDerivedPullbackFactors f R S c).hom.app P)
            ((proEtaleRingDerivedPullbackFactors f R S c).hom.app
              (proEtaleResolutionSingle Y R N))) := by
  classical
  let F := proEtaleResolutionPullback f R S c
  let M := proEtaleResolutionSingle Y R N
  let u := proEtaleResolutionTensorMap Y R P q
  let v := proEtaleResolutionTensorMap X S (F.obj P) (F.map q)
  have hF := (proEtaleCanonicalTensorPullback f R S c a b).1
  have hFP := hF P hP
  have hFH := hF H hH
  have hT := resolutionTotal_flat Y R P H hP hH
  have hFT := hF _ hT
  have hTX := resolutionTotal_flat X S (F.obj P) (F.obj H) hFP hFH
  have hsq := proEtale_resolution_sigma_naturality f R S c P H M q
  have hu : QuasiIso u := resolutionTensor_quasiIso Y R P hP q inferInstance
  let := hu
  have hFu : QuasiIso (F.map u) := inferInstance
  have hFq : QuasiIso (F.map q) := inferInstance
  have hv : QuasiIso v := resolutionTensor_quasiIso X S (F.obj P) hFP (F.map q) hFq
  let := hv
  have htop := proEtale_resolution_representative_square f R S c a b P H hP hH hFP hFH
  refine ⟨hsq, hFu, hv, hT, hFT, hFP, hFH,
    resolution_independent Y R a P M hP,
    resolution_independent X S b (F.obj P) (F.obj M) hFP, hTX, htop, ?_⟩
  let : IsIso (DerivedCategory.Q.map u) := Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso (proEtaleRingModules Y R) (.up ℤ)) u hu
  let : IsIso (DerivedCategory.Q.map v) := Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso (proEtaleRingModules X S) (.up ℤ)) v hv
  let eY := asIso (DerivedCategory.Q.map u)
  let eX := asIso (DerivedCategory.Q.map v)
  refine ⟨eY, eX, rfl, rfl, ?_, ?_, ?_⟩
  · exact resolutionAlpha_isIso Y R a P M H hP hH q eY
  · exact resolutionAlpha_isIso X S b (F.obj P) (F.obj M) (F.obj H) hFP hFH (F.map q) eX
  · rw [resolutionAlpha_formula, resolutionAlpha_formula]
    exact proEtale_resolution_derived_square f R S c a b P H M hP hH hFP hFH q
      eY eX rfl rfl

end AlgebraicGeometry.Scheme

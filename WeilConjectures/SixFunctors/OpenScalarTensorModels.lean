/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenScalarTensorData
import WeilConjectures.SixFunctors.OpenScalarNativeNormalization
import WeilConjectures.SixFunctors.OpenScalarBalancingChain
import WeilConjectures.SixFunctors.OpenScalarProjectionResolved
import WeilConjectures.Algebra.Homology.ScalarHomTensorComparison
import WeilConjectures.SixFunctors.ScalarPullbackTensorCoherence
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Scalar tensor models compatible with open restriction

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 07A6, 0D6D and 0GL1;
sites-modules.tex, Tag 0E8I
(blueprint: lem-sp-canonical-open-scalar-tensor-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

/-- The two scalar tensor facts needed to compare projection adjuncts.
Source: Stacks 07A4 and 07A6
(blueprint: lem-sp-canonical-open-scalar-tensor-models). -/
structure TensorCompatibility (m : Models.{u}) (c : Choices m) where
  scalar_projection_isIso : ∀ {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) (T : Scheme.{u})
    (K : proEtaleDerivedCategory T A), IsIso (scalarProjection m c φ T K)
  lambda_tensor : ∀ {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (F Q : proEtaleDerivedCategory X A),
    (tensor m B U).map
        (Prod.mkHom ((lambda m φ j).inv.app F) ((lambda m φ j).inv.app Q)) ≫
      (restrictionTensor m B j).inv.app ((scalar m φ X).obj F, (scalar m φ X).obj Q) ≫
      (constantPullback (A := B) j).map ((c.scalarTensor φ X).iso.inv.app (F, Q)) =
    (c.scalarTensor φ U).iso.inv.app
        ((constantPullback (A := A) j).obj F, (constantPullback (A := A) j).obj Q) ≫
      (scalar m φ U).map ((restrictionTensor m A j).inv.app (F, Q)) ≫
      (lambda m φ j).inv.app ((tensor m A X).obj (F, Q))

private theorem inverse_tensor_coherence (m : Models.{u}) (c : Choices m) :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B) {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (F Q : proEtaleDerivedCategory X A),
    (tensor m B U).map
        (Prod.mkHom ((lambda m φ j).inv.app F) ((lambda m φ j).inv.app Q)) ≫
      (restrictionTensor m B j).inv.app ((scalar m φ X).obj F, (scalar m φ X).obj Q) ≫
      (constantPullback (A := B) j).map ((c.scalarTensor φ X).iso.inv.app (F, Q)) =
    (c.scalarTensor φ U).iso.inv.app
        ((constantPullback (A := A) j).obj F, (constantPullback (A := A) j).obj Q) ≫
      (scalar m φ U).map ((restrictionTensor m A j).inv.app (F, Q)) ≫
      (lambda m φ j).inv.app ((tensor m A X).obj (F, Q)) := by
  intro A B _ _ _ _ φ U X j _ F Q
  let l := (lambda m φ j).app ((tensor m A X).obj (F, Q)) ≪≫
    (scalar m φ U).mapIso ((restrictionTensor m A j).app (F, Q)) ≪≫
    (c.scalarTensor φ U).iso.app
      ((constantPullback (A := A) j).obj F, (constantPullback (A := A) j).obj Q)
  let r := (constantPullback (A := B) j).mapIso ((c.scalarTensor φ X).iso.app (F, Q)) ≪≫
    (restrictionTensor m B j).app ((scalar m φ X).obj F, (scalar m φ X).obj Q) ≪≫
    (tensor m B U).mapIso ((lambda m φ j).app F |>.prod ((lambda m φ j).app Q))
  have h : l = r := Iso.ext (scalarPullbackTensorCoherence m c φ j F Q)
  simpa only [l, r, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.prod_inv,
    Category.assoc]
    using (congrArg Iso.inv h).symm

private theorem scalarProjection_naturality (m : Models.{u}) (c : Choices m)
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    {K L : proEtaleDerivedCategory T A} (f : K ⟶ L) :
    (tensor m A T).map (Prod.mkHom f (𝟙 (coefficient m φ T))) ≫
        scalarProjection m c φ T L =
      scalarProjection m c φ T K ≫ (scalarRestriction φ T).map ((scalar m φ T).map f) := by
  let F := scalar m φ T
  let a := (scalarPair m φ T).adjunction
  let BA := tensor m A T
  let BB := tensor m B T
  let C := coefficient m φ T
  let E := a.counit.app (unit m B T)
  let ρ (N : proEtaleDerivedCategory T B) :=
    (((m T).closed (proEtaleConstantRing T B)).monoidal.rightUnitor N).hom
  change BA.map (Prod.mkHom f (𝟙 C)) ≫
      a.homEquiv _ _ ((c.scalarTensor φ T).iso.hom.app (L,C) ≫
        BB.map (Prod.mkHom (𝟙 (F.obj L)) E) ≫ ρ (F.obj L)) =
    a.homEquiv _ _ ((c.scalarTensor φ T).iso.hom.app (K,C) ≫
      BB.map (Prod.mkHom (𝟙 (F.obj K)) E) ≫ ρ (F.obj K)) ≫
        (scalarDerivedRestriction (proEtaleConstantRingMap (T := T) φ)).map (F.map f)
  rw [← a.homEquiv_naturality_left, ← a.homEquiv_naturality_right]
  congr 1
  have h := (c.scalarTensor φ T).iso.hom.naturality (Prod.mkHom f (𝟙 C))
  change F.map (BA.map (Prod.mkHom f (𝟙 C))) ≫
      (c.scalarTensor φ T).iso.hom.app (L,C) =
    (c.scalarTensor φ T).iso.hom.app (K,C) ≫
      BB.map (Prod.mkHom (F.map f) (F.map (𝟙 C))) at h
  rw [F.map_id] at h
  have ht : BB.map (Prod.mkHom (F.map f) (𝟙 (F.obj C))) ≫
      BB.map (Prod.mkHom (𝟙 (F.obj L)) E) =
    BB.map (Prod.mkHom (𝟙 (F.obj K)) E) ≫
      BB.map (Prod.mkHom (F.map f) (𝟙 (unit m B T))) := by
    rw [← BB.map_comp, ← BB.map_comp]
    congr 1
    apply Prod.ext <;> simp
  have hr : BB.map (Prod.mkHom (F.map f) (𝟙 (unit m B T))) ≫ ρ (F.obj L) =
      ρ (F.obj K) ≫ F.map f := by
    let := ((m T).closed (proEtaleConstantRing T B)).monoidal
    simpa only [BB, tensor, CoefficientClosedStructure.tensor, tensor_map,
      tensorHom_id] using rightUnitor_naturality (F.map f)
  change F.map (BA.map (Prod.mkHom f (𝟙 C))) ≫
      (c.scalarTensor φ T).iso.hom.app (L,C) ≫
      BB.map (Prod.mkHom (𝟙 (F.obj L)) E) ≫ ρ (F.obj L) =
    ((c.scalarTensor φ T).iso.hom.app (K,C) ≫
      BB.map (Prod.mkHom (𝟙 (F.obj K)) E) ≫ ρ (F.obj K)) ≫ F.map f
  rw [reassoc_of% h, ← Category.assoc _ _ (ρ (F.obj L)), ht]
  simp only [Category.assoc, hr]

private theorem scalarProjection_isIso_of_representatives
    (m : Models.{u}) (c : Choices m) {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    (h : ∀ (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ),
      proEtaleFlatRepresentatives T (proEtaleConstantRing T A) P →
        IsIso (scalarProjection m c φ T (DerivedCategory.Q.obj P)))
    (K : proEtaleDerivedCategory T A) : IsIso (scalarProjection m c φ T K) := by
  let R := proEtaleConstantRing T A
  let H := DerivedCategory.Q.objPreimage K
  obtain ⟨P, q, hP, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) H
  have hp : proEtaleFlatRepresentatives T R P :=
    ⟨hP, fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X n)).symm (hflat n)⟩
  have := h P hp
  have := hq
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let e₁ := (tensor m A T).mapIso (e.prod (Iso.refl (coefficient m φ T)))
  let e₂ := (scalarRestriction φ T).mapIso ((scalar m φ T).mapIso e)
  have hn : e₁.hom ≫ scalarProjection m c φ T K =
      scalarProjection m c φ T (DerivedCategory.Q.obj P) ≫ e₂.hom :=
    scalarProjection_naturality m c φ T e.hom
  have : IsIso (e₁.hom ≫ scalarProjection m c φ T K) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_left e₁.hom _

/-- Canonical scalar tensor models compatible with open inverse image.
Source: Stacks, sites-cohomology.tex, Tags 07A4, 07A6 and 0D6D.
(blueprint: lem-sp-canonical-open-scalar-tensor-models).

Proof: choose the closed symmetric monoidal structures with their representative
coherence from `ringedDerived_closed_symmetric_monoidal`, and the normalized
extension/restriction derived pairs. The normalized scalar tensor comparison gives
`scalarTensor`. For open inverse image, descend the sectionwise tensor and unit
comparisons along flat-term K-flat resolutions. Associativity and the two unit
laws hold on pure-tensor summands, hence after descent. This gives `openMonoidal`
with its prescribed tensorator. To compare scalar extension with tensoring by the
restricted B unit, resolve the first factor by a K-flat complex. The scalar
adjunct in `scalarProjection` sends x tensor b to b tensor x. Its inverse is
x tensor b in the same representative model, so the displayed map is invertible.
Finally both factorizations of pullback along (U,B) to (X,A) send a pure tensor
to the same balanced tensor. Their totalized maps preserve each bidegree, so no
additional sign occurs. Fully faithful restriction to resolving representatives
makes the two inverse tensorator composites equal on arbitrary derived objects.
The construction applies to empty opens, zero rings and nonflat ring maps. -/
theorem open_scalar_tensor_models :
    ∃ m : Models.{u}, ∃ c : Choices m, Nonempty (TensorCompatibility m c) := by
  obtain ⟨m, hm, hcoh⟩ := native_models.{u}
  let μ (T : Scheme.{u}) {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}}
      (a : R ⟶ S) : ScalarHomTensorComparison.{u + 1, u, u + 1, u + 2}
        (J := Scheme.ProEt.topology T) (m T) a :=
    (ScalarHomTensor.scalarHomTensorComparison_exists (m T) a).some
  let c : Choices m := {
    scalarTensor := fun φ T ↦ μ T (proEtaleConstantRingMap (T := T) φ)
    openMonoidal := fun A _ _ {U X} j _ ↦ nativeOpenMonoidal m hm A j
    open_normalization := nativeOpen_normalization m hm }
  refine ⟨m, c, ⟨⟨?_, inverse_tensor_coherence m c⟩⟩⟩
  intro A B _ _ _ _ φ T K
  refine scalarProjection_isIso_of_representatives m c φ T ?_ K
  intro P hp
  let J := Scheme.ProEt.topology T
  let RA := proEtaleConstantRing T A
  let RB := proEtaleConstantRing T B
  let a := proEtaleConstantRingMap (T := T) φ
  let s := scalarPair m φ T
  let E := scalarComplex.{u + 1, u, u + 1} s.extension s.extension_additive
  let O := ringedTensorUnitComplex.{u + 1, u, u + 1} J RB
  let C := ((SheafOfModules.scalarRestriction.{u + 1, u, u + 1} a).mapHomologicalComplex
    (.up ℤ)).obj O
  obtain ⟨β, ⟨hc⟩⟩ := hcoh T RB
  have hP := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr hp.1
  have hEP := (c.scalarTensor φ T).preservesKFlat P hP
  obtain ⟨r, hrpure, hrnorm⟩ := hc.rightUnitor_model (E.obj P) hEP
  obtain ⟨Q, g, hQ, hflat, hg, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := RA) C
  have hq : proEtaleFlatRepresentatives T RA Q :=
    ⟨hQ, fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso RA (Q.X n)).symm (hflat n)⟩
  have := hg
  exact scalarProjection_isIso_of_chain m c φ T β hc P Q hp hq g r hrnorm
    (scalar_balancing_chain_quasiIso m T (μ T) φ P Q hP g hg r hrpure)

end AlgebraicGeometry.ProEtale.OpenScalarTensor

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.RingTheory.PolynomialCotangentIdentification
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Homology.QuasiIso
import Sheaf.RingTheory.LocalizationCotangentVanishing
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Flat.Localization

/-! # Localization of the standard cotangent differential augmentation

Source: Stacks Project, Cotangent Complex, Tags 08PN, 08QL and 08SF, and
Algebra, Tags 00DK, 00CS and 00RT
(blueprint: lem-trf-cotangent-augmentation-localization).

Tensor factors are written in the order `C ⊗[B] N`, as in the existing
standard differential-complex interface. The fraction formulas specify the
same canonical identification as the opposite order in the source.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite Simplicial
open scoped TensorProduct ChangeOfRings

namespace Algebra.CotangentResolution

/-- Termwise tensor with the localization, retaining its scalar action.
Source: Stacks 00DK (blueprint: lem-trf-cotangent-augmentation-localization). -/
abbrev localizationTensor {B : Type u} [CommRing B] (T : Submonoid B) :=
  ModuleCat.extendScalars.{u} (algebraMap B (Localization T))

/-- Transport from ring-map scalar extension to the existing algebra-instance tensor.
Only the equality `toAlgebra_algebraMap` is used. Source: Stacks 00DK
(blueprint: lem-trf-cotangent-augmentation-localization). -/
def localizationTensorIso {B : Type u} [CommRing B] (T : Submonoid B)
    (N : ModuleCat.{u} B) :
    (localizationTensor T).obj N ≅ ModuleCat.of (Localization T) (Localization T ⊗[B] N) :=
  by
    let F : Algebra B (Localization T) → ModuleCat.{u} (Localization T) := fun α ↦
      letI : Algebra B (Localization T) := α
      letI : Module B (Localization T) := α.toModule
      ModuleCat.of (Localization T) (Localization T ⊗[B] N)
    exact eqToIso (congrArg F (toAlgebra_algebraMap (R := B) (S := Localization T)))

/-- The canonical tensor/fraction identification, constructed using Mathlib's
localization universal property, with no choice of an unspecified isomorphism.
Source: Stacks 00DK (blueprint: lem-trf-cotangent-augmentation-localization). -/
def tensorFractionIso {B : Type u} [CommRing B] (T : Submonoid B)
    (N : ModuleCat.{u} B) :
    (localizationTensor T).obj N ≅ ModuleCat.of (Localization T) (LocalizedModule T N) :=
  localizationTensorIso T N ≪≫ (LocalizedModule.equivTensorProduct T N).symm.toModuleIso

/-- Localization of a module map with its localization-ring linearity.
Source: Stacks 00CS (blueprint: lem-trf-cotangent-augmentation-localization). -/
def fractionMap {B : Type u} [CommRing B] (T : Submonoid B)
    {M N : ModuleCat.{u} B} (v : M ⟶ N) :
    ModuleCat.of (Localization T) (LocalizedModule T M) ⟶
      ModuleCat.of (Localization T) (LocalizedModule T N) :=
  ModuleCat.ofHom (IsLocalizedModule.mapExtendScalars T
    (LocalizedModule.mkLinearMap T M) (LocalizedModule.mkLinearMap T N)
    (Localization T) v.hom)

/-- The actual standard differential cochain complex of the algebra map.
Source: Stacks 08PN (blueprint: lem-trf-cotangent-augmentation-localization). -/
abbrev standardDifferentialComplex
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (D : Coherence.{u}) (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :=
  differentialComplex (D.differentials
    (D.standard (Arrow.mk (CommRingCat.ofHom (algebraMap A B)))))

/-- The ring square with bottom arrow the identity of the base and top arrow
localization. Source: Stacks 08QL
(blueprint: lem-trf-cotangent-augmentation-localization). -/
def standardLocalizationSquare (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (T : Submonoid B) :
    Arrow.mk (CommRingCat.ofHom (algebraMap A B)) ⟶
      Arrow.mk (CommRingCat.ofHom (algebraMap A (Localization T))) :=
  Arrow.homMk (𝟙 _) (CommRingCat.ofHom (algebraMap B (Localization T)))
    (by ext a; exact (IsScalarTower.algebraMap_apply A B (Localization T) a).symm)

/-- The canonical localization isomorphism on universal differentials, composed
from the tensor/fraction identification and Mathlib's Kähler base-change map.
Source: Stacks 00RT (2)
(blueprint: lem-trf-cotangent-augmentation-localization). -/
def localizedDifferentialsIso (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (T : Submonoid B) :
    ModuleCat.of (Localization T) (LocalizedModule T
      (CommRingCat.KaehlerDifferential (CommRingCat.ofHom (algebraMap A B)))) ≅
    CommRingCat.KaehlerDifferential (CommRingCat.ofHom (algebraMap A (Localization T))) :=
  (tensorFractionIso T _).symm ≪≫
    (localizationTensor T).mapIso (kahlerAlgebraMapIso A B) ≪≫
    localizationTensorIso T (ModuleCat.of B (KaehlerDifferential A B)) ≪≫
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A B
      (Localization T)).toModuleIso ≪≫ (kahlerAlgebraMapIso A (Localization T)).symm

/-- Tensor the specified augmentation and identify its target with the localized
module of differentials in degree zero. Source: Stacks 08PN and 00DK
(blueprint: lem-trf-cotangent-augmentation-localization). -/
def tensorDifferentialAugmentation
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    {D : Coherence.{u}} {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (T : Submonoid B)
    (a : DifferentialAugmentation D (Arrow.mk (CommRingCat.ofHom (algebraMap A B)))) :=
  ((localizationTensor T).mapHomologicalComplex (ComplexShape.up ℤ)).map a.map ≫
    (HomologicalComplex.singleMapHomologicalComplex (localizationTensor T)
      (ComplexShape.up ℤ) 0).hom.app _ ≫
    (HomologicalComplex.single (ModuleCat.{u} (Localization T))
      (ComplexShape.up ℤ) 0).map (tensorFractionIso T _).hom

/-- Exact localization, its normalized cohomology comparison, the canonical
cotangent localization map, and the commuting augmentation square. The
existential chain map is fixed on every standard tensor generator, not an
arbitrary map; likewise the cohomology comparison is fixed on fraction cycles.
Source: Stacks 08SF, 08QL, 00DK, 00CS and 00RT (2)
(blueprint: lem-trf-cotangent-augmentation-localization).

Proof:
1. The inverse tensor/fraction formulas are n ⊗ b/t ↦ bn/t and
   n/t ↦ n ⊗ 1/t. The relation u(t'n-tn') = 0 proves well-definedness;
   common denominators prove additivity and balancing proves C-linearity.
   They commute with every module map on these generators.
2. Apply lem-weil-pbc-localization-module-exact to cycles, boundaries, and
   0 → boundaries → cycles → cohomology → 0. This gives the displayed
   fraction-cycle-normalized cohomology isomorphisms, naturally in chain maps.
   Hence termwise tensor preserves quasi-isomorphisms.
3. The universal derivation defines a_R on degree-zero generators. The
   augmentation equations εd₀ = εd₁ annihilate the degree -1 differential;
   every other chain-map equation has zero target.
4. lem-trf-localization-cotangent-vanishing gives L[C/B] = 0.
   lem-trf-cotangent-retract-transitivity-vanishing with both maps identity
   gives L[A/A] = 0. Localization is flat by lem-weil-pbc-localization-flat.
   The flat clause of lem-trf-cotangent-zero-relative-square makes the
   canonical standard chain comparison λ a quasi-isomorphism.
5. lem-weil-pbc-kahler-differentials-localization gives κ. The standard map
   h satisfies ε_Ch = ε_B/1. Thus a_Cλ and κ(a_B tensor C) both send
   dq ⊗ b/t to (b/t)d(ε_B(q)/1). These generators span degree zero, and
   every other target degree is zero, so the chain maps, and hence their
   images in D(C), agree.
6. If a_B is a quasi-isomorphism, step 2 applies to its tensor. In cohomology
   cancel the invertible H(λ) from the square to obtain that κ⁻¹a_C is a
   quasi-isomorphism. The fraction arguments work also when 0 belongs to T;
   no nonzero-ring, finite-generation or principal-localization condition occurs. -/
theorem cotangent_augmentation_localization
    [∀ R : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} R)]
    (D : Coherence.{u}) (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (T : Submonoid B) :
    (∀ (N : ModuleCat.{u} B) (n : N) (b : B) (t : T),
      (tensorFractionIso T N).hom
        (Localization.mk b t ⊗ₜ[B, algebraMap B (Localization T)] n) =
          LocalizedModule.mk (b • n) t) ∧
    (∀ (N : ModuleCat.{u} B) (n : N) (t : T),
      (tensorFractionIso T N).inv (LocalizedModule.mk n t) =
        Localization.mk 1 t ⊗ₜ[B, algebraMap B (Localization T)] n) ∧
    (∀ {M N : ModuleCat.{u} B} (v : M ⟶ N),
      (localizationTensor T).map v ≫ (tensorFractionIso T N).hom =
        (tensorFractionIso T M).hom ≫ fractionMap T v) ∧
    (∃ H : ∀ (K : CochainComplex (ModuleCat.{u} B) ℤ) (i : ℤ),
      (((localizationTensor T).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i ≅
        ModuleCat.of (Localization T) (LocalizedModule T (K.homology i)),
      (∀ (K : CochainComplex (ModuleCat.{u} B) ℤ) (i : ℤ) (z : K.cycles i) (t : T),
        ∃ z' : (((localizationTensor T).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).cycles i,
          (((localizationTensor T).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).iCycles i z' =
              Localization.mk 1 t ⊗ₜ[B, algebraMap B (Localization T)] K.iCycles i z ∧
          (H K i).hom ((((localizationTensor T).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K).homologyπ i z') =
              LocalizedModule.mk (K.homologyπ i z) t) ∧
      ∀ {K L : CochainComplex (ModuleCat.{u} B) ℤ} (v : K ⟶ L) (i : ℤ),
        HomologicalComplex.homologyMap
            (((localizationTensor T).mapHomologicalComplex (ComplexShape.up ℤ)).map v) i ≫
          (H L i).hom =
        (H K i).hom ≫ fractionMap T (HomologicalComplex.homologyMap v i)) ∧
    (∀ {K L : CochainComplex (ModuleCat.{u} B) ℤ} (v : K ⟶ L), QuasiIso v →
      QuasiIso (((localizationTensor T).mapHomologicalComplex (ComplexShape.up ℤ)).map v)) ∧
    (∀ (b : B) (t : T),
      (localizedDifferentialsIso A B T).hom
        (LocalizedModule.mk (CommRingCat.KaehlerDifferential.d b) t) =
      Localization.mk 1 t • CommRingCat.KaehlerDifferential.d (algebraMap B (Localization T) b)) ∧
    ∃ (aB : DifferentialAugmentation D
        (Arrow.mk (CommRingCat.ofHom (algebraMap A B))))
      (aC : DifferentialAugmentation D
        (Arrow.mk (CommRingCat.ofHom (algebraMap A (Localization T)))))
      (lam : (((localizationTensor T).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (standardDifferentialComplex D A B)) ⟶
        standardDifferentialComplex D A (Localization T)),
      (∀ (n : ℕ) (c : Localization T)
          (x : (D.standard (Arrow.mk (CommRingCat.ofHom (algebraMap A B)))).algebra.obj
            (op ⦋n⦌)),
        lam.f (-(n : ℤ)) (c ⊗ₜ[B, algebraMap B (Localization T)]
            complexGenerator (D.differentials
              (D.standard (Arrow.mk (CommRingCat.ofHom (algebraMap A B))))) n 1 x) =
          c • complexGenerator (D.differentials
            (D.standard (Arrow.mk (CommRingCat.ofHom (algebraMap A (Localization T)))))) n 1
              ((D.standardMap (standardLocalizationSquare A B T)).map.app (op ⦋n⦌) x)) ∧
      QuasiIso lam ∧
      (DerivedCategory.Q (C := ModuleCat.{u} (CommRingCat.of (Localization T)))).map
        (lam ≫ aC.map) =
        (DerivedCategory.Q (C := ModuleCat.{u} (CommRingCat.of (Localization T)))).map
          (tensorDifferentialAugmentation T aB ≫
          (HomologicalComplex.single (ModuleCat.{u} (Localization T))
            (ComplexShape.up ℤ) 0).map (localizedDifferentialsIso A B T).hom) ∧
      (∀ (b : B) (t : T)
          (x : (D.standard (Arrow.mk (CommRingCat.ofHom (algebraMap A B)))).algebra.obj
            (op ⦋0⦌)),
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (CommRingCat.KaehlerDifferential
            (CommRingCat.ofHom (algebraMap A (Localization T))))).hom
          ((lam ≫ aC.map).f 0 (Localization.mk b t ⊗ₜ[B, algebraMap B (Localization T)]
            complexGenerator (D.differentials
              (D.standard (Arrow.mk (CommRingCat.ofHom (algebraMap A B))))) 0 1 x)) =
          Localization.mk b t • CommRingCat.KaehlerDifferential.d
            (algebraMap B (Localization T)
              ((D.standard (Arrow.mk (CommRingCat.ofHom (algebraMap A B)))).augmentation.app
                (op ⦋0⦌) x))) ∧
      (∀ (b : B) (t : T)
          (x : (D.standard (Arrow.mk (CommRingCat.ofHom (algebraMap A B)))).algebra.obj
            (op ⦋0⦌)),
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (CommRingCat.KaehlerDifferential
            (CommRingCat.ofHom (algebraMap A (Localization T))))).hom
          ((tensorDifferentialAugmentation T aB ≫
              (HomologicalComplex.single (ModuleCat.{u} (Localization T))
                (ComplexShape.up ℤ) 0).map (localizedDifferentialsIso A B T).hom).f 0
            (Localization.mk b t ⊗ₜ[B, algebraMap B (Localization T)]
            complexGenerator (D.differentials
              (D.standard (Arrow.mk (CommRingCat.ofHom (algebraMap A B))))) 0 1 x)) =
          Localization.mk b t • CommRingCat.KaehlerDifferential.d
            (algebraMap B (Localization T)
              ((D.standard (Arrow.mk (CommRingCat.ofHom (algebraMap A B)))).augmentation.app
                (op ⦋0⦌) x))) ∧
      (QuasiIso aB.map → QuasiIso (aC.map ≫
        (HomologicalComplex.single (ModuleCat.{u} (Localization T))
          (ComplexShape.up ℤ) 0).map (localizedDifferentialsIso A B T).inv)) := by
  sorry

end Algebra.CotangentResolution

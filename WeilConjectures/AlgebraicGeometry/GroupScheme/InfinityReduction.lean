/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.GlobalGeometricFrobenius.CondensedGlobalGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPullback.NativeCondensedPullbackFrobenius
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.DeligneLaumon.CondensedClopenCompact.CondensedClopenCompactDecomposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ModelSemilinearComparison.CondensedModelFrobeniusOperatorsBase
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.AlgebraicGeometry.CondensedLisseExtensionInertia.CondensedLisseExtensionInertia

/-!
# Infinity reduction for weights

The source is the latest blueprint section
`part-weights-riemann-hypothesis/sec-deligne-laumon-a1/sec-arbitrary-curves/
sk-lem-wft-infinity-reduction`.  This file records its two assertions.  In particular the
Frobenius in the first assertion is the compact-support operator supplied by
`GlobalGeometricFrobenius`; its extension to the coefficient-section ring is part of the
explicit data below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
universe u

open CategoryTheory CategoryTheory.MonObj AlgebraicGeometry
open CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The coefficient embedding and its compatible condensed section-ring realization.
Source: latest blueprint, coefficient convention in sk-lem-wft-infinity-reduction
(blueprint: sk-lem-wft-infinity-reduction). -/
structure WeightEmbedding (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] where
  iota : PadicAlgCl ell →+* ℂ
  iotaGamma : CategoryTheory.MonObj.Γ (Profinite.padicAlgClRingObj.{u} ell) →+* ℂ
  compat : iotaGamma.comp (Profinite.PadicAlgCl.constRingHom ell) = iota

/-- The numerical eigenvalue bound `wt H_c^r ≤ b`: every eigenvalue `α` of the specified
endomorphism satisfies `|ι(α)| ≤ q^{b/2}`.
Source: latest blueprint, sk-lem-wft-infinity-reduction, statement, first paragraph
(blueprint: sk-lem-wft-infinity-reduction). -/
def weightBound (ell : ℕ) [Fact ell.Prime]
    (iotaGamma : CategoryTheory.MonObj.Γ (Profinite.padicAlgClRingObj.{u} ell) →+* ℂ) (q : ℕ)
    {M : ModuleCat.{u + 1} (CategoryTheory.MonObj.Γ (Profinite.padicAlgClRingObj.{u} ell))}
    (T : M ⟶ M) (b : ℝ) : Prop :=
  ∀ α : CategoryTheory.MonObj.Γ (Profinite.padicAlgClRingObj.{u} ell),
    Module.End.HasEigenvalue T.hom α →
      ‖iotaGamma α‖ ≤ (q : ℝ) ^ (b / 2)

/-- The actual compact-support geometric Frobenius in degree `r` for `K`.
Source: latest blueprint, def-weil-global-geometric-frobenius;
(blueprint: sk-lem-wft-infinity-reduction). -/
def compactFrobenius (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (c : WeilCoefficient ell) (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ c) (r : ℤ) :=
  (GlobalGeometricFrobenius.globalGeometricFrobeniusOnCohomology D ell hEll X₀ c c₀ K r).2

/-- The actual degree-one compact-support module `H_c^1` of a native Weil module `M[0]`.
Source: latest blueprint, sk-lem-wft-infinity-reduction, displayed surjection; def-weil-ordinary-compact-cohomology
(blueprint: sk-lem-wft-infinity-reduction). -/
abbrev compactHOne (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] (c₀ : Compactification (D.geometricFiber X₀).hom)
    (M : NativeL2.WeilModule D ell X₀) : ModuleCat.{u + 1} (PadicAlgCl ell) :=
  (DerivedCategory.homologyFunctor _ 1).obj
    ((condensedQbarCompactSections ell D.k c₀).obj
      ((DerivedCategory.singleFunctor _ 0).obj M.carrier))

/-- The degree-zero derived Weil structure attached to a native Weil module.
Source: the native-to-strict single-complex construction used by the compact-support
Frobenius interface (blueprint: def-weil-global-geometric-frobenius). -/
def nativeTheta (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (M : NativeL2.WeilModule D ell X₀) :
    (CondensedClopenCompact.pull ell (D.geometricFrobenius X₀).hom).obj
      ((DerivedCategory.singleFunctor _ 0).obj M.carrier) ≅
      ((DerivedCategory.singleFunctor _ 0).obj M.carrier) :=
  ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
      (D.geometricFrobenius X₀).hom).mapDerivedCategorySingleFunctor 0).app M.carrier ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso M.str

/-- The transport data used by the canonical compact-support Frobenius.  The point and open
comparisons are the normalized six-functor transports; the endomorphism below is built from them,
so no unrelated linear operator can be supplied.
Source: latest blueprint, def-weil-global-geometric-frobenius, compact-support composite, as used
in sk-lem-wft-infinity-reduction step 6 (blueprint: sk-lem-wft-infinity-reduction). -/
structure NativeCompactFrobeniusData (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] (c₀ : Compactification (D.geometricFiber X₀).hom)
    (M : NativeL2.WeilModule D ell X₀) where
  pointTransport : CondensedClopenCompact.PointTransport ell D.k
    (CondensedClopenCompact.fieldFrobenius D)
  gZ : c₀.Z ⟶ c₀.Z
  proper_frobenius :
    gZ ≫ c₀.g = c₀.g ≫ Spec.map
      (CommRingCat.ofHom (CondensedClopenCompact.fieldFrobenius D).toRingHom)
  open_frobenius : (D.geometricFrobenius X₀).hom ≫ c₀.i = c₀.i ≫ gZ
  openTransport : CondensedClopenCompact.OpenTransport ell c₀.i
    (D.geometricFrobenius X₀).hom gZ open_frobenius

/-- The actual compact-support Frobenius on the native degree-one cohomology module.
Source: latest blueprint, def-weil-global-geometric-frobenius, compact-support composite, as used
in sk-lem-wft-infinity-reduction step 6 (blueprint: sk-lem-wft-infinity-reduction). -/
def nativeCompactFrobenius (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] (c₀ : Compactification (D.geometricFiber X₀).hom)
    (M : NativeL2.WeilModule D ell X₀)
    (P : NativeCompactFrobeniusData D ell X₀ c₀ M) :
    compactHOne D ell X₀ c₀ M ⟶ compactHOne D ell X₀ c₀ M :=
  (DerivedCategory.homologyFunctor _ 1).map
    (CondensedClopenCompact.action P.pointTransport c₀
      (D.geometricFrobenius X₀).hom P.gZ P.proper_frobenius P.openTransport
      ((DerivedCategory.singleFunctor _ 0).obj M.carrier) (nativeTheta D ell X₀ M))

/-!
The regular-point witness records the point deletion, projective transport, actual lisse extension
and the compact-support cohomology map.
-/
/-- The base change `W₀m → P¹_{k_m}` of the given over-`k₀` map `p₁ : W₀ → P¹_{k₀}`,
through the pullback square of `P¹` along `Spec k_m → Spec k₀`.
Source: latest blueprint, sk-lem-wft-infinity-reduction, proof step 4 (the extended open
`W_{0,m}`) (blueprint: sk-lem-wft-infinity-reduction). -/
def baseChangedProjectiveMap (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
    {W₀ : Over (Spec (.of D.k₀))} {W₀m : Over (Spec (.of (D.extensionSubfield m hm)))}
    (base_change : W₀m ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj W₀)
    (p₁ : W₀.left ⟶ ProjectiveLine (Spec (.of D.k₀)))
    (p₁_over : p₁ ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀) = W₀.hom) :
    W₀m.left ⟶ ProjectiveLine (Spec (.of (D.extensionSubfield m hm))) := by
  let p₁O : W₀ ⟶ Over.mk (ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)) :=
    Over.homMk p₁ p₁_over
  let bp := Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))
  let e := (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) bp).isoPullback
  exact base_change.hom.left ≫ ((Over.pullback bp).map p₁O).left ≫ e.inv

/-! The finite constant model and projection used by the infinity-reduction statement. -/

/-- The literal base-change model over `k_m`.
Source: latest blueprint, constant-extension step 1;
(blueprint: sk-lem-wft-infinity-reduction). -/
abbrev infinityConstantExtensionModel (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
    (X₀ : Over (Spec (.of D.k₀))) : Over (Spec (.of (D.extensionSubfield m hm))) :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj X₀

/-- The canonical projection of the base-change model to the original model.
Source: latest blueprint, constant-extension step 1;
(blueprint: sk-lem-wft-infinity-reduction). -/
def infinityConstantExtensionProjection (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
    (X₀ : Over (Spec (.of D.k₀))) :
    Over.mk ((infinityConstantExtensionModel D m hm X₀).hom ≫
      Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) ⟶ X₀ :=
  Over.homMk
    (pullback.fst X₀.hom (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))))
    pullback.condition

/-- The base-change model is locally of finite type.
Source: latest blueprint, constant-extension step 1;
(blueprint: sk-lem-wft-infinity-reduction). -/
instance infinityConstantExtensionModel_lft (D : FiniteFieldDatum.{u}) (m : ℕ)
    (hm : 1 ≤ m) (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] : LocallyOfFiniteType (infinityConstantExtensionModel D m hm X₀).hom := by
  dsimp [infinityConstantExtensionModel]
  infer_instance

/-- The base-change model is quasi-compact.
Source: latest blueprint, constant-extension step 1;
(blueprint: sk-lem-wft-infinity-reduction). -/
instance infinityConstantExtensionModel_qc (D : FiniteFieldDatum.{u}) (m : ℕ)
    (hm : 1 ≤ m) (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] : QuasiCompact (infinityConstantExtensionModel D m hm X₀).hom := by
  dsimp [infinityConstantExtensionModel]
  infer_instance

/-- The base-change model is separated.
Source: latest blueprint, constant-extension step 1;
(blueprint: sk-lem-wft-infinity-reduction). -/
instance infinityConstantExtensionModel_sep (D : FiniteFieldDatum.{u}) (m : ℕ)
    (hm : 1 ≤ m) (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom]
    [QuasiCompact X₀.hom] [IsSeparated X₀.hom] :
    IsSeparated (infinityConstantExtensionModel D m hm X₀).hom := by
  dsimp [infinityConstantExtensionModel]
  infer_instance

/-- The geometric-fibre map induced by the constant-extension projection.
Source: latest blueprint, constant-extension step 1;
(blueprint: sk-lem-wft-infinity-reduction). -/
def constantExtensionGeometricMap (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom]
    (X₀m : Over (Spec (.of (D.extensionSubfield m hm))))
    [LocallyOfFiniteType X₀m.hom] [QuasiCompact X₀m.hom] [IsSeparated X₀m.hom]
    (projection : Over.mk (X₀m.hom ≫
      Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) ⟶ X₀) :
    ((NativeCondensedPullback.constantExtensionDatum D m hm).geometricFiber X₀m).left ⟶
      (D.geometricFiber X₀).left :=
  NativeCondensedPullback.geometricMap D m hm X₀ X₀m projection

/-- The canonical coefficient carrier obtained by upper-star along the geometric map.
Source: latest blueprint, constant-extension step 2;
(blueprint: sk-lem-wft-infinity-reduction). -/
def constantExtensionCarrier (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (m : ℕ) (hm : 1 ≤ m)
    (X₀m : Over (Spec (.of (D.extensionSubfield m hm))))
    [LocallyOfFiniteType X₀m.hom] [QuasiCompact X₀m.hom] [IsSeparated X₀m.hom]
    (projection : Over.mk (X₀m.hom ≫
      Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) ⟶ X₀)
    (K : strictWeilComplexCategory D ell hEll X₀ (WeilCoefficient.qbar)) :=
  (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
    (constantExtensionGeometricMap D m hm X₀ X₀m projection)).mapDerivedCategory.obj K.obj.carrier

/-- The canonical iterated Weil structure on the constant-extension carrier.
Source: latest blueprint, constant-extension step 2;
(blueprint: sk-lem-wft-infinity-reduction). -/
def constantExtensionStructure (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (m : ℕ) (hm : 1 ≤ m)
    (X₀m : Over (Spec (.of (D.extensionSubfield m hm))))
    [LocallyOfFiniteType X₀m.hom] [QuasiCompact X₀m.hom] [IsSeparated X₀m.hom]
    (projection : Over.mk (X₀m.hom ≫
      Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) ⟶ X₀)
    (K : strictWeilComplexCategory D ell hEll X₀ (WeilCoefficient.qbar)) :
    (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
      ((NativeCondensedPullback.constantExtensionDatum D m hm).geometricFrobenius X₀m).hom).mapDerivedCategory.obj
    (constantExtensionCarrier D ell hEll X₀ m hm X₀m projection K) ≅
      constantExtensionCarrier D ell hEll X₀ m hm X₀m projection K :=
  by
    have hlocal : ∀ n : ℕ, NativeCondensedModule.localPositivePower
        (D.geometricFrobenius X₀).hom n =
          ((End.of (D.geometricFrobenius X₀).hom) ^ (n + 1)).asHom := by
      intro n
      induction n with
      | zero => simp [NativeCondensedModule.localPositivePower]
      | succ n ih =>
          simp only [NativeCondensedModule.localPositivePower, ih, pow_succ', End.mul_def]
    have hpow : (NativeCondensedModule.localPositivePower (D.geometricFrobenius X₀).hom
        (m - 1)) = ((End.of (D.geometricFrobenius X₀).hom) ^ m).asHom := by
      rw [hlocal, Nat.sub_add_cancel hm]
    let θm :=
      eqToIso (congrArg
        (fun f ↦ (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar)) f).mapDerivedCategory.obj
          K.obj.carrier) hpow) ≪≫
      AlgebraicGeometry.ProEtale.CondensedRing.ModelSemilinearComparison.iterateStructure
        (WeilCoefficient.ab (WeilCoefficient.qbar)) (D.geometricFrobenius X₀).hom
        (K := K.obj.carrier) K.obj.str m
    let θgeo :
        (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
          (constantExtensionGeometricMap D m hm X₀ X₀m projection)).mapDerivedCategory.obj
          ((CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
            (NativeCondensedModule.localPositivePower (D.geometricFrobenius X₀).hom (m - 1))).mapDerivedCategory.obj
            K.obj.carrier) ≅
          (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
            (constantExtensionGeometricMap D m hm X₀ X₀m projection)).mapDerivedCategory.obj
            K.obj.carrier :=
      (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
        (constantExtensionGeometricMap D m hm X₀ X₀m projection)).mapDerivedCategory.mapIso θm
    have hsource :
        ((CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
          (constantExtensionGeometricMap D m hm X₀ X₀m projection)).mapDerivedCategory ⋙
          (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
            ((NativeCondensedPullback.constantExtensionDatum D m hm).geometricFrobenius X₀m).hom).mapDerivedCategory).obj
          K.obj.carrier =
        (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
          ((NativeCondensedPullback.constantExtensionDatum D m hm).geometricFrobenius X₀m).hom).mapDerivedCategory.obj
          ((CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
            (constantExtensionGeometricMap D m hm X₀ X₀m projection)).mapDerivedCategory.obj K.obj.carrier) := rfl
    have htarget :
        ((CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
          (NativeCondensedModule.localPositivePower (D.geometricFrobenius X₀).hom (m - 1))).mapDerivedCategory ⋙
          (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
            (constantExtensionGeometricMap D m hm X₀ X₀m projection)).mapDerivedCategory).obj
          K.obj.carrier =
        (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
          (constantExtensionGeometricMap D m hm X₀ X₀m projection)).mapDerivedCategory.obj
          ((CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
            (NativeCondensedModule.localPositivePower (D.geometricFrobenius X₀).hom (m - 1))).mapDerivedCategory.obj
            K.obj.carrier) := rfl
    simpa only [constantExtensionCarrier] using
      (eqToIso hsource.symm ≪≫
      ((Functor.mapDerivedCategoryCompIso
        (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
          (constantExtensionGeometricMap D m hm X₀ X₀m projection))
        (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
          ((NativeCondensedPullback.constantExtensionDatum D m hm).geometricFrobenius X₀m).hom)).app
          K.obj.carrier).symm ≪≫
        (Functor.mapDerivedCategoryNatIso
        (CondensedRing.upperStarSquareComparison (WeilCoefficient.ab (WeilCoefficient.qbar))
          (NativeCondensedPullback.geometricMap_frobenius D m hm X₀ X₀m projection))).symm.app
          K.obj.carrier ≪≫
        (Functor.mapDerivedCategoryCompIso
          (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
            (NativeCondensedModule.localPositivePower (D.geometricFrobenius X₀).hom (m - 1)))
          (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
            (constantExtensionGeometricMap D m hm X₀ X₀m projection))).app K.obj.carrier ≪≫
        eqToIso htarget ≪≫ θgeo)

/-- The iterated Weil structure transported to a supplied complex whose carrier is
identified with the canonical constant-extension carrier.
Source: latest blueprint, constant-extension step 2;
(blueprint: sk-lem-wft-infinity-reduction). -/
def transportedConstantExtensionStructure (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (m : ℕ) (hm : 1 ≤ m) (X₀m : Over (Spec (.of (D.extensionSubfield m hm))))
    [LocallyOfFiniteType X₀m.hom] [QuasiCompact X₀m.hom] [IsSeparated X₀m.hom]
    (projection : Over.mk (X₀m.hom ≫
      Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) ⟶ X₀)
    (K : strictWeilComplexCategory D ell hEll X₀ (WeilCoefficient.qbar))
    (Kₘ : strictWeilComplexCategory (NativeCondensedPullback.constantExtensionDatum D m hm)
      ell hEll X₀m (WeilCoefficient.qbar))
    (hKₘ : Kₘ.obj.carrier = constantExtensionCarrier D ell hEll X₀ m hm X₀m projection K) :
    (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
      ((NativeCondensedPullback.constantExtensionDatum D m hm).geometricFrobenius X₀m).hom).mapDerivedCategory.obj
        Kₘ.obj.carrier ≅ Kₘ.obj.carrier :=
  eqToIso (congrArg
      (fun A ↦ (CondensedRing.upperStar (WeilCoefficient.ab (WeilCoefficient.qbar))
        ((NativeCondensedPullback.constantExtensionDatum D m hm).geometricFrobenius X₀m).hom).mapDerivedCategory.obj A)
      hKₘ) ≪≫
    constantExtensionStructure D ell hEll X₀ m hm X₀m projection K ≪≫
    eqToIso hKₘ.symm

/-- Geometric compact-support coefficient cohomology `H_c^r(X, K)`.
Source: latest blueprint, sk-lem-wft-infinity-reduction, statement; def-weil-ordinary-compact-cohomology
(blueprint: sk-lem-wft-infinity-reduction). -/
abbrev compactCohomology (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ (WeilCoefficient.qbar)) (r : ℤ) :=
  (condensedRingCompactCohomology (WeilCoefficient.ab (WeilCoefficient.qbar)) c₀ r).obj
    K.obj.carrier

/-- Constant-extension data for the same geometric complex.  Its carrier is the literal
base-change carrier and its Weil structure is the iterated `θ^[m]` structure; the
compact-support operator is supplied by `extensionFrobenius` below.
Source: latest blueprint, steps 1--2; (blueprint: sk-lem-wft-infinity-reduction). -/
structure ConstantExtensionData (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ (WeilCoefficient.qbar))
    (r : ℤ) (m : ℕ) (hm : 1 ≤ m) where
  cₘ : Compactification
    ((NativeCondensedPullback.constantExtensionDatum D m hm).geometricFiber
      (infinityConstantExtensionModel D m hm X₀)).hom
  Kₘ : strictWeilComplexCategory (NativeCondensedPullback.constantExtensionDatum D m hm)
    ell hEll (infinityConstantExtensionModel D m hm X₀) (WeilCoefficient.qbar)
  Kₘ_carrier : Kₘ.obj.carrier =
    constantExtensionCarrier D ell hEll X₀ m hm (infinityConstantExtensionModel D m hm X₀)
      (infinityConstantExtensionProjection D m hm X₀) K
  Kₘ_structure : Kₘ.obj.str =
    transportedConstantExtensionStructure D ell hEll X₀ m hm
      (infinityConstantExtensionModel D m hm X₀) (infinityConstantExtensionProjection D m hm X₀) K Kₘ Kₘ_carrier

/-- The extension operator is the actual iterated compact-support Frobenius on the same
geometric cohomology object.  The finite-field model and its Weil structure are therefore fixed
by the given `K`, `m`, and `hm`, rather than chosen as unrelated module data.
Source: latest blueprint, sk-lem-wft-infinity-reduction, proof step 2
(blueprint: sk-lem-wft-infinity-reduction). -/
def ConstantExtensionData.extensionFrobenius
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hEll : ell ≠ D.p) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (c₀ : Compactification (D.geometricFiber X₀).hom)
    (K : strictWeilComplexCategory D ell hEll X₀ (WeilCoefficient.qbar))
    (r : ℤ) (m : ℕ) (hm : 1 ≤ m)
    (E : ConstantExtensionData D ell hEll X₀ c₀ K r m hm) :
    compactCohomology (NativeCondensedPullback.constantExtensionDatum D m hm) ell hEll
      (infinityConstantExtensionModel D m hm X₀) E.cₘ E.Kₘ r ⟶
      compactCohomology (NativeCondensedPullback.constantExtensionDatum D m hm) ell hEll
        (infinityConstantExtensionModel D m hm X₀) E.cₘ E.Kₘ r := by
  exact compactFrobenius (NativeCondensedPullback.constantExtensionDatum D m hm) ell hEll
    (infinityConstantExtensionModel D m hm X₀) (WeilCoefficient.qbar) E.cₘ E.Kₘ r


/-! The next two definitions keep the compactification and the localization arrow
canonical.  They are the literal open-immersion lower-shriek map followed by the
proper/open compact-support comparison, rather than a separately supplied linear map. -/

/-- The compactification of `j ≫ f` obtained by precomposing an open immersion.
Source: latest blueprint, sk-lem-wft-infinity-reduction, proof step 6 (compact-support composition)
(blueprint: sk-lem-wft-infinity-reduction). -/
def precompCompactification {X Y S : Scheme.{u}} {f : Y ⟶ S}
    (c : Compactification f) (j : X ⟶ Y) (hj : IsOpenImmersion j) :
    Compactification (j ≫ f) := by
  letI := hj
  exact c.precomp j

/-- The localization map `H_c^1(U, j^*M) → H_c^1(Y, M)` from the counit `j_!j^* → 𝟭`.
Source: latest blueprint, sk-lem-wft-infinity-reduction, proof step 6 (open-closed localization)
(blueprint: sk-lem-wft-infinity-reduction). -/
def compactLocalizationMapRaw (ell : ℕ) [Fact ell.Prime]
    {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : Scheme.{u}} {_aX : X ⟶ Spec (.of k)} {aY : Y ⟶ Spec (.of k)}
    (j : X ⟶ Y) (hj : IsOpenImmersion j) (c : Compactification aY)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) Y))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ell) X))
    (eN : (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) j).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj N) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PadicAlgCl ell)) 1).obj
        ((condensedQbarCompactSections ell k
          (precompCompactification c j hj)).obj
          ((DerivedCategory.singleFunctor _ 0).obj N)) ⟶
      (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PadicAlgCl ell)) 1).obj
        ((condensedQbarCompactSections ell k c).obj
          ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  letI := hj
  let J := (DerivedCategory.singleFunctor _ 0).obj M
  let R := ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification
    (Profinite.padicAlgClRingObj ell) c
  let Rj := ProEtale.CondensedRing.rightDerivedLowerShriekOfCompactification
    (Profinite.padicAlgClRingObj ell) (precompCompactification c j hj)
  let q := (ProEtale.CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (Profinite.padicAlgClRingObj ell) j).counit.app J
  let t := (ProEtale.CondensedRing.mateOpenSourceLowerShriek
    (Profinite.padicAlgClRingObj ell) c j)
  let d : Rj.obj ((DerivedCategory.singleFunctor _ 0).obj N) ⟶ R.obj J :=
    Rj.map eN.inv ≫ t.inv.app _ ≫ R.map q
  exact (DerivedCategory.homologyFunctor _ 1).map
    ((condensedQbarDerivedPointSections ell k).map d)

/-- The localization map for the moved open `V → W`, with its source identified with the
precomposed compactification.
Source: latest blueprint, sk-lem-wft-infinity-reduction, proof steps 5--6
(blueprint: sk-lem-wft-infinity-reduction). -/
def compactLocalizationMapCanonical (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (m : ℕ) (hm : 1 ≤ m)
    (W₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom]
    [IsSeparated W₀.hom]
    (V₀ : Over (Spec (.of (D.extensionSubfield m hm))))
    [LocallyOfFiniteType V₀.hom] [QuasiCompact V₀.hom] [IsSeparated V₀.hom]
    (j : ((NativeCondensedPullback.constantExtensionDatum D m hm).geometricFiber V₀).left ⟶
      (D.geometricFiber W₀).left)
    (hj : IsOpenImmersion j)
    (cW : Compactification (D.geometricFiber W₀).hom)
    (cV : Compactification
      ((NativeCondensedPullback.constantExtensionDatum D m hm).geometricFiber V₀).hom)
    (F : NativeL2.WeilModule D ell W₀)
    (G : NativeL2.WeilModule (NativeCondensedPullback.constantExtensionDatum D m hm) ell V₀)
    (hsource :
      compactHOne (NativeCondensedPullback.constantExtensionDatum D m hm) ell V₀ cV G =
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (PadicAlgCl ell)) 1).obj
          ((condensedQbarCompactSections ell D.k
            (precompCompactification cW j hj)).obj
            ((DerivedCategory.singleFunctor _ 0).obj G.carrier)))
    (eG : (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell) j).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj F.carrier) ≅
      (DerivedCategory.singleFunctor _ 0).obj G.carrier) :
    compactHOne (NativeCondensedPullback.constantExtensionDatum D m hm) ell V₀ cV G ⟶
      compactHOne D ell W₀ cW F := by
  exact eqToHom hsource ≫
    compactLocalizationMapRaw ell (_aX :=
      ((NativeCondensedPullback.constantExtensionDatum D m hm).geometricFiber V₀).hom)
      j hj cW F.carrier G.carrier eG

/-- The canonical comparison of the derived pullback of `F[0]` with `G[0]` for `G` the native
pullback of `F`.
Source: latest blueprint, sk-lem-wft-infinity-reduction, proof step 5
(blueprint: sk-lem-wft-infinity-reduction). -/
def pullbackCarrierTransport (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (m : ℕ) (hm : 1 ≤ m) (W₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom] [IsSeparated W₀.hom]
    (V₀ : Over (Spec (.of (D.extensionSubfield m hm))))
    [LocallyOfFiniteType V₀.hom] [QuasiCompact V₀.hom] [IsSeparated V₀.hom]
    (f₀ : Over.mk (V₀.hom ≫ Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) ⟶ W₀)
    (F : NativeL2.WeilModule D ell W₀)
    (G : NativeL2.WeilModule (NativeCondensedPullback.constantExtensionDatum D m hm) ell V₀)
    (hG : G = NativeCondensedPullback.object D m hm W₀ V₀ f₀ ell F) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
      (NativeCondensedPullback.geometricMap D m hm W₀ V₀ f₀)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj F.carrier) ≅
      (DerivedCategory.singleFunctor _ 0).obj G.carrier := by
  subst G
  exact ((CondensedRing.upperStar (Profinite.padicAlgClRingObj ell)
    (NativeCondensedPullback.geometricMap D m hm W₀ V₀ f₀)).mapDerivedCategorySingleFunctor 0).app
    F.carrier

/-- The projective line over `k_m`, as an object over `Spec k_m`.
Source: latest blueprint, sk-lem-wft-infinity-reduction, proof step 5
(blueprint: sk-lem-wft-infinity-reduction). -/
abbrev extensionProjectiveLineModel (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m) :
    Over (Spec (.of (D.extensionSubfield m hm))) :=
  Over.mk (ProjectiveLine (Spec (.of (D.extensionSubfield m hm))) ↘
    Spec (.of (D.extensionSubfield m hm)))

/-- The projective line over `k_m` is locally of finite type.
Source: latest blueprint, sk-lem-wft-infinity-reduction, proof step 5
(blueprint: sk-lem-wft-infinity-reduction). -/
instance extensionProjectiveLineModel_lft (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m) :
    LocallyOfFiniteType (extensionProjectiveLineModel D m hm).hom := by
  dsimp [extensionProjectiveLineModel]
  infer_instance

/-- The projective line over `k_m` is quasi-compact.
Source: latest blueprint, sk-lem-wft-infinity-reduction, proof step 5
(blueprint: sk-lem-wft-infinity-reduction). -/
instance extensionProjectiveLineModel_qc (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m) :
    QuasiCompact (extensionProjectiveLineModel D m hm).hom := by
  dsimp [extensionProjectiveLineModel]
  infer_instance

/-- The projective line over `k_m` is separated.
Source: latest blueprint, sk-lem-wft-infinity-reduction, proof step 5
(blueprint: sk-lem-wft-infinity-reduction). -/
instance extensionProjectiveLineModel_sep (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m) :
    IsSeparated (extensionProjectiveLineModel D m hm).hom := by
  dsimp [extensionProjectiveLineModel]
  infer_instance

end WeilConjectures

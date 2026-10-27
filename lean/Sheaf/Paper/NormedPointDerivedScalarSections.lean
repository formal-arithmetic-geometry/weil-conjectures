module

public import Sheaf.Topology.ContinuousMapCondensedRingMap
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected

import Sheaf.CategoryTheory.Monoidal.ModuleRestrictionFiniteExact
import Sheaf.CategoryTheory.RestrictedExtensionRelativeTensor
import Sheaf.ProperBaseChange.SingletonSiteModuleComparison
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedExactComparison
import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Normalized sections and scalar change at an algebraically closed normed point

Source: Hemo--Richarz--Scholbach, Section 3 and Lemma 4.1(1), with the ordinary
unbounded terminal-point coefficient-change argument in the DAG proof
(blueprint: lem-sfb-normed-point-derived-scalar-sections).

The auxiliary definitions specialize existing coefficient rings, scalar functors and
section reconstruction. Constant sections are fixed by the point-pullback adjunction;
ordinary comparisons are fixed on balanced generators, and derived comparisons are
fixed by their universal counits on every K-flat representative.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.ProEtale

/-- The existing continuous-map condensed ring, bundled with its canonical multiplication.
Source: HRS Example 3.1 (blueprint: lem-sfb-normed-point-derived-scalar-sections). -/
def normedScalarCondensed (F : Type u) [NormedField F] :
    CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) := by
  letI := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} F
  letI := Profinite.isCommMonObj_continuousMapRingObjOfUniverse.{u, u} F
  exact CommMon.mk (Profinite.continuousMapRingObjOfUniverse.{u, u} F)

/-- The ring F_X = p_X^* C(-,F), using the recorded coefficient pullback.
Source: HRS Section 3 (blueprint: lem-sfb-normed-point-derived-scalar-sections). -/
def normedScalarRing (X : Scheme.{u}) (F : Type u) [NormedField F] :
    CommMon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  (upperStarFromPoint X).mapCommMon.obj (normedScalarCondensed F)

/-- Internal modules over the actual pulled-back coefficient ring.
Source: HRS Section 3 (blueprint: lem-sfb-normed-point-derived-scalar-sections). -/
abbrev normedScalarModules (X : Scheme.{u}) (F : Type u) [NormedField F] :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (normedScalarRing X F).X

/-- Commutativity for the monoid projection used by scalar restriction and extension.
Source: HRS Section 3 (blueprint: lem-sfb-normed-point-derived-scalar-sections). -/
instance normedScalarRing_toMon_comm (X : Scheme.{u}) (F : Type u) [NormedField F] :
    IsCommMonObj (normedScalarRing X F).toMon.X :=
  (normedScalarRing X F).comm

/-- Postcomposition by the continuous field inclusion, followed by p_X^*.
Source: HRS Section 3 (blueprint: lem-sfb-normed-point-derived-scalar-sections). -/
def normedScalarMap (X : Scheme.{u}) {F G : Type u} [NormedField F] [NormedField G]
    (ι : F →+* G) (hι : Continuous ι) : normedScalarRing X F ⟶ normedScalarRing X G := by
  letI := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} F
  letI := Profinite.continuousMapRingObjOfUniverseMonObj.{u, u} G
  letI := Profinite.isCommMonObj_continuousMapRingObjOfUniverse.{u, u} F
  letI := Profinite.isCommMonObj_continuousMapRingObjOfUniverse.{u, u} G
  letI := Profinite.isMonHom_continuousMapRingObjMapOfUniverse.{u, u} ι hι
  exact (upperStarFromPoint X).mapCommMon.map
    (CommMon.homMk (Mon.Hom.mk' (Profinite.continuousMapRingObjMapOfUniverse ι hι)))

/-- The underlying ring-object map, with its endpoints made explicit.
Source: HRS Section 3 (blueprint: lem-sfb-normed-point-derived-scalar-sections). -/
def normedScalarHom (X : Scheme.{u}) {F G : Type u} [NormedField F] [NormedField G]
    (ι : F →+* G) (hι : Continuous ι) :
    (normedScalarRing X F).X ⟶ (normedScalarRing X G).X :=
  (normedScalarMap X ι hι).hom.hom

/-- The underlying coefficient morphism preserves the canonical ring operations.
Source: HRS Section 3 (blueprint: lem-sfb-normed-point-derived-scalar-sections). -/
instance normedScalarHom_isMonHom (X : Scheme.{u}) {F G : Type u}
    [NormedField F] [NormedField G] (ι : F →+* G) (hι : Continuous ι) :
    IsMonHom (normedScalarHom X ι hι) :=
  inferInstanceAs (IsMonHom (normedScalarMap X ι hι).hom.hom)

/-- The ordinary scalar adjunction, in the sections universe.
Source: HRS Section 3 (blueprint: lem-sfb-normed-point-derived-scalar-sections). -/
def normedScalarFieldAdjunction {F G : Type u} [NormedField F] [NormedField G]
    (ι : F →+* G) : ModuleCat.extendScalars.{u, u, u + 1} ι ⊣
      ModuleCat.restrictScalars.{u + 1} ι :=
  ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} ι

/-- The section ring at the terminal object, reconstructed from internal multiplication.
Source: HRS Section 3 (blueprint: lem-sfb-normed-point-derived-scalar-sections). -/
abbrev normedScalarSectionRing (X : Scheme.{u}) (F : Type u) [NormedField F] :=
  (InternalAbelianSheafModule.sectionRingSheaf (Scheme.ProEt.topology X)
    (normedScalarRing X F).X).obj.obj (op (Scheme.ProEt.mk (𝟙 X)))

/-- Terminal sections with the scalar action specified by a constant-section ring map.
Source: HRS Section 3 (blueprint: lem-sfb-normed-point-derived-scalar-sections). -/
def normedScalarSections (X : Scheme.{u}) (F : Type u) [NormedField F]
    (c : F →+* normedScalarSectionRing X F) :
    normedScalarModules X F ⥤ ModuleCat.{u + 1} F :=
  InternalAbelianSheafModule.sectionModuleFunctor (Scheme.ProEt.topology X)
      (normedScalarRing X F).X ⋙
    SheafOfModules.evaluation _ (op (Scheme.ProEt.mk (𝟙 X))) ⋙
    ModuleCat.restrictScalars c

/-- The map from a pro-etale object to the terminal object.
Source: HRS Section 3 (blueprint: lem-sfb-normed-point-derived-scalar-sections). -/
def normedScalarToTop (X : Scheme.{u}) (U : X.ProEt) :
    U ⟶ Scheme.ProEt.mk (𝟙 X) :=
  MorphismProperty.Over.homMk U.hom (Category.comp_id _)

/-- Constants are normalized by the unit of the actual point inverse-image adjunction.
The singleton test object is canonically isomorphic to the terminal object, so this
condition determines the constant-section identification uniquely.
Source: HRS Example 3.1 (blueprint: lem-sfb-normed-point-derived-scalar-sections). -/
def NormedScalarConstants (X : Scheme.{u}) (F : Type u) [NormedField F]
    (c : F ≃+* normedScalarSectionRing X F) : Prop :=
  ∀ r : F, (normedScalarRing X F).X.obj.map
      (normedScalarToTop X
        ((profiniteToProEtOf X).obj (Profinite.of PUnit.{u + 1}))).op (c r) =
    (((pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))).unit.app
        (normedScalarCondensed F).X).hom.app
          (op (Profinite.of PUnit.{u + 1})))
            (ULift.up (ContinuousMap.const _ r))

variable (X : Scheme.{u}) {F G : Type u} [NormedField F] [NormedField G]
  (ι : F →+* G) (hι : Continuous ι)
  (cF : F ≃+* normedScalarSectionRing X F)
  (cG : G ≃+* normedScalarSectionRing X G)

/-- K-flatness transported through the recorded equivalence to sectionwise modules.
Source: Stacks 06YS (blueprint: lem-sfb-normed-point-derived-scalar-sections). -/
def NormedScalarKFlat (P : CochainComplex (normedScalarModules X F) ℤ) : Prop :=
  CochainComplex.IsKFlatIndependentCoefficients
    (R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
      (normedScalarRing X F).X)
    (((InternalAbelianSheafModule.sectionModuleEquivalence (Scheme.ProEt.topology X)
      (normedScalarRing X F).X).functor.mapHomologicalComplex (.up ℤ)).obj P)

section Derived

variable [HasDerivedCategory.{u + 1} (normedScalarModules X F)]
  [HasDerivedCategory.{u + 1} (normedScalarModules X G)]
  [HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} F)]
  [HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} G)]
  [(normedScalarSections X F cF.toRingHom).Additive]
  [(normedScalarSections X G cG.toRingHom).Additive]
  [PreservesFiniteLimits (normedScalarSections X F cF.toRingHom)]
  [PreservesFiniteColimits (normedScalarSections X F cF.toRingHom)]
  [PreservesFiniteLimits (normedScalarSections X G cG.toRingHom)]
  [PreservesFiniteColimits (normedScalarSections X G cG.toRingHom)]
  [PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} ι)]
  [PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1} ι)]
  [(ModuleCat.extendScalars.{u, u, u + 1} ι).Additive]
  [PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1} ι)]
  [PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u + 1} ι)]

/-- The derived comparison is normalized on every K-flat representative by the localized
ordinary balanced map. Its restriction is precisely localization of the identity
restriction comparison; both derived units are pinned independently to their ordinary
insertion-of-one units. Naturality of the displayed isomorphism includes replacement
maps and every derived morphism. The mapped cochain isomorphism includes differentials.
Source: HRS Section 3 and Lemma 4.1(1); Stacks 06YT, 06YY, 07A6
(blueprint: lem-sfb-normed-point-derived-scalar-sections). -/
def NormedScalarDerivedComparison
    (r : Mod.comap (normedScalarHom X ι hι) ⋙
      normedScalarSections X F cF.toRingHom ≅
      normedScalarSections X G cG.toRingHom ⋙ ModuleCat.restrictScalars.{u + 1} ι)
    (b : normedScalarSections X F cF.toRingHom ⋙
      ModuleCat.extendScalars.{u, u, u + 1} ι ≅
      Mod.extendScalars (normedScalarHom X ι hι) ⋙
        normedScalarSections X G cG.toRingHom) : Prop :=
  (ModuleCat.extendScalars.{u, u, u + 1} ι).mapDerivedCategory.IsLeftDerivedFunctor
    (ModuleCat.extendScalars.{u, u, u + 1} ι).mapDerivedCategoryFactors.hom
    (HomologicalComplex.quasiIso (ModuleCat.{u + 1} F) (.up ℤ)) ∧
  ∃ (T : DerivedCategory (normedScalarModules X F) ⥤
        DerivedCategory (normedScalarModules X G))
    (ε : DerivedCategory.Q ⋙ T ⟶
      (Mod.extendScalars (normedScalarHom X ι hι)).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q),
  T.IsLeftDerivedFunctor ε
    (HomologicalComplex.quasiIso (normedScalarModules X F) (.up ℤ)) ∧
  (∀ P : CochainComplex (normedScalarModules X F) ℤ,
    NormedScalarKFlat X P → IsIso (ε.app P)) ∧
  ∃ d : (normedScalarSections X F cF.toRingHom).mapDerivedCategory ⋙
        (ModuleCat.extendScalars.{u, u, u + 1} ι).mapDerivedCategory ≅
      T ⋙ (normedScalarSections X G cG.toRingHom).mapDerivedCategory,
  (∀ P : CochainComplex (normedScalarModules X F) ℤ, NormedScalarKFlat X P →
    (ModuleCat.extendScalars.{u, u, u + 1} ι).mapDerivedCategory.map
        ((normedScalarSections X F cF.toRingHom).mapDerivedCategoryFactors.hom.app P) ≫
      (ModuleCat.extendScalars.{u, u, u + 1} ι).mapDerivedCategoryFactors.hom.app
        (((normedScalarSections X F cF.toRingHom).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex b (.up ℤ)).hom.app P) =
    d.hom.app (DerivedCategory.Q.obj P) ≫
      (normedScalarSections X G cG.toRingHom).mapDerivedCategory.map (ε.app P) ≫
      (normedScalarSections X G cG.toRingHom).mapDerivedCategoryFactors.hom.app
        (((Mod.extendScalars (normedScalarHom X ι hι)).mapHomologicalComplex
          (.up ℤ)).obj P)) ∧
  ∃ rd : (Mod.comap (normedScalarHom X ι hι)).mapDerivedCategory ⋙
        (normedScalarSections X F cF.toRingHom).mapDerivedCategory ≅
      (normedScalarSections X G cG.toRingHom).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u + 1} ι).mapDerivedCategory,
  rd = (Functor.mapDerivedCategoryCompIso
      (Mod.comap (normedScalarHom X ι hι))
      (normedScalarSections X F cF.toRingHom)).symm ≪≫
    Functor.mapDerivedCategoryNatIso r ≪≫
    Functor.mapDerivedCategoryCompIso (normedScalarSections X G cG.toRingHom)
      (ModuleCat.restrictScalars.{u + 1} ι) ∧
  ∃ (aS : T ⊣ (Mod.comap (normedScalarHom X ι hι)).mapDerivedCategory)
    (aM : (ModuleCat.extendScalars.{u, u, u + 1} ι).mapDerivedCategory ⊣
      (ModuleCat.restrictScalars.{u + 1} ι).mapDerivedCategory),
  (∀ P : CochainComplex (normedScalarModules X F) ℤ, NormedScalarKFlat X P →
    aS.unit.app (DerivedCategory.Q.obj P) ≫
      (Mod.comap (normedScalarHom X ι hι)).mapDerivedCategory.map (ε.app P) ≫
      (Mod.comap (normedScalarHom X ι hι)).mapDerivedCategoryFactors.hom.app
        (((Mod.extendScalars (normedScalarHom X ι hι)).mapHomologicalComplex
          (.up ℤ)).obj P) =
    DerivedCategory.Q.map
      (((Mod.extendRestrictAdjunction (normedScalarHom X ι hι)).mapHomologicalComplex
        (.up ℤ)).unit.app P)) ∧
  (∀ P : CochainComplex (ModuleCat.{u + 1} F) ℤ,
    aM.unit.app (DerivedCategory.Q.obj P) ≫
      (ModuleCat.restrictScalars.{u + 1} ι).mapDerivedCategory.map
        ((ModuleCat.extendScalars.{u, u, u + 1} ι).mapDerivedCategoryFactors.hom.app P) ≫
      (ModuleCat.restrictScalars.{u + 1} ι).mapDerivedCategoryFactors.hom.app
        (((ModuleCat.extendScalars.{u, u, u + 1} ι).mapHomologicalComplex (.up ℤ)).obj P) =
    DerivedCategory.Q.map
      (((normedScalarFieldAdjunction ι).mapHomologicalComplex
        (.up ℤ)).unit.app P)) ∧
  ∀ K : DerivedCategory (normedScalarModules X F),
    (normedScalarSections X F cF.toRingHom).mapDerivedCategory.map (aS.unit.app K) ≫
      rd.hom.app (T.obj K) =
    aM.unit.app ((normedScalarSections X F cF.toRingHom).mapDerivedCategory.obj K) ≫
      (ModuleCat.restrictScalars.{u + 1} ι).mapDerivedCategory.map (d.hom.app K)

end Derived

/-- Normalized terminal sections commute with ordinary and unbounded derived scalar
extension and restriction. No completeness, boundedness or sheaf-flatness is assumed.
Source: HRS Section 3 and Lemma 4.1(1)
(blueprint: lem-sfb-normed-point-derived-scalar-sections).

Proof:
1. Apply lem-sfb-normed-point-exact-monoidal at the identity geometric point. Its
constant-section maps identify the two terminal coefficient rings with F and G.
Postcomposition preserves constants, and restriction keeps every additive section.
The finite universal-property lemma lem-sfb-modobj-restriction-finite-exact gives
exact internal restriction.
2. Apply lem-sfb-restricted-extension-relative-tensor and the terminal tensorator.
The resulting balanced comparison sends a tensor m to the same sheaf tensor.
Balancing gives linearity, and the formula preserves insertion of one and all maps.
3. Field modules are flat (lem-weil-pbc-module-over-field-flat), so field extension
is exact by lem-weil-pbc-flat-tensor-exact. Exact termwise functors descend by
lem-weil-pbc-exact-functor-derived-factorization. Localizing the identity restriction
comparison gives exactly the recorded derived restriction comparison.
4. Use lem-sfb-internal-section-scalar-adjunction and
lem-pe-internal-section-tensor-comparison to pass to sectionwise module sheaves.
The universal counit of lem-pur-derived-change-of-rings is invertible on every
K-flat complex. Resolutions exist by lem-pc-kflat-resolution. On the field side,
lem-weil-pbc-singleton-site-module-comparison and def-sfb-left-derived-exact
identify derived extension with exact termwise field extension.
5. On K-flat complexes localize the degreewise balanced comparison and invert the
internal universal counit. Its naturality follows from those two natural maps.
Apply lem-sc-nattrans-from-resolving-class, using
lem-pc-quasi-isomorphisms-multiplicative-system and K-flat resolutions, then descend
by lem-weil-pbc-localization-universal-property. Resolution maps are inverted, so
all descended components are invertible.
6. The representative square is the defining square for that descent. Chain maps
commute with differentials, with no sign from the degree-zero scalar. Naturality
also gives compatibility with replacement maps, their inverses and all roofs.
7. By lem-pur-sheaf-ring-derived-coefficient-adjunction the derived units on K-flat
representatives are the localized insertion-of-one units. The balanced comparison
preserves those generators by step 2. Transport across a flat-term K-flat resolution
proves the final unit square for every unbounded derived object. No flatness of the
internal coefficient map was used. -/
theorem normed_point_derived_scalar_sections
    (k : Type u) [Field k] [IsAlgClosed k]
    (F G : Type u) [NormedField F] [NormedField G]
    [TotallyDisconnectedSpace F] [TotallyDisconnectedSpace G]
    (ι : F →+* G) (hι : Continuous ι) :
    ∃ (cF : F ≃+* normedScalarSectionRing (Spec (.of k)) F)
      (cG : G ≃+* normedScalarSectionRing (Spec (.of k)) G),
    NormedScalarConstants (Spec (.of k)) F cF ∧
    NormedScalarConstants (Spec (.of k)) G cG ∧
    ∃ (_ : HasDerivedCategory.{u + 1} (normedScalarModules (Spec (.of k)) F))
      (_ : HasDerivedCategory.{u + 1} (normedScalarModules (Spec (.of k)) G))
      (_ : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} F))
      (_ : HasDerivedCategory.{u + 1} (ModuleCat.{u + 1} G))
      (_ : (normedScalarSections (Spec (.of k)) F cF.toRingHom).Additive)
      (_ : (normedScalarSections (Spec (.of k)) G cG.toRingHom).Additive)
      (_ : PreservesFiniteLimits (normedScalarSections (Spec (.of k)) F cF.toRingHom))
      (_ : PreservesFiniteColimits (normedScalarSections (Spec (.of k)) F cF.toRingHom))
      (_ : PreservesFiniteLimits (normedScalarSections (Spec (.of k)) G cG.toRingHom))
      (_ : PreservesFiniteColimits (normedScalarSections (Spec (.of k)) G cG.toRingHom))
      (_ : (ModuleCat.extendScalars.{u, u, u + 1} ι).Additive)
      (_ : PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1} ι))
      (_ : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u + 1} ι))
      (_ : PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1} ι))
      (_ : PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1} ι)),
    exactFunctor (normedScalarModules (Spec (.of k)) G)
      (normedScalarModules (Spec (.of k)) F)
      (Mod.comap (normedScalarHom (Spec (.of k)) ι hι)) ∧
    ∃ r : Mod.comap (normedScalarHom (Spec (.of k)) ι hι) ⋙
        normedScalarSections (Spec (.of k)) F cF.toRingHom ≅
      normedScalarSections (Spec (.of k)) G cG.toRingHom ⋙
        ModuleCat.restrictScalars.{u + 1} ι,
    (∀ (N : normedScalarModules (Spec (.of k)) G)
      (x : N.X.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))),
      (r.hom.app N) x = x) ∧
    ∃ b : normedScalarSections (Spec (.of k)) F cF.toRingHom ⋙
        ModuleCat.extendScalars.{u, u, u + 1} ι ≅
      Mod.extendScalars (normedScalarHom (Spec (.of k)) ι hι) ⋙
        normedScalarSections (Spec (.of k)) G cG.toRingHom,
    (∀ (M : normedScalarModules (Spec (.of k)) F) (a : G)
      (m : M.X.obj.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))),
      (b.hom.app M) (a ⊗ₜ[F, ι] m) =
        InternalAbelianSheafModule.internalScalarGenerator
          (Scheme.ProEt.topology (Spec (.of k)))
          (normedScalarHom (Spec (.of k)) ι hι) M
          (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) (cG a) m) ∧
    (∀ M : normedScalarModules (Spec (.of k)) F,
      (normedScalarSections (Spec (.of k)) F cF.toRingHom).map
          ((Mod.extendRestrictAdjunction
            (normedScalarHom (Spec (.of k)) ι hι)).unit.app M) ≫
        r.hom.app ((Mod.extendScalars (normedScalarHom (Spec (.of k)) ι hι)).obj M) =
      (normedScalarFieldAdjunction ι).unit.app
          ((normedScalarSections (Spec (.of k)) F cF.toRingHom).obj M) ≫
        (ModuleCat.restrictScalars.{u + 1} ι).map (b.hom.app M)) ∧
    NormedScalarDerivedComparison (Spec (.of k)) ι hι cF cG r b := by
  sorry

end AlgebraicGeometry.ProEtale

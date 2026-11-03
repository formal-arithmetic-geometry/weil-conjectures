/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleObjects
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingMap
import WeilConjectures.FromJoel.Algebra.Homology.HomologicalComplexFunctorEquiv
public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompExact
import WeilConjectures.Algebra.Homology.RoosCoordinatesQuasiIso
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import all WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement

/-!
# Finite free scalar comparison for pulled-back condensed integral coefficients

Source: latest blueprint, cartesian-coefficients-finite-free proof and
scalar-six-ctf proof (2); Stacks Tag 0941; Bhatt--Scholze, Definition 3.4.10
and Proposition 3.5.1 (blueprint: lem-weil-finite-free-completed-scalar-comparison).

All modules below are internal modules over the pulled-back continuous condensed ring.
The comparison is the localization of the recorded signed Roos augmentation on K-flat
complexes. The quotient tower and its recorded internal derived inverse limit are
identified below. Positive exponent m is indexed by n=m-1.
An algebra embedding encodes the specified inclusion of finite p-adic fields; it imposes
no normality or ramification restriction. All coefficient fields and schemes lie in the
chosen coefficient universe; universe lifting represents any smaller field there.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CurrentScalarCompletion

variable (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
  [Algebra (Padic l) E] [Algebra (Padic l) F]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]

private theorem absoluteValue_map (i : E →ₐ[Padic l] F) (x : E) :
    Padic.coefficientExtensionAbsoluteValue l F (i x) =
      Padic.coefficientExtensionAbsoluteValue l E x := by
  change spectralNorm (Padic l) F (i x) = spectralNorm (Padic l) E x
  unfold spectralNorm
  rw [minpoly.algHom_eq i i.injective]

/-- The given embedding preserves the valuation rings.
Source: compatibility of spectral absolute values, node proof step 1
(blueprint: lem-weil-finite-free-completed-scalar-comparison).
Proof: the minimal polynomial, hence the spectral absolute value, is unchanged by an
injective p-adic algebra map. Membership in each recorded integer ring means value at
most one, so an integral element remains integral. -/
theorem integersMap_mem (i : E →ₐ[Padic l] F)
    (x : Padic.coefficientExtensionIntegers l E) :
    i (x : E) ∈ Padic.coefficientExtensionIntegers l F := by
  have hE := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec.1
  have hF := (Padic.extension_integers_dvr l F
    (Padic.coefficientExtensionAbsoluteValue l F)
    (spectralNorm_extends (K := Padic l) (L := F))).choose_spec.choose_spec.1
  apply (hF _).mpr
  rw [absoluteValue_map l E F i]
  exact (hE _).mp x.property

/-- Restrict the given field embedding to its actual valuation rings.
Source: node proof step 1, continuous integral inclusion
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
def integersMap (i : E →ₐ[Padic l] F) :
    Padic.coefficientExtensionIntegers l E →+* Padic.coefficientExtensionIntegers l F :=
  ((i.toRingHom.comp (Padic.coefficientExtensionIntegers l E).subtype).codRestrict
    (Padic.coefficientExtensionIntegers l F) (integersMap_mem l E F i))

/-- Continuity for the spectral subspace topologies of the two integer rings.
Source: node proof step 1, continuous integral basis paragraph
(blueprint: lem-weil-finite-free-completed-scalar-comparison).
Proof: equality of the spectral absolute values makes the field embedding an isometry.
Restrict this continuous embedding to the valuation subrings with their subspace topologies. -/
theorem integersMap_continuous (i : E →ₐ[Padic l] F) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    letI := (Padic.coefficientExtensionAbsoluteValue l F).toNormedField
    Continuous (integersMap l E F i) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let := (Padic.coefficientExtensionAbsoluteValue l F).toNormedField
  have hi : Isometry i := AddMonoidHomClass.isometry_of_norm i
    (absoluteValue_map l E F i)
  exact (hi.continuous.comp continuous_subtype_val).subtype_mk _

/-- Continuous postcomposition by the integer-ring inclusion, as a ring-sheaf map.
Source: node statement, the continuous inclusion
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
def pointRingSheafMap (i : E →ₐ[Padic l] F) :
    DerivedNakayama.integerRingSheaf l E ⟶ DerivedNakayama.integerRingSheaf l F :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  letI := (Padic.coefficientExtensionAbsoluteValue l F).toNormedField
  ⟨(Profinite.continuousMapRingSheafMapOfUniverse.{u, u}
    (integersMap l E F i) (integersMap_continuous l E F i)).hom⟩

/-- The coefficient inclusion on the point, with the inherited internal ring structure.
Source: node statement, condensed coefficient morphism
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
abbrev pointMap (i : E →ₐ[Padic l] F) :
    DerivedNakayama.integerRing l E ⟶ DerivedNakayama.integerRing l F :=
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (pointRingSheafMap l E F i)

/-- The specified ring-object morphism p_Y^* O_E to p_Y^* O_F.
Source: node statement, phi
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
abbrev ringMap (i : E →ₐ[Padic l] F) (Y : Scheme.{u}) :
    AdicCompletion.ring l E Y ⟶ AdicCompletion.ring l F Y :=
  (upperStarFromPoint Y).map (pointMap l E F i)

/-- Ordinary derived extension along the specified inclusion.
Source: node statement, TK=S tensor_R^L K
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
abbrev extension (i : E →ₐ[Padic l] F) (Y : Scheme.{u}) :=
  (Mod.extendScalars (ringMap l E F i Y)).leftDerivedFunctor

/-- The strict ordinary scalar extension used to compute the derived functor on K-flat P.
Source: node statement, K-flat representative
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
abbrev complexExtension (i : E →ₐ[Padic l] F) (Y : Scheme.{u}) :=
  (Mod.extendScalars (ringMap l E F i Y)).mapHomologicalComplex (.up ℤ)

/-- The existing K-flat computation counit, without choosing a resolution.
Source: derived extension convention and node statement
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
def computation (i : E →ₐ[Padic l] F) (Y : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    (extension l E F i Y).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((complexExtension l E F i Y).obj P) :=
  (Mod.extendScalars (ringMap l E F i Y)).leftDerivedFunctorCounit.app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)

/-- Localization from the existing category of K-flat internal complexes.
Source: node statement, representative independence
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
abbrev flatLocalization (Y : Scheme.{u}) :=
  CochainComplex.ιKFlat (AdicCompletion.Modules l E Y) ⋙ DerivedCategory.Q

/-- Functoriality of the recorded Roos map on identity chain maps.
Source: node statement, naturality of chi
(blueprint: lem-weil-finite-free-completed-scalar-comparison).
Proof: every level tensor map preserves identities; the product and biproduct maps
therefore have identity coordinates, and localization preserves identity. -/
theorem flatRoos_map_id (i : E →ₐ[Padic l] F) (Y : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E Y) ℤ) :
    DerivedCategory.Q.map (AdicCompletion.roosMap l F Y
      ((complexExtension l E F i Y).map (𝟙 P))) = 𝟙 _ := by
  rw [CategoryTheory.Functor.map_id]
  have h : AdicCompletion.roosMap l F Y
      (𝟙 ((complexExtension l E F i Y).obj P)) = 𝟙 _ := by
    ext j : 1
    simp only [AdicCompletion.roosMap, CochainComplex.ofHom,
      AdicCompletion.productMap, CategoryTheory.Functor.map_id, Limits.Pi.map_id,
      HomologicalComplex.id_f]
    change biprod.map (𝟙 _) (𝟙 _) = 𝟙 (_ ⊞ _)
    apply biprod.hom_ext <;> simp
  rw [h, CategoryTheory.Functor.map_id]

/-- Functoriality of the recorded Roos map on composites of chain maps.
Source: node statement, naturality of chi
(blueprint: lem-weil-finite-free-completed-scalar-comparison).
Proof: every level tensor functor preserves composition; products and biproducts
compose coordinatewise, and localization preserves the resulting composite. -/
theorem flatRoos_map_comp (i : E →ₐ[Padic l] F) (Y : Scheme.{u})
    {P Q U : CochainComplex (AdicCompletion.Modules l E Y) ℤ}
    (a : P ⟶ Q) (b : Q ⟶ U) :
    DerivedCategory.Q.map (AdicCompletion.roosMap l F Y
        ((complexExtension l E F i Y).map (a ≫ b))) =
      DerivedCategory.Q.map (AdicCompletion.roosMap l F Y
        ((complexExtension l E F i Y).map a)) ≫
      DerivedCategory.Q.map (AdicCompletion.roosMap l F Y
        ((complexExtension l E F i Y).map b)) := by
  rw [Functor.map_comp]
  have h : AdicCompletion.roosMap l F Y
      ((complexExtension l E F i Y).map a ≫ (complexExtension l E F i Y).map b) =
      AdicCompletion.roosMap l F Y ((complexExtension l E F i Y).map a) ≫
        AdicCompletion.roosMap l F Y ((complexExtension l E F i Y).map b) := by
    ext j : 1
    simp only [AdicCompletion.roosMap, CochainComplex.ofHom,
      AdicCompletion.productMap, Functor.map_comp, ← Limits.Pi.map_comp_map,
      HomologicalComplex.comp_f]
    apply biprod.hom_ext <;> simp [Category.assoc]
  rw [h, Functor.map_comp]

/-- The actual signed Roos model after ordinary scalar extension, functorially on
K-flat complexes. The map of the recorded definition is reused unchanged.
Source: node statement, signed Roos representative
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
def flatRoos (i : E →ₐ[Padic l] F) (Y : Scheme.{u}) :
    CochainComplex.KFlat (AdicCompletion.Modules l E Y) ⥤
      DerivedCategory (AdicCompletion.Modules l F Y) where
  obj P := DerivedCategory.Q.obj
    (AdicCompletion.roos l F Y ((complexExtension l E F i Y).obj P.obj))
  map a := DerivedCategory.Q.map
    (AdicCompletion.roosMap l F Y ((complexExtension l E F i Y).map a.hom))
  map_id P := flatRoos_map_id l E F i Y P.obj
  map_comp a b := flatRoos_map_comp l E F i Y a.hom b.hom

section
variable {C : Type v} [Category.{w} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{w} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]
open MonObj
open scoped CategoryTheory.Obj
end

/-- K-flat quasi-isomorphisms are inverted by the actual Roos construction.
Source: node proof steps 2--3, exact products and K-flat quotient tensors
(blueprint: lem-weil-finite-free-completed-scalar-comparison).
Proof: scalar extension preserves K-flat complexes and their quasi-isomorphisms.
Tensoring with each quotient preserves these quasi-isomorphisms. Exact countable
products preserve them, and the signed Roos cone does too by its cone triangle. -/
theorem flatRoos_inverts (i : E →ₐ[Padic l] F) (Y : Scheme.{u}) :
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E Y) (.up ℤ)).WKFlat.IsInvertedBy
      (flatRoos l E F i Y) := by
  intro P Q a ha
  have : QuasiIso a.hom := ha
  let U := (complexExtension l E F i Y).obj P.obj
  let V := (complexExtension l E F i Y).obj Q.obj
  let c : U ⟶ V := (complexExtension l E F i Y).map a.hom
  let : CountableAB4Star (AdicCompletion.Modules l F Y) :=
    CountableAB4Star.of_epi_π_app_zero
    (Mod.epiπAppZeroOfEpi Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  have hlevel (n : ℕ) : QuasiIso ((AdicCompletion.level l F Y n).map c) := by
    let q := AdicCompletion.quotient l F Y n
    let B := AdicCompletion.finiteModule l F Y n
    let eB : B ≅ (Mod.comap q).obj (Mod.regular (AdicCompletion.finiteRing l F Y n)) :=
      (Functor.mapModComapIso (upperStarFromPoint Y)
        (DerivedNakayama.reductionRing l F (n + 1))).app
          (Mod.regular (DerivedNakayama.quotientRing l F (n + 1)))
    let e : Mod.extendScalars (ringMap l E F i Y) ⋙ tensorRight B ≅
        Mod.extendScalars (ringMap l E F i Y ≫ q) ⋙ Mod.comap q :=
      Functor.isoWhiskerLeft _
        ((BraidedCategory.tensorLeftIsoTensorRight B).symm ≪≫
          (tensoringLeft (AdicCompletion.Modules l F Y)).mapIso eB ≪≫
          (extendTensorNatIso (C := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) q).symm) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Mod.extendScalarsComp (ringMap l E F i Y) q).symm _
    have h := (Mod.extendScalars (ringMap l E F i Y ≫ q) ⋙ Mod.comap q)
      |>.quasiIso_mapHomologicalComplex_map_of_kFlat P.property Q.property a.hom
    let ee := NatIso.mapHomologicalComplex e (.up ℤ)
    have he := ee.hom.naturality a.hom
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (ee.app P.obj) (ee.app Q.obj) he.symm)).mpr h
  let f := Discrete.natTrans
    (F := Discrete.functor (fun n : ℕ ↦ (AdicCompletion.level l F Y n).obj U))
    (G := Discrete.functor (fun n : ℕ ↦ (AdicCompletion.level l F Y n).obj V))
    (fun n ↦ (AdicCompletion.level l F Y n.as).map c)
  have (n : Discrete ℕ) : QuasiIso (f.app n) := hlevel n.as
  have hp : QuasiIso (AdicCompletion.productMap l F Y c) :=
    HomologicalComplex.quasiIso_limMap f
  have hr : QuasiIso (AdicCompletion.roosMap l F Y c) :=
    CochainComplex.quasiIso_of_roos_coordinates
      (AdicCompletion.product l F Y U) (AdicCompletion.product l F Y V)
      (AdicCompletion.roos l F Y U) (AdicCompletion.roos l F Y V)
      (AdicCompletion.oneSubShift l F Y U) (AdicCompletion.oneSubShift l F Y V)
      (fun _ ↦ Iso.refl _) (fun _ ↦ Iso.refl _)
      (by intro j; simp only [Iso.refl_hom, Category.comp_id, Category.id_comp,
        AdicCompletion.roos, CochainComplex.of_d, AdicCompletion.roosD])
      (by intro j; simp only [Iso.refl_hom, Category.comp_id, Category.id_comp,
        AdicCompletion.roos, CochainComplex.of_d, AdicCompletion.roosD])
      (AdicCompletion.productMap l F Y c) (AdicCompletion.roosMap l F Y c)
      (fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm) hp
  exact DerivedCategory.isIso_Q_map_iff_quasiIso _ _ |>.mpr hr

/-- The quotient-completed scalar extension is the localization of the fixed signed
Roos construction. No object is chosen from an existence theorem.
Source: node statement and proof step 3, descent of the whole comparison
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
def quotientCompleted (i : E →ₐ[Padic l] F) (Y : Scheme.{u}) :=
  Localization.lift (flatRoos l E F i Y) (flatRoos_inverts l E F i Y)
    (flatLocalization l E Y)

/-- The canonical factorization isomorphism supplied by localization itself.
Source: node statement, independence of the K-flat representative
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
def roosComparison (i : E →ₐ[Padic l] F) (Y : Scheme.{u}) :=
  Localization.fac (flatRoos l E F i Y) (flatRoos_inverts l E F i Y)
    (flatLocalization l E Y)

private theorem roos_augmentation_naturality (X : Scheme.{u})
    {P P' : CochainComplex (AdicCompletion.Modules l E X) ℤ}
    (a : P ⟶ P') :
    AdicCompletion.augmentation l E X P ≫ AdicCompletion.roosMap l E X a =
      a ≫ AdicCompletion.augmentation l E X P' := by
  ext i : 1
  change biprod.lift ((AdicCompletion.unitProduct l E X P).f i) 0 ≫
    biprod.map ((AdicCompletion.productMap l E X a).f i)
      ((AdicCompletion.productMap l E X a).f (i - 1)) =
      a.f i ≫ biprod.lift ((AdicCompletion.unitProduct l E X P').f i) 0
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst]
    have h : AdicCompletion.unitProduct l E X P ≫ AdicCompletion.productMap l E X a =
        a ≫ AdicCompletion.unitProduct l E X P' := by
      apply Pi.hom_ext
      intro n
      simp only [AdicCompletion.unitProduct, AdicCompletion.productMap, Category.assoc,
        Pi.map_π, Pi.lift_π_assoc, Pi.lift_π]
      exact ((NatTrans.mapHomologicalComplex
        ((rightUnitorNatIso (AdicCompletion.Modules l E X)).inv ≫
          (tensoringRight (AdicCompletion.Modules l E X)).map
            (AdicCompletion.finiteUnit l E X n)) (.up ℤ)).naturality a).symm
    exact congrArg (fun f ↦ f.f i) h
  · simp


/-- The whole Roos augmentation is natural after the scalar computation counit.
Source: node statement and proof step 3
(blueprint: lem-weil-finite-free-completed-scalar-comparison).
Proof: the derived scalar counit is natural, and the tensor units commute with
scalar extension on chain maps. The product maps preserve both coordinates, so the
zero shifted coordinate remains zero; compose these two naturality squares. -/
theorem flatAugmentation_naturality (i : E →ₐ[Padic l] F) (Y : Scheme.{u})
    (P Q : CochainComplex.KFlat (AdicCompletion.Modules l E Y)) (a : P ⟶ Q) :
    (flatLocalization l E Y ⋙ extension l E F i Y).map a ≫
        (computation l E F i Y Q.obj ≫ DerivedCategory.Q.map
          (AdicCompletion.augmentation l F Y ((complexExtension l E F i Y).obj Q.obj))) =
      (computation l E F i Y P.obj ≫ DerivedCategory.Q.map
        (AdicCompletion.augmentation l F Y ((complexExtension l E F i Y).obj P.obj))) ≫
          (flatRoos l E F i Y).map a := by
  have hc := (Mod.extendScalars (ringMap l E F i Y)).leftDerivedFunctorCounit.naturality
    ((HomotopyCategory.quotient _ (.up ℤ)).map a.hom)
  change (extension l E F i Y).map (DerivedCategory.Q.map a.hom) ≫
      computation l E F i Y Q.obj = computation l E F i Y P.obj ≫
        DerivedCategory.Q.map ((complexExtension l E F i Y).map a.hom) at hc
  change (extension l E F i Y).map (DerivedCategory.Q.map a.hom) ≫ _ = _
  rw [← Category.assoc, hc, Category.assoc, ← Functor.map_comp,
    ← roos_augmentation_naturality l F Y, Functor.map_comp]
  exact (Category.assoc _ _ _).symm

/-- The strict zero-shifted-coordinate comparison on all K-flat representatives.
Source: node statement, the canonical quotient scalar maps
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
def flatAugmentation (i : E →ₐ[Padic l] F) (Y : Scheme.{u}) :
    flatLocalization l E Y ⋙ extension l E F i Y ⟶ flatRoos l E F i Y where
  app P := computation l E F i Y P.obj ≫ DerivedCategory.Q.map
    (AdicCompletion.augmentation l F Y ((complexExtension l E F i Y).obj P.obj))
  naturality := flatAugmentation_naturality l E F i Y

/-- The actual comparison on the derived category, obtained by the fully faithful
localization bijection on natural transformations applied to the entire augmentation.
Source: node statement and proof step 3, quotient scalar descent
(blueprint: lem-weil-finite-free-completed-scalar-comparison). -/
def comparison (i : E →ₐ[Padic l] F) (Y : Scheme.{u}) :
    extension l E F i Y ⟶ quotientCompleted l E F i Y :=
  (Localization.fullyFaithfulWhiskeringLeft (flatLocalization l E Y)
    (HomologicalComplex.quasiIso (AdicCompletion.Modules l E Y) (.up ℤ)).WKFlat
    (DerivedCategory (AdicCompletion.Modules l F Y))).preimage
      (flatAugmentation l E F i Y ≫ (roosComparison l E F i Y).inv)

namespace CompletionLimitHelpers

open AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace Test

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y : Scheme.{u})
end Test
namespace Test

end Test

namespace Test
variable (Y : AlgebraicGeometry.Scheme.{u})
  (Λ : CommMon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
  [HasDerivedCategory (CondensedInverseLimit.strictTowers Y Λ)]
end Test

namespace Test
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y : Scheme.{u})
set_option maxHeartbeats 1600000 in
-- The internal-module tower and the two derived-limit realizations have large elaborated types.
end Test

end CompletionLimitHelpers

end WeilConjectures.CurrentScalarCompletion

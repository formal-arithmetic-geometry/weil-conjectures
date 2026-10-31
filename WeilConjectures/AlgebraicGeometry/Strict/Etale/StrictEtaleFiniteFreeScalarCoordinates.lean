/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleCoefficientTransportInterfaces
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.CategoryTheory.ToposFiniteFreeCompact.ToposFiniteFreeCompactConstituents
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleFiniteFreeScalarExact
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckCoefficientUniverse
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.ShrinkYoneda
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Coordinates for the specified finite-free scalar functor

Source: Zheng, Construction 4.1; Stacks, Tags 03CZ and 07A6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option genSizeOf false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
open scoped ChangeOfRings
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

private abbrev coordinateSite (T : Scheme.{u}) :
    CategoryTheory.ToposFiniteFreeCompact.Site.{u + 1, u, u + 1} where
  C := T.Etale
  J := T.smallEtaleTopology

section Identity
universe a v r w
open CategoryTheory.ToposFiniteFreeCompact
variable {A B : CommRingCat.{r}} [Algebra A B]

private abbrev coordinateIdentityLift (T : Site.{a, v, r}) (R : CommRingCat.{r}) :
    AlgebraicInverseImage (𝟭 (Sheaf T.J (Type r)))
      (CategoryTheory.RingedCoefficientCounit.constantRing T.J R)
      (CategoryTheory.RingedCoefficientCounit.constantRing T.J R) where
  ringUnderlying := Iso.refl _
  ringAdd := fun _ _ _ _ h ↦ h
  ringMul := fun _ _ _ _ h ↦ h
  ringZero := fun _ _ h ↦ h
  ringOne := fun _ _ h ↦ h
  modules := 𝟭 _
  moduleUnderlying := Iso.refl _
  moduleAdd := fun _ _ _ _ _ h ↦ h
  moduleZero := fun _ _ _ h ↦ h
  moduleSMul := fun _ _ _ _ _ h ↦ h

private abbrev coordinateIdentityGeometric (T : ScalarSite.{a, v, r, w} A B) :
    Geometric T T where
  inverse := 𝟭 _
  direct := 𝟭 _
  geom := Adjunction.id
  leftExact := inferInstance
  liftA := coordinateIdentityLift T.toSite A
  liftB := coordinateIdentityLift T.toSite B
  point := Iso.refl _
  constantsA := by intro a; simp
  constantsB := by intro b; simp
  limA := inferInstanceAs (PreservesFiniteLimits (𝟭 _))
  colimA := inferInstanceAs (PreservesFiniteColimits (𝟭 _))
  limB := inferInstanceAs (PreservesFiniteLimits (𝟭 _))
  colimB := inferInstanceAs (PreservesFiniteColimits (𝟭 _))
  pushA := 𝟭 _
  pushB := 𝟭 _
  pushUnderlyingA := Iso.refl _
  pushUnderlyingB := Iso.refl _
  adjA := Adjunction.id
  adjB := Adjunction.id
  homA := by intros; rfl
  homB := by intros; rfl
  restriction := Iso.refl _
  restrictionFormula := by
    intros
    simp only [coordinateIdentityLift, Iso.refl_hom]
    rfl

private abbrev coordinateIdentityOpen (T : ScalarSite.{a, v, r, w} A B) : Open T T where
  geometric := coordinateIdentityGeometric T
  subterminal := ⊤_ (Sheaf T.J (Type r))
  isSubterminal := isSubterminal_of_terminal
  slice := (Over.equivalenceOfIsTerminal terminalIsTerminal).symm
  inverseIso :=
    (Functor.leftUnitor _).trans
      (conjugateIsoEquiv
        (Over.equivalenceOfIsTerminal terminalIsTerminal).toAdjunction
        (Over.forgetAdjStar (⊤_ (Sheaf T.J (Type r)))) (Iso.refl _))
  extensionA := 𝟭 _
  extensionB := 𝟭 _
  adjA := Adjunction.id
  adjB := Adjunction.id


private abbrev coordinateScalarSite (T : Site.{a, v, r})
    [hA : HasDerivedCategory.{w} (Mod T A)] [hB : HasDerivedCategory.{w} (Mod T B)]
    [hIA : Abelian.HasKInjectiveResolutions (Mod T A)]
    [hIB : Abelian.HasKInjectiveResolutions (Mod T B)]
    (D : DerivedChangeOfRingsCochainModel.{a, v, r, w, w} (coefficientMap A B T)) :
    ScalarSite.{a, v, r, w} A B :=
  let h := sheafRingCoefficientOrdinaryAdjunction (coefficientMap A B T)
  let hAdj := h.choose_spec.choose_spec D.E D.obj_eq D.map_eq
  { toSite := T
    derivedA := hA
    derivedB := hB
    injectivesA := hIA
    injectivesB := hIB
    model := D
    resLimits := h.choose
    resColimits := h.choose_spec.choose
    adj := hAdj.choose
    adjFormula := hAdj.choose_spec }

end Identity

/-- The coordinate inclusions of restricted scalar extension.
Source: Stacks, Tag 03CZ
(blueprint: lem-pur-strict-etale-finite-free-scalar-coordinates). -/
abbrev StrictEtaleLevelScalarInclusions
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index} {T : Scheme.{u}} {n : ℕ}
    (L : StrictEtaleLevelScalar a T n) (r : ℕ) :=
  ∀ M : DerivedCategory (strictEtaleLevel T O ell (index n)),
    Fin r → (M ⟶ L.restriction.obj (L.derived.obj M))

/-- Naturality, the two finite-matrix identities, and the pure-tensor normalization
on all cochain representatives. The displayed normalization uses the prescribed
scalar counit and restriction factors, so it applies to any supplied universal pair.
Source: Stacks, Tags 03CZ and 07A6
(blueprint: lem-pur-strict-etale-finite-free-scalar-coordinates). -/
def StrictEtaleLevelBasisCoordinates
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index} {T : Scheme.{u}} {n : ℕ}
    (L : StrictEtaleLevelScalar a T n) {r : ℕ}
    (b : Module.Basis (Fin r) (O ⧸ Ideal.span {ell} ^ (index n + 1))
      ((ModuleCat.restrictScalars (a.ring n)).obj
        (ModuleCat.of (O' ⧸ Ideal.span {mu} ^ (n + 1))
          (O' ⧸ Ideal.span {mu} ^ (n + 1)))))
    (ι : StrictEtaleLevelScalarInclusions L r) : Prop :=
  (∀ M N (f : M ⟶ N) i,
    f ≫ ι N i = ι M i ≫ L.restriction.map (L.derived.map f)) ∧
  (∀ M, ∃ q : Fin r → (L.restriction.obj (L.derived.obj M) ⟶ M),
    (∀ i j, ι M i ≫ q j = if i = j then 𝟙 M else 0) ∧
      ∑ i, q i ≫ ι M i = 𝟙 _) ∧
  ∀ (P : CochainComplex (strictEtaleLevel T O ell (index n)) ℤ) i,
    ∃ k : P ⟶ ((SheafOfModules.restrictScalars.{u + 1}
        ((sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T n))).mapHomologicalComplex
          (.up ℤ)).obj
      (((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).mapHomologicalComplex
        (.up ℤ)).obj P),
      (∀ (d : ℤ) (V : T.Etaleᵒᵖ) (x : (P.X d).val.obj V),
        (k.f d).val.app V x =
          (toSheafify T.smallEtaleTopology
            (changeOfRingsPresheaf.{u, u + 1, u + 1}
              (a.sheaf T n) (P.X d)).presheaf).app V
            (((toSheafify T.smallEtaleTopology
                ((Functor.const T.Etaleᵒᵖ).obj
                  (CommRingCat.of (O' ⧸ Ideal.span {mu} ^ (n + 1))))).app V (b i))
              ⊗ₜ[(coefficientQuotientSheaf (J := T.smallEtaleTopology)
                O ell (index n)).obj.obj V, ((a.sheaf T n).hom.app V).hom] x)) ∧
      ι (DerivedCategory.Q.obj P) i ≫ L.restriction.map (L.counit.app P) ≫
        L.restrictionFactors.hom.app
          (((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)).mapHomologicalComplex
        (.up ℤ)).obj P) = DerivedCategory.Q.map k

/-- A finite quotient-ring basis supplies normalized coordinates on the prescribed
unbounded derived scalar extension.
Source: Zheng, Construction 4.1; Stacks, Tags 03CZ and 07A6
(blueprint: lem-pur-strict-etale-finite-free-scalar-coordinates).
Proof: sheafify the finite-basis isomorphism between the constant B-module and a
finite power of the constant A-module. Tensor with each module sheaf. The inclusion
sends x to b_i tensor x and the projection sends b tensor x to its ith basis
coordinate times x. Basis expansion and the Kronecker identities give both matrix
identities, including the empty basis. The formulas commute with restrictions,
module maps and cochain differentials. Exactness of finite-free scalar extension
makes its universal derived counit invertible on every complex. Localize these
natural maps and conjugate by that counit and the supplied exact restriction
factors. Faithful whiskering by localization proves naturality and both matrix
identities on all derived objects, with precisely the representative equation
recorded in StrictEtaleLevelBasisCoordinates. -/
theorem strictEtaleFiniteFreeScalarCoordinates
    {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    (a : StrictEtaleCoefficientChange O O' ell mu phi index)
    (T : Scheme.{u}) (n : ℕ) (L : StrictEtaleLevelScalar a T n) {r : ℕ}
    (b : Module.Basis (Fin r) (O ⧸ Ideal.span {ell} ^ (index n + 1))
      ((ModuleCat.restrictScalars (a.ring n)).obj
        (ModuleCat.of (O' ⧸ Ideal.span {mu} ^ (n + 1))
          (O' ⧸ Ideal.span {mu} ^ (n + 1))))) :
    ∃ ι : StrictEtaleLevelScalarInclusions L r, StrictEtaleLevelBasisCoordinates L b ι := by
  classical
  let A := CommRingCat.of (O ⧸ Ideal.span {ell} ^ (index n + 1))
  let B := CommRingCat.of (O' ⧸ Ideal.span {mu} ^ (n + 1))
  let : Algebra A B := (a.ring n).toAlgebra
  change Module.Basis (Fin r) A B at b
  let : Module.Free A B := Module.Free.of_basis b
  let : Module.Finite A B := Module.Finite.of_basis b
  let : IsGrothendieckAbelian.{u + 1} (strictEtaleLevel T O ell (index n)) :=
    isGrothendieckAbelian_coefficientUniverse _
  let : IsGrothendieckAbelian.{u + 1} (strictEtaleLevel T O' mu n) :=
    isGrothendieckAbelian_coefficientUniverse _
  let hIA : Abelian.HasKInjectiveResolutions
      (strictEtaleLevel T O ell (index n)) := inferInstance
  let hIB : Abelian.HasKInjectiveResolutions
      (strictEtaleLevel T O' mu n) := inferInstance
  let D : DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1, u + 2, u + 2}
      (a.sheaf T n) := (nonempty_derivedChangeOfRingsCochainModel (a.sheaf T n)).some
  let C := coordinateScalarSite (A := A) (B := B) (coordinateSite T)
    (hA := strictEtaleLevelDerived T O ell (index n))
    (hB := strictEtaleLevelDerived T O' mu n) (hIA := hIA) (hIB := hIB) D
  let : HasDerivedCategory.{u + 2}
      (CategoryTheory.ToposFiniteFreeCompact.Mod C.toSite A) := C.derivedA
  let : HasDerivedCategory.{u + 2}
      (CategoryTheory.ToposFiniteFreeCompact.Mod C.toSite B) := C.derivedB
  obtain ⟨ι, _, _, hι, _⟩ :=
    CategoryTheory.ToposFiniteFreeCompact.finiteFreeCompactCoordinates
      (coordinateIdentityOpen C) (coordinateIdentityGeometric C) b
  let E := siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n)
  let R := SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (a.sheaf T n))
  let : PreservesFiniteLimits E := (strictEtaleFiniteFreeScalarExact a T n L
    ⟨r, ⟨b⟩⟩).1
  let : PreservesFiniteColimits E := by
    let : PreservesColimitsOfSize.{0, 0} E :=
      (siteCoefficientTensorAdj (a.sheaf T n)).leftAdjoint_preservesColimits
    infer_instance
  let : IsIso L.counit := (strictEtaleFiniteFreeScalarExact a T n L ⟨r, ⟨b⟩⟩).2
  let : PreservesFiniteLimits R := C.resLimits
  let : PreservesFiniteColimits R := C.resColimits
  let : PreservesFiniteLimits D.E := CategoryTheory.ToposFiniteFreeCompact.scalarLimits C
  let : PreservesFiniteColimits D.E := CategoryTheory.ToposFiniteFreeCompact.scalarColimits C
  let σ : D.E ≅ E := eqToIso (by
    refine CategoryTheory.Functor.ext D.obj_eq ?_
    intro M N f
    exact D.map_eq f)
  let S := CategoryTheory.ToposFiniteFreeCompact.S C
  let U := CategoryTheory.ToposFiniteFreeCompact.U C
  let EC := E.mapHomologicalComplex (.up ℤ)
  let RC := R.mapHomologicalComplex (.up ℤ)
  let DC := D.E.mapHomologicalComplex (.up ℤ)
  let ΦL : DerivedCategory.Q ⋙ (L.derived ⋙ L.restriction) ≅
      (EC ⋙ RC) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (asIso L.counit) L.restriction ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft EC L.restrictionFactors ≪≫
      (Functor.associator _ _ _).symm
  let ΦC : DerivedCategory.Q ⋙ (S ⋙ U) ≅
      (EC ⋙ RC) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight D.E.mapDerivedCategoryFactors U ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft DC R.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex σ (.up ℤ)) RC)
        DerivedCategory.Q
  let τ : L.derived ⋙ L.restriction ≅ S ⋙ U := Localization.liftNatIso
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (.up ℤ)) _ _ _ _ (ΦL ≪≫ ΦC.symm)
  let κ : StrictEtaleLevelScalarInclusions L r := fun M i ↦ ι M i ≫ τ.inv.app M
  refine ⟨κ, ?_, ?_, ?_⟩
  · intro M N f i
    dsimp only [κ]
    rw [← Category.assoc, hι.1, Category.assoc]
    simpa only [CategoryTheory.Functor.comp_map, Category.assoc]
      using congrArg (ι M i ≫ ·) (τ.inv.naturality f)
  · intro M
    obtain ⟨q, hq, hsum⟩ := hι.2.1 M
    refine ⟨fun i ↦ τ.hom.app M ≫ q i, ?_, ?_⟩
    · intro i j
      dsimp only [κ]
      by_cases hij : i = j
      · simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, if_pos hij] using hq i j
      · simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, if_neg hij] using hq i j
    · dsimp only [κ]
      calc
        (∑ i, (τ.hom.app M ≫ q i) ≫ (ι M i ≫ τ.inv.app M)) =
            τ.hom.app M ≫ (∑ i, q i ≫ ι M i) ≫ τ.inv.app M := by
          simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
        _ = 𝟙 _ := by
          erw [hsum, Category.id_comp]
          exact τ.hom_inv_id_app M
  · intro P i
    obtain ⟨k, hk, hrep⟩ := hι.2.2 P i
    change ι (DerivedCategory.Q.obj P) i ≫
      U.map (D.E.mapDerivedCategoryFactors.hom.app P) ≫
      R.mapDerivedCategoryFactors.hom.app (DC.obj P) = DerivedCategory.Q.map k at hrep
    let j := RC.map ((NatIso.mapHomologicalComplex σ (.up ℤ)).hom.app P)
    refine ⟨k ≫ j, ?_, ?_⟩
    · intro d V x
      change (σ.hom.app (P.X d)).val.app V ((k.f d).val.app V x) = _
      rw [hk]
      have hσ : σ.hom.app (P.X d) = eqToHom (D.obj_eq (P.X d)) := by
        simp only [σ, eqToIso.hom, eqToHom_app]
      rw [hσ]
      change ((eqToHom (D.obj_eq (P.X d)).symm ≫
        eqToHom (D.obj_eq (P.X d))).val.app V) _ = _
      simp only [eqToHom_trans, eqToHom_refl, SheafOfModules.id_val,
        PresheafOfModules.id_app, ModuleCat.id_apply]
      rfl
    · have ht : τ.inv.app (DerivedCategory.Q.obj P) ≫ ΦL.hom.app P = ΦC.hom.app P := by
        dsimp only [τ, Localization.liftNatIso]
        rw [Localization.liftNatTrans_app]
        simp [Localization.Lifting.iso]
      have hL : ΦL.hom.app P = L.restriction.map (L.counit.app P) ≫
          L.restrictionFactors.hom.app (EC.obj P) := by simp [ΦL]
      have hC : ΦC.hom.app P = U.map (D.E.mapDerivedCategoryFactors.hom.app P) ≫
          R.mapDerivedCategoryFactors.hom.app (DC.obj P) ≫
          DerivedCategory.Q.map j := by
        simp only [comp_obj, isoWhiskerRight_twice, Iso.trans_hom, Iso.symm_hom,
          isoWhiskerRight_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
          associator_inv_app, whiskerRight_app, associator_hom_app, whiskerLeft_app,
          Functor.comp_map, Category.comp_id, Category.id_comp, ΦC, j]
        erw [Category.id_comp]
      change (ι (DerivedCategory.Q.obj P) i ≫ τ.inv.app _) ≫
        L.restriction.map (L.counit.app P) ≫
        L.restrictionFactors.hom.app (EC.obj P) = _
      calc
        _ = ι (DerivedCategory.Q.obj P) i ≫ τ.inv.app _ ≫ ΦL.hom.app P := by
          rw [hL]
          simp only [Category.assoc]
        _ = ι (DerivedCategory.Q.obj P) i ≫ ΦC.hom.app P := by rw [ht]
        _ = (ι (DerivedCategory.Q.obj P) i ≫
            U.map (D.E.mapDerivedCategoryFactors.hom.app P) ≫
            R.mapDerivedCategoryFactors.hom.app (DC.obj P)) ≫
              DerivedCategory.Q.map j := by rw [hC]; simp only [Category.assoc]
        _ = DerivedCategory.Q.map k ≫ DerivedCategory.Q.map j := by rw [hrep]
        _ = DerivedCategory.Q.map (k ≫ j) := by rw [DerivedCategory.Q.map_comp]

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive

import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Complete.CompleteCoefficientDatumSupplement
import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
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
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Cones
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicSliceScalarComparison
import WeilConjectures.AlgebraicGeometry.Finite.FiniteModelDerivedScalarComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement

/-! # The coefficient-change square for a finite-quotient constant model

Source: Stacks Project, Tags 06YY, 07A6 and 094I.
(blueprint: lem-weil-pbc-finite-quotient-model-residue-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective
attribute [local irreducible] completedAdicChangeData

private abbrev residueModules (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) CommRingCat.{t + 1}) :=
  SheafOfModules.{t + 1} ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj R)

private def residueChange (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    DerivedCategory (residueModules X R) ⥤ DerivedCategory (residueModules X S) :=
  completedAdicDerivedChange X f

private instance residueRestriction_limits (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    PreservesFiniteLimits (completedRestriction X f) :=
  (SheafOfModules.sheafRingDerivedCoefficientAdjunction f).choose

private instance residueRestriction_colimits (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    PreservesFiniteColimits (completedRestriction X f) :=
  (SheafOfModules.sheafRingDerivedCoefficientAdjunction f).choose_spec.choose

private theorem residueChange_adjunction (X : Scheme.{t})
    {R S : Sheaf (ProEt.topology X) CommRingCat.{t + 1}} (f : R ⟶ S) :
    Nonempty (residueChange X f ⊣ (completedRestriction X f).mapDerivedCategory) := by
  let D := completedAdicChangeData X f
  let E : residueModules X R ⥤ residueModules X S := D.choose
  let hE : ∀ M, E.obj M = SheafOfModules.changeOfRings f M := D.choose_spec.choose
  let hm : ∀ {M N : residueModules X R} (a : M ⟶ N),
      E.map a = eqToHom (hE M) ≫ SheafOfModules.changeOfRingsHom f M a ≫
        eqToHom (hE N).symm := fun a ↦ D.choose_spec.choose_spec.choose a
  let : E.Additive := D.choose_spec.choose_spec.choose_spec.choose
  let L : DerivedCategory (residueModules X R) ⥤ DerivedCategory (residueModules X S) :=
    D.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose
  let ε : DerivedCategory.Qh ⋙ L ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    D.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose
  have hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ)) :=
    D.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose_spec.1
  have h := (SheafOfModules.sheafRingDerivedCoefficientAdjunction f).choose_spec.choose_spec
  have ha := (h E hE hm).choose_spec.2 L ε hL
  exact ⟨ha.choose⟩

private def residueChange_comp (X : Scheme.{t})
    {R S V : Sheaf (ProEt.topology X) CommRingCat.{t + 1}}
    (f : R ⟶ S) (g : S ⟶ V) :
    residueChange X f ⋙ residueChange X g ≅ residueChange X (f ≫ g) := by
  let a := (residueChange_adjunction X f).some
  let b := (residueChange_adjunction X g).some
  let c := (residueChange_adjunction X (f ≫ g)).some
  let e : (completedRestriction X g).mapDerivedCategory ⋙
      (completedRestriction X f).mapDerivedCategory ≅
      (completedRestriction X (f ≫ g)).mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (completedRestrictCompIso X f g).symm
  exact ((a.comp b).ofNatIsoRight e).leftAdjointUniq c

private theorem residueCoefficient_square (X : Scheme.{t})
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hc : FinitePerfectModelsCompatible X d φ) (n : ℕ) :
    adicConstantMap X (adicQuotientMap d.ideal (n + 1) (0 + 1)
        (Nat.succ_le_succ (Nat.zero_le n))) ≫ φ 0 =
      φ n ≫ completedAdicQuotientCommMap X d n 0 (Nat.zero_le n) := by
  let p := Ideal.Quotient.mk (d.ideal ^ (n + 1))
  let q := adicQuotientMap d.ideal (n + 1) (0 + 1)
    (Nat.succ_le_succ (Nat.zero_le n))
  have hp : Function.Surjective (RingHom.ulift p) := by
    intro y
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective y.down
    exact ⟨ULift.up x, congrArg ULift.up hx⟩
  let : Epi (CommRingCat.ofHom (RingHom.ulift p)) :=
    ConcreteCategory.epi_of_surjective _ hp
  let : (constantSheaf (ProEt.topology X) CommRingCat.{t + 1}).IsLeftAdjoint :=
    (constantSheafAdj (ProEt.topology X) CommRingCat.{t + 1}
      terminalIsTerminal).isLeftAdjoint
  have : Epi (adicConstantMap X p) := by
    unfold adicConstantMap
    infer_instance
  have hq : q.comp p = Ideal.Quotient.mk (d.ideal ^ (0 + 1)) := by
    ext x
    rfl
  apply (cancel_epi (adicConstantMap X p)).1
  calc
    adicConstantMap X p ≫ adicConstantMap X q ≫ φ 0 =
        adicConstantMap X (Ideal.Quotient.mk (d.ideal ^ (0 + 1))) ≫ φ 0 := by
      rw [← Category.assoc, residueConstantMap_comp, hq]
    _ = completedAdicScalar X d ≫ completedAdicCommProjection X d 0 := (hc.2 0).symm
    _ = completedAdicScalar X d ≫ completedAdicCommProjection X d n ≫
        completedAdicQuotientCommMap X d n 0 (Nat.zero_le n) := by
      rw [completedAdicCommProjection_comp]
    _ = adicConstantMap X p ≫ φ n ≫
        completedAdicQuotientCommMap X d n 0 (Nat.zero_le n) := by
      rw [← Category.assoc, hc.2 n, Category.assoc]

private def residueRestrictionComparison (X : Scheme.{t})
    (R : Sheaf (ProEt.topology X) RingCat.{t + 1}) (U : X.ProEt)
    (M : DerivedCategory (SheafOfModules.{t + 1} R)) :
    (ringedDerivedRestrictionGeneral R U).obj M ≅
      ringedSiteDerivedRestrictionOfUniverses R U M := by
  let F := SheafOfModules.overFunctor.{t + 1} R U
  have := (ringedOverFunctor_exactGeneral R U).1
  have := (ringedOverFunctor_exactGeneral R U).2.1
  have := (ringedOverFunctor_exactGeneral R U).2.2
  exact F.mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso M).symm ≪≫
    F.mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage M)

set_option linter.unusedVariables false in
/-- A model on a pro-etale chart remains a model after passage to residue coefficients.
All coefficient rings are condensed rings, and all modules are module objects over their
actual pullbacks from the point. The maps `mn`, `m₀`, `q` are a coefficient reduction and its
residue; `b`, `φn`, `φ₀` give the compatible model coefficient square. In the finite case
one takes `Bn` and `B₀` to be the discrete condensed quotient and residue rings.
The model `P` is allowed to be any derived object, hence also a constant realization.
Its residue model is constructed by total derived extension along `b_X`.

Source: det-def-sfb-coefficient-change and det-def-sfb-derived-extension-of-scalars;
Stacks Tags 06YY and 0D6D.
Proof: pull back both coefficient equations from the point. Derived scalar transitivity
identifies reduction along `mn` followed by `q` with reduction along `m₀`, and identifies
extension along `φn` followed by `q` with extension along `b` followed by `φ₀`.
Move the given chart isomorphism across `q` using the slice scalar comparison, apply the
slice extension to that isomorphism, and compose with the two transitivity isomorphisms.
This is the coefficient-square and slice-transport argument of the previous proof, now
on the actual condensed coefficient categories. No flatness, projectivity, boundedness,
nonempty-chart condition, or choice of a representative complex is required.
(blueprint: lem-weil-pbc-finite-quotient-model-residue-comparison). -/
theorem finiteQuotient_model_residueComparison (X : Scheme.{t}) (U : X.ProEt)
    (mn : Λ ⟶ Λn) [IsMonHom mn] (m₀ : Λ ⟶ Λ₀) [IsMonHom m₀]
    (q : Λn ⟶ Λ₀) [IsMonHom q] (hm : mn ≫ q = m₀)
    (φn : Bn ⟶ Λn) [IsMonHom φn] (φ₀ : B₀ ⟶ Λ₀) [IsMonHom φ₀]
    (b : Bn ⟶ B₀) [IsMonHom b] (hs : φn ≫ q = b ≫ φ₀)
    (M : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{t + 1}) (condensedRingObj Λ X)))
    (P : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{t + 1}) (condensedRingObj Bn X)))
    (e : Nonempty
      ((CondensedRing.upperStar Λn U.hom).mapDerivedCategory.obj
          ((Mod.extendScalars (coefficientMap mn X)).leftDerivedFunctor.obj M) ≅
        (CondensedRing.upperStar Λn U.hom).mapDerivedCategory.obj
          ((Mod.extendScalars (coefficientMap φn X)).leftDerivedFunctor.obj P))) :
    Nonempty
      ((CondensedRing.upperStar Λ₀ U.hom).mapDerivedCategory.obj
          ((Mod.extendScalars (coefficientMap m₀ X)).leftDerivedFunctor.obj M) ≅
        (CondensedRing.upperStar Λ₀ U.hom).mapDerivedCategory.obj
          ((Mod.extendScalars (coefficientMap φ₀ X)).leftDerivedFunctor.obj
            ((Mod.extendScalars (coefficientMap b X)).leftDerivedFunctor.obj P))) := by
  have hmX : coefficientMap mn X ≫ coefficientMap q X = coefficientMap m₀ X := by
    rw [← coefficientMap_comp, hm]
  have hsX : coefficientMap φn X ≫ coefficientMap q X =
      coefficientMap b X ≫ coefficientMap φ₀ X := by
    rw [← coefficientMap_comp, ← coefficientMap_comp, hs]
  let em := Mod.derivedExtendScalarsCompIso
    (coefficientMap mn X) (coefficientMap q X) (coefficientMap m₀ X) hmX
  let ec :=
    (Mod.derivedExtendScalarsCompIso (coefficientMap φn X) (coefficientMap q X)
      (coefficientMap φn X ≫ coefficientMap q X) rfl).symm ≪≫
    Mod.derivedExtendScalarsCompIso (coefficientMap b X) (coefficientMap φ₀ X)
      (coefficientMap φn X ≫ coefficientMap q X) hsX.symm
  let r₀ := (CondensedRing.upperStar Λ₀ U.hom).mapDerivedCategory
  let s := (completedAdic_slice_scalarComparison X U q).some
  exact ⟨r₀.mapIso (em.app M) ≪≫ (s.app _).symm ≪≫
    (completedAdicSliceDerivedChange X U q).mapIso e.some ≪≫ s.app _ ≪≫
    r₀.mapIso (ec.app P)⟩

private theorem residueConstantMap_comp (X : Scheme.{t}) {A B C : Type t}
    [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    adicConstantMap X f ≫ adicConstantMap X g = adicConstantMap X (g.comp f) := by
  unfold adicConstantMap
  rw [← Functor.map_comp]
  rfl

end AlgebraicGeometry.Scheme

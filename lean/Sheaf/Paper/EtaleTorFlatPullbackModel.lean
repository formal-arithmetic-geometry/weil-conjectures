module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import Sheaf.Paper.FiniteCoefficientFlatModel
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.AlgebraicGeometry.EtaleConstantModuleFlat

/-! # Bounded flat etale models and their geometric pullbacks

Source: Stacks Project, sites-cohomology.tex, Tags 06YQ and 0G7E;
blueprint main-20261015, sec-proetale-coefficients/sk-cor-pe-finite-tor-comparison,
lem-sf-flat-model.md, small-etale clause; derived.tex, Tag 015F
(blueprint: lem-sf-etale-tor-flat-pullback-model).

`etaleTorFlatPullbackModelIso` specifies the representing isomorphism as the inverse
image of the chosen isomorphism followed by the exact localization comparison.
`etale_tor_flat_pullback_model` gives existence and the assertions for every model.
The existing constant-module realization is used only to apply the recorded site
flatness and K-flatness predicates to ordinary ModuleCat-valued etale sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The specified representing isomorphism after exact geometric inverse image.
Source: Stacks Project, derived.tex, Tag 015F, and sites-modules.tex, Tag 04JC
(blueprint: lem-sf-etale-tor-flat-pullback-model).
This is literally `l(e)` followed by the component of `mapDerivedCategoryFactors`.
It uses the ordinary constant-coefficient inverse image, not a chosen map of modules. -/
def etaleTorFlatPullbackModelIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategoryModule A Y)
    (V : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (e : M ≅ _root_.DerivedCategory.Q.obj V) :
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj M ≅
      _root_.DerivedCategory.Q.obj
        (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj V) :=
  (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.mapIso e ≪≫
    ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategoryFactors).app V

/-- Bounded flat models exist in the prescribed Tor interval, and every such model
and its termwise geometric inverse image are K-flat. The pullback still has flat terms
and the same support; its representing isomorphism is `etaleTorFlatPullbackModelIso`.
Source: Stacks Project, Tags 06YQ, 0G7E, 03EP, 04JC and 015F; blueprint
main-20261015, lem-sf-flat-model.md, small-etale clause
(blueprint: lem-sf-etale-tor-flat-pullback-model).

Proof:
1. Apply the small-etale clause of lem-sf-flat-model to obtain a flat model in
   [a,b]. The constant-module flatness equivalence converts its categorical
   flatness to IsFlatOnSite without changing its terms or representing isomorphism.
2. For any model with the stated support and flat terms, its constant-module
   realization is bounded above by b: the realization preserves zero objects.
   Apply lem-weil-pbc-independent-bounded-flat-kflat to obtain K-flatness.
3. Convert site-flatness back to categorical flatness. Geometric inverse image
   preserves categorical flatness, as checked on geometric stalks. Convert back
   to site-flatness on X. Inverse image preserves zero objects and thus the
   support interval. Apply the same bounded-above flat criterion on X.
4. Apply etaleTorFlatPullbackModelIso to the chosen representing isomorphism;
   it is precisely l(e) followed by the exact localization comparison.
No local freeness of terms or finiteness condition on f is used. -/
theorem etale_tor_flat_pullback_model
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    (X Y : Scheme.{u}) (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (a b : ℤ) (_hab : a ≤ b)
    (M : DerivedCategoryModule (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) Y)
    (_hM : @DerivedCategory.isBoundedConstructible.{u}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) inferInstance
      ((Equiv.ulift : ULift.{u + 1} (Padic.coefficientExtensionRing l E n) ≃
        Padic.coefficientExtensionRing l E n).finite_iff.mpr
          (Padic.finite_coefficientExtensionRing l E n hn)) Y M)
    (_hTor : DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) Y a b M) :
    (fun (A : Type (u + 1)) [CommRing A] (K : DerivedCategoryModule A Y) ↦
      (∃ V : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
        (∀ h : ℤ, h < a ∨ b < h → IsZero (V.X h)) ∧
        (∀ h : ℤ, SheafOfModules.IsFlatOnSite
          (J := Y.smallEtaleTopology)
          (R := (constantSheaf Y.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of A))
          ((Scheme.etaleSumFlatModuleRealization Y A).obj (V.X h))) ∧
        Nonempty (K ≅ _root_.DerivedCategory.Q.obj V)) ∧
      (∀ V : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
        (∀ h : ℤ, h < a ∨ b < h → IsZero (V.X h)) →
        (∀ h : ℤ, SheafOfModules.IsFlatOnSite
          (J := Y.smallEtaleTopology)
          (R := (constantSheaf Y.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of A))
          ((Scheme.etaleSumFlatModuleRealization Y A).obj (V.X h))) →
        ∀ _e : K ≅ _root_.DerivedCategory.Q.obj V,
          CochainComplex.IsKFlatIndependentCoefficients
            ((Scheme.etaleSumFlatComplexRealization Y A).obj V) ∧
          CochainComplex.IsKFlatIndependentCoefficients
            ((Scheme.etaleSumFlatComplexRealization X A).obj
              (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj V)) ∧
          (∀ h : ℤ, SheafOfModules.IsFlatOnSite
            (J := X.smallEtaleTopology)
            (R := (constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj
              (CommRingCat.of A))
            ((Scheme.etaleSumFlatModuleRealization X A).obj
              ((((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex
                (.up ℤ)).obj V).X h))) ∧
          (∀ h : ℤ, h < a ∨ b < h → IsZero
            ((((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex
              (.up ℤ)).obj V).X h)) ∧
          Nonempty ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj K ≅
            _root_.DerivedCategory.Q.obj
              (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj V))))
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) M := by
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E n)
  have hkflat (T : Scheme.{u})
      (V : CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
      (hz : ∀ h : ℤ, h < a ∨ b < h → IsZero (V.X h))
      (hf : ∀ h : ℤ, SheafOfModules.IsFlatOnSite
        (J := T.smallEtaleTopology)
        (R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of A))
        ((Scheme.etaleSumFlatModuleRealization T A).obj (V.X h))) :
      CochainComplex.IsKFlatIndependentCoefficients
        ((Scheme.etaleSumFlatComplexRealization T A).obj V) := by
    let := Scheme.etaleConstantModuleFunctor_isEquivalence T A
    let F := Scheme.etaleSumFlatModuleRealization T A
    have : F.PreservesZeroMorphisms := by
      dsimp [F, Scheme.etaleSumFlatModuleRealization]
      infer_instance
    let P : CochainComplex _ ℤ := (F.mapHomologicalComplex (.up ℤ)).obj V
    have : P.IsStrictlyLE b := (CochainComplex.isStrictlyLE_iff P b).2
      (fun h hh ↦ F.map_isZero (hz h (Or.inr hh)))
    exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
      ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of A))
      P b hf
  constructor
  · obtain ⟨V, hV, e⟩ :=
      (finiteCoefficient_hasTorAmplitude_iff_flatModel D l _hl E n hn Y M _hM
        a b _hab).1 _hTor
    exact ⟨V, hV.1, fun h ↦ (Scheme.etaleConstantModule_flat_iff Y A _).1 (hV.2 h), e⟩
  · intro V hz hf e
    have hflat (h : ℤ) : SheafOfModules.IsFlatOnSite
        (J := X.smallEtaleTopology)
        (R := (constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of A))
        ((Scheme.etaleSumFlatModuleRealization X A).obj
          ((upperStar (ModuleCat.{u + 1} A) f).obj (V.X h))) := by
      apply (Scheme.etaleConstantModule_flat_iff X A _).1
      exact Functor.PreservesFlat.flat_obj (F := upperStar (ModuleCat.{u + 1} A) f)
        ((Scheme.etaleConstantModule_flat_iff Y A _).2 (hf h))
    have hzero (h : ℤ) (hh : h < a ∨ b < h) :
        IsZero ((upperStar (ModuleCat.{u + 1} A) f).obj (V.X h)) :=
      (upperStar (ModuleCat.{u + 1} A) f).map_isZero (hz h hh)
    exact ⟨hkflat Y V hz hf,
      hkflat X (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex
        (.up ℤ)).obj V) hzero hflat,
      hflat, hzero, ⟨etaleTorFlatPullbackModelIso A f M V e⟩⟩

end AlgebraicGeometry.Etale

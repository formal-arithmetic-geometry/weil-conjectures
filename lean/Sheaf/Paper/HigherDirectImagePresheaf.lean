module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Sheaf.Topology.OpenModuleCohomology
public import Sheaf.Topology.PresheafModuleStalkFunctor
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMap
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties
import Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives
import Sheaf.Paper.PQFCohomology

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-! # Higher direct image as a sheafified cohomology presheaf
Source: literature/stacks-project/cohomology.tex, Lemma 01E4
(blueprint: lem-weil-pbc-higher-direct-image-presheaf).
-/

/-- Stacks 01E4 with every datum tied. For an injective resolution I of F, the presheaf
P_p is `sectionCohomologyPresheaf (f_*I) p`, V ↦ H^p(I(f⁻¹V)); theta is
`sectionCohomologyTheta (f_*I) p` followed by the resolution comparison
H^p(f_*I) ≅ R^p f_*F. The statement says:
(1) the canonical comparison P_p^# → R^p f_*F is an isomorphism;
(2) theta is universal: every map from P_p to a sheaf of modules factors uniquely
through theta;
(3) for each y, the map induced by theta on module stalks is an isomorphism;
(4) the value of P_p on V is H^p(f⁻¹V, F) (open module cohomology, through the same
resolution and exact evaluation), and under these identifications the restriction
maps of P_p are the cohomology restriction maps;
(5) the canonical map f_*F → R^0 f_*F is an isomorphism.
Source: literature/stacks-project/cohomology.tex, Lemma 01E4
(blueprint: lem-weil-pbc-higher-direct-image-presheaf).

Proof: (1) f_*I computes R^p f_*F; module sheafification is exact and commutes with
homology, and its counit on sheaves is invertible, so the comparison is invertible.
(2) theta is the adjoint of an isomorphism, hence universal. (3) sheafification
preserves stalks (Sheaves 007Z), and theta factors as the sheafification unit followed
by an isomorphism. (4) I restricted to f⁻¹V is an injective resolution (01E1), whose
sections are I(f⁻¹V); restriction of cohomology is induced by restriction of the
resolution (01E2), and the evaluation at V of f_*I is I(f⁻¹V). (5) f_* is left exact. -/
theorem higherDirectImagePresheaf {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (I : InjectiveResolution F) (p : ℕ) :
    IsIso (Scheme.Modules.sectionCohomologyComparison
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) p ≫
      (I.isoRightDerivedObj (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) p).inv) ∧
    (∀ (Q : SheafOfModules.{u} (moduleRings Y.toRingedSpace))
      (a : Scheme.Modules.sectionCohomologyPresheaf
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) p ⟶
        (SheafOfModules.forget (moduleRings Y.toRingedSpace)).obj Q),
      ∃! b : ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj F ⟶ Q,
        Scheme.Modules.sectionCohomologyTheta
            (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj I.cocomplex) p ≫
          (SheafOfModules.forget (moduleRings Y.toRingedSpace)).map
            ((I.isoRightDerivedObj (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) p).inv ≫
              b) = a) ∧
    (∀ y : Y, IsIso ((PresheafOfModules.moduleStalkFunctor (moduleRings Y.toRingedSpace).obj y).map
      (Scheme.Modules.sectionCohomologyTheta
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex) p ≫
        (SheafOfModules.forget (moduleRings Y.toRingedSpace)).map
          (I.isoRightDerivedObj (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) p).inv))) ∧
    (∀ (V W : Y.Opens) (i : W ⟶ V),
      (RingedSpace.openModuleCohomologyRestriction X.toRingedSpace p
          (homOfLE (f.preimage_mono (leOfHom i)))).app F ≫
        (I.isoRightDerivedObj (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ W)) p ≪≫
          ((((SheafOfModules.forget (moduleRings Y.toRingedSpace)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj
              (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj I.cocomplex)).sc p).mapHomologyIso
                  (PresheafOfModules.toPresheaf (moduleRings Y.toRingedSpace).obj ⋙
                    (evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op W))).hom =
      (I.isoRightDerivedObj (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)) p ≪≫
          ((((SheafOfModules.forget (moduleRings Y.toRingedSpace)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj
              (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
                (ComplexShape.up ℕ)).obj I.cocomplex)).sc p).mapHomologyIso
                  (PresheafOfModules.toPresheaf (moduleRings Y.toRingedSpace).obj ⋙
                    (evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V))).hom ≫
        (Scheme.Modules.sectionCohomologyPresheaf
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex) p).presheaf.map i.op) ∧
    IsIso ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).toRightDerivedZero.app F) := by
  sorry

end AlgebraicGeometry

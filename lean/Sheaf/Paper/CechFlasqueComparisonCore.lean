module
public import Sheaf.Paper.CechCupResolutionComparisonData
public import Mathlib.Topology.Sheaves.Flasque
@[expose] public section
universe v
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The canonical core maps from a flasque computing resolution to its Cech total complex.
Source: Stacks Project, Tags 01EQ and 0FKV.
(blueprint: lem-sc-cech-flasque-resolution-comparison-core)

Proof: define `alpha` degreewise by restriction of global sections into Cech degree
zero and the total-complex inclusion. Define `beta` from the augmentation into the
resolution degree zero row and the corresponding total-complex inclusion. Restriction
naturality and the augmentation chain-map equation prove that both families are chain
maps. The augmented Cech complex of each flasque term is exact in positive degrees,
while sheaf gluing identifies degree-zero homology with global sections. The
first-quadrant column comparison for the resulting double complex therefore proves
that `alpha` is a quasi-isomorphism. The construction also works for degree zero and
for an empty cover of the empty scheme. -/
theorem cechFlasqueComparisonCore {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) (hU : iSup U = ⊤) {F : X.Modules}
    (D : CupAcyclicResolution F)
    (hD : ∀ n : ℕ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (D.K.X n))) :
    ∃ alpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K ⟶ (cupCechDouble U D.K).total (ComplexShape.up ℕ),
      ∃ beta : (cechComplexFunctor U).obj F.presheafModuleCat ⟶
        (cupCechDouble U D.K).total (ComplexShape.up ℕ),
      (∀ n : ℕ, alpha.f n = moduleCechZero U (D.K.X n) ≫
        (cupCechDouble U D.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp)) ∧
      (∀ n : ℕ, beta.f n =
        ((cechComplexFunctor U).map
          ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
            (D.augmentation.f 0).val)).f n ≫
        (cupCechDouble U D.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp)) ∧
      QuasiIso alpha := by sorry

end
end AlgebraicGeometry.Scheme.Modules

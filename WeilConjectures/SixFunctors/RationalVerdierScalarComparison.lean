/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixTensorHom
public import WeilConjectures.AlgebraicGeometry.CondensedVerdierBiduality
public import WeilConjectures.CategoryTheory.EvaluationBidualComparisonTransport
import WeilConjectures.CategoryTheory.RationalVerdierEvaluationComparison
import WeilConjectures.SixFunctors.ListedCoefficientCtf
import WeilConjectures.SixFunctors.ModCondensedCachedInstances

/-! # Evaluation and biduality under actual condensed scalar extension

Source: current blueprint thm-coef-rational-verdier, proof paragraphs 1 and 3.
(blueprint: lem-coef-rational-verdier-condensed-scalar-comparison).

The dualizing-object identification is an explicit input. The dual comparison is
then the canonical internal-Hom mate, followed by that identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures

/-- The normalized scalar-duality equations for a specified source dualizing object.
The input w is the proposed dualizing-object identification; every later map is
fixed by the actual internal-Hom comparison. No identification is selected here.
Source: current blueprint rational duality, proof paragraphs 1 and 3.
(blueprint: lem-coef-rational-verdier-condensed-scalar-comparison). -/
def RationalVerdierScalarCompatibility {Λ Λ' : ScalarSixRing.{u}}
    (a : Λ ⟶ Λ') (Z : Scheme.{u})
    (W : ConstantModelConstructibleFiniteTor Λ.X Z) : Prop :=
  letI := DerivedCategory.braidedCategory'
      (ModuleRingedComparison.internalModules Λ.X Z)
  letI := DerivedCategory.braidedCategory'
      (ModuleRingedComparison.internalModules Λ'.X Z)
  ∀ (W' : moduleDerived Λ'.X Z)
      (w : (scalarSixChange a Z).obj W.obj ≅ W')
      (K : ConstantModelConstructibleFiniteTor Λ.X Z),
      ∃ (hK : IsIso (scalarSixHomComparison a Z K.obj W.obj))
        (hDK : IsIso (scalarSixHomComparison a Z ((ihom K.obj).obj W.obj) W.obj)),
        (scalarSixChange a Z).obj K.obj ◁
            (evaluationDualComparison (scalarSixChange a Z) w K.obj hK).hom ≫
              (ihom.ev ((scalarSixChange a Z).obj K.obj)).app W' =
          Functor.LaxMonoidal.μ (scalarSixChange a Z) K.obj _ ≫
            (scalarSixChange a Z).map ((ihom.ev K.obj).app W.obj) ≫ w.hom ∧
        (condensedVerdierBiduality Λ'.X Z W').app
            ((scalarSixChange a Z).obj K.obj) =
          (scalarSixChange a Z).map
              ((condensedVerdierBiduality Λ.X Z W.obj).app K.obj) ≫
            (evaluationDualComparison (scalarSixChange a Z) w
              ((ihom K.obj).obj W.obj) hDK).hom ≫
            (pre (evaluationDualComparison (scalarSixChange a Z) w K.obj hK).inv).app W'

set_option maxHeartbeats 1200000 in
-- The two native derived scalar comparisons share large module-object instances.
/-- Scalar dual comparison preserves the actual evaluation and double-dual maps.
This applies both to integral localization and finite field extensions, once their
specified dualizing-object identification is supplied.
Source: current blueprint rational Verdier duality, proof paragraphs 1 and 3.
(blueprint: lem-coef-rational-verdier-condensed-scalar-comparison).

Proof: internal-Hom stability puts DK in the same constructible finite-Tor domain
as K and W. Apply scalarSixTensorHom at (K,W) and (DK,W); these are the actual
invertible evaluation mates. Derived scalar extension carries the canonical braided
monoidal structure. The evaluation and double-dual equations are therefore the
generic uncurrying equations, with this functor and the specified identification.
No equivalence or essential surjectivity of scalar extension is required. -/
theorem coef_rational_verdier_scalar_comparison (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (hcd : BaseFieldFiniteCD l k)
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') (ha : ListedCoefficientMap l a)
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    ∀ W : ConstantModelConstructibleFiniteTor Λ.X X.left,
      RationalVerdierScalarCompatibility a X.left W := by
  intro W
  dsimp only [RationalVerdierScalarCompatibility]
  intro W' w K
  let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
  let : LocallyOfFiniteType (X.left ↘ Spec (.of k)) := ‹LocallyOfFiniteType X.hom›
  let : QuasiCompact (X.left ↘ Spec (.of k)) := ‹QuasiCompact X.hom›
  let : IsSeparated (X.left ↘ Spec (.of k)) := ‹IsSeparated X.hom›
  let DK : ConstantModelConstructibleFiniteTor Λ.X X.left :=
    ⟨(ihom K.obj).obj W.obj,
      (internalHom_stability Λ.X l k hcd (listedCoefficientCtf l a ha).1
        K.obj W.obj K.property W.property).1⟩
  have hK := ((scalarSixTensorHom l k a ha X).2 K W).1
  have hDK := ((scalarSixTensorHom l k a ha X).2 DK W).1
  let := DerivedCategory.symmetricCategory
    (ModuleRingedComparison.internalModules Λ.X X.left)
  let := DerivedCategory.symmetricCategory
    (ModuleRingedComparison.internalModules Λ'.X X.left)
  let := Mod.extendScalarsMonoidal
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X.left)
  let : (scalarSixChange a X.left).Braided :=
    (Mod.extendScalars
      (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X.left)).leftDerivedFunctorBraided
      (Mod.extendScalars_map_braiding_hom_δ _)
  refine ⟨hK, hDK, ?_, ?_⟩
  · exact RationalVerdierCondensed.evaluation (scalarSixChange a X.left) w K.obj hK
  · exact RationalVerdierCondensed.biduality (scalarSixChange a X.left) w K.obj hK hDK

end WeilConjectures

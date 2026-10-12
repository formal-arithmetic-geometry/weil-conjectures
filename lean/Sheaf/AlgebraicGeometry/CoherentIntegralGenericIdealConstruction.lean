module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.CoherentStalkMapExtends
import Sheaf.AlgebraicGeometry.CoherentLocalIsomorphism
import Sheaf.AlgebraicGeometry.CoherentHomsOverOpen
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk
import Sheaf.Algebra.Homology.ModuleStalkExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- The lattice construction before proving injectivity.

Source: Stacks Project, Tag 01YE, first two paragraphs of the integral-case proof.
(blueprint: lem-weil-pbc-coherent-integral-generic-ideal-map-construction).

Proof sketch: the generic local ring of an integral scheme is a field.  The generic
stalk of a coherent module is therefore finite dimensional; choose a basis and extend
the resulting map from a finite free module to a neighbourhood of the generic point.
After shrinking, the map is an isomorphism there.  Give the closed complement its
reduced induced structure and apply the extension-over-an-open lemma to a power of
its ideal.  This produces a map from a finite coproduct of copies of one ideal
sheaf, still an isomorphism at the generic stalk.  The ideal and its finite coproduct
are coherent by local Noetherianity.  The formal proof is left as this named theorem
for the next stage worker. -/
theorem coherent_integral_generic_ideal_construction (Z : Scheme.{w}) [IsNoetherian Z]
    [IsIntegral Z] (G : Z.Modules) (hG : RingedSpace.IsCoherent Z.toRingedSpace G) :
    ∃ (r : ℕ) (I : Z.IdealSheafData),
      RingedSpace.IsCoherent Z.toRingedSpace I.toModules ∧
      RingedSpace.IsCoherent Z.toRingedSpace (∐ fun _ : Fin r => I.toModules) ∧
      ∃ (χ : (∐ fun _ : Fin r => I.toModules) ⟶ G),
        IsIso ((RingedSpace.moduleStalkFunctor Z.toRingedSpace (genericPoint Z)).map χ) := by
  sorry

end AlgebraicGeometry.Scheme.Modules

module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
public import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
public import Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk
import Sheaf.Algebra.Homology.ModuleStalkExact

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules

/-- A map in the integral lattice construction is injective once it is generically an
isomorphism.  This is the coordinatewise generic-stalk argument of Stacks, Tag 01YE.
(blueprint: lem-weil-pbc-coherent-integral-generic-ideal-map-mono).

Proof sketch: take the coherent kernel of the map.  Exactness of module stalks and
the generic isomorphism show that its generic stalk is zero.  Embed this kernel in
the finite coproduct of copies of the ideal and project to each coordinate.  Each
coordinate image is a quasi-coherent ideal with zero generic stalk, hence is zero on
an integral scheme.  All coordinates of every kernel section therefore vanish, so
the kernel is zero and the map is mono.  Coherence of the kernel and the image
ideals supplies the stated finiteness hypotheses.  The formal proof is left as this
named theorem for the next stage worker. -/
theorem mono_of_coherent_ideal_sum_generic_iso (Z : Scheme.{w}) [IsNoetherian Z]
    [IsIntegral Z] (G : Z.Modules) (hG : RingedSpace.IsCoherent Z.toRingedSpace G)
    (r : ℕ) (I : Z.IdealSheafData)
    (χ : (∐ fun _ : Fin r => I.toModules) ⟶ G)
    (hI : RingedSpace.IsCoherent Z.toRingedSpace I.toModules)
    (hSum : RingedSpace.IsCoherent Z.toRingedSpace (∐ fun _ : Fin r => I.toModules))
    (hχ : IsIso ((RingedSpace.moduleStalkFunctor Z.toRingedSpace (genericPoint Z)).map χ)) :
    Mono χ := by
  sorry

end AlgebraicGeometry.Scheme.Modules

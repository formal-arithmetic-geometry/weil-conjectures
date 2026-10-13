module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- A prescribed injective generic stalk map from a closed pushforward of the
structure module extends after restricting its source to a nonzero ideal.
Source: Stacks Project, Tags 01Y4, 01YB and 01YE, extending stalk maps and
clearing denominators in the ideal-lattice construction.
(blueprint: new-generic-ideal-stalk-embedding-extension)

Proof: the closed pushforward of the structure module is coherent because the
closed immersion is finite and X is Noetherian. Extend the prescribed stalk map
on a neighbourhood of the image of the generic point (01Y4). Choose the reduced
ideal of its closed complement and extend the local map from a sufficiently high
power of that ideal times the source (01YB). On affine opens, multiplication of
this ideal with i_*O_W is the pushforward of its image ideal on W; thus the source
is i_*J. Near the generic point the complement ideal is the unit ideal, so J has
full generic stalk and is nonzero. The extension agrees with the prescribed map
on that stalk, giving the displayed equation. Its kernel is a quasi-coherent
submodule of i_*J. The defining ideal of W annihilates this kernel, so it descends
to a quasi-coherent submodule of J on W. Injectivity of the prescribed generic map
makes its generic stalk zero. A quasi-coherent submodule of an ideal on an
integral scheme with zero generic stalk is zero: on every nonempty affine open it
is a submodule of a domain and injects into its fraction field. The kernel is
therefore zero and the extended map is mono. The construction uses no rank or
maximal-ideal-annihilation hypothesis on G. -/
theorem generic_ideal_stalk_embedding_extension {X W : Scheme.{u}} [IsNoetherian X]
    (i : W ⟶ X) [IsClosedImmersion i] [IsIntegral W]
    (G : X.Modules) (hGcoh : RingedSpace.IsCoherent X.toRingedSpace G)
    (ψ : (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj ((pushforward i).obj
          (SheafOfModules.unit W.ringCatSheaf)) ⟶
      (RingedSpace.moduleStalkFunctor X.toRingedSpace
        (i.base (genericPoint W))).obj G)
    (hψ : Function.Injective ψ) :
    ∃ (J : W.IdealSheafData), J ≠ ⊥ ∧
      ∃ (α : (pushforward i).obj J.toModules ⟶ G), Mono α ∧
        (RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).map α =
        (RingedSpace.moduleStalkFunctor X.toRingedSpace
          (i.base (genericPoint W))).map ((pushforward i).map J.toModulesι) ≫ ψ := by sorry

end AlgebraicGeometry.Scheme.Modules

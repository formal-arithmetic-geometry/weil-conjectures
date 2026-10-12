module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Shapes.Products

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
/-- The second-page coproduct comparison is a monomorphism.
Source: Stacks Project, Tag 08DZ, second-page direct-sum reduction; Tag 009E (5),
identification of stalks of direct sums. This is the injectivity half only.
(blueprint: lem-pc-truncated-direct-image-second-page-coproduct-mono).

Proof: Let F be the composite of lower truncation at a, cohomology in degree r,
and the higher-direct-image functor in degree p. These functors are additive:
truncation and cohomology are additive, as are singleFunctor, derived direct image,
and its cohomology. For each i the universal property hc defines a projection
pi_i : S -> E_i which is identity on the i-th summand and zero on all other
summands. Thus F(pi_i) composed with the comparison phi is the i-th projection
from the sheaf coproduct of the F(E_j), by functoriality and preservation of zero.
At every point y of Y, the stalk of that coproduct is the algebraic direct sum
of the stalk modules, with its canonical injections. If phi_y sends a vector
to zero, applying the stalk map of every F(pi_i) makes each component of that
vector zero. A direct-sum vector is determined by its components, so phi_y is
injective. A morphism of module sheaves whose maps on all stalks are injective
is monic: two sections with the same image have equal germs everywhere, hence
are equal by the sheaf separation axiom. Therefore phi is monic. This argument
needs neither quasi-coherence nor the qcqs hypotheses. For the empty family
the source is the zero sheaf, so its map to F(S) is automatically monic; for a
singleton it is the image under F of an isomorphism. It also applies when r < a,
when all cohomology sheaves in question are zero. -/
theorem truncated_directImage_secondPage_coproduct_mono
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (I : Type u) (E : I → schemeDerivedQCohCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (a : ℤ) (p : ℕ) (r : ℤ) :
    Mono (Sigma.desc (fun i ↦ (schemeModuleHigherDirectImage f (p : ℤ)).map
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) r).map
          ((DerivedCategory.TStructure.t.truncGE a).map (ι i))))) := by
  sorry

end AlgebraicGeometry

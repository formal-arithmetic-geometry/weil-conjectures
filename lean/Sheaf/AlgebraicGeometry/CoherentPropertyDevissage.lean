module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Sheaf.Topology.PresheafModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.CoherentFiltrationIntegralSubschemes
import Sheaf.AlgebraicGeometry.CoherentPropertyIrreducible
import Sheaf.AlgebraicGeometry.IntegralIdealGenericStalk

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- Devissage criterion for properties of coherent modules.
Source: Stacks Project, Cohomology of Schemes, Lemma 30.12.6 (Tag 01YI),
coherent.tex line 3270 (blueprint: lem-pc-coherent-property-devissage).
The proof follows the five steps of 01YI. First (1) and (0) give invariance
under isomorphism and then finite-filtration induction (including the empty
filtration). Second, the coherent-filtration lemma gives quotients supported
on integral closed subschemes, and the generic-stalk lemma identifies their
generic points and shows their supports lie in the support of the original
module. Third, Noetherian minimality supplies a minimal irreducible closed
support on which the property could fail. Fourth, applying
`lem-pc-coherent-property-irreducible` to that support uses minimality for its
proper integral subschemes and hypothesis (2) for the chosen minimal one,
yielding a contradiction. Finally every filtration quotient has the property,
so the first step gives it for the original coherent module.
-/
theorem coherent_property_devissage
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (P : X.Modules → Prop)
    (hP_zero : ∀ F : X.Modules, IsZero F → P F)
    (hP_seq : ∀ (S : ShortComplex X.Modules), S.ShortExact →
      RingedSpace.IsCoherent X.toRingedSpace S.X₁ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₂ →
      RingedSpace.IsCoherent X.toRingedSpace S.X₃ →
      ((P S.X₁ ∧ P S.X₂) ∨ (P S.X₁ ∧ P S.X₃) ∨ (P S.X₂ ∧ P S.X₃)) →
      P S.X₁ ∧ P S.X₂ ∧ P S.X₃)
    (hP_integral : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsIntegral Z]
      [IsClosedImmersion i] (ξ : Z),
      ∃ G : X.Modules,
        RingedSpace.IsCoherent X.toRingedSpace G ∧
        (∀ x : X, (¬ Subsingleton (G.presheaf.stalk x)) ↔
          x ∈ Set.range i.base) ∧
        (∀ (r : X.presheaf.stalk (i.base ξ)),
          r ∈ IsLocalRing.maximalIdeal _ →
            ∀ m : (PresheafOfModules.stalkObj X.ringCatSheaf.presheaf (i.base ξ) G.val),
              r • m = 0) ∧
        (∃ hκ : Module (X.residueField (i.base ξ))
            (PresheafOfModules.stalkObj X.ringCatSheaf.presheaf (i.base ξ) G.val),
          @Module.finrank _ _ _ _ hκ = 1) ∧
        P G)
    : ∀ F : X.Modules, RingedSpace.IsCoherent X.toRingedSpace F → P F := by
  sorry

end AlgebraicGeometry

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Mathlib.AlgebraicGeometry.Over
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints
import Sheaf.Paper.ShiftedTensorMorphismCalculus
import Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility
import Sheaf.AlgebraicGeometry.SingleTensorAugmentationCoherence

/-! # Associativity, signed symmetry and units of scalar module cups

Source: Stacks Project, Cohomology, Tags 0FP4 and 0FP5, section-cup-product and
remark-cup-product, specialized to arbitrary module sheaves in degree zero.
(blueprint: lem-sfb-module-cup-associativity-symmetry-unit).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- The scalar cohomology cup is associative under the coefficient associator, symmetric
with the Koszul sign, and unital on both sides under the coefficient unitors. The unit
is the canonical image of the global section one, not a chosen degree-zero class.
Only the degree equalities are transported by `cast`; all coefficient isomorphisms
act through `scalarCohomologyMap`, the recorded derived cohomology functor.
Source: Stacks Project, Cohomology, Tags 0FP4 and 0FP5, section-cup-product and
remark-cup-product (blueprint: lem-sfb-module-cup-associativity-symmetry-unit).

Proof:
1. Write star for the unsigned ordinary module cup. The normalized shifted-Hom
comparison (lem-sfb-module-cup-shifted-hom-comparison) identifies its image with
m[p+q] composed with the shifted derived tensor of the two representing morphisms
and the inverse unit map d. The class of one represents the identity of O_X[0],
and coefficient maps act by postcomposition. The shifted tensor calculus
(lem-pur-shifted-tensor-morphism-calculus) applies because O_X is flat, without
requiring any flatness of the three target coefficients.
2. Expand the two iterated ordinary cups. Naturality moves their inner augmentation
maps to the target. The two resulting composites agree by the associator equation
of lem-sfb-single-tensor-augmentation-coherence. Shifted tensor associativity equates
the remaining maps, and monoidal unit coherence equates the iterates of d.
Injectivity and coefficient naturality of the comparison give ordinary associativity.
3. Move the coefficient symmetry past m using augmentation symmetry. The shifted tensor
calculus exchanges the two representing morphisms with sign (-1)^(p*q). Symmetry of
the tensor square of the unit fixes d. Additivity and injectivity of the comparison
then give the ordinary signed symmetry, including the calculation omitted in 0FP5.
4. The class of one represents the identity. Augmentation unit coherence replaces
s(lambda) composed with m by the derived left unitor, and similarly on the right.
The unitors of def-pc-scheme-derived-tensor-structure descend from the ordinary module
unitors. With lem-pur-derived-tensor-additive-constraints, the shift extractions t(0,p)
and t(p,0) introduce sign one on these models. Unitor naturality reduces either
composite to the original representing morphism; the two unitors agree on the unit.
Injectivity of the comparison gives both ordinary unit laws in every degree.
5. By lem-sc-scalar-cup-module-cup-compatibility, the recorded scalar cup in degrees
i,j is (-1)^(i*j) times star. Bilinearity and coefficient additivity transport the
identities above: pq+(p+q)r = qr+p(q+r) gives associativity; the square of (-1)^(pq)
is one and pq=qp give symmetry; and the exponents 0*p and p*0 vanish for the units.
No quasi-coherence or geometric finiteness hypothesis enters this argument. -/
theorem scalarCohomologyCup_associativity_symmetry_unit
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G L : X.Modules) (p q r : ℕ)
    (a : scalarCohomology f F p) (b : scalarCohomology f G q)
    (c : scalarCohomology f L r) :
    scalarCohomologyMap f (α_ F G L).hom ((p + q) + r)
        (scalarCohomologyCup f (F ⊗ G) L (p + q) r
          (scalarCohomologyCup f F G p q a b) c) =
      cast (congrArg (fun n : ℕ ↦ ↥(scalarCohomology f (F ⊗ (G ⊗ L)) n))
        (Nat.add_assoc p q r).symm)
        (scalarCohomologyCup f F (G ⊗ L) p (q + r) a
          (scalarCohomologyCup f G L q r b c)) ∧
    scalarCohomologyMap f (β_ F G).hom (p + q)
        (scalarCohomologyCup f F G p q a b) =
      (-1 : k) ^ (p * q) •
        cast (congrArg (fun n : ℕ ↦ ↥(scalarCohomology f (G ⊗ F) n))
          (Nat.add_comm q p)) (scalarCohomologyCup f G F q p b a) ∧
    cast (congrArg (fun n : ℕ ↦ ↥(scalarCohomology f F n)) (Nat.zero_add p))
        (scalarCohomologyMap f (λ_ F).hom (0 + p)
          (scalarCohomologyCup f (SheafOfModules.unit X.ringCatSheaf) F 0 p
            (((@Functor.toRightDerivedZero _ _ _ _ _
              (@InjectiveResolution.instHasInjectiveResolutions _ _ _
                (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2) _
              (RingedSpace.globalSectionsFunctor X.toRingedSpace) _).app
                (SheafOfModules.unit X.ringCatSheaf)).hom (1 : Γ(X, ⊤))) a)) = a ∧
    cast (congrArg (fun n : ℕ ↦ ↥(scalarCohomology f F n)) (Nat.add_zero p))
        (scalarCohomologyMap f (ρ_ F).hom (p + 0)
          (scalarCohomologyCup f F (SheafOfModules.unit X.ringCatSheaf) p 0 a
            (((@Functor.toRightDerivedZero _ _ _ _ _
              (@InjectiveResolution.instHasInjectiveResolutions _ _ _
                (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2) _
              (RingedSpace.globalSectionsFunctor X.toRingedSpace) _).app
                (SheafOfModules.unit X.ringCatSheaf)).hom (1 : Γ(X, ⊤))))) = a := by
  sorry

end AlgebraicGeometry.Scheme.Modules

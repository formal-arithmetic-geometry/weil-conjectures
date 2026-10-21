/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.Paper.GaloisPartitionModules
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.ZMod.Basic
import Sheaf.Paper.CtfHomLocallyConstant
import Sheaf.Paper.SfHomTriangulated
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Sheaf.Algebra.Homology.BoundedBelowInjectiveResolutionMono
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement
import Sheaf.AlgebraicGeometry.NoetherianCtfFlatModel
import Sheaf.Paper.CtfHomLocalizationDevissage
import Sheaf.Paper.DualizingLocallyClosedInheritance

/-!
# Uniform internal Hom bounds for a fixed Galois partition

Source: ILO, Travaux de Gabber, Expose XVII, Definition 7.6.8 and Proposition 7.6.9,
printed pp. 313--314 (blueprint: lem-per-ctf-hom-condition-b).

The dualizing hypothesis uses the ordinary etale derived Hom and the transpose of
signed evaluation. Its hypothesis is packaged here to avoid importing the downstream coefficient
change theorem merely for its biduality abbreviation.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The dualizing hypothesis in condition (B), written using the existing adjunction
and signed tensor symmetry. The canonical arrow is the transpose of evaluation after
swapping its tensor factors. This local packaging avoids repeatedly elaborating the
same large coefficient-category expression; its data is the displayed formula.
Source: ILO XVII, Proposition 7.6.9 (blueprint: lem-per-ctf-hom-condition-b). -/
def HasConditionBDuality (R : Type (u + 1)) [CommRing R] [Finite R]
    (X : Scheme.{u}) (Q : DerivedCategoryModule R X) : Prop :=
  ∀ M : DerivedCategoryModule R X,
    DerivedCategory.isBoundedConstructible R X M →
    DerivedCategory.isBoundedConstructible R X
      (((derivedHom (ModuleCat.{u + 1} R) X).obj (op M)).obj Q) ∧
    IsIso
      ((derivedTensorHomAdjunction (ModuleCat.{u + 1} R)
        (((derivedHom (ModuleCat.{u + 1} R) X).obj (op M)).obj Q)).homEquiv M Q
          (((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app
            (((derivedHom (ModuleCat.{u + 1} R) X).obj (op M)).obj Q)).app M ≫
              (derivedTensorHomAdjunction (ModuleCat.{u + 1} R) M).counit.app Q))

/-- Condition (B) gives a partition and a cohomological upper bound uniform in the
second argument; the ordinary Hom degree estimate gives the lower endpoint.
No finite-generation assumption is made on the second argument's coefficient stalks.

Source: ILO XVII, Definition 7.6.8 and Proposition 7.6.9, pp. 313--314
(blueprint: lem-per-ctf-hom-condition-b).

Proof:
1. By lem-per-galois-partition-exact-refinement, the partition classes are exact,
extension closed and have common refinements. Apply
lem-sbc-cohomology-in-weak-serre-subcategory to get triangulated derived classes.
2. Consider the first arguments satisfying (B). Internal Hom triangles
(lem-sf-hom-triangulated), their long exact cohomology sequences
(lem-sf-derived-homology-long-exact), and common refinements show that this class
is triangulated: use the larger upper bound, increasing it by one after rotation.
3. Use lem-per-noetherian-ctf-flat-model and its finite stupid filtration to reduce
to flat constructible sheaves. Its model supported in [a,b] gives P in D^{le b}.
4. Use Noetherian induction, including the empty closed subscheme. The dualizing
hypothesis passes to locally closed subschemes by
lem-per-dualizing-locally-closed-inheritance. A flat constructible sheaf is locally
constant on a dense open, where lem-per-ctf-hom-locally-constant applies. Apply the
induction hypothesis on the proper closed complement, then
lem-per-ctf-hom-localization-devissage. This proves (B) for every P.
5. For N in [u,v], apply (B) to N[v]. Shift compatibility gives the upper endpoint
v+c, the output partition, and the constructible clause.
6. Represent N by a complex zero below u and take the bounded-below injective
resolution of lem-weil-pbc-complex-injective-resolution-mono, using
lem-weil-pbc-module-sheaves-enough-injectives. It is K-injective by
lem-weil-pbc-bounded-below-injectives-kinjective. Compute the Hom complex of
def-pur-derived-internal-hom from the model in Step 3. For n<u-b its factors
Hom(F^p,I^{p+n}) vanish: either p>b or p+n<u. Thus r=b works. For P=0 take r=0.
None of these steps imposes finite generation on N. -/
theorem ctf_hom_condition_b
    (ℓ : ℕ) [Fact ℓ.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (Q : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) X)
    (_hQ : DerivedCategory.isBoundedConstructible (ULift.{u + 1} (ZMod ℓ)) X Q)
    (_hdual : HasConditionBDuality (ULift.{u + 1} (ZMod ℓ)) X Q)
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    [Algebra (ZMod ℓ) A]
    (P : DerivedCategoryModule A X)
    (_hP : DerivedCategory.boundedConstructibleFiniteTor A X P) :
    ∃ r : ℤ, _root_.DerivedCategory.IsLE P r ∧
      ∀ partition : Scheme.GaloisPartition X,
        ∃ (partition' : Scheme.GaloisPartition X) (c : ℤ),
          ∀ (u v : ℤ), u ≤ v → ∀ N : DerivedCategoryModule A X,
            partition.boundedDerived A N →
            _root_.DerivedCategory.homologyConcentratedIn u v N →
            partition'.boundedDerived A
              (((derivedHom (ModuleCat.{u + 1} A) X).obj (op P)).obj N) ∧
            _root_.DerivedCategory.homologyConcentratedIn (u - r) (v + c)
              (((derivedHom (ModuleCat.{u + 1} A) X).obj (op P)).obj N) ∧
            (DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X N →
              DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X
                (((derivedHom (ModuleCat.{u + 1} A) X).obj (op P)).obj N)) := by
  sorry

end AlgebraicGeometry.Etale

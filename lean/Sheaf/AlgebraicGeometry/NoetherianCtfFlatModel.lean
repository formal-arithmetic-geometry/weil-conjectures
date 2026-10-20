/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N7
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.ZMod.Basic
import Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModelOfClass
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Sheaf.AlgebraicGeometry.NoetherianConstructibleGaloisPartition
import Sheaf.DeligneLaumon.NoetherianConstructibleFlatLifting

/-!
# Constructible flat models over Noetherian coefficient algebras

Source: Stacks Project, Tag 03TT and remark-projective-each-degree;
ILO, Expose XVII, 7.3.1 and proof of 7.6.1, p. 314
(blueprint: lem-per-noetherian-ctf-flat-model).

Constructibility uses the existing arbitrary-coefficient `Scheme.IsConstructibleSheaf`:
locally constant with finitely generated module stalks on a finite stratification.
On the Noetherian scheme all locally closed subsets are constructible automatically.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- A constructible complex of Tor amplitude `[a,b]` over a Noetherian coefficient
algebra has a flat constructible model in that interval, simultaneously constant with
finite projective values on connected finite etale Galois covers of reduced strata.
Source: Stacks Project, Tag 03TT and remark-projective-each-degree;
ILO, Expose XVII, 7.3.1 and proof of 7.6.1, p. 314
(blueprint: lem-per-noetherian-ctf-flat-model).

Proof plan:
1. Let T be the constructible sheaves. The Noetherian constructible Serre theorem
(lem-sfb-discrete-noetherian-constructible-serre) gives zero, isomorphism, kernel,
cokernel and extension closure. Finite type equals finite presentation by
lem-weil-pbc-noetherian-submodule-finite. Disjoint the finite affine cover, intersect
its pieces with local partitions, and obtain the equivalent global partition notion.
2. Let S be the flat sheaves in T. Zero and isomorphism closure are immediate;
binary biproduct closure follows from extension closure and the direct sum of exact
tensor functors. The lifting square is lem-per-noetherian-constructible-flat-lifting.
3. Apply lem-sf-flat-model-class-resolution with these classes and the given Tor
interval. The bounded-above class resolution, truncated by its cokernel in degree a,
gives F with flat constructible terms, supported in [a,b], and Q(F) isomorphic to K.
4. Apply lem-per-noetherian-constructible-galois-partition to the finite family of
terms in [a,b]. This gives one reduced connected stratification and one connected
finite etale Galois cover per stratum trivializing all terms, with finitely presented
module values. No trivialization of an infinite family is required.
5. Pullback preserves flatness by lem-weil-pbc-ringed-topos-flat-module-pullback,
first to each cover and then to a geometric point. The constant stalk comparison
lem-weil-pbc-constant-sheaf-geometric-stalk is linear (germs commute with scalars),
so each value module is flat. Apply lem-weil-pbc-finitely-presented-flat-module-projective.
Splitting a finite generating surjection exhibits it as a summand of a finite free module.
6. For the empty scheme use the zero complex and empty partition. The sheaf axiom
for the empty covering makes every module sheaf zero. Zero terms elsewhere have
zero projective values, including when a=b. -/
theorem exists_noetherian_ctf_flat_model
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] [Algebra (ZMod l) A]
    (a b : ℤ) (_hab : a ≤ b) (K : DerivedCategoryModule A X)
    (_hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K)
    (_hTor : DerivedCategory.hasTorAmplitudeIn A X a b K) :
    ∃ F : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      Nonempty ((_root_.DerivedCategory.Q).obj F ≅ K) ∧
      (∀ q : ℤ, (q < a ∨ b < q) → IsZero (F.X q)) ∧
      (∀ q : ℤ, ObjectProperty.flat (F.X q) ∧ Scheme.IsConstructibleSheaf (F.X q)) ∧
      ∃ S : Scheme.FiniteLocallyClosedStratification X,
        (∀ i : Fin S.n, IsReduced (S.domain i)) ∧
        ∀ i : Fin S.n, ∃ hS : ConnectedSpace (S.domain i),
          ∃ V : (S.domain i).FiniteEtale,
            @PreGaloisCategory.IsGalois _ _
              (@Scheme.FiniteEtale.galoisCategory (S.domain i) hS) V ∧
            ConnectedSpace V.obj.left ∧
            ∀ q : ℤ, a ≤ q → q ≤ b →
              ∃ M : ModuleCat.{u + 1} A, Module.Finite A M ∧ Module.Projective A M ∧
                Nonempty
                  ((upperStar (ModuleCat.{u + 1} A) (V.obj.hom ≫ S.immersion i)).obj
                      (F.X q) ≅
                    (constantSheaf V.obj.left.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) := by
  sorry

end AlgebraicGeometry.Etale

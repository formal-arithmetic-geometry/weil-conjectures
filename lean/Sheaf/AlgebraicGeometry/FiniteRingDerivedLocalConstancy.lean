/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.AlgebraicGeometry.EtaleDerivedMapPresheaves
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

import WeilConjectures.ConstructibleSheaf.Defs
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.CategoryTheory.Triangulated.TStructure.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Topology.Connected.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
import Sheaf.AlgebraicGeometry.FiniteFreeConstantLocalLift
import Sheaf.RingTheory.FiniteConeFreeModel
import Sheaf.AlgebraicGeometry.ConnectiveSingleHom
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.Paper.FiniteFreeEtaleLocalActual
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.Paper.SiteBoundedConstantModel

/-!
# Finite-ring derived local constancy

Source: Stacks Project, Tag 094G, lemma-locally-constant; the bounded finite-source
extension of Tag 09BE and connected constancy described in the DAG
(blueprint: lem-weil-pbc-finite-ring-derived-local-constancy).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- Bounded finite lisse complexes have finite constant local models, finite lisse
Hom and isomorphism sheaves, and on a connected scheme the model is any geometric fibre.
Source: Stacks, Tag 094G and the finite-source extension of Tag 09BE
(blueprint: lem-weil-pbc-finite-ring-derived-local-constancy).

Proof:
1. Induct on the cohomological interval. Truncate to a bounded representative;
   in a single degree trivialize its finite locally constant cohomology sheaf.
2. Lift finite generators of top cohomology locally to cycles using
   lem-pc-finite-free-constant-local-lift. The cone has a shorter interval and finite
   lisse cohomology by lemma-constructible-flc-serre and the long exact sequence.
3. Apply induction to the cone. Orthogonality and lem-sc-connective-single-hom
   represent the boundary by an ordinary top-degree sheaf map. Make its components
   constant locally using lemma-constructible-hom-constant-locally. Its shifted cone
   is the desired model; TR3 and the long exact sequence identify it with K.
4. Refine the local models for K and L together. Apply lem-pc-ring-finite-cone-free-model
   to obtain a bounded-above finite free resolution of the source model.
5. Cut this resolution sufficiently far below the target's lower bound. Orthogonality
   and lem-weil-pbc-hom-out-of-triangle-exact identify its Hom into the target with
   the original Hom, both algebraically and on every localized site.
6. By lem-weil-pbc-finite-free-etale-local-actual maps are locally chain maps and
   equality is locally homotopy. Make finitely many map and homotopy components
   constant. Geometric stalks detect their equations. The finite algebraic homotopy
   classes compute derived Hom by lem-pc-ring-derived-map-representative.
   lem-weil-pbc-site-sheafification-sections-local glues this identification.
7. An algebraic isomorphism stays invertible under constant sheaves; conversely an
   exact geometric stalk detects invertibility of a constant algebraic map. Thus
   the isomorphism sheaf is the constant subset of algebraic isomorphisms, possibly empty.
8. For connected X the union of images of cover members with a fixed model class
   is open and closed: a nonempty overlap identifies the two classes at a geometric
   stalk. It contains the chosen point, hence is all X. All local models therefore
   identify with the chosen geometric fibre. No finite Tor bound is used. -/
theorem finiteRing_derived_local_constancy
    (X : Scheme.{u}) (B : Type (u + 1)) [CommRing B] [Finite B]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (hbounded : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) n).obj K))
    (hlisse : ∀ n : ℤ, IsFiniteLocallyConstantSheaf
      ((DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) n).obj K)) :
    (∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀,
      ∃ E : CochainComplex (ModuleCat.{u + 1} B) ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) ∧
        (∀ n : ℤ, Finite (E.X n)) ∧ Nonempty
          ((upperStar (ModuleCat.{u + 1} B) (𝒰.f i)).mapDerivedCategory.obj K ≅
            DerivedCategory.Q.obj
              (((constantSheaf (𝒰.X i).smallEtaleTopology
                (ModuleCat.{u + 1} B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj E))) ∧
    (∀ L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero
        ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) n).obj L)) →
      (∀ n : ℤ, IsFiniteLocallyConstantSheaf
        ((DerivedCategory.homologyFunctor
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) n).obj L)) →
      IsFiniteLocallyConstantSheafOfTypes
        ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).obj
          (derivedHomPresheaf B K L)) ∧
      IsFiniteLocallyConstantSheafOfTypes
        ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).obj
          (derivedIsoPresheaf B K L))) ∧
    (∀ (U : Scheme.{u}) (E G : CochainComplex (ModuleCat.{u + 1} B) ℤ),
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (E.X n)) →
      (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n)) →
      (∀ n : ℤ, Finite (E.X n)) → (∀ n : ℤ, Finite (G.X n)) →
      Nonempty
        (((presheafToSheaf U.smallEtaleTopology (Type (u + 1))).obj
          (derivedHomPresheaf B
            (DerivedCategory.Q.obj
              (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj E))
            (DerivedCategory.Q.obj
              (((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj G)))) ≅
          (constantSheaf U.smallEtaleTopology (Type (u + 1))).obj
            (DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj G))) ∧
    (ConnectedSpace X → ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x : Spec (.of Ω) ⟶ X),
      ∃ 𝒰 : Cover.{u} etalePrecoverage X, ∀ i : 𝒰.I₀, Nonempty
        ((upperStar (ModuleCat.{u + 1} B) (𝒰.f i)).mapDerivedCategory.obj K ≅
          (constantSheaf (𝒰.X i).smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj
            ((@Functor.mapDerivedCategory _ _ _ _ _ _ _ _
              (((pointSmallEtale x).ulift.{u + 1}).sheafFiber (A := ModuleCat.{u + 1} B))
              (Functor.additive_of_preserves_binary_products _) _ _).obj K))) := by
  sorry

end AlgebraicGeometry.Etale

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Sheaf.CategoryTheory.LocallyConstantFiniteTypeModules
public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.BoundedAboveRHomHyperExt
import Sheaf.AlgebraicGeometry.ConstructibleExtFilteredColimit

/-!
# Constructible derived internal Hom and uniformly bounded below coproducts

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVII,
proof of Proposition 10.1.1, printed p. 325, first paragraph
(blueprint: lem-per-constructible-rhom-coproduct-continuity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Derived internal Hom from a bounded above complex with constructible cohomology
commutes with coproducts whose summands have a common lower cohomological bound.
The map is induced by applying RHom(K,-) to the coproduct inclusions.
The coefficient ring need only be Noetherian; the target complexes need neither
constructible cohomology nor upper bounds, and K need not have finite Tor amplitude.

Source: ILO, Travaux de Gabber, Expose XVII, proof of Proposition 10.1.1, p. 325,
first paragraph (blueprint: lem-per-constructible-rhom-coproduct-continuity).

Proof:
1. By lem-pur-ringed-site-grothendieck-abelian, filtered colimits of module sheaves
   are exact. Direct sums are filtered colimits of finite biproducts and are exact.
   Lem-kun-grothendieck-derived-coproducts computes the derived coproduct L by
   termwise sums of representatives. Thus H^q(L) is the sum of H^q(L_i), and L is
   bounded below by the same c. For the empty family both sides of the comparison
   vanish, since the Hom complex into zero is zero.
2. Express sums of H^q(L_i) as filtered colimits of finite subsums, using the
   nonempty filtered poset of finite subsets of I. Apply
   lem-per-constructible-ext-filtered-colimit with the given K. Finite sums of
   K-injective resolutions are K-injective: each component of a map from an
   acyclic complex has a null homotopy, and the finite tuple gives a null homotopy.
   The Hom-complex formula therefore proves finite additivity of Ext. Passing
   to the filtered colimit identifies the sums of Ext^p(K,H^q(L_i)) with
   Ext^p(K,H^q(L)), by the canonical inclusions.
3. Apply lem-per-bounded-above-rhom-hyperext with the same r,c to every L_i and L.
   Naturality gives the spectral sequence comparison for the displayed map;
   Step 2 identifies its E2 page. Exact sums commute with kernels, images and
   quotients, so page induction preserves this identification. At (p,q), outgoing
   differentials vanish for s>q-c+1 and incoming ones for s>p+r. Stabilization is
   therefore uniform in i. In total degree n only c<=q<=n+r occur, giving finite
   abutment filtrations of a common length. Exact sums identify their graded
   pieces with the sums of E-infinity terms. Induction on this finite filtration
   gives an isomorphism on the abutment in each degree n.
4. Apply lem-weil-pbc-unbounded-derived-iso-cohomology to these cohomology
   isomorphisms. No upper bound or constructibility of the L_i enters the argument. -/
theorem isIso_sigmaComparison_derivedHom_of_constructible
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (X : Scheme.{u}) [IsNoetherian X] (K : DerivedCategoryModule A X)
    (_hK : ∃ r : ℤ, K.IsLE r)
    (_hc : ∀ j : ℤ, ∃ S : Scheme.FiniteLocallyClosedStratification X,
      ∀ i : Fin S.n, Scheme.IsFiniteLocallyConstantSheaf
        ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj
          ((_root_.DerivedCategory.homologyFunctor _ j).obj K)))
    (I : Type (u + 1)) (L : I → DerivedCategoryModule A X)
    (_hL : ∃ c : ℤ, ∀ i : I, (L i).IsGE c) :
    ∃ hcoprod : HasCoproducts.{u + 1} (DerivedCategoryModule A X),
      IsIso (@sigmaComparison I _ _ _ _
        ((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)) L
        (@HasColimitsOfShape.has_colimit _ _ _ _ (hcoprod I) (Discrete.functor L))
        (@HasColimitsOfShape.has_colimit _ _ _ _ (hcoprod I)
          (Discrete.functor fun i ↦
            ((derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj (L i)))) := by
  sorry

end AlgebraicGeometry.Etale

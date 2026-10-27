/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Sober
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.StrictHenselization
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Sheaf.AlgebraicGeometry.IsRegularScheme
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularRingSmoothAscent
import WeilConjectures.RingTheory.RegularRingNormal
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.FunctionField
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Module.Torsion.Basic
import Sheaf.TraceFormula.ReducedSchemeImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Topology.Constructible
import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# Separated gluing of rationally disjoint smooth trait models

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, 4.3 Proposition 4,
first two proof paragraphs, printed pp. 106–107.
(blueprint: lem-sfb-rationally-disjoint-model-separated-gluing)

The nonexistence hypothesis uses representatives on fibrewise dense opens containing X.
Any representative of a rational identity extends by gluing with the entire generic identity;
these normalized representatives therefore express the same nonexistence condition.
Generic identifications and chart intersections are expressed by cartesian squares.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Rationally disjoint smooth models admit shrinking and separated gluing.
Source: BLR, Néron Models, 4.3 Proposition 4, printed pp. 106–107, first two proof
paragraphs (blueprint: lem-sfb-rationally-disjoint-model-separated-gluing).

Proof plan, following the node's eleven steps:
1. A DVR is regular and Noetherian; smooth ascent and regular-normal imply that the models
are reduced; finite type over a Noetherian trait gives finitely many components. Smoothness
also gives flatness (regular-ring-smooth-ascent, regular-ring-normal, smooth-flat).
2. At the generic point of each integral special fibre the local ring is a DVR with the
same uniformizer: use smooth-geometrically-reduced, fibre-stalk-quotient, and flat torsionfree.
3. Take the reduced schematic closure of each cross diagonal; its generic restriction is
exactly the diagonal (reduced-scheme-image and scheme-image-restrict-open).
4. Near a special generic point, choose an affine with injective germ, hence an integral
neighbourhood. Its graph closure is integral and the projection identifies function fields
(noetherian-injective-germ-neighbourhood and integral-scheme-stalks-in-function-field).
5. A local intermediate subring of the fraction field dominating a DVR is that DVR.
The finite-type-stalk-isomorphism-open-neighbourhood lemma then makes the projection locally
invertible. Gluing this inverse with the generic identity would violate the hypothesis.
6. Chevalley's theorem makes each special projected image constructible, and step 5 says
it omits the special generic point (chevalley-constructible-image).
7. Such a constructible subset of an irreducible Noetherian space has proper closure.
Delete the finitely many closures. Each resulting open retains the generic fibre and the
special generic point; with one model the deleted union is empty.
8. The restricted schematic cross closure has empty special fibre, so it is exactly the
generic diagonal; this is a closed immersion (closed-immersion-base-change).
9. Glue the opens along the common generic fibre (glue-schemes, scheme-morphism-gluing).
The chart intersections are exactly X, and the special fibre is their disjoint coproduct.
10. Smoothness is local on the source; the Noetherian opens are quasi-compact, and finitely
many finite-type charts give finite type (smooth-local-on-source).
11. On the product cover the diagonal is closed on equal charts by separatedness of the
models, and on distinct charts by step 8. Closed immersions are local on the target, so
Y is separated. This checks equal and mixed products, including the one-model case. -/
theorem exists_separated_gluing_of_rationally_disjoint_models
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (π : R) (_hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (E : Type u) [Field E] [Algebra R E] [IsFractionRing R E]
    (X : Scheme.{u}) (x : X ⟶ Spec (.of E))
    [Nonempty X] [Smooth x] [IsSeparated x] [LocallyOfFiniteType x] [QuasiCompact x]
    (r : ℕ) (_hr : 0 < r) (M : Fin r → Scheme.{u})
    (m : ∀ i, M i ⟶ Spec (.of R))
    [∀ i, Smooth (m i)] [∀ i, IsSeparated (m i)]
    [∀ i, LocallyOfFiniteType (m i)] [∀ i, QuasiCompact (m i)]
    (g : ∀ i, X ⟶ M i)
    (hg : ∀ i, IsPullback (g i) x (m i)
      (Spec.map (CommRingCat.ofHom (algebraMap R E))))
    (h_irred : ∀ i, IrreducibleSpace ((m i).fiber (IsLocalRing.closedPoint R)))
    (h_disjoint : ∀ (i j : Fin r), i ≠ j →
      ¬ ∃ (U : (M i).Opens) (f : U.toScheme ⟶ M j) (s : X ⟶ U.toScheme),
        (∀ t : Spec (.of R), Dense ((m i).fiberι t ⁻¹' (U : Set (M i)))) ∧
        f ≫ m j = U.ι ≫ m i ∧ s ≫ U.ι = g i ∧ s ≫ f = g j) :
    ∃ (V : ∀ i, (M i).Opens) (a : ∀ i, X ⟶ (V i).toScheme),
      (∀ i, a i ≫ (V i).ι = g i) ∧
      (∀ (i : Fin r) (ξ : (m i).fiber (IsLocalRing.closedPoint R)),
        IsGenericPoint ((m i).fiberι _ ξ)
          (Set.range ((m i).fiberι (IsLocalRing.closedPoint R))) →
          (m i).fiberι _ ξ ∈ V i) ∧
      (∀ (i j : Fin r), i ≠ j →
        ∃ d : X ⟶ pullback ((V i).ι ≫ m i) ((V j).ι ≫ m j),
          d ≫ pullback.fst _ _ = a i ∧ d ≫ pullback.snd _ _ = a j ∧
          IsClosedImmersion d) ∧
      ∃ (Y : Scheme.{u}) (y : Y ⟶ Spec (.of R))
        (c : ∀ i, (V i).toScheme ⟶ Y) (w : X ⟶ Y),
        Smooth y ∧ IsSeparated y ∧ LocallyOfFiniteType y ∧ QuasiCompact y ∧
        (∀ i, IsOpenImmersion (c i)) ∧
        (∀ i, c i ≫ y = (V i).ι ≫ m i) ∧
        (∀ i, a i ≫ c i = w) ∧
        (∀ p : Y, ∃ (i : Fin r) (q : (V i).toScheme), c i q = p) ∧
        IsPullback w x y (Spec.map (CommRingCat.ofHom (algebraMap R E))) ∧
        (∀ (i j : Fin r), i ≠ j → IsPullback (a i) (a j) (c i) (c j)) ∧
        ∃ z : ∀ i, ((V i).ι ≫ m i).fiber (IsLocalRing.closedPoint R) ⟶
            y.fiber (IsLocalRing.closedPoint R),
          (∀ i, z i ≫ y.fiberι _ = ((V i).ι ≫ m i).fiberι _ ≫ c i) ∧
          Nonempty (IsColimit (Cofan.mk (y.fiber (IsLocalRing.closedPoint R)) z)) := by
  sorry

end AlgebraicGeometry

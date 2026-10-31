/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DualityPairing
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.EtaleSupport
import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.AlgebraicGeometry.ClosedPointField
import WeilConjectures.AlgebraicGeometry.DimensionPreservedFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleDomainPullbackCalculus
import WeilConjectures.AlgebraicGeometry.DeltaRestriction
import WeilConjectures.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSupport
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Constructible
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Properties

/-! # Finite support of the cone of Verdier biduality

Source: literature/blueprint/latest/blueprint/sec-six-functors/
`sk-thm-pd-verdier-duality/det-pd-biduality-finite-support.md` and its proof
(blueprint: det-pd-biduality-finite-support).

The double-dual arrow is extracted from the recorded ambient pairing theorem.
A cone is specified by a distinguished triangle on that arrow, without choosing
representatives. The invertible-exponent condition spells out the coefficient
condition implicit in the source's characteristic different from ell convention.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Etale

/-- Under biduality in dimension at most `d - 1`, the cone of the canonical double-dual
arrow on a proper `d`-dimensional scheme is bounded constructible, with one common
finite set of closed points supporting every cohomology sheaf.

Source: latest blueprint, `sk-thm-pd-verdier-duality/`
`det-pd-biduality-finite-support.md` and `.proof.md`
(blueprint: det-pd-biduality-finite-support).

Proof:
1. Properness gives separatedness and finite type. Apply only the preservation clause
   of lem-sf-finite-ring-geometric-duality twice, to K and its Verdier dual. The cone
   triangle and lem-sf-derived-homology-long-exact express each cone cohomology as an
   extension of a cokernel by a kernel. By thm-constructible-serre it is constructible.
   A common cohomology interval [a,b] for K and its double dual bounds the cone in
   [a-1,b].
2. At a nonclosed x, lem-kun-closed-point-field gives positive transcendence degree.
   Choose an affine neighbourhood V and a finite set of algebra generators, one of
   which has transcendental image in the residue field. That coordinate defines
   V to the affine line and sends x to its generic point. By
   lem-weil-pbc-open-subspace-dimension-monotone, dim V is at most d. Apply
   lem-fin-coordinate-generic-dimension and
   lem-weil-pbc-dimension-preserved-field-extension: the geometric generic fibre has
   dimension at most d-1 and is separated of finite type over the algebraic closure
   of k(t).
3. Pullback preserves bounded constructibility and the Tor interval by
   lem-coef-etale-domain-pullback-calculus. The coefficient exponent remains invertible
   after field extension. Apply the induction hypothesis there.
   det-pd-generic-dualizing-twist identifies the pulled-back double-dual arrow with
   biduality on the geometric generic fibre, locally on V; the twist and shift cancel
   on double Hom. lem-weil-delta-restriction compares it with restriction of delta_K.
   Exact inverse image (prop-weil-pbc-inverse-image-modules-exact) commutes with
   cohomology (lem-weil-pbc-exact-functor-complex-cohomology).
   lem-weil-pbc-etale-cover-detects-iso and
   lem-weil-pbc-unbounded-derived-iso-cohomology give invertibility globally.
4. Apply exact derived pullback to the cone triangle, using
   lem-weil-pbc-exact-functor-derived-factorization and the cohomology sequence.
   All its pulled-back cohomology sheaves vanish. Embed the algebraic closure of
   k(t) into an algebraic closure of kappa(x), by
   lem-weil-pbc-algebraic-extension-embeds-algebraically-closed. The fibre-product
   property gives a lift of this geometric point to the geometric generic fibre.
   lemma-openclosed-stalk-upperstar then gives a zero stalk above x, and
   lem-weil-pbc-constructible-module-support-constructible makes x absent from the
   support. Thus every cohomology support consists only of closed points.
5. X is Noetherian by lem-weil-pbc-finite-type-over-noetherian. Each support is
   constructible by lem-weil-pbc-constructible-module-support-constructible. Express
   it as a finite union of open intersections with closed subsets. Each closed
   subset has finitely many irreducible components by
   lem-sc-noetherian-closed-subset-finite-components. A component meeting the open
   contains its generic point there (lem-sc-scheme-sober); that point is closed in X,
   so the component is a singleton. Each support is therefore finite. Unite these
   sets over the finite cohomology interval from step 1 to obtain the common S.
-/
theorem biduality_cone_boundedConstructible_finiteSupport
    (A : Type (u + 1)) [CommRing A] [Finite A] (d : ℕ) (hd : 1 ≤ d)
    (ih : ∀ (k' : Type u) [Field k'] [IsAlgClosed k']
      [HasInvertibleExponent A (Spec (.of k'))]
      (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k'))
      [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY],
      topologicalKrullDim Y ≤ (d - 1 : ℕ) →
      ∀ (L : DerivedCategoryModule A Y),
        DerivedCategory.isBoundedConstructible A Y L →
        (∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A Y a b L) →
        IsIso (AmbientDualityPairing.bidualityMap (ModuleCat.{u + 1} A) Y
          (ambient_duality_pairing A aY).1 L))
    {k : Type u} [Field k] [IsAlgClosed k]
    [HasInvertibleExponent A (Spec (.of k))]
    (X : Scheme.{u}) (aX : X ⟶ Spec (.of k)) [IsProper aX]
    (hX : topologicalKrullDim X = (d : ℕ))
    (K : DerivedCategoryModule A X)
    (hK : DerivedCategory.isBoundedConstructible A X K)
    (hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A X a b K)
    (Δ : DerivedCategoryModule A X)
    (g : (dualityDoubleFunctor (derivedHom (ModuleCat.{u + 1} A) X)
      (dualizingComplex A aX)).obj K ⟶ Δ)
    (h : Δ ⟶ K⟦(1 : ℤ)⟧)
    (hΔ : Triangle.mk (AmbientDualityPairing.bidualityMap (ModuleCat.{u + 1} A) X
      (ambient_duality_pairing A aX).1 K) g h ∈ distTriang _) :
    DerivedCategory.isBoundedConstructible A X Δ ∧
      ∃ S : Set X, S.Finite ∧ S ⊆ closedPoints X ∧
        ∀ q : ℤ, Scheme.etaleSheafSupport
          ((sheafCompose X.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1})).obj
              ((_root_.DerivedCategory.homologyFunctor
                (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj Δ)) ⊆ S := by
  sorry

end AlgebraicGeometry.Etale

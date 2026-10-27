module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.NoetherianSpace
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Stalk
import WeilConjectures.AlgebraicGeometry.Regular
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.DedekindDomain.Dvr
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Height

/-! # Extending a generic morphism to a fibrewise dense big open

Source: Bosch--Lutkebohmert--Raynaud, Neron Models, 1.2 Proposition 8,
proof before Weil extension, printed p.15 (PDF p.21); local spreading in 1.2 Lemma 5.
(blueprint: lem-sfb-proper-generic-map-big-open)

The generic inclusion is named `η`, with its composite into `Spec D` prescribed.
Base change uses the recorded `Over.pullback` conventions. Equality of the generic
open with the entire generic fibre means that its canonical inclusion is an isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A generic morphism to a proper relative target extends on a fibrewise dense open
containing every point whose local ring has dimension at most one.

Source: BLR, Neron Models, 1.2 Proposition 8, proof before Weil extension,
printed p.15 (PDF p.21), and 1.2 Lemma 5.
(blueprint: lem-sfb-proper-generic-map-big-open)

Proof plan from the accepted DAG split:
1. The empty source is immediate. Otherwise localization of the normal domain D
   makes T normal (lem-weil-pbc-localization-normal-domain). Smooth normal ascent
   (lem-sfb-smooth-normal-ascent), smooth flatness (lem-pc-smooth-flat), and locally
   Noetherian ascent (pqf-lem-locnoeth-lft, pqf-def-locnoeth) make X normal and
   Noetherian. Its finitely many components are clopen and integral
   (lem-sc-noetherian-finite-irreducible-components,
   lem-sfb-normal-locally-finite-components). Openness of the structure map
   (lem-weil-pbc-flat-lfp-open) makes each component's generic fibre dense;
   its generic point lies over the generic point of T (lem-sc-scheme-sober).
2. On a component C, restrict f_E to Spec k(C). At each generic-fibre point z,
   the canonical local-spectrum morphism factors through X_E, by the local-ring
   morphism classification (lem-weil-pbc-morphism-from-spec-local-ring,
   lem-weil-pbc-spec-local-ring-canonical-morphism, def-pc-base-change).
   Its restriction to the function field is the same component map
   (lem-sc-integral-scheme-stalks-in-function-field).
3. At a vertical point of local dimension at most one the normal local domain
   cannot have dimension zero, so it is a DVR (lem-sc-normal-dim1-dvr,
   def-sc-discrete-valuation-ring). Its fraction field is k(C). The canonical
   local-spectrum maps give a commuting valuative square by the same local-ring
   classification. Proper valuative existence extends the component map over
   this stalk (lemma-nagata-proper-valuative-criterion-existence-api).
4. Spread these stalk maps to neighbourhoods (lem-sfb-local-ring-map-spread).
   Properness supplies local finite type and relative separatedness
   (def-weil-proper-morphism). On their integral generic fibres the extensions
   agree with f_E at the function field, hence everywhere by
   lem-sfb-relative-separated-dominant-ext, using
   lem-sc-integral-scheme-stalks-in-function-field and localization normality.
5. On each overlap, the dense generic fibre and reduced source give equality
   by lem-sfb-relative-separated-dominant-ext. Distinct components are disjoint.
   Glue (lem-weil-pbc-scheme-morphism-gluing) to v on the union V. It is over T,
   contains the whole generic fibre and all points of local dimension at most
   one, and restricts to f_E.
6. At a nongeneric point t of T, its local ring is a DVR
   (lem-sc-dedekind-localization-dvr). For a component generic point ξ of X_t,
   the fibre-stalk quotient (lem-sbc-scheme-fibre-stalk-quotient) identifies the
   fibre stalk with O_{X,ξ}/π. Its only prime is maximal, so the maximal ideal
   of O_{X,ξ} is minimal over (π), using the local-spectrum description
   (lem-weil-pbc-spec-local-ring-canonical-morphism, lem-sc-scheme-sober).
   The principal ideal height bound (lem-sfb-krull-principal-ideal-height-bound)
   and localization dimension formula
   (lem-weil-pbc-localization-dimension-chains-below-prime) give dimension at most
   one. Thus ξ belongs to V.
7. Every nongeneric fibre has all its component generic points in V, hence V_t
   is dense. The generic fibre is entirely in V. Empty fibres are automatic. -/
theorem proper_generic_map_big_open
    (D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D]
    [IsIntegrallyClosed D] (hD : ringKrullDim D = 1)
    (E : Type u) [Field E] [Algebra D E] [IsFractionRing D E]
    (T : (Spec (.of D)).Opens) (hT : Nonempty T)
    (η : Spec (.of E) ⟶ T.toScheme)
    (hη : η ≫ T.ι = Spec.map (CommRingCat.ofHom (algebraMap D E)))
    (X Y : Over T.toScheme) [IsAffine X.left] [Smooth X.hom] [IsProper Y.hom]
    (fE : (Over.pullback η).obj X ⟶ (Over.pullback η).obj Y) :
    ∃ (V : X.left.Opens) (v : Over.mk (V.ι ≫ X.hom) ⟶ Y),
      IsIso (((Over.pullback η).map
        (Over.homMk V.ι rfl : Over.mk (V.ι ≫ X.hom) ⟶ X)).left) ∧
      (Over.pullback η).map v = (Over.pullback η).map
        (Over.homMk V.ι rfl : Over.mk (V.ι ≫ X.hom) ⟶ X) ≫ fE ∧
      (∀ x : X.left, ringKrullDim (X.left.presheaf.stalk x) ≤ 1 → x ∈ V) ∧
      ∀ t : T.toScheme, Dense ((X.hom.fiberι t) ⁻¹' (V : Set X.left)) := by
  sorry

end AlgebraicGeometry

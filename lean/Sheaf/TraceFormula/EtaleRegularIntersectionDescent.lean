module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.RingTheory.Etale.LocalDimension
import Sheaf.RingTheory.FlatUnderRegular

/-!
# Étale descent of regular intersections and codimension

Source: Stacks Project, Étale Morphisms, Tags 025N, 039S and 02GO,
and the local strict-normal-crossings criterion in the blueprint unit
(blueprint: lem-trf-etale-regular-intersection-descent).

The finite intersection is constructed by iterating the chosen scheme pullbacks.
Codimension is represented by `Order.coheight`, whose defining supremum is the
supremum of lengths of strict specialization chains.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
A scheme equipped with its structure morphism to a fixed scheme.
Source: the fibre-product construction in Stacks Tag 01JP
(blueprint: lem-trf-etale-regular-intersection-descent).
-/
structure SchemeOver (X : Scheme.{u}) where
  carrier : Scheme.{u}
  map : carrier ⟶ X

/--
Iterated fibre product of a finite family of schemes over `X`, with the empty
intersection equal to `X`.
Source: Stacks Tag 01JP (blueprint: lem-trf-etale-regular-intersection-descent).
-/
def intersectionData {X : Scheme.{u}} {n : ℕ}
    (D : Fin n → Scheme.{u}) (i : (j : Fin n) → D j ⟶ X) :
    Finset (Fin n) → SchemeOver X
  | J =>
      if h : J.Nonempty then
        let j : Fin n := J.min' h
        let prev : SchemeOver X := intersectionData D i (J.erase j)
        { carrier := pullback prev.map (i j)
          map := pullback.fst prev.map (i j) ≫ prev.map }
      else
        { carrier := X, map := 𝟙 X }
termination_by J => J.card
decreasing_by
  exact Finset.card_erase_lt_of_mem (Finset.min'_mem J h)

/-- The scheme-theoretic intersection indexed by a finite set.
Source: Stacks Tag 01JP (blueprint: lem-trf-etale-regular-intersection-descent).
-/
def intersectionScheme {X : Scheme.{u}} {n : ℕ}
    (D : Fin n → Scheme.{u}) (i : (j : Fin n) → D j ⟶ X)
    (J : Finset (Fin n)) : Scheme.{u} :=
  (intersectionData D i J).carrier

/-- The canonical map from an iterated intersection to its ambient scheme.
Source: Stacks Tag 01JP (blueprint: lem-trf-etale-regular-intersection-descent).
-/
def intersectionMap {X : Scheme.{u}} {n : ℕ}
    (D : Fin n → Scheme.{u}) (i : (j : Fin n) → D j ⟶ X)
    (J : Finset (Fin n)) : intersectionScheme D i J ⟶ X :=
  (intersectionData D i J).map

/-- Base change of an intersection to the spectrum of a stalk.
Source: Stacks Tag 02GO (blueprint: lem-trf-etale-regular-intersection-descent).
-/
def localIntersection {X : Scheme.{u}} {n : ℕ}
    (D : Fin n → Scheme.{u}) (i : (j : Fin n) → D j ⟶ X)
    (J : Finset (Fin n)) (W : Scheme.{u}) (v : W ⟶ X) (w : W) : Scheme.{u} :=
  pullback (intersectionMap D i J) (W.fromSpecStalk w ≫ v)

/-- The projection from a stalk-local intersection to the stalk spectrum.
Source: Stacks Tag 02GO (blueprint: lem-trf-etale-regular-intersection-descent).
-/
def localIntersectionProjection {X : Scheme.{u}} {n : ℕ}
    (D : Fin n → Scheme.{u}) (i : (j : Fin n) → D j ⟶ X)
    (J : Finset (Fin n)) (W : Scheme.{u}) (v : W ⟶ X) (w : W) :
    localIntersection D i J W v w ⟶ Spec (.of (W.presheaf.stalk w)) :=
  pullback.snd (intersectionMap D i J) (W.fromSpecStalk w ≫ v)

/--
Étale-local regularity and expected codimension descend for all finite
scheme-theoretic intersections (blueprint: lem-trf-etale-regular-intersection-descent).

Proof (Stages 3 will fill the details), following Tags 025N, 039S and 02GO:
1. Describe each finite intersection on affine charts as the quotient by the sum
   of the defining ideals, and identify its stalk after the étale base change.
2. Apply flat descent of regularity for the resulting flat local stalk map.
3. At the generic point of each irreducible component, use étale invariance of
   local Krull dimension and the component codimension hypothesis.
4. Translate the local dimension at the generic point into the chain-supremum
   codimension in `X`, proving the assertion for every component.
-/
theorem etale_regular_intersection_descent
    {X : Scheme.{u}} [IsLocallyNoetherian X] {n : ℕ}
    (D : Fin n → Scheme.{u}) (i : (j : Fin n) → D j ⟶ X)
    (hclosed : ∀ j : Fin n, IsClosedImmersion (i j))
    (hlocal : ∀ (x : X) (J : Finset (Fin n)),
      ∃ (W : Scheme.{u}) (v : W ⟶ X) (w : W),
        Etale v ∧ v w = x ∧
        let P : Scheme.{u} := localIntersection D i J W v w
        IsLocallyNoetherian P ∧
        (∀ z : P, IsRegularLocalRing (P.presheaf.stalk z)) ∧
        (∀ z : P, closure ({z} : Set P) ∈ irreducibleComponents P →
          Order.coheight (localIntersectionProjection D i J W v w z) = (J.card : ℕ∞))) :
    ∀ J : Finset (Fin n),
      IsLocallyNoetherian (intersectionScheme D i J) ∧
      (∀ z : intersectionScheme D i J,
        IsRegularLocalRing ((intersectionScheme D i J).presheaf.stalk z)) ∧
      (∀ z : intersectionScheme D i J,
        closure ({z} : Set (intersectionScheme D i J)) ∈
            irreducibleComponents (intersectionScheme D i J) →
          Order.coheight (intersectionMap D i J z) = (J.card : ℕ∞)) := by
  sorry

end AlgebraicGeometry

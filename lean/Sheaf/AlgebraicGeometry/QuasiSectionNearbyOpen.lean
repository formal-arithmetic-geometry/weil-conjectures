module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Sober
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Sheaf.RingTheory.PuncturedLocalClosedPoints
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.ClosedFibrePointQuasiFiniteCriterion

/-!
# An integral quasi-section meeting a nearby open

Source: Stacks Project, More on Morphisms, Tag 05GU,
`lemma-quasi-finite-quasi-section-meeting-nearby-open-X`, statement and reduced-closure
construction in its proof, together with Tag 05GT
(blueprint: lem-sfb-quasi-section-nearby-open).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A closed fibre point with a generalization in a prescribed open, outside its fibre,
lies on an integral closed subscheme whose generic point lies in that open and outside
that fibre, and which is quasi-finite over the base at the point above the original point.

Source: Stacks Project, More on Morphisms, Tags 05GU and 05GT,
`lemma-quasi-finite-quasi-section-meeting-nearby-open-X` and its preceding local-ring lemma.
The integral and generic-point clauses record the source's reduced-closure construction.
(blueprint: lem-sfb-quasi-section-nearby-open)

Proof plan:
1. By pqf-lem-locnoeth-lft, X is locally Noetherian. Choose a Noetherian affine chart
   Spec R about x (pqf-def-locnoeth). The local ring B at x is R localized at the prime
   of x, by lem-weil-pbc-spec-local-ring-canonical-morphism. It is Noetherian by
   lem-weil-pbc-localization-noetherian and nonzero because that prime is proper.
   The canonical map c : Spec B → X sends the closed point to x and has image exactly
   the generalizations of x.
2. Put A = O_{S,f(x)}. The local-ring map induced by f makes f composed with c factor
   through Spec A, by lem-weil-pbc-morphism-from-spec-local-ring. Only the maximal
   ideal of A maps to f(x), by lem-weil-pbc-primes-of-localization. Thus the inverse
   image of V, minus the zero locus of the extended maximal ideal of A, is an open W
   in the punctured spectrum of B. It is nonempty because the given generalization
   lifts under c and does not map to f(x).
3. Apply lem-per-punctured-local-closed-points to W to choose q closed in the puncture.
   The only primes containing q are q and the maximal ideal of B. The image b = c(q)
   belongs to V, does not map to f(x), and specializes to x.
4. Give the closure of b its reduced induced closed subscheme structure i : Z → X
   using lem-weil-pbc-reduced-induced-closed-subscheme. This closure contains x and
   is nonempty and irreducible. Hence Z is integral (def-pc-integral-scheme), and
   the point z above b is generic. The closed-immersion homeomorphism identifies the
   closure of i(z) with the image of i (def-weil-closed-immersion).
5. Let a be the point of Z above x. In the affine chart from step 1, the prime
   correspondence of lem-weil-pbc-primes-of-localization shows that every
   generalization of a is either a or z. The point a is closed in the fibre Z_{f(x)},
   since the induced closed immersion embeds it into X_{f(x)}, where x is closed
   (def-pc-scheme-fibre, def-weil-closed-immersion). As z is outside that fibre, a has
   no other generalization in it.
6. The composite i followed by f is locally of finite type: its affine rings are
   quotients of the finite-type affine rings of f, so their algebra generators are
   the images of those generators (lem-weil-pbc-lft-affine-pairs). Apply
   lem-sfb-closed-fibre-point-quasifinite-criterion to a. This supplies the remaining
   quasi-finiteness clause; the witnesses of step 4 supply all other conclusions.
-/
theorem exists_integral_closed_quasiSection_nearby_open
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (x : X)
    (hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x)))) (V : X.Opens)
    (hnearby : ∃ x' : X, x' ∈ V ∧ x ∈ closure ({x'} : Set X) ∧ f x' ≠ f x) :
    ∃ (Z : AlgebraicGeometry.Scheme.{u}) (i : Z ⟶ X),
      IsIntegral Z ∧ IsClosedImmersion i ∧
        ∃ z a : Z, IsGenericPoint z (Set.univ : Set Z) ∧ i a = x ∧
          i z ∈ V ∧ f (i z) ≠ f x ∧ (i ≫ f).IsQuasiFiniteAtPoint a ∧
          closure ({i z} : Set X) = Set.range i := by
  sorry

end AlgebraicGeometry.Scheme.Hom

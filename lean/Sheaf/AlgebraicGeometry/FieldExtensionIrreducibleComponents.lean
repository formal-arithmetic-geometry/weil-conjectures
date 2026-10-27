module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.Irreducible
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Sober
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.FieldTheory.FieldTensorUniqueMinimalPrime
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IsSepClosed

/-!
# Irreducible components under extension of the ground field

Source: Stacks Project, Varieties, Tags 04KW and 04KX
(blueprint: lem-sfb-field-extension-irreducible-components).

The projection has nonempty inverse images of components, each a union of components.
Its actual set-theoretic images define a surjection on irreducible components.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For an arbitrary field extension, inverse images of irreducible components are nonempty
unions of components, and actual images of components are components, surjectively.
Source: Stacks Project, Varieties, Tags 04KW and 04KX
(blueprint: lem-sfb-field-extension-irreducible-components).

The last two conjuncts express well-definedness and surjectivity of the assignment
`C ↦ p '' C`, without choosing any component or taking the closure of its image.

Proof:
1. For any field extension E/F and F-scheme Y, the projection Y_E to Y is flat and surjective:
apply flatness and surjectivity of Spec E to Spec F and their stability under base change. A
component has a generic point by sobriety. In a scheme, a point is component-generic exactly when
it has no proper generalization: a generalization of a component-generic point has irreducible
closure containing that component, hence the same closure and the same point by sobriety;
conversely place the closure of the point inside a component and use its generic point. We will
use this criterion throughout. Each component-generic point w of Y_E maps to a component-generic
point of Y: if z' is a generalization of z=r(w), generalizations lift along the flat map r, giving
a generalization w' of w with r(w')=z'; the criterion gives w'=w, so z'=z, and the criterion makes
z component-generic. These assertions apply without any finiteness assumptions.
Uses: lem-pc-field-extension-flat, lem-weil-pbc-flat-morphism-base-change, lem-pc-field-extension-
surjective, lem-weil-pbc-surjective-base-change, lem-weil-pbc-scheme-sober, lem-sc-irreducible-
components-cover, def-sc-generic-point, def-weil-irreducible-components, lem-weil-pbc-flat-
generalizations-lift.

2. Fix a component T of X, with generic point eta. Choose a closed subscheme i:Z to X whose image
is T. Its field base change Z_K to X_K is a closed immersion. Its image is exactly p^{-1}(T): one
inclusion follows from the commuting square; for the converse a point w of X_K above t in T gives
Spec kappa(w) to X factoring through Z. Indeed, locally i is Spec(A/I) to Spec A and the prime for
t contains I, so A to kappa(w) kills I. Pair this factorization with Spec kappa(w) to Spec K in
the fibre-product universal property. Thus |Z_K| is identified with p^{-1}(T). Flatness is not
needed for this identification.
Uses: lem-weil-pbc-closed-subset-closed-subscheme, lem-weil-pbc-closed-immersion-base-change, def-
weil-closed-immersion, def-weil-residue-field, def-pc-scheme-fibre, def-pc-fibre-product.

3. Let B be an irreducible component of Z_K and xi its generic point. Applying the generic-point
image assertion from step 1 to the K/k extension of Z shows that xi maps to eta, since Z is
irreducible. If xi' is a generalization of xi in X_K, its image generalizes eta. By the criterion
of step 1, eta has no proper generalization in X, so p(xi')=eta and xi' lies in p^{-1}(T)=|Z_K|.
The subspace topology of the closed immersion makes it a generalization there as well. Since xi is
component-generic in Z_K, xi'=xi. The criterion now makes xi component-generic in X_K, and
closedness of |Z_K| identifies the two closures of xi. Hence B is a component of X_K. The
components cover Z_K, so p^{-1}(T) is a union of components of X_K. It is nonempty because p is
surjective and T is nonempty.
Uses: lem-weil-pbc-flat-generalizations-lift, lem-weil-pbc-scheme-sober, lem-sc-irreducible-
components-cover, def-weil-closed-immersion, def-sc-generic-point, def-weil-irreducible-
components.

4. First prove the image assertion when E/F is algebraic, for an arbitrary F-scheme Y. The map
Spec E to Spec F is integral: an algebraic element satisfies a nonzero polynomial over a field,
and division by its leading coefficient makes the equation monic. Its base change r:Y_E to Y is
integral, hence universally closed, in particular closed. For a component B of Y_E with generic
point xi, step 1 makes r(xi) component-generic in Y. Let T be its component. Continuity gives r(B)
contained in the closure of {r(xi)}, namely T. Closedness of r gives the reverse inclusion since
r(B) contains r(xi). Therefore the actual image r(B), not just its closure, equals T.
Uses: def-weil-finite-integral-morphism, lem-sbc-integral-morphism-base-change, pqf-lem-integral-
univclosed, def-weil-proper-morphism, lem-weil-pbc-flat-generalizations-lift, lem-weil-pbc-scheme-
sober, def-sc-generic-point.

5. For an algebraic extension E/F, the component map just constructed is surjective. Given a
component T of Y, steps 2--3 give a nonempty union of components inside r^{-1}(T). Choose one, B.
Step 4 makes r(B) a component, and r(B) is contained in T. Maximality of an irreducible component
forces r(B)=T. This argument also covers algebraic extensions of infinite degree.
Uses: def-weil-irreducible-components.

6. We also need the component bijection over a separably closed field F. If E/F is any extension
and Y is an F-scheme, the fibre of r:Y_E to Y at y is Spec(kappa(y) tensor_F E): compose the
fibre-product universal properties and then use the affine-spectrum tensor description. The field-
tensor lemma makes this fibre irreducible and nonempty because F is separably closed. The scheme-
theoretic fibre has the topology of r^{-1}(y), and r is open because schemes over a field are
universally open. The continuous open-map theorem with irreducible fibres therefore gives mutually
inverse maps B maps to r(B) and T maps to r^{-1}(T) on components. In particular these are actual
images. This proves the comparison needed below using the existing tensor and topological lemmas,
rather than introducing a node for a clause of the item.
Uses: def-pc-scheme-fibre, def-pc-fibre-product, def-weil-residue-field, lem-weil-pbc-fibre-
product-affine-spectra, lem-weil-pbc-field-tensor-irreducible, lem-sc-scheme-over-field-
universally-open, lem-sc-open-map-irreducible-fibres-components.

7. Return to arbitrary K/k. Choose an algebraic closure Omega of K and let A be the subfield of
elements of Omega algebraic over k. The relative-algebraic-closure lemma makes A algebraically
closed, hence separably closed: a nonconstant polynomial splits into linear factors by successive
root extraction and division, so in particular every separable polynomial splits. We have
compatible inclusions k into A into Omega and K into Omega. Write a:X_Omega to X_K, b:X_Omega to
X_A, and c:X_A to X. Fibre-product functoriality gives p composed with a = c composed with b. For
a component C of X_K, step 5 for the algebraic extension Omega/K provides a component D of X_Omega
with a(D)=C. Step 6 over A makes b(D) a component of X_A. Step 4 for the algebraic extension A/k
makes c(b(D)) a component of X. The commuting equality gives p(C)=p(a(D))=c(b(D)), proving the
actual-image assertion for every C.
Uses: lem-pc-algebraic-closure-exists-unique, lem-weil-pbc-relative-algebraic-closure-algclosed,
def-weil-algebraic-closure, def-kun-separably-closed, def-pc-fibre-product.

8. Finally, for a component T of X choose a component C contained in the nonempty union p^{-1}(T)
from step 3. Step 7 makes p(C) a component of X contained in T, so maximality gives p(C)=T. Thus C
maps to p(C) is a well-defined surjection on components. If X is empty, both component sets are
empty and the assertion about individual T is vacuous.
Uses: def-weil-irreducible-components. -/
theorem field_extension_irreducible_components
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) :
    (∀ T ∈ irreducibleComponents X,
      ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⁻¹' T).Nonempty ∧
      ∃ S : Set (Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))),
        S ⊆ irreducibleComponents
          ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ⁻¹' T = ⋃₀ S) ∧
    (∀ C ∈ irreducibleComponents
        ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) '' C ∈
        irreducibleComponents X) ∧
    (∀ T ∈ irreducibleComponents X,
      ∃ C ∈ irreducibleComponents
          ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) '' C = T) := by
  sorry

end AlgebraicGeometry

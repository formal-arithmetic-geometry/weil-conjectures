module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.Constructible
public import Sheaf.AlgebraicGeometry.RingedSubspace

import Sheaf.AlgebraicGeometry.FlatMonomorphismLocalStructure
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.AlgebraicGeometry.InverseImageStructureStalkIso
import Sheaf.AlgebraicGeometry.StalkIsomorphismLifting

/-! # Ringed images of quasi-compact flat monomorphisms

Source: Raynaud, Un critère d'effectivité de descente, §1, Propositions 1.1 and 1.2(i),
Corollary 1.3, printed pp. 1–2; Stacks Project, Tags 081I and 03HV.
(blueprint: lem-sfb-qc-flat-monomorphism-ringed-image)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A quasi-compact flat monomorphism is its inverse-image ringed subspace, and represents
maps whose image is contained in its image. Its image is generalization stable and
retrocompact; another such morphism with the same image is uniquely isomorphic over the base.

Source: Raynaud, §1, Propositions 1.1 and 1.2(i), Corollary 1.3, printed pp. 1–2;
Stacks Project, Tags 081I and 03HV.
(blueprint: lem-sfb-qc-flat-monomorphism-ringed-image).

Proof plan:
1. Monicity makes the diagonal invertible by the pullback universal property.
   Apply lem-per-flat-monomorphism-local-structure: the point map is injective and
   every actual structural stalk map is invertible.
2. For a closed subset C of X, choose its closed subscheme Z using
   lem-weil-pbc-closed-subset-closed-subscheme. The composite Z to S is quasi-compact
   (def-weil-finite-type-morphism, def-weil-closed-immersion), so has a schematic image F
   (lemma-nagata-scheme-image-ideal-qc). Flat base change of schematic images
   (lem-sfb-scheme-image-flat-base-change) and monicity identify F times_S X with Z;
   use lemma-nagata-scheme-image-of-closed-immersion for the last identification.
3. The affine quotient description in def-weil-closed-immersion gives f⁻¹(F) = C.
   By injectivity, f(C) = range(f) ∩ F. Hence the continuous bijection X to range(f)
   is closed and is a homeomorphism for the subspace topology.
4. Transpose the structural sheaf map along def-weil-pbc-topological-inverse-image.
   By lem-pc-inverse-image-structure-stalk-iso its stalk maps are those of f, hence
   isomorphisms. The stalk criterion lem-weil-pbc-sets-sheaf-iso-on-stalks makes the
   transpose an isomorphism of sheaves (the inverse preserves ring operations and
   restrictions). Transport across the homeomorphism identifies the actual sheaf of X
   with the inverse-image sheaf in def-a1-ringed-subspace. Locality of its stalks and
   def-weil-locally-ringed-space-morphism give the locally ringed isomorphism over S.
5. Generalizations lift along flat maps (lem-weil-pbc-flat-generalizations-lift).
   For a quasi-compact open U, quasi-compactness of f makes f⁻¹(U) quasi-compact;
   its continuous image is range(f) ∩ U, proving retrocompactness, including U empty.
6. If g has image in range(f), restrict its codomain and compose with the inverse
   homeomorphism to get a continuous lift. Apply new-lem-zl-stalk-isomorphism-lifting
   to obtain a scheme lift, unique by monicity. A factorization implies image containment.
7. Apply the lifting criterion to two morphisms with equal images in both directions.
   Cancel the monomorphisms to see that the lifts are inverse, and cancel once more
   for uniqueness of the isomorphism over S. No finiteness or separation is used.
-/
theorem quasiCompact_flat_monomorphism_ringed_image
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [Flat f] [Mono f] :
    (∃ hlocal : ∀ x : Set.range f,
        IsLocalRing ((LocallyRingedSpace.ringedSubspace
          S.toLocallyRingedSpace (Set.range f)).presheaf.stalk x),
      ∃ e : X.toLocallyRingedSpace ≅ LocallyRingedSpace.locallyRingedSubspace
          S.toLocallyRingedSpace (Set.range f) hlocal,
        e.hom.toShHom ≫ LocallyRingedSpace.ringedSubspaceι
          S.toLocallyRingedSpace (Set.range f) = f.toLRSHom.toShHom) ∧
    StableUnderGeneralization (Set.range f) ∧
    IsRetrocompact (Set.range f) ∧
    (∀ (T : Scheme.{u}) (g : T ⟶ S),
      (∃! a : T ⟶ X, a ≫ f = g) ↔ Set.range g ⊆ Set.range f) ∧
    (∀ (Y : Scheme.{u}) (g : Y ⟶ S) [QuasiCompact g] [Flat g] [Mono g],
      Set.range g = Set.range f → ∃! e : X ≅ Y, e.hom ≫ g = f) := by
  sorry

end AlgebraicGeometry

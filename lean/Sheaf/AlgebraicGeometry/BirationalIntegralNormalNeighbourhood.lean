/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Topology.Sober
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.AlgebraicGeometry.StructureSheaf
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Topology.Irreducible

/-!
# Integral neighbourhoods for a birational morphism at a normal point

Source: Stacks Project, Varieties, Tag 0BFP,
lemma-modification-normal-iso-over-codimension-1, first paragraph of proof (4);
Properties, Tag 0BX3, lemma-ring-affine-open-injective-local-ring.
(blueprint: lem-sfb-birational-integral-normal-neighbourhood)
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A birational morphism with reduced source admits an integral affine neighbourhood of
any normal point of a locally Noetherian target, with integral entire inverse image.
The restriction remains birational, in the component-generic-point and stalk-map sense.

Source: Stacks Project, Varieties, Tag 0BFP, proof (4), first paragraph; Properties,
Tag 0BX3 (blueprint: lem-sfb-birational-integral-normal-neighbourhood).

Proof:
1. Use `lem-sfb-noetherian-injective-germ-neighbourhood` to choose an affine neighbourhood
   with injective germ map. The normal local ring is a domain: localize at its maximal
   ideal in `def-weil-pbc-normal-ring`; that localization is the local ring itself.
   The section ring embeds in this domain and is therefore a domain. By clause (2) of
   `lem-weil-pbc-spec-domain-stalks-function-field`, the affine neighbourhood is integral.
2. Its irreducibility and `lem-sc-components-open-injection` imply that exactly one
   component of the target meets it; existence follows from
   `lem-sc-irreducible-components-cover`. By `lem-sc-scheme-sober` this component has a
   unique generic point. Every open meeting its closure contains that point, so it lies
   in the neighbourhood. Birationality gives a unique component-generic point of the
   source over it, proving that the entire inverse image is nonempty.
3. Every point of that inverse image lies in a component by
   `lem-sc-irreducible-components-cover`. Its generic point exists by
   `lem-sc-scheme-sober` and belongs to the same inverse image, since it generalizes the
   chosen point. Its image must be the unique target component-generic point in the
   neighbourhood. Injectivity on generic points identifies it with the point in step 2.
   Thus that point is generic for the entire inverse image, which is irreducible.
4. An open subscheme of a reduced scheme is reduced (`def-pc-reduced-scheme`,
   `def-weil-open-immersion`): its stalks are unchanged, since neighbourhoods contained
   in the open are cofinal in all neighbourhoods (`def-weil-pbc-module-stalk`). Together
   with nonemptiness and irreducibility this gives integrality by `def-pc-integral-scheme`.
   The same open-stalk identifications show that the restricted generic stalk map is the
   original isomorphism. The two integral schemes have their unique generic points,
   and the restricted map sends one to the other, proving the asserted birationality.
-/
theorem exists_integral_affine_neighbourhood_of_birational_normal_stalk
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : Y ⟶ X) [IsReduced Y]
    (x : X)
    (hnormal : ∀ (p : Ideal (X.presheaf.stalk x)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hgeneric : Set.BijOn f (genericPoints Y) (genericPoints X))
    (hstalk : ∀ η : Y, η ∈ genericPoints Y → IsIso (f.stalkMap η)) :
    ∃ (V : X.Opens) (hxV : x ∈ V),
      IsAffineOpen V ∧ Function.Injective (X.presheaf.germ V x hxV) ∧
      IsIntegral V.toScheme ∧ IsIntegral (f ⁻¹ᵁ V).toScheme ∧
      Set.BijOn (f ∣_ V) (genericPoints (f ⁻¹ᵁ V).toScheme) (genericPoints V.toScheme) ∧
      ∀ η : (f ⁻¹ᵁ V).toScheme, η ∈ genericPoints (f ⁻¹ᵁ V).toScheme →
        IsIso ((f ∣_ V).stalkMap η) := by
  sorry

end AlgebraicGeometry

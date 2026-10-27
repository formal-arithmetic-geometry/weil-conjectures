module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.FunctionField

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Extension of generic sections over a normal integral base

Source: Stacks Project, Morphisms, Tag 0AB1 (lemma-finite-birational-over-normal),
applied to the reduced closure of a prescribed generic section; de Jong 1997, section 3.8,
last paragraph (blueprint: lem-sfb-finite-normal-generic-section-extension).

## Main statement

A section of a finite morphism over an integral scheme whose local rings are normal domains
is uniquely determined by, and exists for, its restriction to the generic point. The target
scheme is arbitrary: no reducedness, normality, integrality, or flatness is imposed on it.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

set_option autoImplicit false in
/-- Restriction of sections of a finite morphism to the generic point is bijective.

Source: Stacks Project, Morphisms, Tag 0AB1 (lemma-finite-birational-over-normal),
applied to the reduced closure of a prescribed generic section; de Jong 1997, section 3.8,
last paragraph (blueprint: lem-sfb-finite-normal-generic-section-extension).

Proof plan:
1. Cover S by nonempty affine opens U = Spec A, using lem-weil-pbc-affine-opens-basis.
   Finite affineness gives the inverse image Spec B with B finite over A. By
   lem-sc-integral-function-field-affine-fraction the generic germ A → K is injective and
   K is its fraction field. By lem-weil-pbc-affine-open-stalk-localization, the maximal
   localizations of A are local rings of S. Their normality and
   lem-weil-pbc-normal-domain-of-local-normal make A integrally closed in K.
2. A prescribed generic section yields an A-algebra map B → K. By
   lem-weil-pbc-finite-algebra-is-integral each element of B satisfies a monic equation
   over A. Its image is therefore integral over A and belongs to A by normality. Take
   its unique preimage under the injective germ map. Injectivity proves preservation
   of addition, multiplication, zero and one, and compatibility with A. Applying
   def-weil-affine-spectrum gives a section over U with the prescribed generic value.
3. Two sections over any nonempty affine W with the same generic restriction give
   coordinate maps into its section ring whose composites with its injective germ
   into K agree. Thus the maps, and hence the sections, coincide. No property of B
   beyond finiteness was used for existence, and no reducedness is needed for uniqueness.
4. Cover the overlaps U ∩ V by nonempty affine opens. Step 3 makes the local sections
   agree there, hence on the overlaps. By lem-weil-pbc-scheme-morphism-gluing they glue
   to a global section. Its composite with f is the identity since this holds on the
   cover, and its generic restriction is the prescribed section.
5. Step 3 and uniqueness in lem-weil-pbc-scheme-morphism-gluing prove global uniqueness.
   Thus restriction is injective and surjective. Associativity and the section equation
   show that restriction lands in the displayed subtype. If the generic-section set
   is empty, the existence of this restriction map forces the global-section set empty
   too, and the same bijectivity assertion applies.
-/
theorem finite_normal_generic_section_extension
    {S X : Scheme.{u}} [IsIntegral S]
    (hS : ∀ x : S,
      IsDomain (S.presheaf.stalk x) ∧ IsIntegrallyClosed (S.presheaf.stalk x))
    (f : X ⟶ S) [IsFinite f] :
    Function.Bijective
      (fun s : {s : S ⟶ X // s ≫ f = 𝟙 S} =>
        (⟨S.fromSpecStalk (genericPoint S) ≫ s.1,
          by simp [s.2]⟩ :
          {a : Spec S.functionField ⟶ X // a ≫ f = S.fromSpecStalk (genericPoint S)})) := by
  sorry

end AlgebraicGeometry

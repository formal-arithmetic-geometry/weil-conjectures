module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism

import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.FieldTheory.CommonExtensionFields
import Sheaf.AlgebraicGeometry.UnramifiedLocusBaseChange

/-! # The universal unramified and radicial locus in the base is open

Source: Stacks Project, Tag 05X9,
`spaces-more-morphisms-lemma-where-unramified-universally-injective`, specialized to schemes.
(blueprint: lem-sfb-universal-unramified-radicial-open)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- There is an open subscheme of the base representing simultaneous unramifiedness
and universal injectivity after every base change.

Source: Stacks Project, Tag 05X9,
`spaces-more-morphisms-lemma-where-unramified-universally-injective` (scheme case).
(blueprint: lem-sfb-universal-unramified-radicial-open)

Proof (the live node's nine steps):
1. The commutative triangle and local finite type of p imply local finite type of f:
choose affine neighbourhoods in B, C and A. Finite algebra generators over the base
also generate over the intermediate ring. Use lem-weil-pbc-lft-affine-pairs and
lem-weil-pbc-lft-pointwise-criterion.
2. For any two points over the same base point, lem-weil-common-extension-fields
embeds their residue fields into a common field. The prime kernel of the tensor map
and lem-weil-pbc-fibre-product-points give a point of the fibre product over that pair;
the residue fields and their maps are those of def-weil-residue-field.
3. Let U be the unramified locus of f. By lem-trf-unramified-locus-base-change it is
open and pulls back to the unramified locus of f_T. Local finite type is preserved by
lem-weil-pbc-lft-base-change; source locality in def-weil-unramified-morphism says
that f_T is unramified exactly when its whole source lies above U.
4. Define B0 = B minus p(A minus U). It is open by closedness of p. Step 2 shows
that h(T) lies in B0 exactly when f_T is unramified. The factorization criterion
lem-weil-pbc-morphism-factors-through-open-subscheme identifies this containment
with factorization through B0.
5. Set A0 = A ×_B B0, C0 = C ×_B B0 and D = A ×_C A. The universal property
in def-pc-fibre-product identifies these base changes with the inverse-image open
subschemes (def-weil-open-immersion), using unique open factorization. It also
identifies A0 ×_{C0} A0 with D ×_B B0, compatibly with the diagonal. Restrictions
of p and p2 to these opens are closed: if F is closed in r⁻¹(B0), write it as
F' ∩ r⁻¹(B0) with F' closed; then r(F) = r(F') ∩ B0. This uses only restrictions
to an open base, not stability of closed maps under arbitrary base change.
6. By step 4, f0 is unramified. Its diagonal is an open immersion by
 def-weil-unramified-morphism. Write J for its open image and E for the closed
complement in D0 = A0 ×_{C0} A0. Closedness of p20 makes V = B0 minus p20(E)
open in B0, hence in B.
7. For h into B0, the base change of this diagonal is the diagonal of f_T by
 def-pc-fibre-product. It is an open immersion by
lem-weil-pbc-open-immersion-base-change. Identifying it with its image by
lem-weil-pbc-open-immersion-iso-onto-image and using unique open factorization
shows that its image is the inverse image of J. Thus it is surjective exactly
when the inverse image of E is empty.
8. By the point-lifting argument of step 2, that inverse image is empty exactly
when h(T) lies in V, hence exactly when h factors through V by
lem-weil-pbc-morphism-factors-through-open-subscheme.
9. The diagonal criterion in def-weil-radicial-morphism identifies its surjectivity
with universal injectivity of f_T. For arbitrary h into B, step 4 first factors h
through B0 when f_T is unramified, and steps 7 and 8 then factor it through V.
Conversely, a factorization through V gives unramifiedness by step 4 and universal
injectivity by steps 7 and 8. This proves both directions for every T and h. -/
theorem exists_universalUnramifiedRadicialOpen {A B C : Scheme.{u}}
    (p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C) (hf : f ≫ q = p)
    [LocallyOfFiniteType p] (hp : IsClosedMap p.base)
    (hp2 : IsClosedMap (pullback.fst f f ≫ p).base) :
    ∃ V : B.Opens, ∀ (T : Scheme.{u}) (h : T ⟶ B),
      (IsUnramified (pullback.map p h q h f (𝟙 T) (𝟙 B)
        (by simpa only [Category.comp_id] using hf.symm) (by simp)) ∧
      UniversallyInjective (pullback.map p h q h f (𝟙 T) (𝟙 B)
        (by simpa only [Category.comp_id] using hf.symm) (by simp))) ↔
      ∃ l : T ⟶ V.toScheme, l ≫ V.ι = h := by
  sorry

end AlgebraicGeometry

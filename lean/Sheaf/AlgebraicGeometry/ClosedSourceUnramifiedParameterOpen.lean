module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.AlgebraicGeometry.UnramifiedLocusBaseChange

import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # The unramified parameter open for a closed source

Source: Stacks Project, Tag 05X8, `spaces-more-morphisms-lemma-where-unramified`,
specialized to schemes (blueprint: lem-sfb-closed-source-unramified-parameter-open).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A closed, locally finite type source has the specified open parameter locus for
unramifiedness after arbitrary base change.

Source: Stacks Project, Tag 05X8, `spaces-more-morphisms-lemma-where-unramified`
(scheme specialization) (blueprint: lem-sfb-closed-source-unramified-parameter-open).

Proof plan (the node's six steps):
1. Apply clause (a) of `lemma-nagata-finite-type-to-separated-target`, namely
`locallyOfFiniteType_of_comp`, to the triangle. Since the composite is p, f is locally
of finite type; no finiteness or separatedness of q is required (Tag 01T8).
2. By `lem-trf-unramified-locus-base-change`, the union U_f of unramified source opens
is open. Its complement Z is closed, so p(Z) is closed by the hypothesis on p.
Its complement B₀ has its open subscheme structure (`def-weil-open-immersion`, Tag 01IK).
3. For h : T → B, the pullback universal property (`def-pc-fibre-product`) identifies
A ×_B T with A ×_C (C ×_B T), compatibly with the induced f_T. The morphism f_T is
locally of finite type by `lem-weil-pbc-lft-base-change`, and
`lem-trf-unramified-locus-base-change` identifies its locus with the inverse image of U_f.
4. By source locality of `def-weil-unramified-morphism`, f_T is unramified exactly
when its locus is its entire source, equivalently when the inverse image of Z is empty.
5. The image of that inverse image under A ×_B T → T is h⁻¹(p(Z)). One inclusion is
commutativity. For the other, points a ∈ Z and t ∈ T over the same b lift to a point
of the fibre product by `lem-weil-pbc-fibre-product-points`: the tensor product
κ(a) ⊗_{κ(b)} κ(t) is nonzero, since both factors are nonzero vector spaces over
κ(b), so it has a prime ideal (Tag 01JT). Thus the inverse image of Z is empty
exactly when h⁻¹(p(Z)) is empty.
6. This last condition is exactly that the image of h lies in B₀. Apply
`lem-weil-pbc-morphism-factors-through-open-subscheme` to get its factorization;
conversely a factorization has image in B₀. This proves both implications (Tags 01HI, 01IK). -/
theorem exists_closedSourceUnramifiedParameterOpen {A B C : Scheme.{u}}
    (p : A ⟶ B) (q : C ⟶ B) (f : A ⟶ C) (hf : f ≫ q = p)
    [LocallyOfFiniteType p] (hp : IsClosedMap p) :
    LocallyOfFiniteType f ∧
      ∃ B₀ : B.Opens, (B₀ : Set B) =
        (p '' {z : A | ∃ O : A.Opens, z ∈ O ∧ IsUnramified (O.ι ≫ f)}ᶜ)ᶜ ∧
        ∀ (T : Scheme.{u}) (h : T ⟶ B),
          IsUnramified (pullback.map p h q h f (𝟙 T) (𝟙 B)
            ((Category.comp_id p).trans hf.symm)
            ((Category.comp_id h).trans (Category.id_comp h).symm)) ↔
          ∃ l : T ⟶ B₀.toScheme, l ≫ B₀.ι = h := by
  sorry

end AlgebraicGeometry

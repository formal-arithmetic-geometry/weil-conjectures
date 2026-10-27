module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Exactness detected in a faithful conservative square

Source: WeilConjectures/WeilSheaf/OpenImmersion.lean, equivariant extension-by-zero
instances; WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebra.lean, exact transport;
Stacks Project, Tag 010N.
(blueprint: lem-sf-exact-conservative-square-finite-preservation)
-/

@[expose] public section

universe uC vC uD vD uA vA uB vB

open CategoryTheory Limits

namespace CategoryTheory.Functor

-- The stated exactness hypothesis on q is unnecessary for the shorter reflection proof.
set_option linter.unusedVariables false in
/-- An arbitrary functor in a naturally commuting square is additive and exact when
its other three sides are additive and preserve short exact sequences, and its target
vertical functor is faithful and conservative. Finite preservation means preservation of
actual limiting cones and colimiting cocones, including empty diagrams, kernels,
cokernels, equalizers and coequalizers; additivity also preserves the actual finite
biproduct diagrams.

Source: WeilConjectures/WeilSheaf/OpenImmersion.lean, equivariant finite-preservation
instances; WeilConjectures/CategoryTheory/Endofunctor/IsoAlgebra.lean, exact transport;
Stacks Project, Tag 010N.
(blueprint: lem-sf-exact-conservative-square-finite-preservation)

Proof plan:
1. Put T = p ⋙ L. Naturality of eta conjugates the maps of H ⋙ q to those of T.
   Additivity of p, L and q, followed by faithfulness of q, proves additivity of H
   and hence preservation of zero morphisms.
2. Applying p and L to a short exact sequence gives a short exact sequence. The
   components of eta identify its maps with the maps of H ⋙ q, so the latter
   sequence is short exact too, and the two maps of H compose to zero.
3. Faithfulness of q reflects monomorphisms and epimorphisms by cancellation.
4. Form the image-to-kernel comparison for the two maps of H. Exactness of q
   preserves its image and kernel by lem-sp-exact-functor-preserves-homology.
   The image sequence under q is exact, so q sends this comparison to an
   isomorphism. Conservativity makes the original comparison an isomorphism.
   Together with step 3, this proves preservation of short exact sequences.
5. Apply the finite-limit/finite-colimit equivalence of exact_tfae (Tag 010N),
   the equivalence in lem-sp-exact-functor-preserves-homology. The preservation
   classes assert universal properties of the mapped cones and cocones. Empty
   shapes give the zero object, and parallel-pair shapes give kernels, cokernels,
   equalizers and coequalizers.
6. Applying the additive H to the finite biproduct identities preserves the
   projection-injection identities and the sum decomposition of the identity.
   These give the universal properties of the actual image biproduct diagrams,
   including the empty family.
-/
theorem additive_exact_finite_preservation_of_conservative_square
    {C : Type uC} [Category.{vC} C] [Abelian C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    (p : C ⥤ A) (q : D ⥤ B) (L : A ⥤ B)
    [p.Additive] [q.Additive] [L.Additive]
    (hp : ∀ S : ShortComplex C, S.ShortExact → (S.map p).ShortExact)
    (hq : ∀ S : ShortComplex D, S.ShortExact → (S.map q).ShortExact)
    (hL : ∀ S : ShortComplex A, S.ShortExact → (S.map L).ShortExact)
    [q.Faithful] [q.ReflectsIsomorphisms]
    (H : C ⥤ D) (eta : H ⋙ q ≅ p ⋙ L) :
    ∃ (_ : H.Additive),
      (∀ S : ShortComplex C, S.ShortExact → (S.map H).ShortExact) ∧
        PreservesFiniteLimits H ∧ PreservesFiniteColimits H := by
  -- Faithfulness alone reflects short exactness in abelian categories.
  have : (H ⋙ q).Additive := additive_of_iso eta.symm
  have : H.Additive := additive_of_comp_faithful H q
  refine ⟨inferInstance, ?_⟩
  have hH : ∀ S : ShortComplex C, S.ShortExact → (S.map H).ShortExact := by
    intro S hS
    apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful q
    exact ShortComplex.shortExact_of_iso (S.mapNatIso eta.symm) (hL _ (hp S hS))
  exact ⟨hH, (H.exact_tfae.out 0 3).mp hH⟩

end CategoryTheory.Functor


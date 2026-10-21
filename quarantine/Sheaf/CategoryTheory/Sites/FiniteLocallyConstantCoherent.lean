module

public import Sheaf.CategoryTheory.Sites.CoherentTopos
public import Sheaf.CategoryTheory.Sites.FiniteLocallyConstant

import Sheaf.TraceFormula.FinitarySiteCoherentGenerators
import Sheaf.CategoryTheory.Sites.CoherentEpimorphicQuotient
import Mathlib.CategoryTheory.Sites.LeftExact
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.Sites.CoherentObjectApproximation
import Sheaf.CategoryTheory.Sites.CoherentToposRepair

@[expose] public section

/-!
# Finite locally constant set sheaves are coherent and stable under finite operations

Source: literature/stacks-project/sites-modules.tex, Section 093P (blueprint:
lem-trf-finite-locally-constant-coherent).
-/

universe w u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Finite locally constant objects are coherent and stable under the stated finite
operations. Source: Stacks Project, Modules on Sites, Section 093P, Definition
093Q and Lemmas 093R, 093S(1), 093U(1); Orgogozo, author draft, §8.1
(blueprint: lem-trf-finite-locally-constant-coherent).

The finite-limit, finite-cover site in the node gives a coherent topos by
`lem-trf-finitary-site-coherent-generators`. We use its intrinsic coherent-topos
form here. The covering-family universe `w` is retained in both the hypothesis
and the coherent-object conclusion; finite coproducts use universe zero.

1. Choose a small coherent generating family closed under finite limits, using
   `def-trf-coherent-topos`. Refine the finite trivializing cover of F by these
   generators. Quasi-compactness of the terminal object gives a finite subcover.
   Pulling back the trivializations makes each restriction a finite coproduct
   of its coherent covering object. Such coproducts are coherent by
   `lem-trf-coherent-object-approximation`. Constant finite sheaves in a slice
   are these coproducts, since sheafification preserves coproducts.
2. The sections of these trivializations give an epimorphism P to F, where P
   is a finite coproduct of coherent objects. Its kernel pair is a finite
   coproduct of equalizers of pairs of these sections. On each common covering
   product, finite extensivity (`lem-trf-set-sheaf-finite-extensivity`) identifies
   an equalizer with a coproduct summand. A summand of a quasi-compact object
   is quasi-compact: add its complementary summand to any cover, take a finite
   subcover, and pull back. Thus the equalizers and the kernel pair are
   quasi-compact. Apply `lem-trf-coherent-epimorphic-quotient` to P to F.
   Here product with a fixed object preserves colimits and epimorphisms:
   presheaf colimits are sectionwise, products of sets preserve colimits, and
   sheafification preserves finite limits by
   `lem-weil-pbc-sheafification-sets-exact`.
3. Refine finitely many trivializing families by their products. Finite
   extensivity further decomposes each covering object into finitely many
   summands on which every arrow of a finite diagram is induced by a map of
   finite sets (093S(1)). Finite limits and coproducts are then computed on
   those finite sets. The empty cases are the singleton and empty sets.
4. For an arrow, take the same refinement. Products with covering objects
   preserve images: they preserve pushouts and finite limits, and images in
   a topos are equalizers of cokernel pairs. The image of a map of finite
   constant objects is the coproduct indexed by the image finite set.
5. For the two projections of an internal equivalence relation, use a common
   finite refinement. Product with a covering object preserves coequalizers.
   The coequalizer of the resulting maps of finite constant objects is the
   coproduct indexed by the coequalizer finite set. This gives the quotient
   clause, using `def-weil-pbc-constant-sheaf` and the same finite extensivity.
-/
theorem finiteLocallyConstant_coherent
    {E : Type u} [Category.{v} E] [HasCoproducts.{w} E] [HasCoproducts.{0} E]
    [HasFiniteLimits E]
    [HasImages E] [HasColimitsOfShape WalkingParallelPair E]
    (_hE : IsCoherentTopos.{w} E) (F : E) :
    IsFiniteLocallyConstant F →
      IsCoherentObject.{w} F ∧
      (∀ (n : ℕ) (G : Fin n → E),
        (∀ i, IsFiniteLocallyConstant (G i)) →
          IsFiniteLocallyConstant (∐ G)) ∧
      (∀ (J : Type) [SmallCategory J] [FinCategory J] (D : J ⥤ E),
        (∀ j, IsFiniteLocallyConstant (D.obj j)) →
          IsFiniteLocallyConstant (limit D)) ∧
      (∀ {G H : E} (f : G ⟶ H),
        IsFiniteLocallyConstant G → IsFiniteLocallyConstant H →
          IsFiniteLocallyConstant (image f)) ∧
      (∀ {R G : E} (r₁ r₂ : R ⟶ G),
        IsEquivalenceRelation r₁ r₂ →
        IsFiniteLocallyConstant R → IsFiniteLocallyConstant G →
          IsFiniteLocallyConstant (coequalizer r₁ r₂)) := by
  sorry

end CategoryTheory

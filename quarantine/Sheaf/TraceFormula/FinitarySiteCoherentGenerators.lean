/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.Sites.CoherentTopos
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.LeftExact

import Sheaf.CategoryTheory.Sites.CoveringRepresentableCoequalizer
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Sheaf.CategoryTheory.Sites.CoherentEpimorphicQuotient
import Sheaf.CategoryTheory.Sites.CoherentToposRepair
import Sheaf.TraceFormula.SiteQuasicompactSheafificationCriterion

/-!
# Coherent generators for finitary sites

-- Reused by the Q28 stage-2 delivery after duplicate verification.

Source: Orgogozo, §8.1, printed p. 17; Illusie--Laszlo--Orgogozo,
Exposé XI, Lemma 2.5 (blueprint: lem-trf-finitary-site-coherent-generators).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v u' v' w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Coherent generators and the geometric-morphism criterion for a finite-cover site.
Source: Orgogozo, §8.1, printed p. 17; Illusie--Laszlo--Orgogozo,
Exposé XI, Lemma 2.5 (blueprint: lem-trf-finitary-site-coherent-generators).

Proof:
1. Each covering presieve is finite, so the identity refinement verifies
   lem-trf-site-quasicompact-sheafification-criterion. Every sheafified representable
   is quasi-compact, without a subcanonical hypothesis.
2. The sheafification adjunction and Yoneda identify maps from `H_U` to `F` with
   `F(U)`. By lem-weil-pbc-sheafification-sets-exact, sheafification preserves the
   terminal object, products, and pullbacks of representables along site arrows.
3. Apply lem-weil-pbc-sheaf-covering-representable-coequalizer-presentation to all
   site objects, using identity covers. Its coequalizer map is epi, so the `H_U`
   generate. Quasi-compactness selects finitely many summands when `F` is quasi-compact.
4. By lem-weil-pbc-site-sheaf-sets-limits-sectionwise and
   lem-weil-pbc-site-sheaf-sets-epi-locally-surjective, epimorphisms are stable under
   pullback. By def-weil-pbc-sheafification and
   lem-weil-pbc-site-sheafification-sections-local, coproduct sections locally lie
   in one summand. Hence jointly epic families are stable under pullback, epic
   images of quasi-compact objects are quasi-compact, and finite coproducts of
   quasi-compact objects are quasi-compact. Include the empty case using the strict
   initial object of lem-trf-set-sheaf-finite-extensivity.
5. For arbitrary maps `H_V → H_U` and `H_W → H_U`, the sheafification section lemma
   gives finite covers on which these are site arrows. Their pullback is therefore
   covered by finitely many representable pullbacks, which are quasi-compact by
   steps 1 and 2. Step 4 makes the original pullback quasi-compact.
6. Cover quasi-compact `B,C` mapping to `H_U` by finite families of generators, as
   in step 3. Step 5 and pullback stability give a finite quasi-compact cover of
   `B ×_{H_U} C`. Thus `H_U` is quasi-separated and hence coherent by
   def-trf-coherent-topos.
7. Quasi-compact subobjects of generators are coherent. Since the terminal
   generator is quasi-separated, this class is closed under products. Equalizers
   are pullbacks along diagonals and are quasi-compact by quasi-separatedness of
   the target product. Hence the class is closed under all finite limits. Iterate
   finite products and equalizers starting with the small generating family; the
   union of these small stages is small in def-weil-size-convention. It is a full
   generating finite-limit-closed subcategory of coherent objects, proving coherence
   of the topos and coherence of the entire finite-limit closure of the generators.
8. Finite coproducts of coherent objects are coherent: use
   lem-trf-set-sheaf-finite-extensivity to split pullbacks into summands. The pieces
   of a quasi-compact object over a finite coproduct are quasi-compact, by adjoining
   the complementary summands to any cover and then selecting a finite subcover.
   Quasi-separatedness of each target summand and step 4 prove the assertion,
   including the strict initial object. This works in any coherent topos using
   its small-site presentation from def-trf-coherent-topos.
9. A coherent object `A` admits an epi `P → A` from a finite coproduct of generators.
   Its kernel pair is quasi-compact by quasi-separatedness of `A` and step 4, and
   admits an epi from another finite coproduct `Q` of generators. Either family
   may be empty; the kernel pair need not be representable.
10. By def-trf-geometric-morphism, the inverse image is a left exact left adjoint,
    so it preserves coproducts, epimorphisms, and the kernel pair of step 9. Under
    the generator hypothesis, step 8 makes the image of `P` coherent, while the
    image of `Q` and its epic image, the transported kernel pair, are quasi-compact.
11. Apply lem-trf-coherent-epimorphic-quotient in the target topos to the transported
    epimorphism and its quasi-compact kernel pair. Its quotient is coherent. This
    holds for every coherent `A`, exactly IsCoherentGeometricMorphism.
-/
theorem finitarySiteCoherentGenerators
    {C : Type u} [Category.{v} C] [HasFiniteLimits C]
    (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (hfinite : ∀ (X : C) (R : Presieve X), R ∈ J X → R.uncurry.Finite) :
    ∃ hE : IsCoherentTopos.{max u v w} (Sheaf J.toGrothendieck (Type (max u v w))),
      (∀ (U : C),
        IsCoherentObject.{max u v w}
          ((presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
            (uliftYoneda.{max u w}.obj U))) ∧
      (∀ (X : Sheaf J.toGrothendieck (Type (max u v w))),
        ∃ (I : Type (max u v w)) (U : I → C)
          (f : ∀ i, (presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
            (uliftYoneda.{max u w}.obj (U i)) ⟶ X),
          Epi (Sigma.desc f)) ∧
      (∃ (P : ObjectProperty (Sheaf J.toGrothendieck (Type (max u v w)))),
        (∀ (U : C), P ((presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
          (uliftYoneda.{max u w}.obj U))) ∧
        (∀ X, P X → IsCoherentObject.{max u v w} X) ∧
        ∀ (K : Type) [SmallCategory K] [FinCategory K],
          P.IsClosedUnderLimitsOfShape K) ∧
      (∀ (E' : Type u') [Category.{v'} E']
        [HasCoproducts.{max u v w} E'] [HasFiniteLimits E']
        (hE' : IsCoherentTopos.{max u v w} E')
        (f : GeometricMorphism E' (Sheaf J.toGrothendieck (Type (max u v w)))),
        (∀ (U : C), IsCoherentObject.{max u v w}
          (f.inverse.obj ((presheafToSheaf J.toGrothendieck (Type (max u v w))).obj
            (uliftYoneda.{max u w}.obj U)))) →
        IsCoherentGeometricMorphism hE' hE f) := by
  sorry

end CategoryTheory

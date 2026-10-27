/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import WeilConjectures.AlgebraicGeometry.FiniteEtaleDescent
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum

/-!
# Étale descent of universal coequalizers with finite étale targets

Source: literature/stacks-project/pione.tex, Tag 0BN9,
lemma-finite-etale-covers-limits-colimits, the finite-colimit proof and its
base-change verification (blueprint: lem-sc-etale-local-universal-coequalizer-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- Universal coequalizers with finite étale targets descend along a set-indexed étale cover.
The local universal property uses iterated pullbacks, canonically identified with pullback
along the composite. All factoring maps are in the whole category of schemes over the base,
not just its finite étale subcategory.

Source: Stacks Project, pione.tex, Tag 0BN9, lemma-finite-etale-covers-limits-colimits,
finite-colimit proof (blueprint: lem-sc-etale-local-universal-coequalizer-descent).

Proof:
1. The representable-sheaf property (lem-weil-pbc-small-etale-representable-presheaf-sheaf,
   Tags 03O3 and 03O4), applied on the source scheme, glues morphisms between arbitrary
   schemes over an étale cover. Equality can also be checked on that cover. Pullback
   preserves étale covers (lem-weil-pbc-etale-covering-base-change).
2. On each overlap the two quotient targets represent the same equalizing maps. Their
   universal properties produce inverse comparison maps. Uniqueness proves their diagonal
   normalization and the cocycle identity on triple overlaps (def-pc-fibre-product).
3. If the index universe is larger than the schemes, choose a small subcover by choosing
   one preimage for each point of the base. Form coproducts of its members and targets
   (lem-weil-pbc-scheme-coproduct-family). The resulting morphism between coproducts is
   finite étale: its restriction over each disjoint target summand is the given finite
   étale map. Use lem-weil-pbc-etale-composition-cancellation,
   lem-weil-pbc-etale-local-on-source, lem-weil-pbc-closed-finite-etale-zariski-local,
   and lem-weil-pbc-open-immersion-base-change. The coproduct cover is étale surjective.
4. Glue the overlap comparisons using step 1. Step 2 gives their cocycle, hence a descent
   datum (def-pd-descent-datum). Apply lem-galois-descent to obtain the finite étale global
   target and the compatible local isomorphisms. Universal uniqueness recovers the
   compatible comparison with every original cover member if a subcover was chosen.
5. Transport the local quotient maps through these isomorphisms and glue by step 1.
   Check the equalizing equation on the cover; neither source scheme needs to be étale.
6. After any base change, pull back the cover. The original universal properties give
   local factors for every equalizing map into an arbitrary scheme. Uniqueness makes
   these factors agree on overlaps, so step 1 glues them uniquely. Their factorization
   equation and uniqueness are checked on the pulled-back cover.
-/
theorem etaleLocalUniversalCoequalizerDescent
    (Y : Scheme.{u}) (Z P : Over Y) (a b : Z ⟶ P)
    (I : Type w) (U : I → Scheme.{u}) (ι : ∀ i : I, U i ⟶ Y)
    (hι : ∀ i : I, Etale (ι i))
    (hcover : ∀ y : Y, ∃ (i : I) (x : U i), ι i x = y)
    (Q : ∀ i : I, MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤ (U i))
    (q : ∀ i : I, (Over.pullback (ι i)).obj P ⟶ Over.mk (Q i).hom)
    (heq : ∀ i : I, (Over.pullback (ι i)).map a ≫ q i =
      (Over.pullback (ι i)).map b ≫ q i)
    (hlocal : ∀ (i : I) (V : Scheme.{u}) (v : V ⟶ U i) (H : Over V)
      (h : (Over.pullback v).obj ((Over.pullback (ι i)).obj P) ⟶ H),
      (Over.pullback v).map ((Over.pullback (ι i)).map a) ≫ h =
        (Over.pullback v).map ((Over.pullback (ι i)).map b) ≫ h →
      ∃! k : (Over.pullback v).obj (Over.mk (Q i).hom) ⟶ H,
        (Over.pullback v).map (q i) ≫ k = h) :
    ∃ (Q₀ : MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤ Y) (q₀ : P ⟶ Over.mk Q₀.hom),
      a ≫ q₀ = b ≫ q₀ ∧
      (∀ i : I, ∃ θ : (Over.pullback (ι i)).obj (Over.mk Q₀.hom) ≅ Over.mk (Q i).hom,
        (Over.pullback (ι i)).map q₀ ≫ θ.hom = q i) ∧
      ∀ (Y' : Scheme.{u}) (g : Y' ⟶ Y) (H : Over Y')
        (h : (Over.pullback g).obj P ⟶ H),
        (Over.pullback g).map a ≫ h = (Over.pullback g).map b ≫ h →
        ∃! k : (Over.pullback g).obj (Over.mk Q₀.hom) ⟶ H,
          (Over.pullback g).map q₀ ≫ k = h := by
  sorry

end AlgebraicGeometry

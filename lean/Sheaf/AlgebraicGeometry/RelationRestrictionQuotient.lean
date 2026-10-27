/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.CategoryTheory.SiteCoveringsCommonRefinement
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Fppf quotients and restriction of an equivalence relation

Source: Stacks Project, Groupoids, Tags 02VH and 045Z, with tau = fppf
(blueprint: lem-sfb-relation-restriction-quotient).

The presheaf coequalizers are the sectionwise quotients. Their chosen sheafifications
are specified by the reflection universal property. This avoids assuming sheafification
for every small-valued presheaf on the big site. The restricted relation and both
projections are written directly as pullbacks, in exactly the orientation in Tag 02VH.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Restriction along an arbitrary morphism gives a monomorphism of fppf quotient
sheaves. It is an isomorphism if the saturation map is an fppf cover.
Source: Stacks Project, Groupoids, Tags 02VH and 045Z
(blueprint: lem-sfb-relation-restriction-quotient).

Proof:
1. By def-pc-fibre-product, sections of `pullback (pullback.snd g t ≫ s) g` are triples
   `(a,r,b)` satisfying `a ≫ g = r ≫ t` and `r ≫ s = b ≫ g`. Its projections are
   `b,a`, namely `pullback.snd (pullback.snd g t ≫ s) g` and
   `pullback.fst (pullback.snd g t ≫ s) g ≫ pullback.fst g t`.
   Thus the restricted relation is exactly the
   inverse image of the equivalence relation on sections of `V`. Monicity makes the
   arrow `r` unique. The resulting map of sectionwise quotient sets, `[a] ↦ [a ≫ g]`,
   is well defined, injective and natural.
2. By def-weil-pbc-sheafification, the two reflection properties `hη` and `hη'`
   give the canonical map `α` with the displayed quotient-projection equation.
   This equation determines `α` uniquely: cancel the presheaf coequalizer projection,
   then apply injectivity in `hη'`.
3. For sections with equal images, use lem-weil-pbc-site-sheafification-sections-local
   and lem-weil-pbc-site-coverings-common-refinement to represent both on one fppf
   cover. Local equality in the original quotient sheaf gives further covers where
   their quotient classes agree. Step 1 gives equality in the restricted quotient.
   Sheaf separation (def-weil-pbc-sites-and-cohomology) then gives equality globally.
   The componentwise injections imply `Mono α`.
4. If `h = pullback.snd g t ≫ s` is surjective, flat and locally finitely presented,
   its singleton family is an fppf cover (def-pc-fppf-site). Represent a section of
   the original quotient sheaf locally by a map to `V` using the local-sections
   lemma. Pull back the covering `h` along this map. The pullback projections supply
   `a` and `r` with `a ≫ g = r ≫ t` and `r ≫ s` equal to the given representative.
   Thus `[a]` maps to the section on this further cover. Site composition gives
   local lifts over a cover of the original test scheme. No property of `g` is used.
5. The local lifts agree on overlaps by step 3, and glue uniquely by the sheaf
   condition (def-weil-pbc-sites-and-cohomology). Sheaf separation shows that their
   image is the original section. The unique lifts are natural in the test scheme,
   giving an inverse to `α` and hence `IsIso α`.
-/
theorem relation_restriction_quotient {S : Scheme.{u}} {R V A : Over S}
    (s t : R ⟶ V) [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ V ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    (g : A ⟶ V)
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun k : F.obj ⟶ G.obj ↦ η ≫ k))
    (F' : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η' : coequalizer (yoneda.map (pullback.snd (pullback.snd g t ≫ s) g))
      (yoneda.map (pullback.fst (pullback.snd g t ≫ s) g ≫ pullback.fst g t)) ⟶ F'.obj)
    (hη' : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun k : F'.obj ⟶ G.obj ↦ η' ≫ k)) :
    ∃ α : F' ⟶ F,
      (coequalizer.π (yoneda.map (pullback.snd (pullback.snd g t ≫ s) g))
          (yoneda.map (pullback.fst (pullback.snd g t ≫ s) g ≫ pullback.fst g t)) ≫ η') ≫
          α.hom =
        yoneda.map g ≫ (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) ∧
      Mono α ∧
      (Surjective (pullback.snd g t ≫ s).left →
        Flat (pullback.snd g t ≫ s).left →
        LocallyOfFinitePresentation (pullback.snd g t ≫ s).left → IsIso α) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

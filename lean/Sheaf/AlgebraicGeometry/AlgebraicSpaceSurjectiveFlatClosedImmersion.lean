/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Sheaf.AlgebraicGeometry.RepresentableEtaleFppfLocalLifting
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! # Surjective flat closed immersions of algebraic spaces

Source: Stacks Project, More on Morphisms of Spaces, Tag 05XD
(lemma-where-isomorphism), final paragraph of the proof; Morphisms, Tag 04PW
(lemma-characterize-flat-closed-immersions)
(blueprint: lem-sfb-space-surjective-flat-closed-immersion-isomorphism).

Flatness uses all compatible étale scheme charts. Surjectivity says that the point image
of def-a1-space-point-topology is all of |Y|, and closed immersion means
representability by closed immersions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- A point-surjective, chartwise flat morphism representable by closed immersions is
an isomorphism of algebraic spaces, without finiteness or reducedness assumptions.
Source: Stacks Project, Tag 05XD (lemma-where-isomorphism), proof, final paragraph,
using Tag 04PW (lemma-characterize-flat-closed-immersions)
(blueprint: lem-sfb-space-surjective-flat-closed-immersion-isomorphism).

Proof:
1. Choose a representable surjective étale scheme atlas U → Y using
   def-trf-algebraic-space. The hypothesis represents W = X ×_Y U by a scheme,
   with closed immersion j : W → U. By lem-trf-space-fibre-products-etale-covers,
   W → X is étale. The chart test of def-sfb-space-morphism-properties makes j flat.
   The hypothesis `pointImage i = univ` says that |i| is surjective. By
   lem-a1-space-point-open-calculus, representability and point-surjectivity of i
   give surjectivity on every scheme base change, hence surjectivity of j.
2. The scheme result lem-sfb-surjective-flat-closed-immersion-isomorphism makes j
   an isomorphism. For a test scheme T and y ∈ Y(T), apply
   lem-a1-representable-etale-fppf-local-lifting to the atlas to obtain an fppf cover
   V = T ×_Y U → T and a map a : V → U over y. The fibre of X(V) → Y(V) over y|_V
   is a singleton: X ×_Y V identifies with W ×_U V, whose projection is an isomorphism.
   The identification sends (x,z) to (x,a(z),z); its inverse forgets the middle entry.
3. If x and x' in X(T) have the same image y, their restrictions to this V agree
   by uniqueness of the lift. The sheaf equalizer of def-weil-pbc-sites-and-cohomology
   gives x = x'. Thus every component X(T) → Y(T) is injective.
4. The unique local lift of y has equal restrictions on V ×_T V by step 3, hence
   glues to x ∈ X(T) by the sheaf equalizer. Its image is y by separatedness of Y.
   Each component is therefore bijective. Restriction of a lift is the unique lift
   of the restricted section, so the inverses are natural. They form an inverse
   morphism Y → X in the full subcategory of algebraic spaces. -/
theorem isIso_of_surjective_of_flat_of_closedImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (i : X ⟶ Y) (hf : MapIsFlat i)
    (hs : pointImage i.hom.hom = Set.univ)
    (hc : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom) :
    IsIso i := by
  sorry

end AlgebraicGeometry.AlgebraicSpace

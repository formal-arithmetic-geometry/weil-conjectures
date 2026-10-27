/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import Sheaf.AlgebraicGeometry.ZariskiCechFaceTotalSite
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
import WeilConjectures.AlgebraicGeometry.InjectiveModuleCechAugmentation
import WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # The derived augmentation unit on a module for a Zariski open cover

Source: Stacks Project, spaces-simplicial.tex, Tag 0D7F,
lemma-augmentation-spectral-sequence-modules, and cohomology.tex, Tags 01EP and 01EQ,
with only injective order maps (blueprint: lem-sfb-zariski-cech-module-derived-unit).

The face total site is presented on its tuple-labelled open basis. The assertion concerns
all module sheaves in degree zero in the ordinary unbounded derived categories. It makes
no assertion about descent of arbitrary unbounded complexes or strictification of diagrams.
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ZariskiCechFaceTotal

/-- The canonical derived augmentation unit is invertible for every module in degree zero.
The existential preparation consists only of proofs about the explicitly constructed
site and restriction functor; in particular, it imposes no additional hypothesis.

Source: Stacks Project, spaces-simplicial.tex, Tag 0D7F, injective alternating-face
resolution proof, combined with cohomology.tex, Tags 01EP and 01EQ. Agent-supplied
adaptation to the small Zariski site and injective order maps
(blueprint: lem-sfb-zariski-cech-module-derived-unit).

Proof:
1. The vertical-cover sheaf criterion makes toOpens continuous. Restriction is exact,
   since its components are restrictions to open intersections. The compatible-family
   right adjoint is the augmentation pushforward. Module sheaves on the small total
   site form a Grothendieck category and admit K-injective resolutions, giving A.
   Choose a nonnegative injective resolution K of G using
   lem-weil-pbc-ring-sheaves-grothendieck and lem-sp-grothendieck-enough-injectives.
   By lem-weil-pbc-module-open-restriction-injectives, its restrictions to tuple
   intersections remain injective. On each disjoint union a family of injectives is
   injective, by choosing a lift on every summand. Thus a^*K resolves a^*G and is
   componentwise injective in the sense of lem-sfb-semisimplicial-ringed-total-category.
2. Apply lem-sfb-face-component-injective-total-model with J = a^*K and both comparison
   maps the identity. Its first-quadrant bicomplex has terms
   product over tuples i of j_i,* (K^q restricted to the tuple intersection).
   The horizontal differential is the alternating restriction differential.
   The normalized total-model comparison identifies the restriction augmentation
   b : K to Tot(C) with the actual canonical derived adjunction unit at G[0].
3. On each open V, the row augmentation is the Cech augmentation for the cover
   (V intersect W_i) with injective coefficient K^q restricted to V. Its degree-zero
   components are restriction, and the scalar restriction at V is the identity.
   By lem-sc-injective-module-cech-augmentation each row augmentation is a
   quasi-isomorphism. Exactness on every open implies exactness of sheaves.
   The map b commutes with vertical differentials because restriction does; the
   first horizontal differential kills its image by equality of double restrictions.
   Apply lem-sc-first-quadrant-column-augmentation with its flipped row convention:
   b is a quasi-isomorphism. Each total diagonal is finite, also for infinite I.
4. Localization inverts b by def-weil-abstract-derived-category. Its identification
   with the canonical unit in step 2 proves the assertion. Only the resolution of
   a module in degree zero is used, so no unbounded convergence hypothesis occurs. -/
theorem zariski_cech_module_derived_unit (X : Scheme.{u}) {I : Type u}
    (W : I → X.Opens) (hW : iSup W = ⊤) :
    ∃ A : Augmentation W, ∀ G : X.Modules, A.IsUnitIso W G := by
  sorry

end AlgebraicGeometry.ZariskiCechFaceTotal

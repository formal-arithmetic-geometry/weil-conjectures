/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Sheaf.AlgebraicGeometry.AffineClosedSpecializationLocalization
import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Vanishing of pro-etale shriek sections near a disjoint closed subset

Source: Stacks Project, Tag 09AG, lemma-jshriek-zero
(blueprint: lem-weil-pbc-proetale-shriek-specialization-zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- Shriek sections vanish on an affine object all of whose points specialize to the
closed fibre disjoint from the source. Here the opposite localization functor's left
Kan extension is the abelian direct-sum presheaf indexed by lifts to `U`; sheafifying
it is precisely the `j_!` of Stacks, Tag 09AG, lemma-jshriek-zero
(blueprint: lem-weil-pbc-proetale-shriek-specialization-zero).

Proof plan:
1. Apply `lem-weil-pbc-site-sheafification-sections-local` to the underlying set
   presheaf. Addition, negation and zero are defined on local representatives and descend
   by local equality. The group laws and universal property identify this with abelian
   sheafification (`lem-weil-pbc-algebraic-sheaf-iff-underlying-sets`).
2. Refine representatives to a finite affine covering of `V`, and express the pulled-back
   closed immersions as arbitrary ideals in these affine rings
   (`def-weil-pbc-proetale-covering`, `lem-weil-pbc-closed-immersion-base-change`).
3. Localize each ring at elements invertible modulo its closed-fibre ideal, using
   `lem-weil-pbc-affine-closed-specialization-localization`. These weakly etale affine
   objects cover `V`: lift generalizations along the flat covering maps using
   `lem-weil-pbc-flat-generalizations-lift`. Their maps are affine by the affine-transition
   clause of `lem-weil-pbc-spec-colimit-limit`, so the finite family satisfies the
   covering condition on every affine open. Composition uses
   `lem-weil-proetale-weakly-etale-localization`.
4. A nonempty localized object cannot map to `U`: a specialization over `Z` would give,
   using its residue field, a point of the empty pullback `U ×[X] Z`. Thus its direct
   sum has no indices. On an empty localized object, the empty covering gives zero
   sections of `G`, so the direct sum is zero there too
   (`def-weil-extension-by-zero-presheaf`, `def-pc-fibre-product`).
5. Each representative restricts to zero on this covering, hence the section is zero
   by sheaf uniqueness (`def-weil-pbc-sites-and-cohomology`). If `V` is empty, use its
   empty covering directly. -/
theorem shriek_sections_subsingleton_of_specializes_closed
    {X Z : Scheme.{u}} (U : X.ProEt) (i : Z ⟶ X) [IsClosedImmersion i]
    (hdisjoint : IsEmpty ↥(pullback U.hom i))
    (V : X.ProEt) [IsAffine V.left]
    (hspecializes : ∀ v : V.left, ∃ z : ↥(pullback V.hom i),
      Specializes v ((pullback.fst V.hom i) z))
    (G : Sheaf (topology U.left) AddCommGrpCat.{u + 1}) :
    Subsingleton
      ((sheafify (topology X)
        ((MorphismProperty.Over.map ⊤ U.prop).op.leftKanExtension G.obj)).obj (op V)) := by
  sorry

end AlgebraicGeometry.Scheme.ProEt

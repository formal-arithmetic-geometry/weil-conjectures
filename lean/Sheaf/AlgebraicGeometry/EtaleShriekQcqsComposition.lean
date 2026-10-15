/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.DerivedCategories
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

/-!
# Composition of qcqs etale compact-support candidates

Source: Stacks Project, More on Etale Cohomology, Tag 0F7J,
`lemma-shriek-composition`, with Tag 0F7I for arbitrary chosen compactifications
(blueprint: lem-weil-pbc-etale-shriek-qcqs-composition).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- For a finite commutative coefficient ring and separated finite-type morphisms of qcqs
schemes, the bounded-below compact-support functors attached to any three chosen
compactifications compose up to natural isomorphism.

Source: Stacks Project, More on Etale Cohomology, Tags 0F7J and 0F7I
(blueprint: lem-weil-pbc-etale-shriek-qcqs-composition).

Proof plan:
1. Apply `lem-weil-pbc-compatible-compactification-triangle` to the compactification of `g`.
   This gives a compactification of `f` over its open part and a compatible one of `f ≫ g`.
2. The successive-open adjunctions of `lem-weil-pbc-extension-by-zero-adjunction` identify
   the composite extensions by zero with extension along the composite. The exactness of
   `lem-weil-pbc-extension-by-zero-exact` descends this isomorphism to bounded-below complexes.
3. Apply `lem-weil-pbc-etale-open-proper-interchange` to the proper/open pullback square,
   then whisker with extension by zero from `X`. A finite coefficient ring is torsion;
   no restriction on residue characteristics is required.
4. Use `lem-weil-pbc-ringed-topoi-derived-pushforward-composition` for the proper maps.
   Together with step 2 this identifies the compatible models' composite with the model
   for `f ≫ g`; all functors preserve bounded-below objects.
5. Whisker the comparison from `lem-weil-pbc-etale-shriek-compactification-independence`
   for `f` with the functor for `g`, and then compose with its comparison for `f ≫ g`.
   This gives the asserted isomorphism for the original three choices.
-/
theorem nonempty_iso_etaleShriek_qcqs_compactification_comp
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [CompactSpace Z] [QuasiSeparatedSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (cf : Compactification f) (cg : Compactification g)
    (cgf : Compactification (f ≫ g)) :
    Nonempty
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cf ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cg ≅
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} Λ) cgf) := by
  sorry

end AlgebraicGeometry.Etale

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q43
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.Paper.ReducedSourceFactors
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Scheme theoretic image of a reduced scheme

Source: Stacks Project, Morphisms, Lemma 29.6.4 (Tag 056B), together with
Schemes, Lemma 26.12.4 (Tag 0356) (blueprint: lem-trf-reduced-scheme-image).

The scheme-theoretic image is Mathlib's canonical image `f.image` with closed
immersion `f.imageι`.  For a reduced source its kernel ideal sheaf is the
vanishing ideal of the topological closure of the image, so this canonical
closed subscheme is reduced and has the asserted minimal factorization property.
The node's final clause, the scheme-theoretic closure of a reduced open
subscheme `V ⊆ X`, is the instance `f := V.ι` (the scheme-theoretic closure is
by definition the scheme-theoretic image of the open immersion).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme.IdealSheafData

/--
Stacks Project, Morphisms, Lemma 29.6.4 (Tag 056B), with the reduced induced
closed subscheme supplied by Tags 01J3 and 0356.
(blueprint: lem-trf-reduced-scheme-image)

For a morphism `f : U ⟶ X` from a reduced scheme, the canonical
scheme-theoretic image `f.imageι : f.image ⟶ X` is the reduced induced closed
subscheme on the closure of `Set.range f`.  The last clause spells out the
meaning of “smallest closed subscheme through which `f` factors”: every closed
factor of `f` receives a unique factor from `f.image` over `X`.

Proof plan:
1. Let `T` be the closed subset given by the closure of the underlying image.
   The reduced induced closed subscheme theorem (`lem-weil-pbc-reduced-induced-
   closed-subscheme`) gives the reduced closed immersion cut out by the
   vanishing ideal of `T`.
2. Since `U` is reduced and the image of `f` lies in `T`, the reduced-source
   factorization theorem (Stacks Tag 0356, represented by
   `lem-weil-pbc-reduced-source-factors-through-closed-subscheme`) factors `f`
   through this reduced closed subscheme.
3. If `i : Z ⟶ X` is any closed immersion through which `f` factors, its closed
   range contains `Set.range f`, hence contains `T`.  Applying the same
   reduced-source factorization theorem to the reduced induced closed
   subscheme gives a factorization of `f.imageι` through `i`; closed
   immersions make that factor unique.  This proves minimality and identifies
   the canonical image with the reduced induced structure on `T`.
4. For a reduced open subscheme `V ⊆ X`, take `U := V` and `f := V.ι`.  Its
   underlying image is `V` (`Opens.range_ι`), and the scheme-theoretic closure
   of `V` is by definition (Stacks, Morphisms,
   definition-scheme-theoretically-dense, clause (1))
   the scheme-theoretic image of this open immersion.  Steps 1-3 therefore
   identify that closure with the reduced induced closed subscheme on the
   closure of `V`.
-/
theorem schemeTheoreticImage_reduced
    (U X : Scheme.{u}) (f : U ⟶ X) [IsReduced U] :
    IsClosedImmersion f.imageι ∧
      IsReduced f.image ∧
      f.ker = vanishingIdeal
        (TopologicalSpace.Closeds.mk (closure (Set.range f)) isClosed_closure) ∧
      Set.range f.imageι = closure (Set.range f) ∧
      ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i],
        (∃ g : U ⟶ Z, g ≫ i = f) →
          ∃! h : f.image ⟶ Z, h ≫ i = f.imageι := by
  sorry

end AlgebraicGeometry

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Abelian
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-!+# Left exact sheafification for Grothendieck abelian coefficients

Source: Stacks Project, Sites, Tag 00WJ (set-valued prototype); blueprint
main-20261015, proof of `lem-sfb-finite-upper-star-exact`, first paragraph;
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`,
`hasSheafify_of_isGrothendieckAbelian`; Mathlib, Sites/Abelian, `sheafIsAbelian`
(blueprint: lem-sfb-grothendieck-sheafification).

`Sheaf J A` uses the Hom-tested sheaf condition `Presheaf.IsSheaf`.
`HasSheafify J A` asserts that the sheaf inclusion has a left adjoint preserving finite limits.
-/

@[expose] public section

universe v u

namespace CategoryTheory.GrothendieckTopology

/-- Source: Stacks Project, Sites, Tag 00WJ (set-valued prototype); blueprint
main-20261015, proof of `lem-sfb-finite-upper-star-exact`, first paragraph; the
Grothendieck-coefficient construction is `hasSheafify_of_isGrothendieckAbelian` in
`WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`, and abelianness is
Mathlib's `sheafIsAbelian` (blueprint: lem-sfb-grothendieck-sheafification).

Proof plan:
1. Choose a generator of `A`. By `lem-coef-grothendieck-locally-presentable` and
   `lem-coef-object-presentability-rank`, it is presentable at an infinite regular cardinal.
   By `lem-coef-small-family-regular-bound`, enlarge that cardinal above the number of site
   arrows, retaining presentability in the same universe.
2. Iterate the matching-family plus construction through that cardinal. By
   `lem-sfb-transfinite-plus-sheaf-convergence`, its values satisfy the Hom-tested sheaf
   condition, so its functor corestricts to `Sheaf J A`.
3. By `lem-sfb-transfinite-plus-sheaf-orthogonality`, precomposition with the canonical
   unit gives natural Hom bijections into every sheaf. Fullness of the inclusion gives
   the sheafification adjunction of `def-weil-pbc-sheafification`.
4. By `lem-sfb-transfinite-plus-finite-limits`, that same corestricted functor preserves
   finite limits. The adjunction and this preservation give `HasSheafify J A`.
5. Apply `lem-sfb-abelian-sheaves-left-exact-reflector` to this reflector and the abelian
   category `A`, obtaining an abelian structure on the Hom-tested sheaf category.
-/
theorem hasSheafify_and_nonempty_abelian_of_isGrothendieckAbelian
    {C : Type v} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Type u) [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A] :
    HasSheafify J A ∧ Nonempty (Abelian (Sheaf J A)) := by
  let : HasSheafify J A := hasSheafify_of_isGrothendieckAbelian J A
  exact ⟨inferInstance, ⟨sheafIsAbelian⟩⟩

end CategoryTheory.GrothendieckTopology

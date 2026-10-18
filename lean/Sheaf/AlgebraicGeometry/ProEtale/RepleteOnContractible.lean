/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.CategoryTheory.RepleteSheafTopos
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
import Sheaf.AlgebraicGeometry.ProEtale.WeakContractibleEquivalences

/-!
# Sequential limits on weakly contractible pro-étale objects

Source: literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
`sk-prop-pe-replete/det-pe-replete-on-contractible.md` and its proof
(blueprint: det-pe-replete-on-contractible).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Every transition and every limit projection of an epimorphic inverse sequence is
surjective on sections over a weakly contractible object.

Source: blueprint main-20261015, `sec-proetale-coefficients`, unit `sk-prop-pe-replete`,
`det-pe-replete-on-contractible.md` and `det-pe-replete-on-contractible.proof.md`
(blueprint: det-pe-replete-on-contractible).

The hypothesis `hW` uses the existing weak-contractibility definition, equivalently
condition 3 of `det-pe-weak-contractible-equivalences`: epimorphisms of sheaves induce
surjections on sections at `W`. Values lie in `Type (max (u + 1) w)`, allowing arbitrary
larger sets without equating the object and morphism universes of the site.

Proof:
1. Apply condition 3 of `det-pe-weak-contractible-equivalences` to every adjacent
   transition. In terms of `hW`, epimorphisms are locally surjective, and `hW` gives
   surjectivity on `W`-sections.
2. Fix `m` and a section `a` of `F_m` at `W`. Choose a preimage under each surjective
   transition for each target section. Starting with `b_0 = a`, recursively apply
   these choices at indices `m + r` to construct `b_r` at all stages above `m`.
   The preimage equations give adjacent compatibility above `m`.
3. Set `x_{m+r} = b_r` and define the finitely many earlier `x_n` by applying the
   transition maps in descending order. Compatibility below `m` holds by definition,
   compatibility from `m` upwards by step 2, and `x_m = a`. For `m = 0` the earlier
   range is empty. These choices concern sets of sections, not sheaf morphisms.
4. The sectionwise limit formula of `det-pe-replete-definition` identifies this tuple
   with a section of `limit F` at `W`, and `limit.π F (op m)` evaluates it to `x_m = a`.
   As `a` and `m` were arbitrary, every limit projection is surjective on sections.
-/
theorem proetale_surjective_sections_of_epi_tower
    (X : Scheme.{u}) (F : ℕᵒᵖ ⥤ Sheaf (ProEt.topology X) (Type (max (u + 1) w)))
    (hF : ∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op))
    (W : X.ProEt) (hW : (ProEt.topology X).IsWeaklyContractible.{max (u + 1) w} W) :
    (∀ n : ℕ,
      Function.Surjective ((F.map (homOfLE (Nat.le_succ n)).op).hom.app (op W))) ∧
    (∀ m : ℕ, Function.Surjective ((limit.π F (op m)).hom.app (op W))) := by
  sorry

end AlgebraicGeometry.Scheme

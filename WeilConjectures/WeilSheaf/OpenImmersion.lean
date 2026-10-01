/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Category

/-!
# Direct images of Weil sheaves along an open immersion

The ordinary direct image `j_*`, the higher direct images `Rⁱj_*`, the extension by zero `j_!`
and the canonical map `j_! ⟶ j_*` along an open immersion. Placeholders with `sorry` bodies;
see `WeilConjectures.WeilSheaf.Defs`.

## Main declarations

- `AlgebraicGeometry.WeilSheaf.directImage`, `AlgebraicGeometry.WeilSheaf.extensionByZero` and
  `AlgebraicGeometry.WeilSheaf.extensionByZeroToDirectImage`: the two extensions along an open
  immersion and the canonical map between them.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

-- TODO(unify): sk-d-real-boundary
/-- The *ordinary* sheaf direct image `j_*` along an open immersion `j`; its stalks at the
missing points are the inertia invariants. -/
noncomputable def directImage (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X := sorry

-- TODO(unify): sk-d-real-boundary
/-- The higher direct image `Rⁱj_*` along an open immersion `j`. -/
noncomputable def higherDirectImage (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] (i : ℕ) :
    WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X := sorry

-- TODO(unify): sk-prop-sf-open-closed-triangle
/-- Extension by zero `j_!` along an open immersion `j`. -/
noncomputable def extensionByZero (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    WeilSheaf k₀ l U ⥤ WeilSheaf k₀ l X := sorry

-- TODO(unify): sk-prop-sf-open-closed-triangle
instance (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    (directImage (k₀ := k₀) (l := l) j).Additive := sorry

-- TODO(unify): sk-prop-sf-open-closed-triangle
instance (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))] :
    (extensionByZero (k₀ := k₀) (l := l) j).Additive := sorry

-- TODO(unify): sk-prop-sf-open-closed-triangle
/--
The canonical map `j_! ⟶ j_*`, whose cokernel is the boundary sheaf `B` supported on the
complement of `U`:

```
  j_! F ──────▶ j_* F ──────▶ B ──────▶ 0
    │             │
    │ j_! α       │ j_* α
    ▼             ▼
  j_! G ──────▶ j_* G
```
-/
noncomputable def extensionByZeroToDirectImage (j : U ⟶ X) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    extensionByZero (k₀ := k₀) (l := l) j ⟶ directImage j := sorry

end WeilSheaf

end AlgebraicGeometry

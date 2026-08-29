/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Conservative

/-!
# The comparison `f_! ⟶ f_*` is an isomorphism for a proper morphism

For a proper morphism `f : X ⟶ Y` admitting a compactification, the canonical comparison
`ι_f : f_! ⟶ f_*` of `WeilConjectures.SixFunctors.LowerShriek.Comparison` is an isomorphism.

The proof runs in two steps. First, for an open immersion `j : U ⟶ X` whose range is clopen,
the comparison `j_! ⟶ j_*` is an isomorphism: the range of `j` and its open complement `W`
are complementary opens of `X`, the comparison restricts to an isomorphism along `j` for
formal reasons (`AlgebraicGeometry.Etale.isIso_openImmersionRestriction_map_lowerShriekToLowerStar`)
and along `W` because both sides vanish there
(`AlgebraicGeometry.Etale.isIso_openImmersionRestriction_openImmersionLowerShriekToLowerStar`),
and the two restrictions are jointly conservative
(`AlgebraicGeometry.Etale.isIso_of_isCompl_of_isIso_openImmersionRestriction`).

Second, `AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar_of_isIso` reduces `ι_f` to the
comparison for the open immersion `i` of the chosen compactification. Properness of `f` enters
only through `AlgebraicGeometry.Compactification.isClopen_range_openImmersion`: since the
structure morphism `g` of the compactification is separated, `i` is proper as soon as `i ≫ g`
is, and a proper open immersion has clopen range.

## Main results

- `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClopen_range`: the
  comparison `j_! ⟶ j_*` is an isomorphism for an open immersion `j` with clopen range.
- `AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar`: for a proper `f`, the comparison
  `ι_f : f_! ⟶ f_*` is an isomorphism.
-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

section Clopen

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- **The comparison `j_! ⟶ j_*` is an isomorphism for an open immersion `j` with clopen
range.** The range of `j` and its complement `W` are complementary opens of `X`, the
comparison restricts to an isomorphism along `j` for formal reasons and along `W` because
both sides vanish there, and the two restrictions are jointly conservative. -/
theorem Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClopen_range
    (hj : IsClopen (Set.range j.base)) :
    IsIso (Etale.openImmersionLowerShriekToLowerStar A j) := by
  let W := Scheme.Hom.complOpensRange j hj.isClosed
  have hcompl : IsCompl j.opensRange W.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    exact Scheme.Hom.isCompl_complOpensRange j hj.isClosed
  have hjk : Set.range j.base ∩ Set.range W.ι.base = ∅ := by
    rw [Scheme.Hom.range_ι_complOpensRange]
    exact Set.inter_compl_self _
  have happ : ∀ F, IsIso ((Etale.openImmersionLowerShriekToLowerStar A j).app F) := fun F ↦
    Etale.isIso_of_isCompl_of_isIso_openImmersionRestriction A j W.ι _ hcompl inferInstance
      (Etale.isIso_openImmersionRestriction_openImmersionLowerShriekToLowerStar A j W.ι hjk F)
  exact NatIso.isIso_of_isIso_app _

end Clopen

section Proper

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [IsProper f]

/-- **For a proper morphism `f`, the canonical comparison `ι_f : f_! ⟶ f_*` is an
isomorphism.**

```
       i
   X ─────→ P            f_! = g_* ∘ i_! ──→ g_* ∘ i_* ≅ f_*
    ╲       │
   f ╲      │ g
      ↘     ↓
            Y
```
-/
instance Etale.isIso_lowerShriekToLowerStar :
    IsIso (Etale.lowerShriekToLowerStar A f) :=
  Etale.isIso_lowerShriekToLowerStar_of_isIso A f
    (Etale.isIso_openImmersionLowerShriekToLowerStar_of_isClopen_range A
      (HasCompactification.compactification f).i
      ((HasCompactification.compactification f).isClopen_range_openImmersion ‹IsProper f›))

end Proper

end AlgebraicGeometry

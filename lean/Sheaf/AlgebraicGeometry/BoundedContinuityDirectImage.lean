/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuityDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Bounded-below continuity of higher direct images

Source: Weil conjectures blueprint, snapshot main-20261015,
sec-proetale-coefficients/sk-cor-pe-bounded-continuity,
sk-lem-bounded-continuity-direct-image.md and its proof
(blueprint: det-lem-bounded-continuity-direct-image).

## Main definitions

- `moduleComplexHigherDirectImage`: higher direct image, read as an abelian sheaf.

## Main statements

- `boundedContinuityDirectImage`: invertibility of the canonical filtered-colimit comparison.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Integer-degree higher direct image of a complex of modules over an arbitrary ring
sheaf, regarded as an abelian sheaf. Localize the module complex, apply the recorded
universal right-derived module direct image over `g_*A`, take degree-q homology, and
forget scalars. This reuses `Scheme.ProEt.ringHigherDirectImage` rather than choosing a
second derived construction. The coefficient sheaf A need not come from the target.
For bounded-below complexes this also agrees with deriving the direct image of the
underlying abelian sheaves: the exact forgetful functor commutes with homology and
underlying injective module sheaves are direct-image acyclic.

Source: the blueprint, sk-lem-bounded-continuity-direct-image.md and its proof, first
paragraph; Stacks Project, Tag 0D6I
(blueprint: det-lem-bounded-continuity-direct-image). -/
noncomputable def moduleComplexHigherDirectImage {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (A : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}) (q : ℤ) :
    CochainComplex (SheafOfModules.{u + 1} A) ℤ ⥤
      Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1} :=
  DerivedCategory.Q ⋙ Scheme.ProEt.ringHigherDirectImage g A q ⋙
    SheafOfModules.toSheaf.{u + 1}
      ((Scheme.proEtaleSheafDirectImage g RingCat.{u + 1}).obj A)

/-- Higher direct images commute with filtered colimits of complexes having one common
strict lower bound. `colimit.post` is the canonical map: its composite with the i-th
colimit leg is higher direct image of the canonical map K_i to the termwise colimit.
Both sides and the isomorphism are in abelian sheaves on the original target site.

Source: Weil conjectures blueprint, snapshot main-20261015,
sk-lem-bounded-continuity-direct-image.md and its proof
(blueprint: det-lem-bounded-continuity-direct-image).

Proof:
Apply det-pe-bounded-continuity-direct-image with X=Y, Y=Z, f=g and R=A, obtaining
invertibility of the canonical comparison in module sheaves over g_*A. Its displayed
colimit.desc is definitionally colimit.post for localization followed by the module
higher direct image. Hence that composite preserves the colimit of K. The forgetful
functor from g_*A-module sheaves to abelian sheaves preserves colimits, by the module
sheafification construction. Composing these preservation statements gives invertibility
of colimit.post for moduleComplexHigherDirectImage, with the original common lower
bound a and every integer q. -/
theorem boundedContinuityDirectImage {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [QuasiCompact g] [QuasiSeparated g]
    (A : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1})
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex (SheafOfModules.{u + 1} A) ℤ)
    (a : ℤ) (hK : ∀ (i : I) (n : ℤ), n < a → IsZero ((K.obj i).X n)) (q : ℤ) :
    IsIso (colimit.post K (moduleComplexHigherDirectImage g A q)) := by
  let F := DerivedCategory.Q ⋙ Scheme.ProEt.ringHigherDirectImage g A q
  have hF : IsIso (colimit.post K F) :=
    Scheme.ProEt.boundedContinuityDirectImage g A K a hK q
  have := hF
  have : PreservesColimit K F := preservesColimit_of_isIso_post F K
  change IsIso (colimit.post K (F ⋙ SheafOfModules.toSheaf.{u + 1}
    ((Scheme.proEtaleSheafDirectImage g RingCat.{u + 1}).obj A)))
  infer_instance

end AlgebraicGeometry.ProEtale

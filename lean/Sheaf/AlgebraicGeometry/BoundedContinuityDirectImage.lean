/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import Mathlib.Algebra.Category.Grp.AB

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
sheaf, regarded as an abelian sheaf. Forget scalars termwise, localize, apply the recorded
universal right-derived direct image, and take degree-q homology. On bounded-below complexes
this is the underlying abelian sheaf of the module-valued derived direct image: injective
module sheaves are acyclic for direct image on underlying abelian sheaves, and the exact
forgetful functor identifies the two computations. The target coefficient ring would be
g_*A, so A need not come from the target. K-injective resolutions and derived categories
here are supplied by the Grothendieck property of the actual pro-etale sheaf categories.

Source: the blueprint, sk-lem-bounded-continuity-direct-image.md and its proof, first
paragraph; Stacks Project, Tag 0D6I
(blueprint: det-lem-bounded-continuity-direct-image). -/
noncomputable def moduleComplexHigherDirectImage {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (A : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1}) (q : ℤ) :
    CochainComplex (SheafOfModules.{u + 1} A) ℤ ⥤
      Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1} :=
  let C := Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}
  let D := Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1}
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} C
  letI := HasDerivedCategory.ofIsGrothendieckAbelian.{u + 1} D
  (SheafOfModules.toSheaf.{u + 1} A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    DerivedCategory.Q ⋙
    (lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorOfQuasiIsoResolutions
      (fun L ↦ ⟨(CochainComplex.kInjectiveResolutionFunctor.{u + 1} C).obj L,
        (CochainComplex.toKInjectiveResolution.{u + 1} C).app L,
        inferInstance, (CochainComplex.monoQuasiIso_toKInjectiveResolution_app C L).2⟩) ⋙
    DerivedCategory.homologyFunctor D q

/-- Higher direct images commute with filtered colimits of complexes having one common
strict lower bound. `colimit.post` is the canonical map: its composite with the i-th
colimit leg is higher direct image of the canonical map K_i to the termwise colimit.
Both sides and the isomorphism are in abelian sheaves on the original target site.

Source: Weil conjectures blueprint, snapshot main-20261015,
sk-lem-bounded-continuity-direct-image.md and its proof
(blueprint: det-lem-bounded-continuity-direct-image).

Proof for stage 3:
Apply det-pe-bounded-continuity-direct-image, renaming its schemes X,Y as Y,Z, its
morphism f as g and its ring sheaf R as A. Read its conclusion on underlying abelian
sheaves. The exact forgetful functor and the acyclicity of underlying injective module
sheaves identify its R^q g_* with moduleComplexHigherDirectImage. The complex colimit
is the termwise module-sheaf colimit, with the same common lower bound a. Naturality
identifies each cocone leg with higher direct image of the original colimit inclusion;
the universal property of the sheaf colimit then identifies its canonical comparison
with colimit.post K (moduleComplexHigherDirectImage g A q). Thus this map is invertible
for every integer q, including q<a. -/
theorem boundedContinuityDirectImage {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    [QuasiCompact g] [QuasiSeparated g]
    (A : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1})
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex (SheafOfModules.{u + 1} A) ℤ)
    (a : ℤ) (hK : ∀ (i : I) (n : ℤ), n < a → IsZero ((K.obj i).X n)) (q : ℤ) :
    IsIso (colimit.post K (moduleComplexHigherDirectImage g A q)) := by
  sorry

end AlgebraicGeometry.ProEtale

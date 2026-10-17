/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Cohomology with support

Let `i : Z ⟶ X` be a closed immersion with open complement `j : U ⟶ X`. The functor of
*sections with support in `Z`* sends a sheaf `F` on `X` to

`Γ_Z(X, F) = ker (Γ(X, F) ⟶ F(U))`,

the global sections whose restriction to the open complement vanishes. The *cohomology with
support* `H^q_Z(X, F)` is its `q`-th right derived functor, and for complexes it is the
`q`-th cohomology object of the total right derived functor `RΓ_Z(X, -)` on the derived
category (blueprint `def-pur-support-cohomology`).

The functor of sections with support is defined for an arbitrary site `(C, J)` with global
sections and an object `U` of `C` (`CategoryTheory.Sheaf.ΓSupport`), and specialised to the
small étale site (`AlgebraicGeometry.Etale.sectionsWithSupport`) and to the small pro-étale
site (`AlgebraicGeometry.ProEtale.sectionsWithSupport`), where `U` is the open complement of
`Z`.

## Main definitions

- `CategoryTheory.Sheaf.ΓSupport`: the sections with support away from an object `U`.
- `AlgebraicGeometry.Etale.sectionsWithSupport`, `AlgebraicGeometry.Etale.supportCohomology`,
  `AlgebraicGeometry.Etale.rightDerivedSectionsWithSupport`,
  `AlgebraicGeometry.Etale.derivedSupportCohomology`: `Γ_Z(X, -)`, `H^q_Z(X, -)` on sheaves,
  `RΓ_Z(X, -)` and `H^q_Z(X, -)` on the derived category of the small étale site.
- `AlgebraicGeometry.ProEtale.sectionsWithSupport`, `AlgebraicGeometry.ProEtale.supportCohomology`,
  `AlgebraicGeometry.ProEtale.rightDerivedSectionsWithSupport`,
  `AlgebraicGeometry.ProEtale.derivedSupportCohomology`: the same on the small pro-étale site.
-/

@[expose] public section

universe u' u v w

open CategoryTheory Limits Opposite

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{w} A] [Abelian A] [HasSheafify J A] [HasGlobalSectionsFunctor J A]

/-- The sections with support away from an object `U` of the site: the kernel
`F ↦ ker (Γ(F) ⟶ F(U))` of the restriction from the global sections to the sections on `U`.
For `U` the open complement of a closed subscheme `Z` this is the functor `Γ_Z` of sections
with support in `Z`. -/
noncomputable def Sheaf.ΓSupport (U : Cᵒᵖ) : Sheaf J A ⥤ A :=
  kernel (Sheaf.natTransΓRes J A U)

/-- The inclusion `Γ_Z(F) ⟶ Γ(F)` of the sections with support. -/
noncomputable def Sheaf.ΓSupportι (U : Cᵒᵖ) : Sheaf.ΓSupport J A U ⟶ Sheaf.Γ J A :=
  kernel.ι _

instance (U : Cᵒᵖ) (F : Sheaf J A) : Mono ((Sheaf.ΓSupportι J A U).app F) := by
  have : Mono (Sheaf.ΓSupportι J A U) := by dsimp [Sheaf.ΓSupportι]; infer_instance
  infer_instance

@[reassoc (attr := simp)]
lemma Sheaf.ΓSupportι_app_comp_ΓRes (U : Cᵒᵖ) (F : Sheaf J A) :
    (Sheaf.ΓSupportι J A U).app F ≫ Sheaf.ΓRes F U = 0 := by
  have := congr_app (kernel.condition (Sheaf.natTransΓRes J A U)) F
  rw [NatTrans.comp_app, NatTrans.app_zero] at this
  exact this

instance (U : Cᵒᵖ) : (Sheaf.ΓSupport J A U).Additive where
  map_add {F G f g} := by
    rw [← cancel_mono ((Sheaf.ΓSupportι J A U).app G)]
    simp only [Preadditive.add_comp, NatTrans.naturality, Functor.map_add,
      Preadditive.comp_add]

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

namespace Etale

variable [HasSmallSiteSheafify A] {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Blueprint `def-pur-support-cohomology`: Cohomology with support.

The functor `Γ_Z(X, -)` of sections with support in the closed subscheme `i : Z ⟶ X` of étale
sheaves on `X`: `Γ_Z(X, F) = ker (Γ(X, F) ⟶ F(U))` for the open complement `U` of `Z`. -/
noncomputable def sectionsWithSupport : Sheaf X.smallEtaleTopology A ⥤ A :=
  Sheaf.ΓSupport X.smallEtaleTopology A (op (Scheme.Etale.mk i.openComplement.ι))

instance : (sectionsWithSupport A i).Additive := by
  dsimp [sectionsWithSupport]; infer_instance

/-- Blueprint `def-pur-support-cohomology`: Cohomology with support.

The cohomology with support `H^q_Z(X, F)` of an étale sheaf `F` on `X`: the `q`-th right
derived functor of the sections with support in `Z`. -/
noncomputable def supportCohomology (q : ℕ) : Sheaf X.smallEtaleTopology A ⥤ A :=
  (sectionsWithSupport A i).rightDerived q

/-- Blueprint `def-pur-support-cohomology`: Cohomology with support.

The derived sections with support `RΓ_Z(X, -) : D(X_ét) ⥤ D(A)`, the total right derived
functor of the sections with support in `Z`. -/
noncomputable def rightDerivedSectionsWithSupport :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ DerivedCategory A :=
  (sectionsWithSupport A i).rightDerivedFunctor

/-- Blueprint `def-pur-support-cohomology`: Cohomology with support.

The cohomology with support `H^q_Z(X, K) = H^q(RΓ_Z(X, K))` of a complex `K` of étale sheaves
on `X`. -/
noncomputable def derivedSupportCohomology (q : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology A) ⥤ A :=
  rightDerivedSectionsWithSupport A i ⋙ DerivedCategory.homologyFunctor A q

end Etale

namespace ProEtale

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- Blueprint `def-pur-support-cohomology`: Cohomology with support.

The functor `Γ_Z(X, -)` of sections with support in the closed subscheme `i : Z ⟶ X` of
sheaves on the small pro-étale site of `X`: `Γ_Z(X, F) = ker (Γ(X, F) ⟶ F(U))` for the open
complement `U` of `Z`. -/
noncomputable def sectionsWithSupport : Sheaf (Scheme.ProEt.topology X) A ⥤ A :=
  Sheaf.ΓSupport (Scheme.ProEt.topology X) A (op (Scheme.ProEt.mk i.openComplement.ι))

instance : (sectionsWithSupport A i).Additive := by
  dsimp [sectionsWithSupport]; infer_instance

/-- Blueprint `def-pur-support-cohomology`: Cohomology with support.

The cohomology with support `H^q_Z(X, F)` of a pro-étale sheaf `F` on `X`: the `q`-th right
derived functor of the sections with support in `Z`. -/
noncomputable def supportCohomology (q : ℕ) : Sheaf (Scheme.ProEt.topology X) A ⥤ A :=
  (sectionsWithSupport A i).rightDerived q

/-- Blueprint `def-pur-support-cohomology`: Cohomology with support.

The derived sections with support `RΓ_Z(X, -) : D(X_proét) ⥤ D(A)`. -/
noncomputable def rightDerivedSectionsWithSupport :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤ DerivedCategory A :=
  (sectionsWithSupport A i).rightDerivedFunctor

/-- Blueprint `def-pur-support-cohomology`: Cohomology with support.

The cohomology with support `H^q_Z(X, K) = H^q(RΓ_Z(X, K))` of a complex `K` of pro-étale
sheaves on `X`. -/
noncomputable def derivedSupportCohomology (q : ℤ) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤ A :=
  rightDerivedSectionsWithSupport A i ⋙ DerivedCategory.homologyFunctor A q

end ProEtale

end AlgebraicGeometry

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices

/-! # Scalar transport through restricted section complexes

Source: Stacks Project, Tags 01E4 and 01E5.
(blueprint: lem-pc-resolution-sections-homology-scalar)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

/-- The homology comparison of restricted section complexes is semilinear.
Source: Stacks Project, Tags 01E4 and 01E5.
(blueprint: lem-pc-resolution-sections-homology-scalar)

Proof: Put U = f inverse V. The ring map displayed here is pullback of sections
along f: the canonical chart V.toSpecΓ cancels ΓSpecIso, and restriction to the
whole of U is the identity. In every degree, R.components expresses R.sections
as a module morphism on U followed by the restriction comparison and restriction
along the equality U.ι_image_top. Each of these maps preserves multiplication
by the pulled-back section. Hence the section complex comparison is semilinear
for Γ(S,V) to Γ(U,O_U). Restrict scalars on the global section complex along
this ring map. The comparison is then a map of complexes of Γ(S,V)-modules;
its map on homology is linear. Exact forgetful evaluation and its homology
comparison identify that map with the three arrows T below. Thus T(b*y)=a*T(y).
This uses neither the augmentation nor resolution naturality: it is a statement
about the pinned degreewise section comparison. It also holds for p=0, empty
opens, and zero modules, since the same module maps and homology comparisons
are used in those cases. -/
theorem resolutionSectionsHomology_scalar
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (I : InjectiveResolution F)
    (p : ℕ) (V : S.Opens) (R : RestrictedResolutionSections I (f ⁻¹ᵁ V)) :
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let T := (((RingedSpace.globalSectionsComplex R.resolution).sc p).mapHomologyIso
      (forget₂ _ AddCommGrpCat.{u})).inv ≫
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) p).map
        R.sections.hom ≫
      (((((SheafOfModules.forget S.ringCatSheaf).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K).sc p).mapHomologyIso
          (PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
            (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V))).hom
    ∀ (a : Γ(S, V)) (y : (RingedSpace.globalSectionsComplex R.resolution).homology p),
      T ((((Scheme.ΓSpecIso Γ(S, V)).inv ≫ h.appTop).hom a) • y) = a •
        (show (sectionCohomologyPresheaf K p).obj (op V) from T y) := by
  sorry

end AlgebraicGeometry.Scheme.Modules

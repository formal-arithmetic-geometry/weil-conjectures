/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-! # Scalar compatibility of the normalized resolution class

Source: Stacks Project, Tags 01E4, 01E5 and 03FD.
(blueprint: lem-pc-resolution-section-scalar-map)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

/-- The canonical section class map intertwines multiplication endomorphisms.
No Ext comparison, affine open, finiteness or quasi-coherence is assumed.
Source: Stacks Project, Tags 01E4 and 01E5; naturality of derived functors.
(blueprint: lem-pc-resolution-section-scalar-map)

Proof: Write U = f inverse V and M = F restricted to U. For a section a of O_S on V,
let b be its image in Gamma(U,O_U). The canonical chart and GammaSpecIso cancel, so b
is exactly the scalar displayed below. Multiplication by b is an endomorphism of M.
Lift it to a cochain endomorphism of R.resolution. Alternatively multiply the restriction of
I to U termwise by b, then conjugate by R.comparison. Both lifts induce multiplication by b
on M, because R.augmentation preserves the resolved module. By the comparison theorem
for injective resolutions they are homotopic. R.components identifies their section
complex maps. Homotopic maps induce equal maps on homology, and isoRightDerivedObj is
natural for these lifts. The section-complex endomorphism is multiplication by a when
viewed as sections over V of f_* I. Exact evaluation preserves this endomorphism;
sectionCohomologyTheta is a presheaf module morphism, and the final inverse resolution
comparison is a sheaf module morphism. Thus the displayed map takes cohomology of
multiplication by b to multiplication by a. There is no vanishing argument here.
Degree zero gives multiplication on sections; empty opens and zero modules give zero
maps, so the same identity holds. -/
theorem resolutionSectionClass_map_smulHom
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (I : InjectiveResolution F)
    (p : ℕ) (V : S.Opens) (R : RestrictedResolutionSections I (f ⁻¹ᵁ V)) :
    let h := f.resLE V (f ⁻¹ᵁ V) le_rfl ≫ V.toSpecΓ
    let M := (restrictFunctor (f ⁻¹ᵁ V).ι).obj F
    let C := RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p
    let c := resolutionSectionClass R.resolution
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
      V R.sections p ≫ Hom.app (I.isoRightDerivedObj (pushforward f) p).inv V
    ∀ (a : Γ(S, V)) (x : C.obj M),
      c ((C.map (M.smulHom (((Scheme.ΓSpecIso Γ(S, V)).inv ≫ h.appTop).hom a))).hom x) =
        a • c x := by sorry

end AlgebraicGeometry.Scheme.Modules

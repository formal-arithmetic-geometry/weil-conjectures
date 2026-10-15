/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.CategoryTheory.SiteMorphismComposition
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import Sheaf.CategoryTheory.SitePullbackAbelianUnderlying
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization

/-!
# Limits under inverse image along a pro-etale immersion

Source: Stacks Project, Tag 09AA (1), with open slice restriction, and Modules on Sites,
Tags 03D2, 03DB and 04JC
(blueprint: lem-weil-pbc-proetale-immersion-limit-preservation).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Inverse image along a locally closed immersion preserves all small limits, also on
abelian and module sheaves. The module underlying-sheaf comparison is natural; the graph
condition on arbitrary test sheaves expresses transport of the scalar action under the
finite-product comparison. The final functor is characterized on both objects and maps
by the specified sheaf tensor extension, so it is not an arbitrary exact functor.

Source: Stacks Project, Tag 09AA (1), and Modules on Sites, Tags 03D2, 03DB and 04JC
(blueprint: lem-weil-pbc-proetale-immersion-limit-preservation).

Proof:
1. For an affine closed immersion, use the extra left adjoint of inverse image
   (lem-weil-pbc-affine-closed-inverse-image-left-adjoint). A right adjoint preserves
   limits (lem-weil-pbc-right-adjoint-preserves-limits), which exist sectionwise
   (lem-weil-pbc-site-sheaf-sets-limits-sectionwise).
2. For an open immersion, identify the site with a slice by
   lem-weil-proetale-weakly-etale-localization. Inverse image is sectionwise restriction:
   the object over the open is terminal in the inverse-image indexing diagram.
   Sectionwise limits therefore commute with this restriction.
3. Cover the target of a closed immersion by affine opens. Their inverse images are
   affine. By lem-weil-pbc-site-morphism-composition, the restricted limit comparison
   is the affine closed comparison after open restriction. It is an isomorphism by
   steps 1 and 2. Local inverses glue by the sheaf condition, giving the global result.
4. Factor the immersion into closed then open; inverse-image composition gives the result.
5. Use lem-weil-pbc-site-pullback-abelian-underlying and componentwise group operations
   on limits (lem-weil-pbc-algebraic-sheaf-iff-underlying-sets) to obtain the abelian
   assertion. Additivity and exactness are lem-weil-pbc-site-pullback-abelian-exact.
6. Apply finite-product-preserving inverse image to the module action. All module laws
   are preserved equalities of composites. Kernels and cokernels have the underlying
   abelian kernels and cokernels, with cokernels sheafified. Limits are created on
   underlying sheaves (lem-weil-pbc-module-sheaves-limits-sectionwise). The limit
   comparison is linear on all projections, hence its inverse is linear as well.
7. For a ring isomorphism c, the map m tensor s to c inverse(s) times m, with inverse
   m to m tensor 1, identifies extension with transport of scalar action. Balancing
   proves the inverse identities and naturality. This transport preserves kernels,
   cokernels and all limits. In particular it preserves countable products. -/
theorem proEtale_immersion_inverseImage_preservesLimits
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsImmersion f] :
    PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleSheafInverseImage f (Type (u + 1))) ∧
    PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}) ∧
    ∀ R : Sheaf (ProEt.topology X) CommRingCat.{u + 1},
      ∃ (_ : (proEtaleModuleInverseImage f R).Additive),
        PreservesFiniteLimits (proEtaleModuleInverseImage f R) ∧
        PreservesFiniteColimits (proEtaleModuleInverseImage f R) ∧
        PreservesLimitsOfSize.{u + 1, u + 1} (proEtaleModuleInverseImage f R) ∧
        Nonempty (proEtaleModuleInverseImage f R ⋙ SheafOfModules.toSheaf _ ≅
          SheafOfModules.toSheaf _ ⋙ proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}) ∧
        (∃ (eR : (proEtaleSheafInverseImage f (Type (u + 1))).obj
            ((sheafCompose (ProEt.topology X) (CategoryTheory.forget CommRingCat.{u + 1})).obj R) ≅
            (sheafCompose (ProEt.topology Y) (CategoryTheory.forget CommRingCat.{u + 1})).obj
              ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
          (eM : proEtaleModuleInverseImage f R ⋙ SheafOfModules.toSheaf _ ⋙
              sheafCompose (ProEt.topology Y) (CategoryTheory.forget AddCommGrpCat.{u + 1}) ≅
            (SheafOfModules.toSheaf _ ⋙
              sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})) ⋙
                proEtaleSheafInverseImage f (Type (u + 1))),
          ∀ (M : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
              (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
            (T : Sheaf (ProEt.topology X) (Type (u + 1)))
            (a : T ⟶ (sheafCompose (ProEt.topology X)
              (CategoryTheory.forget CommRingCat.{u + 1})).obj R)
            (b t : T ⟶ (SheafOfModules.toSheaf _ ⋙
              sheafCompose (ProEt.topology X) (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj M),
            (∀ (U : X.ProEtᵒᵖ) (x : T.obj.obj U),
              @id (M.val.obj U) (t.hom.app U x) =
                @id (R.obj.obj U) (a.hom.app U x) •
                  @id (M.val.obj U) (b.hom.app U x)) →
            ∀ (V : Y.ProEtᵒᵖ)
              (x : ((proEtaleSheafInverseImage f (Type (u + 1))).obj T).obj.obj V),
              @id (((proEtaleModuleInverseImage f R).obj M).val.obj V)
                ((eM.inv.app M).hom.app V
                  (((proEtaleSheafInverseImage f (Type (u + 1))).map t).hom.app V x)) =
                @id (((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R).obj.obj V)
                  (eR.hom.hom.app V
                    (((proEtaleSheafInverseImage f (Type (u + 1))).map a).hom.app V x)) •
                @id (((proEtaleModuleInverseImage f R).obj M).val.obj V)
                  ((eM.inv.app M).hom.app V
                    (((proEtaleSheafInverseImage f (Type (u + 1))).map b).hom.app V x))) ∧
        ∀ (S : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
          (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S),
          ∃ (P : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤
              SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology Y)
                (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
            (hobj : ∀ M, P.obj M = SheafOfModules.changeOfRings.{u, u + 1, u + 1}
              c.hom ((proEtaleModuleInverseImage f R).obj M)),
            (∀ (M N : SheafOfModules.{u + 1} ((sheafCompose (ProEt.topology X)
                  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) (a : M ⟶ N),
              P.map a = eqToHom (hobj M) ≫
                SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} c.hom
                  ((proEtaleModuleInverseImage f R).obj M)
                    ((proEtaleModuleInverseImage f R).map a) ≫ eqToHom (hobj N).symm) ∧
            ∃ (_ : P.Additive), PreservesFiniteLimits P ∧ PreservesFiniteColimits P ∧
              PreservesLimitsOfSize.{u + 1, u + 1} P := by
  sorry

end AlgebraicGeometry.Scheme

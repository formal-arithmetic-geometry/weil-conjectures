/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.AffinePerfectModuleModel
import Sheaf.AlgebraicGeometry.OpenDerivedRestrictionComparison
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport
import Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison
/-! # Elementwise torsion for an affine model of a supported target

Source: Stacks Project, Tag 08EJ, affine support paragraph, and Tag 06Z0.
(blueprint: new-affine-open-supported-model-torsion).
-/
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
/-- Vanishing away from the zero locus implies power annihilation on affine cohomology.
Source: Stacks Project, Tag 08EJ, affine support paragraph, and Tag 06Z0.
(blueprint: new-affine-open-supported-model-torsion).

Proof: Fix i and put N = H^i(M). Compare F with affine derived tilde followed by
canonical affine-site transport: the two comparisons after Q lift to a natural
isomorphism by localization. Exactness of tilde identifies the transported sheaf
of N with H^i(F(M)). Apply homology to hM and undo affine-site transport; exact
open restriction and its stalk isomorphism identify this sheaf with the affine
restriction of H^i(E'[k]). The homology shift isomorphism identifies its stalks
with stalks of H^(i+k)(E'). Compatibility of f with restriction and the affine
chart identifies D(f|U) with the points of U outside the global V(f). Hence the
sheaf of N has zero stalks there. Tilde stalks are prime localizations of N,
so Module.notMem_support_iff gives disjointness of D(f|U) and Module.support A N.
LocalizedModule.subsingleton_iff_disjoint makes the localization at powers of
f|U zero. For m, its localization equals zero; the localization equality criterion
provides a power (f|U)^n annihilating m. The exponent may depend on m and i.
For f=0, n=1 works; for a unit f, N is zero; for empty U, A and N are zero.
No finite generation, boundedness, or perfectness is needed. -/
theorem affine_open_supported_model_torsion
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (f : RingCat.sectionsSubring (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))
    (E' : schemeDerivedQCohCategory X)
    (hSupport : ∀ (i : ℤ) (x : X), x ∉ X.zeroLocus (U := ⊤) {f.val (op ⊤)} →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E'.obj).val.presheaf x)))
    (U : X.Opens) (hU : IsAffineOpen U) (k : ℤ)
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} (X.sheaf.obj.obj (op U)))]
    (F : DerivedCategory (ModuleCat.{u} (X.sheaf.obj.obj (op U))) ⥤
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)))
    (hF : Nonempty (DerivedCategory.Q ⋙ F ≅
      (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q))
    (M : DerivedCategory (ModuleCat.{u} (X.sheaf.obj.obj (op U))))
    (hM : Nonempty (F.obj M ≅
      (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
        (E'.obj⟦k⟧))) :
    ∀ (i : ℤ) (m : (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (X.sheaf.obj.obj (op U))) i).obj M),
      ∃ n : ℕ, (f.val (op U)) ^ n • m = 0 := by sorry
end AlgebraicGeometry.Scheme

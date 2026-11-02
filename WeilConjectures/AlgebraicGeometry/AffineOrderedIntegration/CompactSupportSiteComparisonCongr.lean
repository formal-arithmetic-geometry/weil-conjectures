/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationData
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement

/-! Compact-support site comparison transport across equal projections. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity AffineLinePurity VectorIntegrationSite

private theorem map_id_id {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {a : D} {x : C} (s : a ⟶ F.obj x) :
    s = s ≫ F.map ((𝟙 x) ≫ 𝟙 x) := by simp

/-- The canonical site comparison is compatible with transport of the chosen lower shriek
along an equality of the underlying projections.

Source: the identity specialization of compactification independence, Stacks Tag 0F7I,
and the canonical reassociations in the final paragraph of projection-purity agreement
(blueprint: lem-pur-compact-support-site-comparison-congr).

Proof: eliminate the equality of projections. The two compactification instances then
agree by proof irrelevance. The pro-etale congruence is the identity by its definition.
The etale congruence is the comparison of the chosen compactification with itself;
the compactification comparison identity law makes it the identity. The other etale
factor is the same self-comparison and is also the identity. Functoriality sends the
two identity factors to the identity, and the two unit laws finish the equality.
This argument also applies to the empty scheme, the zero complex and the zero ring. -/
theorem compactSupportSiteComparison_congr
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    {f g : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g]
    (h : f = g)
    (W : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (rightDerivedLowerShriekCongr (ModuleCat.{u + 1} A) h).hom.app
        ((comparison A X).obj W.obj) ≫
      (compactSupportSiteComparison A
        (HasCompactification.compactification g)).hom.app W =
      (compactSupportSiteComparison A
        (HasCompactification.compactification f)).hom.app W ≫
        (comparison A Y).map
          ((Etale.rightDerivedLowerShriekIso A
            (HasCompactification.compactification f)).hom.app W.obj ≫
            (Etale.rightDerivedLowerShriekCongr A h).hom.app W.obj) := by
  subst g
  have he := (Etale.unboundedEtaleCompactSupport_comparison_coherence A f).1
    (HasCompactification.compactification f)
  have hi : Etale.rightDerivedLowerShriekIso A
      (HasCompactification.compactification f) = Iso.refl _ := he
  have hg : Etale.rightDerivedLowerShriekCongr A (rfl : f = f) = Iso.refl _ := he
  simp only [rightDerivedLowerShriekCongr_rfl, hi, hg, Iso.refl_hom,
    NatTrans.id_app, Category.id_comp]
  exact map_id_id (comparison A Y) _

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration

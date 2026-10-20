/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.EtaleTensorPositiveObjectCohomology
import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
import Sheaf.AlgebraicGeometry.ZariskiOpenRestrictionInjectives
import Sheaf.CategoryTheory.AcyclicCechEdgeCompatibility
import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.AlgebraicGeometry.ModuleOpenRestrictionInjectives
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
import WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor

/-! Comparison squares for additive structure-sheaf cohomology. -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- Coherent power is semilinear and the normalized etale comparison respects powers.
Source: Stacks Project, Tags 03P2, 03AZ, 03F7, 03FD and 0A3P.
(blueprint: new-coherent-power-comparison).

Proof: Choose a finite affine cover of the proper scheme. Separatedness makes all
positive tuple intersections affine. Affine module vanishing, the module/abelian
comparison, restriction of injectives and etale object vanishing make the tuples
acyclic in all three cohomology theories. The normalized Cech edges are invertible.
On each intersection identify tensor pullback of the unit module with the unit
module through tensorPullbackObjUnitToUnit. Both supplied power maps act on the
common section complex by s -> s^p. Additive edge naturality identifies this map
with the two coefficient endomorphisms. The change-of-site comparison is the
normalized family: it is natural on quasi-coherent modules, is the identity on
sections, and commutes with connecting maps. Uniqueness identifies it with the
recorded normalized comparison. The module/abelian edge is the fixed resolution
comparison by resolution normalization. Multiplication by a is a module morphism;
its resolution map is termwise scalar multiplication, so its action on module
cohomology and on the Cech edge is scalar multiplication. The ring identity
(a*s)^p = a^p*s^p therefore gives semilinearity. Additive edge naturality for the
two power maps gives the second square for every etale map satisfying the stated
formula. No etale map is needed for the first assertion. Degree zero, repeated
intersections and the empty scheme are included. The maps are already assumed
additive, so no further prime or characteristic assumption is required. -/
theorem coherentPowerComparison
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (p q : ℕ)
    (FrZ : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (unit X) ⟶
      (SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (unit X))
    (hFrZ : ∀ (U : X.Opensᵒᵖ) (s : Γ(X, U.unop)), FrZ.hom.app U s = s ^ p) :
    (∀ (a : k) (v : scalarCohomology f (unit X) q),
      structureCoherentFrobenius f q FrZ (a • v) =
        a ^ p • structureCoherentFrobenius f q FrZ v) ∧
    ∀ (FrE : structureTensorEtaleSheaf X ⟶ structureTensorEtaleSheaf X)
    (hFrE : ∀ (U : X.Etaleᵒᵖ) (s : (structureTensorEtaleSheaf X).obj.obj U),
      (tensorPullbackObjUnitToUnit U.unop.hom).app ⊤ (FrE.hom.app U s).down =
        (@id Γ(U.unop.left, ⊤)
          ((tensorPullbackObjUnitToUnit U.unop.hom).app ⊤ s.down)) ^ p)
    (x : @Sheaf.H _ _ (Opens.grothendieckTopology X)
      ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).obj (unit X))
      inferInstance (HasExt.standard _) q),
    normalizedCoherentEtaleComparison f (unit X) q
        (@Sheaf.H.map _ _ _ inferInstance (HasExt.standard _) _ _ FrZ q x) =
      Sheaf.H.map FrE q (normalizedCoherentEtaleComparison f (unit X) q x) := by
  sorry

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Sheaf.Algebra.Homology.FilteredColimitsTensor
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.RingedToposPullbackFilteredColimits
import Sheaf.Algebra.Homology.FlatTruncationTower

/-! # RingedToposAdaptedFlatResolution

Source: Stacks Project, Tag 0G7E (lemma-pullback-K-flat), adapted resolution step.
(blueprint: lem-weil-pbc-ringed-topos-pullback-adapted-flat-resolution). -/

@[expose] public section
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

/-- A flat K-flat resolution may be chosen with K-flat termwise pullback.
Source: Stacks Project, Cohomology on Sites, Tag 0G7E, first paragraph of the proof
of lemma-pullback-K-flat, using Tags 077J, 06YQ and 06YR.
(blueprint: lem-weil-pbc-ringed-topos-pullback-adapted-flat-resolution).

Proof: choose a strictly compatible tower E_n of bounded-above flat resolutions of
P.truncLE n. Each augmentation is a quasi-isomorphism. Take its degreewise filtered
colimit L, with the induced augmentation q to P. Exact filtered colimits commute
with homology, while the good truncations stabilize in each fixed degree. Hence q
is a quasi-isomorphism. Flat sheaves and K-flat complexes are closed under filtered
colimits; bounded-above flat complexes are K-flat. Thus L has flat terms and is
K-flat. The filtered-colimit preservation theorem for the specified module pullback makes
uStar preserve the displayed degreewise colimit. Each uStar(E_n) is still bounded above
and has flat terms by flat pullback, hence is K-flat. Their filtered colimit uStar(L)
is K-flat. This construction makes no K-flatness or flat-term assumption on P. -/
theorem exists_pullback_adapted_flat_resolution
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{w}} {S RI : Sheaf JD CommRingCat.{w}}
    (uInv : Sheaf JC (Type (w)) ⥤ Sheaf JD (Type (w)))
    (uPush : Sheaf JD (Type (w)) ⥤ Sheaf JC (Type (w)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      ringedSiteModules.{w} ((sheafCompose JD
        (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (hobj : ∀ M : ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R),
      uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (a : M ⟶ N),
      uStar.map a = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫ eqToHom (hobj N).symm)
    [uStar.Additive]
    (P : CochainComplex (ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) :
    ∃ (L : CochainComplex (ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ) (q : L ⟶ P),
      L.IsKFlatIndependentCoefficients ∧
      (∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (L.X n)) ∧ QuasiIso q ∧
      CochainComplex.IsKFlatIndependentCoefficients
        ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := by
  sorry

end SheafOfModules

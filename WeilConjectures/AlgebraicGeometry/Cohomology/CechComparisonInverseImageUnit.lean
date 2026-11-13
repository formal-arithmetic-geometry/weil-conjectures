/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonSystem
public import WeilConjectures.AlgebraicGeometry.Cohomology.CechInverseImageCochainMap
import WeilConjectures.AlgebraicGeometry.Cohomology.CechCoverRelativeEffacement
import WeilConjectures.AlgebraicGeometry.Cohomology.CechInverseImageDegreeZero
import WeilConjectures.AlgebraicGeometry.Cohomology.CechComparisonInverseImageSuccessor
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import WeilConjectures.CategoryTheory.InjectiveCechAugmentationQuasiIso

/-! # Čech comparison and the inverse-image unit

Source: Stacks Project, Tags 01FD and 01EQ, applied to abelian sheaves.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- The comparison commutes with inverse image for the adjunction unit alone.
Unlike coefficient naturality, this assertion concerns only one abelian sheaf and
its exact inverse image. There are no module coefficients or scalar restrictions.

Source: Stacks Project, Tag 01FD, Lemma 20.15.1, with the coefficient map equal to
identity on inverse image; Tag 01EQ, Lemma 20.11.2, for the comparison construction. -/
theorem cechComparison_inverseImage_unit
    {X Y : Scheme.{u}} {ι : Type u} (g : Y ⟶ X)
    (U : ι → X.Opens) (V : ι → Y.Opens) (hcover : iSup U = ⊤)
    (hcover' : iSup V = ⊤)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (c : CechComparisonSystem U hcover) (c' : CechComparisonSystem V hcover')
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ)
    (x : (TopCat.Sheaf.cechCohomologyFunctor U q).obj F) :
    (c'.comparison q).app ((invImage g).obj F)
        (HomologicalComplex.homologyMap
          (cechInverseImageCochainMap g U V hinter F ((invImage g).obj F)
            ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base).unit.app
              F).hom) q x) =
      Sheaf.H.mapFunctor (invImage g) (constIso g).symm F q
        ((c.comparison q).app F x) := by
  induction q generalizing F with
  | zero =>
    rw [c.zero, c'.zero]
    exact cechInverseImage_degree_zero g U V hcover hcover' hinter F x
  | succ q ih =>
    obtain ⟨T, hF, hT, hg, hg', hsurj⟩ :=
      exists_cechCoverRelativeEffacement g U V hcover hinter F
    subst F
    obtain ⟨y, rfl⟩ := hsurj q x
    exact cechComparison_inverseImage_succ_step g U V hcover hcover' hinter c c' T hT hg hg' q y
      (ih T.X₃ y)

end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

import WeilConjectures.RingTheory.WContractibleGeometricCriterion
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WContractibleAffineEvaluation
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Exact point sections with independent coefficient universes

Source: Stacks 03CW, 0946; the affine weakly contractible point argument
(blueprint: lem-weil-point-proetale-sections-exact).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance 3000] WeilConjectures.integralOperationsAbSheafify
  WeilConjectures.integralOperationsAbLocallyBijective
universe t u w w'
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

/-- Final-object module evaluation in a universe containing site and coefficients.
Source: Stacks 03CW (blueprint: lem-weil-point-proetale-sections-exact). -/
abbrev pointModuleSectionsOfUniverses (k : Type t) [Field k]
    (A : Sheaf (Scheme.ProEt.topology (Spec (.of k))) CommRingCat.{max u (t + 1)}) :
    ringedSiteModules.{max u (t + 1)}
        ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj A) ⥤
      ModuleCat.{max u (t + 1)}
        (((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj A).obj.obj
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) :=
  SheafOfModules.forget.{max u (t + 1)}
      ((sheafCompose (Scheme.ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj A) ⋙
    PresheafOfModules.evaluation _ (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))

end AlgebraicGeometry.ProEtale

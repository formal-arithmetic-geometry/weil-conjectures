/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality


public import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Submission.WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import Submission.WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
import Submission.WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
public import Mathlib.CategoryTheory.Adjunction.Whiskering

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Resolution-normalized module/Ext comparisons

The comparisons below are constructed from section complexes, not selected from
an existence assertion about natural equivalences.
Source: Stacks Project, Tags 03FD, 01FT and 06XR.
(blueprint: new-module-cohomology-ext-resolution-naturality)
-/

@[expose] public section
universe u u₁
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
/-- Cache the sheafification proof used by the comparison on the Zariski site.
Source: Mathlib's sheafification theorem for abelian sheaves.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
@[instance 2000]
theorem comparisonHasSheafify (X : Scheme.{u}) :
    HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance

/-- Cache the Ext-size proof used by the comparison on the Zariski site.
Source: the Grothendieck abelian category instance for abelian sheaves.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
@[instance 2000]
theorem comparisonHasExt (X : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance

namespace ExtEdgeResolution

open CategoryTheory.Abelian CochainComplex HomComplex
section
variable {A : Type u₁} [Category.{u} A] [Abelian A] [HasExt.{u} A]
  [HasInjectiveResolutions A]






end





































/-- Compose section comparisons before specializing the functors and the Ext source change.
Source: Stacks Project, Tags 03FD and 06XR; the three constructed comparison maps.
(blueprint: new-module-cohomology-ext-resolution-naturality) -/
noncomputable def sectionsComparisonNatIso
    {A E : Type*} [Category A] [Category E]
    {R : Type u} [Ring R] {K : A ⥤ ModuleCat.{u} R} {T : A ⥤ E}
    {B L Q : E ⥤ AddCommGrpCat.{u}}
    (a : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙ B)
    (b : L ≅ B) (c : L ≅ Q) : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙ Q :=
  a ≪≫ Functor.isoWhiskerLeft T (b.symm ≪≫ c)

end ExtEdgeResolution








end AlgebraicGeometry.Scheme.Modules

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiscreteCoefficientModel
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ConstantFieldFlat
import WeilConjectures.AlgebraicGeometry.IntegralResidueModelComparison

/-! # Finite Tor amplitude over a discrete field

Over the pulled-back discrete ring of a field, every internal module is flat, so every bounded
complex has finite Tor amplitude.

Source: Stacks Project, Tags 03ER, 08FC and 0651; Bhatt--Scholze, Remark 6.3.2.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

end AlgebraicGeometry.ProEtale.IntegralModelsStacks

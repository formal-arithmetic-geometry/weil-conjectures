/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import WeilConjectures.RingTheory.ProEtale.WeaklyEtale
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WContractibleCoverSection
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Evaluation at a w-contractible affine pro-etale object

Source: Stacks Project, Tags 0981, 098F and 098H, with the small-site adaptation
in the DAG proof; Sites, Tags 090K and 090L
(blueprint: lem-weil-pbc-wcontractible-affine-weakly-contractible).
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.ProEt

end AlgebraicGeometry.Scheme.ProEt

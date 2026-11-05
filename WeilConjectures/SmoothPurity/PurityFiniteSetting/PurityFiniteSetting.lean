/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra

/-!
# The finite coefficient setting for purity

Source: blueprint sec-smooth-purity/sk-def-purity-conv/def-pur-conventions.md
(blueprint: def-pur-conventions).

The fixed field datum, coefficient closure, finite subextension and positive level are
bundled together. The coefficient ring is the existing quotient construction, not new data.
The small pro-etale site retains its object universe u+1 and morphism universe u.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace WeilConjectures

attribute [instance] PurityFiniteSetting.finiteExtension

namespace PurityFiniteSetting

attribute [instance] forgetEtale_additive

attribute [instance] forgetEtale_preservesFiniteColimits

attribute [instance] forgetEtale_preservesFiniteLimits

attribute [instance] forget_preservesSheafification

end PurityFiniteSetting
end WeilConjectures

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore

/-! Split compatibility squares for integral finite-extension reduction pairing. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.derivedInternalHomOfUniverses
  CategoryTheory.homComplexFunctor
  WeilConjectures.IntegralHom.totalTensor WeilConjectures.IntegralHom.homModelMap
  WeilConjectures.IntegralHom.projection WeilConjectures.IntegralHom.evaluate

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)

end WeilConjectures.IntegralFiniteExtension

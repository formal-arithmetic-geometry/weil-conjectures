/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportAdjunctions
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportSources
public import Mathlib.Algebra.CharP.CharAndCard

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-geometric-indices). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- A smooth morphism in the recorded separated finite-type geometric domain,
with its compactification and relative dimension displayed.
Source: standing setting (blueprint: def-pur-transport-geometric-indices). -/
structure SmoothDatum (D : WeilConjectures.FiniteFieldDatum.{u}) where
  X : Over (Spec (.of D.k))
  Y : Over (Spec (.of D.k))
  [xFinite : LocallyOfFiniteType X.hom]
  [xQuasiCompact : QuasiCompact X.hom]
  [xSeparated : IsSeparated X.hom]
  [yFinite : LocallyOfFiniteType Y.hom]
  [yQuasiCompact : QuasiCompact Y.hom]
  [ySeparated : IsSeparated Y.hom]
  map : X.left ⟶ Y.left
  [isOver : map.IsOver (Spec (.of D.k))]
  [separated : IsSeparated map]
  [finiteType : LocallyOfFiniteType map]
  [quasiCompact : QuasiCompact map]
  dim : ℕ
  [smooth : SmoothOfRelativeDimension dim map]
  compactification : Compactification map

attribute [instance] SmoothDatum.xFinite SmoothDatum.xQuasiCompact SmoothDatum.xSeparated
  SmoothDatum.yFinite SmoothDatum.yQuasiCompact SmoothDatum.ySeparated
  SmoothDatum.isOver SmoothDatum.separated SmoothDatum.finiteType
  SmoothDatum.quasiCompact SmoothDatum.smooth

/-- An explicit restricted adjunction at one geometric index. Its two membership
fields supply only proofs: both functors are the literal operations already recorded.
Source: the adjunction clause (blueprint: def-pur-transport-geometric-indices). -/
structure ExplicitAdjunction (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (c : Coefficient ell) (s : SmoothDatum D) where
  support_closed : ∀ K, property ell c s.X.left K → property ell c s.Y.left
    ((CondensedRing.rightDerivedLowerShriekOfCompactification
      (c.obj ell) s.compactification).obj K)
  source_closed : ∀ K, property ell c s.Y.left K → property ell c s.X.left
    ((c.smoothSource ell s.map s.dim).obj K)
  adjunction : support ell c s.compactification support_closed ⊣
    source ell c s.map s.dim source_closed

end AlgebraicGeometry.ProEtale.PurityTransport

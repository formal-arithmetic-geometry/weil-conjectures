/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ZetaWeil.FiniteRingTrace.KVConstructible.KunnethVerdierConstructibleAdjunctions

/-! # Product maps using the current constructible exceptional adjunction

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-lefschetz-verdier/
sec-kunneth-formulas-and-external-duality/sk-thm-sf-kunneth-verdier/sk-def-sf-kv-maps/
def-sf-kv-maps.md,
clauses (i)--(iv), with Wei Yang #1423 (blueprint: def-sf-kv-maps).

Ku and beta are the published native constructions. Alpha is their specified exceptional
adjunction transpose, using the current Brown restriction rather than another presentation
of the right adjoint. Kappa is beta followed by internal Hom applied to alpha.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.CurrentTrace

open CompactificationReindexing RelativeKunneth ProductComparisons

variable {k : Type u} [Field k] (Λ : ScalarSixRing.{u})

local instance baseLocallyOfFiniteType (k : Type u) [Field k] :
    LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))
local instance baseQuasiCompact (k : Type u) [Field k] :
    QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))
local instance baseIsSeparated (k : Type u) [Field k] :
    IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))


/-- Canonical Nagata models for the same four support functors in the product construction.
Source: clause (i) (blueprint: def-sf-kv-maps). -/
def models (G : Geometry k) : ProductComparisons.Models G where
  f₁ := compactificationOverField G.f₁.hom
  f₂ := compactificationOverField G.f₂.hom
  relative :=
    { f := compactificationOverField G.u.hom
      g := compactificationOverField G.v.hom
      q := compactificationOverField G.q.hom
      total := compactificationOverField (G.q ≫ G.v).hom }

/-- The exceptional identity comparison is the adjoint of the canonical support-identity
map, with compactification independence retained.
Source: unit normalization in clause (iv) (blueprint: def-sf-kv-maps). -/
def identityExceptional (H : RelativeKunneth.CanonicalCompositionData Λ.X k)
    (X : SepFinType k) (S : CurrentConstructibleExceptionalData Λ.X (𝟙 X : X ⟶ X).hom)
    (M : ConstantModelConstructibleFiniteTor Λ.X X.obj.left) : M ⟶ S.right.obj M :=
  S.adjunction.homEquiv M M ⟨
    (lowerComparison Λ H (𝟙 X) S (Compactification.ofIsProper (𝟙 X.obj.left)) M).inv ≫
      (CompactSupportComposition.identity Λ.X X.obj.left).hom.app M.obj⟩

end AlgebraicGeometry.ProEtale.CondensedRing.CurrentTrace

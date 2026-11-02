/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.FilteredOperationsSupportCompositor

/-!
# Normalized ordinary compact-support exchange

Source: latest blueprint,
part-duality-trace-formula/sec-lefschetz-verdier/
sec-trace-classes-and-the-lefschetz-verdier-formula/sec-additivity-of-trace-classes/
sk-i-additivity/sk-i-additivity.proof.md,
Filtered operations and The trace morphism on filtered complexes
(blueprint: lem-trf-filtered-operations-hom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [local irreducible]
  AlgebraicGeometry.ProEtale.CondensedRing.derivedHom
  AlgebraicGeometry.ProEtale.CondensedRing.derivedTensor

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures
variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ]
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing

/-- The normalized ordinary compact-support exchange extracted from the same coherent
system as `traceSupportComp`. Its proper/open formula is part of that system's predicate.
Source: latest blueprint, filtered trace morphism
(blueprint: lem-trf-filtered-operations-hom). -/
def traceSupportExchange {k : Type u} [Field k]
    (h : CompactSupportComposition.CoherentData Λ k)
    {X Y X' Y' : SepFinType k} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X'.obj.left ⟶ X.obj.left} {v : Y'.obj.left ⟶ Y.obj.left}
    (sq : IsPullback a f'.hom.left f.hom.left v)
    (c : Compactification f.hom.left) (d : Compactification f'.hom.left) :
    (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (rightDerivedLowerShriekOfCompactification Λ c ⋙ moduleObjectDerivedPullback Λ v) ≅
      (localizingClosureProEtale Λ X.obj.left).ι ⋙
        (moduleObjectDerivedPullback Λ a ⋙ rightDerivedLowerShriekOfCompactification Λ d) :=
  h.exchange sq c d

end WeilConjectures

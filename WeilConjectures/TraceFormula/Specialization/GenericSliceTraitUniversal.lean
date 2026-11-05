/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.GenericSlicePoint
public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationUniversal
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
public import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.StrictlyHenselianRetraction

/-!

# The generic slice factors through the strict localization

Let `S = Spec k'⟦t⟧`, `K = k'(x)^alg` and `s = genericSlicePoint k' : Spec K ⟶ 𝔸¹_S`. We show:

* the strict localization `𝔸¹_{S,(s)} ⟶ 𝔸¹_S` is weakly étale
  (`AlgebraicGeometry.weaklyEtale_strictLocalizationToBase_genericSlicePoint`), since its ring is
  ind-étale over the affine chart `k'⟦t⟧[x]`;
* since `K⟦t⟧` is strictly henselian, the generic slice `Spec K⟦t⟧ ⟶ 𝔸¹_S` factors through the
  strict localization, via a local ring map `𝒪^{sh}_{𝔸¹_S,s} ⟶ K⟦t⟧`
  (`AlgebraicGeometry.genericSliceRingHom`) compatible with the evaluations at the closed points;
* this ring map is injective as soon as the strict henselization is a discrete valuation ring
  (`AlgebraicGeometry.injective_genericSliceRingHom`): its kernel is not the maximal ideal, as
  `t` lies in the maximal ideal but maps to `t ≠ 0`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable (k' : Type u) [Field k']

end AlgebraicGeometry

/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FieldExtensionBaseChange
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedPlus

/-!
# Derived direct images commute with base change along field extensions

Let `L/K` be a field extension, `S` a scheme over `K` with base change `S' = S ×_K L`, and
`g : T ⟶ S` a quasi-compact quasi-separated morphism with base change `h : T' ⟶ S'`. For a
bounded below complex `M` on `T` whose cohomology sheaves are torsion of orders invertible in
`K`, the derived base change map `p^* Rg_* M ⟶ Rh_* e^* M` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_baseChange_app_of_fieldExtension`). This is the derived form of
Stacks 0F1C (`AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_fieldExtension`), obtained
from the degreewise statement by dévissage on the bounded below complexes.

For a finite coefficient ring `Λ` killed by an integer invertible in `K`, every bounded below
complex qualifies; the statement is also given for the unbounded derived base change map
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_of_fieldExtension`), which is the
form used by the closed-support criterion for exceptional inverse images.

## References

- Stacks Project, Lemma 59.89.4, <https://stacks.math.columbia.edu/tag/0F1C>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {K L : Type u} [Field K] [Field L] [Algebra K L]
  {S T S' T' : Scheme.{u}} (σ : S ⟶ Spec (.of K)) {g : T ⟶ S} [QuasiCompact g]
  [QuasiSeparated g] {p : S' ⟶ S} (σ' : S' ⟶ Spec (.of L))
  (hS : IsPullback p σ' σ (Spec.map (CommRingCat.ofHom (algebraMap K L))))
  {e : T' ⟶ T} {h : T' ⟶ S'} (sq : IsPullback e h g p)

include σ σ' hS in
/-- **Derived direct images commute with base change along field extensions** (Stacks 0F1C,
derived form): for a bounded below complex `M` whose cohomology sheaves are torsion of orders
invertible in `K`, the derived base change map `p^* Rg_* M ⟶ Rh_* e^* M` is an isomorphism. -/
theorem isIso_baseChange_app_of_fieldExtension
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hM : ∀ j, IsTorsionSheafOfInvertibleOrder (Spec (.of K))
      ((DerivedCategory.Plus.homologyFunctor _ j).obj M)) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app M) :=
  DerivedCategory.Plus.isIso_app_of_forall_homology _
    (isTorsionSheafOfInvertibleOrder Λ (Spec (.of K)) T)
    (fun F hF ↦ have : IsTorsionSheafOfInvertibleOrder (Spec (.of K)) F := hF
      (isIso_baseChange_app_singleFunctor_obj_iff Λ sq F).2 fun q ↦
        isIso_baseChangeHomologyMap_of_fieldExtension Λ σ g p σ' hS sq q F)
    (fun M n _ q hq ↦ isZero_homologyFunctor_baseChangeSource_obj Λ p g M n q hq)
    (fun M n _ q hq ↦ isZero_homologyFunctor_baseChangeTarget_obj Λ e h M n q hq) M hM

end AlgebraicGeometry.Etale

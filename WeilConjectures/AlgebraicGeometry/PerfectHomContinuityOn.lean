/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Open-local continuity predicate for canonical perfect Hom transport

## References

* Stacks Project, Tag 09RE.
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Continuity on an open, quantified over every scheme presenting that open and
all perfect pairs (Stacks, Tag 09RE). -/
def PerfectHomContinuityOn
    {I : Type u} [Preorder I] (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (W : X.Opens) : Prop :=
  ∀ (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t], t.opensRange = W →
    ∀ (s : Y ⟶ Spec (R.obj i)), s = t ≫ s₀ →
      ∀ [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
        [∀ U : Y.Opens,
          HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
        (P Q : schemeDerivedCategory Y), Y.IsPerfect P → Y.IsPerfect Q →
    (∀ (j₀ : I) (hij₀ : i ≤ j₀)
      (φ : (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
        (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q),
      ∃ (j : I) (hj₀j : j₀ ≤ j)
        (f : (derivedPullback
            (pullback.fst s (Spec.map (R.map (homOfLE (hij₀.trans hj₀j)))))).obj P ⟶
          (derivedPullback
            (pullback.fst s (Spec.map (R.map (homOfLE (hij₀.trans hj₀j)))))).obj Q),
        perfectLimitMap R c s (hij₀.trans hj₀j) f = φ) ∧
    (∀ (j : I) (hij : i ≤ j)
      (a b : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P ⟶
        (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Q),
      perfectLimitMap R c s hij a = perfectLimitMap R c s hij b →
      ∃ (k : I) (hjk : j ≤ k), ∀ (l : I) (hkl : k ≤ l),
        perfectStageMap R s hij (hjk.trans hkl) a =
          perfectStageMap R s hij (hjk.trans hkl) b)

end AlgebraicGeometry

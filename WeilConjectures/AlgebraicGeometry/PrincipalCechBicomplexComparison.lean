/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalCechColumns
public import Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.AlgebraicGeometry.PrincipalCechHorizontalSquare
import WeilConjectures.AlgebraicGeometry.PrincipalCechRegroupDifferential
import WeilConjectures.AlgebraicGeometry.PrincipalCechRegroupNaturality

/-!
# The explicit Čech bicomplex and its total comparison

## References

* Stacks Project, Tag 08D1, <https://stacks.math.columbia.edu/tag/08D1>
* Stacks Project, Tag 08C2, <https://stacks.math.columbia.edu/tag/08C2>
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

variable {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)

/-- The Čech bicomplex constructed from product columns and alternating restrictions
(Stacks, Tag 08D1). -/
def principalCechBicomplex
    (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
    HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  CochainComplex.of (fun p ↦ (principalCechColumnFunctor r f p).obj F)
    (fun p ↦ (principalCechHorizontal r f p).app F)
    (by exact principalCechHorizontal_square A r f F)

/-- Coefficient maps act on every product column. -/
def principalCechBicomplexFunctor :
    CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ ⥤
      HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ) where
  obj := principalCechBicomplex r f
  map i :=
    { f p := (principalCechColumnFunctor r f p).map i
      comm' := by
        intro p q hpq
        obtain rfl : p + 1 = q := hpq
        simp only [principalCechBicomplex, CochainComplex.of_d]
        exact (principalCechHorizontal r f p).naturality i }
  map_id F := by ext p : 1; exact (principalCechColumnFunctor r f p).map_id F
  map_comp i j := by ext p : 1; exact (principalCechColumnFunctor r f p).map_comp i j

/-- Regrouping subset coordinates identifies the two total functors naturally
(Stacks, Tags 08D1 and 08C2). -/
theorem principalCechBicomplexComparison_exists :
    Nonempty (principalCechFunctor r f ≅ principalCechBicomplexFunctor r f ⋙
      HomologicalComplex₂.totalFunctor (ModuleCat.{u} A)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) := by
  let B := principalCechBicomplexFunctor r f ⋙
    HomologicalComplex₂.totalFunctor (ModuleCat.{u} A)
      (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let e (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (p : ℤ) :
      (principalCechBicomplex r f F).X p ≅
        (principalCechColumnFunctor r f p).obj F := Iso.refl _
  have he (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (p : ℤ) :
      (principalCechBicomplex r f F).d p (p + 1) ≫ (e F (p + 1)).hom =
        (e F p).hom ≫ (principalCechHorizontal r f p).app F := by
    simp [e, principalCechBicomplex]
  have hi (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) (n : ℤ) :
      IsIso (principalCechTotalRegroup r f F (principalCechBicomplex r f F) (e F) n) :=
    principalCechTotalRegroup_isIso r f F _ (e F) n
  let E (F : CochainComplex (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) ℤ) :
      B.obj F ≅ (principalCechFunctor r f).obj F :=
    HomologicalComplex.Hom.isoOfComponents
      (C₁ := (principalCechBicomplex r f F).total (ComplexShape.up ℤ))
      (C₂ := principalCechTotal r f F)
      (fun n ↦ asIso (principalCechTotalRegroup r f F
        (principalCechBicomplex r f F) (e F) n)) (by
          intro n m hnm
          obtain rfl : n + 1 = m := hnm
          simpa only [asIso_hom, principalCechTotal, CochainComplex.of_d] using
            principalCechTotalRegroup_comm r f F _ (e F) (he F) n) ≪≫
      (principalCechObjIso r f F).symm
  refine ⟨(NatIso.ofComponents E ?_).symm⟩
  intro F G g
  apply HomologicalComplex.Hom.ext
  funext n
  apply (cancel_mono ((principalCechObjIso r f G).hom.f n)).1
  have hn := principalCechTotalRegroup_naturality r f F G g
    (principalCechBicomplex r f F) (principalCechBicomplex r f G) (e F) (e G)
    ((principalCechBicomplexFunctor r f).map g)
    (by intro p; simp [e, principalCechBicomplexFunctor]) n
  simpa [E, B, Category.assoc] using hn.symm

end
end AlgebraicGeometry

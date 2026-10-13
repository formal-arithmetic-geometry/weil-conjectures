/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.PrincipalCechColumns
public import Mathlib.Algebra.Homology.TotalComplex

/-! # Regrouping the graded terms of principal Čech columns

Source: Stacks, Tag 08D1, alternating total cochains
(blueprint: lem-sc-principal-cech-total-regrouping).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
noncomputable section

variable {A : Type u} [CommRing A] (r : ℕ) (f : Fin r → A)
variable (F : CochainComplex (SheafOfModules.{u}
  (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)

/-- Include a single product row into the explicit cochains, extending by zero.
Source: Stacks, Tag 08D1 (blueprint: lem-sc-principal-cech-total-regrouping). -/
def principalCechRowToTerms (p q n : ℤ) (hpq : p + q = n) :
    ((principalCechColumnFunctor r f p).obj F).X q ⟶ principalCechTerms r f F n := by
  classical
  let component (J : {J : Finset (Fin r) // J.Nonempty}) :
      ((principalCechColumnFunctor r f p).obj F).X q ⟶
        (affineOpenSections A (principalCechIntersection r f J.val)).obj
          (F.X (n + 1 - (J.val.card : ℤ))) :=
    if h : (J.val.card : ℤ) = p + 1 then
      (Limits.Pi.π (fun S : principalCechRowIndex r p ↦
        (principalCechSectionFunctor r f S.val.val).obj F) ⟨J, h⟩).f q ≫
      (affineOpenSections A (principalCechIntersection r f J.val)).map
        (eqToHom (congrArg F.X (by omega : q = n + 1 - (J.val.card : ℤ))))
    else 0
  exact ModuleCat.ofHom
    { toFun := fun x J ↦ component J x
      map_add' := fun x y ↦ by funext J; exact (component J).hom.map_add x y
      map_smul' := fun a x ↦ by funext J; exact (component J).hom.map_smul a x }

/-- The subset coordinate of a row inclusion is its projection, or zero off the row.
Source: Stacks, Tag 08D1 (blueprint: lem-sc-principal-cech-total-regrouping). -/
theorem principalCechRowToTerms_apply (p q n : ℤ) (hpq : p + q = n)
    (x : ((principalCechColumnFunctor r f p).obj F).X q)
    (J : {J : Finset (Fin r) // J.Nonempty}) :
    principalCechRowToTerms r f F p q n hpq x J =
      if h : (J.val.card : ℤ) = p + 1 then
        (affineOpenSections A (principalCechIntersection r f J.val)).map
          (eqToHom (congrArg F.X (by omega : q = n + 1 - (J.val.card : ℤ))))
          ((Limits.Pi.π (fun S : principalCechRowIndex r p ↦
            (principalCechSectionFunctor r f S.val.val).obj F) ⟨J, h⟩).f q x)
      else 0 := by
  classical
  change (if h : (J.val.card : ℤ) = p + 1 then
    (Limits.Pi.π (fun S : principalCechRowIndex r p ↦
      (principalCechSectionFunctor r f S.val.val).obj F) ⟨J, h⟩).f q ≫
      (affineOpenSections A (principalCechIntersection r f J.val)).map
        (eqToHom (congrArg F.X (by omega : q = n + 1 - (J.val.card : ℤ))))
    else 0) x = _
  split_ifs <;> rfl

/-- The explicit graded regrouping map, for any bicomplex with the given columns.
It uses the coproduct universal property, rather than a chosen existence witness.
Source: Stacks, Tag 08D1 (blueprint: lem-sc-principal-cech-total-regrouping). -/
def principalCechTotalRegroup
    (B : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (e : ∀ p, B.X p ≅ (principalCechColumnFunctor r f p).obj F) (n : ℤ) :
    (B.total (ComplexShape.up ℤ)).X n ⟶ principalCechTerms r f F n :=
  B.totalDesc (fun p q h ↦ (e p).hom.f q ≫ principalCechRowToTerms r f F p q n h)

/-- Regrouping is an isomorphism of modules in each total degree.
Source: Stacks, Tag 08D1, the finite alternating total
(blueprint: lem-sc-principal-cech-total-regrouping).

Proof: evaluate each categorical product of section complexes in degree q. Its
projections exhibit a product of the section modules in that degree, since evaluation
preserves products. Nonempty subsets have cardinalities between 1 and r, so only
rows 0 through r-1 are nonzero. The diagonal coproduct therefore has finite support.
For each subset J, put its coordinate in the unique summand p=card(J)-1,
q=n+1-card(J), using the inverse of e p and the degreewise product identification.
Sum these finitely many coordinate insertions. This is an inverse of the displayed
map: after a subset projection only its own row survives, and on each coproduct
summand all its product projections are recovered. Empty rows are zero objects;
for r=0 both families are empty and the same argument identifies zero modules.
The proof uses no differential or boundedness of F. -/
theorem principalCechTotalRegroup_isIso
    (B : HomologicalComplex₂ (ModuleCat.{u} A) (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (e : ∀ p, B.X p ≅ (principalCechColumnFunctor r f p).obj F) (n : ℤ) :
    IsIso (principalCechTotalRegroup r f F B e n) := by sorry

end
end AlgebraicGeometry

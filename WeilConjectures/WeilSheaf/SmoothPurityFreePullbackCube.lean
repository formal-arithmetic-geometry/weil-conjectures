/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Comparing free-module pullback before and after coefficient extension -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

variable {A B C D E F : Type*} [Category A] [Category B] [Category C]
  [Category D] [Category E] [Category F]
  {P : A ⥤ B} {RP : B ⥤ A} (p : P ⊣ RP)
  {FY : A ⥤ C} {RFY : C ⥤ A} (fy : FY ⊣ RFY)
  {FX : B ⥤ D} {RFX : D ⥤ B} (fx : FX ⊣ RFX)
  {Q : C ⥤ D} {RQ : D ⥤ C} (q : Q ⊣ RQ)
  {EY : C ⥤ E} {REY : E ⥤ C} (ey : EY ⊣ REY)
  {EX : D ⥤ F} {REX : F ⥤ D} (ex : EX ⊣ REX)
  {FY' : A ⥤ E} {RFY' : E ⥤ A} (fy' : FY' ⊣ RFY')
  {FX' : B ⥤ F} {RFX' : F ⥤ B} (fx' : FX' ⊣ RFX')
  {Q' : E ⥤ F} {RQ' : F ⥤ E} (q' : Q' ⊣ RQ')

end CategoryTheory

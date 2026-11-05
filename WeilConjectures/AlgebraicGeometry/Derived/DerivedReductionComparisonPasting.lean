/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionComparisonFormula
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Pasting of normalized derived reduction comparisons

Source: Stacks Project, Tags 06YY and 0D6D
(blueprint: lem-weil-pbc-completed-reduction-pullback-square).

Reduction comparisons normalized on good representatives paste along squares of exact
functors whenever the underlying ordinary comparisons paste.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

section Square

variable {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  (F₁ : A ⥤ B) (F₂ : B ⥤ D) (F₃ : A ⥤ C) (F₄ : C ⥤ D)
  [F₁.Additive] [F₂.Additive] [F₃.Additive] [F₄.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits F₃] [PreservesFiniteColimits F₃]
  [PreservesFiniteLimits F₄] [PreservesFiniteColimits F₄]

end Square

section Pasting

variable {BY BY' BX BX' DY DY' DX DX' : Type*}
  [Category BY] [Category BY'] [Category BX] [Category BX']
  [Category DY] [Category DY'] [Category DX] [Category DX']
  [Abelian BY] [Abelian BY'] [Abelian BX] [Abelian BX']
  [Abelian DY] [Abelian DY'] [Abelian DX] [Abelian DX']
  [HasDerivedCategory BY] [HasDerivedCategory BY'] [HasDerivedCategory BX]
  [HasDerivedCategory BX'] [HasDerivedCategory DY] [HasDerivedCategory DY']
  [HasDerivedCategory DX] [HasDerivedCategory DX']
  (Fg : BY ⥤ BY') (Ff' : BY' ⥤ BX') (Ff : BY ⥤ BX) (Fg' : BX ⥤ BX')
  (Gg : DY ⥤ DY') (Gf' : DY' ⥤ DX') (Gf : DY ⥤ DX) (Gg' : DX ⥤ DX')
  [Fg.Additive] [Ff'.Additive] [Ff.Additive] [Fg'.Additive]
  [Gg.Additive] [Gf'.Additive] [Gf.Additive] [Gg'.Additive]
  [PreservesFiniteLimits Fg] [PreservesFiniteColimits Fg]
  [PreservesFiniteLimits Ff'] [PreservesFiniteColimits Ff']
  [PreservesFiniteLimits Ff] [PreservesFiniteColimits Ff]
  [PreservesFiniteLimits Fg'] [PreservesFiniteColimits Fg']
  [PreservesFiniteLimits Gg] [PreservesFiniteColimits Gg]
  [PreservesFiniteLimits Gf'] [PreservesFiniteColimits Gf']
  [PreservesFiniteLimits Gf] [PreservesFiniteColimits Gf]
  [PreservesFiniteLimits Gg'] [PreservesFiniteColimits Gg']
  (RY : BY ⥤ DY) (RY' : BY' ⥤ DY') (RX : BX ⥤ DX) (RX' : BX' ⥤ DX')
  [RY.Additive] [RY'.Additive] [RX.Additive] [RX'.Additive]
  (MY : DerivedCategory BY ⥤ DerivedCategory DY)
  (MY' : DerivedCategory BY' ⥤ DerivedCategory DY')
  (MX : DerivedCategory BX ⥤ DerivedCategory DX)
  (MX' : DerivedCategory BX' ⥤ DerivedCategory DX')
  (εY : DerivedCategory.Q ⋙ MY ⟶ RY.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εY' : DerivedCategory.Q ⋙ MY' ⟶ RY'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εX : DerivedCategory.Q ⋙ MX ⟶ RX.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εX' : DerivedCategory.Q ⋙ MX' ⟶ RX'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)

end Pasting

section TowerPasting

variable {BY BY' BX BX' : Type*}
  [Category BY] [Category BY'] [Category BX] [Category BX']
  [Abelian BY] [Abelian BY'] [Abelian BX] [Abelian BX']
  [HasDerivedCategory BY] [HasDerivedCategory BY'] [HasDerivedCategory BX]
  [HasDerivedCategory BX'] [HasDerivedCategory (ℕᵒᵖ ⥤ BY)] [HasDerivedCategory (ℕᵒᵖ ⥤ BY')]
  [HasDerivedCategory (ℕᵒᵖ ⥤ BX)] [HasDerivedCategory (ℕᵒᵖ ⥤ BX')]
  (Fg : BY ⥤ BY') (Ff' : BY' ⥤ BX') (Ff : BY ⥤ BX) (Fg' : BX ⥤ BX')
  [Fg.Additive] [Ff'.Additive] [Ff.Additive] [Fg'.Additive]
  [PreservesFiniteLimits Fg] [PreservesFiniteColimits Fg]
  [PreservesFiniteLimits Ff'] [PreservesFiniteColimits Ff']
  [PreservesFiniteLimits Ff] [PreservesFiniteColimits Ff]
  [PreservesFiniteLimits Fg'] [PreservesFiniteColimits Fg']
  [((Functor.whiskeringRight ℕᵒᵖ BY BY').obj Fg).Additive]
  [((Functor.whiskeringRight ℕᵒᵖ BY' BX').obj Ff').Additive]
  [((Functor.whiskeringRight ℕᵒᵖ BY BX).obj Ff).Additive]
  [((Functor.whiskeringRight ℕᵒᵖ BX BX').obj Fg').Additive]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ BY BY').obj Fg)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ BY BY').obj Fg)]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ BY' BX').obj Ff')]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ BY' BX').obj Ff')]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ BY BX).obj Ff)]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ BY BX).obj Ff)]
  [PreservesFiniteLimits ((Functor.whiskeringRight ℕᵒᵖ BX BX').obj Fg')]
  [PreservesFiniteColimits ((Functor.whiskeringRight ℕᵒᵖ BX BX').obj Fg')]
  (RY : BY ⥤ ℕᵒᵖ ⥤ BY) (RY' : BY' ⥤ ℕᵒᵖ ⥤ BY') (RX : BX ⥤ ℕᵒᵖ ⥤ BX)
  (RX' : BX' ⥤ ℕᵒᵖ ⥤ BX')
  [RY.Additive] [RY'.Additive] [RX.Additive] [RX'.Additive]
  (MY : DerivedCategory BY ⥤ DerivedCategory (ℕᵒᵖ ⥤ BY))
  (MY' : DerivedCategory BY' ⥤ DerivedCategory (ℕᵒᵖ ⥤ BY'))
  (MX : DerivedCategory BX ⥤ DerivedCategory (ℕᵒᵖ ⥤ BX))
  (MX' : DerivedCategory BX' ⥤ DerivedCategory (ℕᵒᵖ ⥤ BX'))
  (εY : DerivedCategory.Q ⋙ MY ⟶ RY.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εY' : DerivedCategory.Q ⋙ MY' ⟶ RY'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εX : DerivedCategory.Q ⋙ MX ⟶ RX.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εX' : DerivedCategory.Q ⋙ MX' ⟶ RX'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)

end TowerPasting

end AlgebraicGeometry.Scheme

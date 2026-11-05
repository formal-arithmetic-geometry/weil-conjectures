/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityExactDescentNormalization
public import WeilConjectures.WeilSheaf.SmoothPurityProperTraceCoordinates
public import WeilConjectures.WeilSheaf.SmoothPurityShriekFreeComparison
public import WeilConjectures.WeilSheaf.SmoothPurityAmbientOpenExchange
public import WeilConjectures.WeilSheaf.SmoothPurityInverseMateExchange

/-! # The geometric comparison underlying descended extension by zero -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {B B' C D : Type*} [Category B] [Category B'] [Category C] [Category D]
  {F : C ⥤ C} {G : D ⥤ D} {l : B ⥤ B'} {r : B' ⥤ B}
  {L : C ⥤ D} {R : D ⥤ C} (adjB : l ⊣ r) (adj : L ⊣ R)
  (eL : L ⋙ G ≅ F ⋙ L) (eR : R ⋙ F ≅ G ⋙ R)
  (hmate : (mateEquiv adj adj (TwoSquare.mk _ _ _ _ eL.inv)).natTrans = eR.hom)
  {PB : B ⥤ IsoAlgebra F} {PB' : B' ⥤ IsoAlgebra G}

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {k : Type u} [Field k] [Finite k] {X Y : Scheme.{u}}
  {s : X ⟶ Spec (.of k)} {t : Y ⟶ Spec (.of k)}
  {j : X ⟶ Y} [IsOpenImmersion j] {h : j ≫ t = s}
  (hc : UpperStarWeilCompatible Λ j h)

end AlgebraicGeometry.ProEtale.CondensedRing

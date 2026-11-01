/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import WeilConjectures.DeligneLaumon.FieldShriekCompositionQcqs

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
/-! # Verdier-exchange definition interface

Source: literature/blueprint/latest/blueprint/sec-six-functors/
sk-thm-sf-verdier-exchange, construction and normalization clauses
(blueprint: def-sf-verdier-exchange-data).

The exceptional functors below are the existing constructible adjoints. In particular
none of these definitions uses an ambient exceptional-adjoint datum.
The complete definition interface is moved out of the quarantined theorem module.
There is no existence assertion and no import of either exchange theorem module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u a b c d e v w z
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme


namespace WeilConjectures
namespace VerdierExchange
open CategoryTheory.Pretriangulated.Opposite

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

open ConstructibleExceptionalCoefficients

/-- The existing ambient ring-stage internal Hom on the original small pro-etale site.
The finite and integral cases use precisely the coefficient sheaves of RingStage.
Source: blueprint sk-def-sf-operations (i), specialized to the displayed duals
(blueprint: def-sf-verdier-exchange-data). -/
abbrev ringHom (T : Scheme.{u}) (s : RingStage.{u} l) :=
  derivedInternalHomOfUniverses.{u + 1, u, u}
    (ProEt.topology T) ((s.coefficients l).ring T)

/-- Internal Hom into the specified dualizing object, restricted in its first variable
by the existing full finite-Tor inclusion. The target remains the ambient derived category.
Source: blueprint sk-thm-sf-verdier-exchange, definition of D_T
(blueprint: def-sf-verdier-exchange-data). -/
def ringDual (T : Scheme.{u}) (s : RingStage.{u} l)
    (omega : C.{u} l Ω T (s.stage l)) :
    (C.{u} l Ω T (s.stage l))ᵒᵖ ⥤
      DerivedCategory (pbcModules T ((s.coefficients l).ring T)) :=
  (s.inclusion.{u} l Ω T).op ⋙
    (Functor.curry.obj (ringHom l T s)).flip.obj ((s.inclusion.{u} l Ω T).obj omega)

/-- Substitution of the dualizing-object comparison in the second variable of RHom.
This is the second arrow in the required exchange; it acts on the actual internal Hom.
Source: blueprint sk-thm-sf-verdier-exchange, proof step 3
(blueprint: def-sf-verdier-exchange-data). -/
def substitute {X Y : Scheme.{u}} (f : X ⟶ Y) (s : RingStage.{u} l)
    (omega omega' : C.{u} l Ω X (s.stage l)) (c : omega ≅ omega') :
    ringDual l Ω X s omega ⋙ PurCompactSupport.push (s.coefficients l) f ≅
      ringDual l Ω X s omega' ⋙ PurCompactSupport.push (s.coefficients l) f :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (s.inclusion.{u} l Ω X).op
      ((Functor.curry.obj (ringHom l X s)).flip.mapIso
        ((s.inclusion.{u} l Ω X).mapIso c)))
    (PurCompactSupport.push (s.coefficients l) f)

/-- The required orientation of Verdier exchange: invert tensor-Hom exchange, then
apply Rf_* RHom(M,-) to c_Lambda. No objectwise isomorphism is selected.
Source: blueprint sk-thm-sf-verdier-exchange, proof step 3
(blueprint: def-sf-verdier-exchange-data). -/
def exchange {X Y : Scheme.{u}} (f : X ⟶ Y) (s : RingStage.{u} l)
    (F : C.{u} l Ω X (s.stage l) ⥤ C.{u} l Ω Y (s.stage l))
    (G : C.{u} l Ω Y (s.stage l) ⥤ C.{u} l Ω X (s.stage l))
    (omegaY : C.{u} l Ω Y (s.stage l)) (omegaX : C.{u} l Ω X (s.stage l))
    (theta : ringDual l Ω X s (G.obj omegaY) ⋙
        PurCompactSupport.push (s.coefficients l) f ≅
      F.op ⋙ ringDual l Ω Y s omegaY)
    (c : G.obj omegaY ≅ omegaX) :
    F.op ⋙ ringDual l Ω Y s omegaY ≅
      ringDual l Ω X s omegaX ⋙ PurCompactSupport.push (s.coefficients l) f :=
  theta.symm ≪≫ substitute l Ω f s (G.obj omegaY) omegaX c

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
  [f.IsOver (Spec (.of D.k))] [g.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (Sf : System.{u} l Ω D hl (f := f)) (Sg : System.{u} l Ω D hl (f := g))
  (Sfg : System.{u} l Ω D hl (f := f ≫ g))
  (cf : Compactification f) (cg : Compactification g) (cfg : Compactification (f ≫ g))

end Geometry

end VerdierExchange
end WeilConjectures

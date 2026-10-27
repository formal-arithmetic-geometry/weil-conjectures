/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.NormalizedInverseImageSquare
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Subterminal

/-! # Normalized scalar/site diagrams
Source: blueprint main-20261015, sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-diagram).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option linter.checkUnivs false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.CompactScalarSite
variable {A B : Type (max u v)} [CommRing A] [CommRing B] (φ : A →+* B)

/-- The exact open left adjoint, characterized with its fully faithful unit.
Source: Stacks 0E8I (blueprint: def-pur-compact-scalar-site-diagram). -/
structure OpenModel {T W : Presentation.{u, v}} {R : Type (max u v)} [CommRing R]
    {g : GeometricMorphism (Sheaf T.J (Type (max u v)))
      (Sheaf W.J (Type (max u v)))} (L : InverseModel T W R g) where
  functor : derived T R ⥤ derived W R
  adj : functor ⊣ inverse L
  [unitIso : IsIso adj.unit]

attribute [instance] OpenModel.unitIso

/-- An actual Cartesian open square, with its specified open adjunctions.
The scalar and site maps are fixed by their inverse open mates, hence by the
open units. They cannot be replaced by unrelated isomorphisms of the endpoints.
Source: Stacks 0E8I and 0GL1
(blueprint: def-pur-compact-scalar-site-diagram). -/
structure OpenSquare (X T : Vertex.{u, v} φ) where
  square : InverseSquare φ X T
  U : Sheaf T.W.J (Type (max u v))
  subterminal : IsSubterminal U
  presentation : Sheaf X.W.J (Type (max u v)) ≌ Over U
  inclusion : square.p.inverse ≅ Over.star U ⋙ presentation.inverse
  tildePresentation : Sheaf X.tildeW.J (Type (max u v)) ≌ Over (T.ν.inverse.obj U)
  tildeInclusion : square.tildeP.inverse ≅
    Over.star (T.ν.inverse.obj U) ⋙ tildePresentation.inverse
  induced : X.ν.inverse ≅ presentation.functor ⋙
    Over.post T.ν.inverse ⋙ tildePresentation.inverse
  IA : OpenModel square.LA
  IB : OpenModel square.LB
  tildeIA : OpenModel square.tildeLA
  tildeIB : OpenModel square.tildeLB
  beta : IA.functor ⋙ T.scalar.model.T ≅ X.scalar.model.T ⋙ IB.functor
  beta_normalized :
    (mateEquiv IA.adj IB.adj
      (TwoSquare.mk X.scalar.model.T IA.functor IB.functor T.scalar.model.T beta.inv)).natTrans =
      square.scalar.comparison.inv
  tildeBeta : tildeIA.functor ⋙ T.tildeScalar.model.T ≅
    X.tildeScalar.model.T ⋙ tildeIB.functor
  tildeBeta_normalized :
    (mateEquiv tildeIA.adj tildeIB.adj
      (TwoSquare.mk X.tildeScalar.model.T tildeIA.functor tildeIB.functor
        T.tildeScalar.model.T tildeBeta.inv)).natTrans =
      square.tildeScalar.comparison.inv
  eA : IA.functor ⋙ inverse T.NA ≅ inverse X.NA ⋙ tildeIA.functor
  eA_normalized :
    (mateEquiv IA.adj tildeIA.adj
      (TwoSquare.mk (inverse X.NA) IA.functor tildeIA.functor (inverse T.NA) eA.inv)).natTrans =
      (Functor.mapDerivedCategorySquareIso square.aA).inv
  eB : IB.functor ⋙ inverse T.NB ≅ inverse X.NB ⋙ tildeIB.functor
  eB_normalized :
    (mateEquiv IB.adj tildeIB.adj
      (TwoSquare.mk (inverse X.NB) IB.functor tildeIB.functor (inverse T.NB) eB.inv)).natTrans =
      (Functor.mapDerivedCategorySquareIso square.aB).inv

/-- The factorization data for the mixed square, with all functors on the
actual derived module-sheaf categories of the six fixed presentations.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-diagram). -/
structure Factorization where
  X : Vertex.{u, v} φ
  T : Vertex.{u, v} φ
  Y : Vertex.{u, v} φ
  j : OpenSquare φ X T
  p : InverseSquare φ T Y
  RA : DirectModel p.LA
  RB : DirectModel p.LB
  tildeRA : DirectModel p.tildeLA
  tildeRB : DirectModel p.tildeLB

/-- The untilde compact-support factorization functor in A coefficients.
Source: blueprint sk-thm-purity-transport, Step 5
(blueprint: def-pur-compact-scalar-site-diagram). -/
def factorA (D : Factorization.{u, v} φ) := D.j.IA.functor ⋙ D.RA.functor

/-- The same untilde functor in B coefficients.
Source: blueprint sk-thm-purity-transport, Step 5
(blueprint: def-pur-compact-scalar-site-diagram). -/
def factorB (D : Factorization.{u, v} φ) := D.j.IB.functor ⋙ D.RB.functor

/-- The tilde compact-support factorization in A coefficients.
Source: blueprint sk-thm-purity-transport, Step 5
(blueprint: def-pur-compact-scalar-site-diagram). -/
def tildeFactorA (D : Factorization.{u, v} φ) := D.j.tildeIA.functor ⋙ D.tildeRA.functor

/-- The tilde compact-support factorization in B coefficients.
Source: blueprint sk-thm-purity-transport, Step 5
(blueprint: def-pur-compact-scalar-site-diagram). -/
def tildeFactorB (D : Factorization.{u, v} φ) := D.j.tildeIB.functor ⋙ D.tildeRB.functor

/-- The coefficient map c_{p,j}, with the canonical functor associators inserted.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-diagram). -/
def coefficient (D : Factorization.{u, v} φ) :
    factorA φ D ⋙ D.Y.scalar.model.T ⟶ D.X.scalar.model.T ⋙ factorB φ D :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D.j.IA.functor (directScalar φ D.p.scalar D.RA D.RB) ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight D.j.beta.hom D.RB.functor ≫
    (Functor.associator _ _ _).hom

/-- The specified counit/open-balancing map on the tilde side.
Source: blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-compact-scalar-site-diagram). -/
def tildeCoefficient (D : Factorization.{u, v} φ) :
    tildeFactorA φ D ⋙ D.Y.tildeScalar.model.T ⟶
      D.X.tildeScalar.model.T ⋙ tildeFactorB φ D :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D.j.tildeIA.functor
      (directScalar φ D.p.tildeScalar D.tildeRA D.tildeRB) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight D.j.tildeBeta.hom D.tildeRB.functor ≫
    (Functor.associator _ _ _).hom

/-- The actual site comparison C_{p,j,A}. No inverse of d is used to construct it.
Source: Stacks 07A7 and 0E8I
(blueprint: def-pur-compact-scalar-site-diagram). -/
def siteA (D : Factorization.{u, v} φ) :
    factorA φ D ⋙ inverse D.Y.NA ⟶ inverse D.X.NA ⋙ tildeFactorA φ D :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D.j.IA.functor (directSiteA φ D.p D.RA D.tildeRA) ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight D.j.eA.hom D.tildeRA.functor ≫
    (Functor.associator _ _ _).hom

/-- The actual site comparison C_{p,j,B}.
Source: Stacks 07A7 and 0E8I
(blueprint: def-pur-compact-scalar-site-diagram). -/
def siteB (D : Factorization.{u, v} φ) :
    factorB φ D ⋙ inverse D.Y.NB ⟶ inverse D.X.NB ⋙ tildeFactorB φ D :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D.j.IB.functor (directSiteB φ D.p D.RB D.tildeRB) ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight D.j.eB.hom D.tildeRB.functor ≫
    (Functor.associator _ _ _).hom


end CategoryTheory.CompactScalarSite

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.ConstantCoefficientToposModel

/-! # Normalized scalar/site diagrams
Source: blueprint main-20261015, sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-normalized-inverse-image-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.checkUnivs false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.CompactScalarSite
variable {A B : Type (max u v)} [CommRing A] [CommRing B] (φ : A →+* B)

/-- Normalization of one ordinary module inverse-image square by its specified
set square. This is before localization and tests every generalized section.
Source: Stacks 03D2 and 07A7
(blueprint: def-pur-normalized-inverse-image-square). -/
def InverseSquareNormalized {X Y Xt Yt : Presentation.{u, v}}
    {R : Type (max u v)} [CommRing R]
    {νX : GeometricMorphism (Sheaf Xt.J (Type (max u v)))
      (Sheaf X.J (Type (max u v)))}
    {νY : GeometricMorphism (Sheaf Yt.J (Type (max u v)))
      (Sheaf Y.J (Type (max u v)))}
    {p : GeometricMorphism (Sheaf X.J (Type (max u v)))
      (Sheaf Y.J (Type (max u v)))}
    {pt : GeometricMorphism (Sheaf Xt.J (Type (max u v)))
      (Sheaf Yt.J (Type (max u v)))}
    (NX : InverseModel Xt X R νX) (NY : InverseModel Yt Y R νY)
    (LP : InverseModel X Y R p) (Lt : InverseModel Xt Yt R pt)
    (sets : νY.inverse ⋙ pt.inverse ≅ p.inverse ⋙ νX.inverse)
    (a : NY.lift.modules ⋙ Lt.lift.modules ≅ LP.lift.modules ⋙ NX.lift.modules) : Prop :=
  ∀ M : modules Y R,
    (underlying Xt R).map (a.hom.app M) ≫
        NX.lift.moduleUnderlying.hom.app (LP.lift.modules.obj M) ≫
        νX.inverse.map (LP.lift.moduleUnderlying.hom.app M) =
      Lt.lift.moduleUnderlying.hom.app (NY.lift.modules.obj M) ≫
        pt.inverse.map (NY.lift.moduleUnderlying.hom.app M) ≫
        sets.hom.app ((underlying Y R).obj M)

/-- A square of geometric morphisms, with its specified set-level commutation
and both module lifts. Each ordinary inverse-image square is normalized by the
underlying set square; the derived square is its exact descent.
Source: Stacks 07A7 and blueprint sk-thm-purity-transport, Steps 1 and 3
(blueprint: def-pur-normalized-inverse-image-square). -/
structure InverseSquare (T Y : Vertex.{u, v} φ) where
  p : GeometricMorphism (Sheaf T.W.J (Type (max u v)))
    (Sheaf Y.W.J (Type (max u v)))
  tildeP : GeometricMorphism (Sheaf T.tildeW.J (Type (max u v)))
    (Sheaf Y.tildeW.J (Type (max u v)))
  LA : InverseModel T.W Y.W A p
  LB : InverseModel T.W Y.W B p
  tildeLA : InverseModel T.tildeW Y.tildeW A tildeP
  tildeLB : InverseModel T.tildeW Y.tildeW B tildeP
  scalar : ScalarPullback φ LA LB Y.scalar T.scalar
  tildeScalar : ScalarPullback φ tildeLA tildeLB Y.tildeScalar T.tildeScalar
  sets : Y.ν.inverse ⋙ tildeP.inverse ≅ p.inverse ⋙ T.ν.inverse
  aA : Y.NA.lift.modules ⋙ tildeLA.lift.modules ≅ LA.lift.modules ⋙ T.NA.lift.modules
  aB : Y.NB.lift.modules ⋙ tildeLB.lift.modules ≅ LB.lift.modules ⋙ T.NB.lift.modules
  normalizedA : InverseSquareNormalized T.NA Y.NA LA tildeLA sets aA
  normalizedB : InverseSquareNormalized T.NB Y.NB LB tildeLB sets aB

/-- Counit-normalized direct-image site comparison, the actual mate of the
specified inverse-image identification.
Source: Stacks 07A7 (blueprint: def-pur-normalized-inverse-image-square). -/
def directSiteA {T Y : Vertex.{u, v} φ} (p : InverseSquare φ T Y)
    (R : DirectModel p.LA) (tildeR : DirectModel p.tildeLA) :
    R.functor ⋙ inverse Y.NA ⟶ inverse T.NA ⋙ tildeR.functor :=
  (mateEquiv R.adj tildeR.adj (TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso p.aA).hom)).natTrans

/-- The same site mate in B coefficients.
Source: Stacks 07A7 (blueprint: def-pur-normalized-inverse-image-square). -/
def directSiteB {T Y : Vertex.{u, v} φ} (p : InverseSquare φ T Y)
    (R : DirectModel p.LB) (tildeR : DirectModel p.tildeLB) :
    R.functor ⋙ inverse Y.NB ⟶ inverse T.NB ⋙ tildeR.functor :=
  (mateEquiv R.adj tildeR.adj (TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso p.aB).hom)).natTrans

/-- The counit-defined scalar/direct-image constituent chi, rather than an
arbitrary isomorphism of the endpoints.
Source: Stacks 07A6 and 07A7
(blueprint: def-pur-normalized-inverse-image-square). -/
def directScalar {T W : Presentation.{u, v}}
    {g : GeometricMorphism (Sheaf T.J (Type (max u v)))
      (Sheaf W.J (Type (max u v)))}
    {LA : InverseModel T W A g} {LB : InverseModel T W B g}
    {SW : Scalar φ W} {ST : Scalar φ T}
    (l : ScalarPullback φ LA LB SW ST) (RA : DirectModel LA) (RB : DirectModel LB) :
    RA.functor ⋙ SW.model.T ⟶ ST.model.T ⋙ RB.functor :=
  (mateEquiv RA.adj RB.adj (TwoSquare.mk _ _ _ _ l.comparison.hom)).natTrans


end CategoryTheory.CompactScalarSite

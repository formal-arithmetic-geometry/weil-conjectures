/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.CategoryTheory.FlatRingedDiagramRestriction
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.Data.PNat.Basic
import Sheaf.CategoryTheory.DiagramSiteRealization
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Flat scalar transport of strict-tower exchange

Source: blueprint main-20261015, completed-exchange-coherence proof, second paragraph,
strict coefficient supplement; Stacks 07A7, remark-base-change
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange).

The auxiliary records only spell out the given corners, edges, derived operations,
and canonical square comparisons. In particular the square comparisons are normalized
on underlying sheaves and on complexes, rather than arbitrary derived isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u w uA vA uB vB uC vC uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace CategoryTheory
namespace FlatScalarTowerExchange

/-- The positive inverse-sequence category, lifted to the site universe.
Source: strict coefficient supplement, J = positive integers opposite
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev Index := ULiftHom.{u} (ULift.{u} ℕ+ᵒᵖ)

set_option genInjectivity false in
set_option linter.checkUnivs false in
/-- One of the four sites with its compatible flat coefficient change.
Source: strict coefficient supplement, corner data
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
structure Corner where
  site : Type u
  category : SmallCategory site
  topology : GrothendieckTopology site
  R : Sheaf topology CommRingCat.{u}
  S : Sheaf topology CommRingCat.{u}
  a : R ⟶ S
  flat : SheafOfModules.IsFlatOnSite.{u, u, u, u}
    ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose topology (forget₂ CommRingCat RingCat)).map a)).obj
      (SheafOfModules.unit.{u} ((sheafCompose topology (forget₂ CommRingCat RingCat)).obj S)))

  /-- A chosen unbounded localization for the R diagrams, in Hom universe w. -/
  derivedR : HasDerivedCategory.{w} (Index.{u} ⥤ ringedSiteModules.{u}
    ((sheafCompose topology (forget₂ CommRingCat RingCat)).obj R))
  /-- A chosen unbounded localization for the S diagrams, in Hom universe w. -/
  derivedS : HasDerivedCategory.{w} (Index.{u} ⥤ ringedSiteModules.{u}
    ((sheafCompose topology (forget₂ CommRingCat RingCat)).obj S))

attribute [instance] Corner.category Corner.derivedR Corner.derivedS

/-- R-module strict diagrams at a corner.
Source: strict coefficient supplement, derived strict diagrams
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev Corner.modulesR (T : Corner.{u, w}) :=
  Index.{u} ⥤ ringedSiteModules.{u}
    ((sheafCompose T.topology (forget₂ CommRingCat RingCat)).obj T.R)

/-- S-module strict diagrams at a corner.
Source: strict coefficient supplement, derived strict diagrams
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev Corner.modulesS (T : Corner.{u, w}) :=
  Index.{u} ⥤ ringedSiteModules.{u}
    ((sheafCompose T.topology (forget₂ CommRingCat RingCat)).obj T.S)

/-- The inherited abelian structure, named once to keep subsequent type elaboration small.
Source: Stacks 03DA and the product-site realization
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
instance Corner.modulesRAbelian (T : Corner.{u, w}) : Abelian T.modulesR := inferInstance

/-- The inherited abelian structure for S diagrams, with no new category structure.
Source: Stacks 03DA and the product-site realization
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
instance Corner.modulesSAbelian (T : Corner.{u, w}) : Abelian T.modulesS := inferInstance

/-- The underlying set-sheaf functor for a coefficient sheaf.
Source: Stacks 03D3, underlying sheaves of modules
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev underlying {C : Type u} [SmallCategory C] {K : GrothendieckTopology C}
    (R : Sheaf K CommRingCat.{u}) :=
  SheafOfModules.toSheaf.{u} ((sheafCompose K (forget₂ CommRingCat RingCat)).obj R) ⋙
    sheafCompose K (forget AddCommGrpCat)

/-- The actual ordinary scalar restriction on strict diagrams at a corner.
Source: Stacks 03D3 and strict coefficient supplement
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev Corner.restrict (T : Corner.{u, w}) : T.modulesS ⥤ T.modulesR :=
  (Functor.whiskeringRight Index.{u} _ _).obj (SheafOfModules.restrictScalars.{u}
    ((sheafCompose T.topology (forget₂ CommRingCat RingCat)).map T.a))

set_option genInjectivity false in
/-- A specified exact localization, determined by its comparison on complexes.
Source: Stacks 04VG and strict coefficient supplement, termwise restriction
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
structure LocalizedFunctor
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    (F₀ : A ⥤ B) [F₀.Additive] where
  functor : DerivedCategory A ⥤ DerivedCategory B
  factor : DerivedCategory.Q ⋙ functor ≅ F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

/-- The actual derived restriction at a corner, with its exact-localization factor.
Source: normalized restriction comparisons in the strict coefficient supplement
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev Corner.Restriction (T : Corner.{u, w}) :=
  LocalizedFunctor T.restrict

set_option genInjectivity false in
/-- A geometric edge on the prescribed corner rings; the fields are exactly those
of FlatRingedDiagramInput not already supplied by the corners.
Source: strict coefficient supplement, edge data
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
structure EdgeData (U V : Corner.{u, w}) where
  R : FlatRingedModuleImage V.R U.R
  S : FlatRingedModuleImage V.S U.S
  sameInverse : R.morphism.inverse = S.morphism.inverse
  sameDirect : R.morphism.direct = S.morphism.direct
  sameAdjunction : HEq R.morphism.adj S.morphism.adj
  coherent : R.inverse.ringUnderlying.hom ≫
      (sheafCompose U.topology (forget CommRingCat)).map U.a =
    R.morphism.inverse.map ((sheafCompose V.topology (forget CommRingCat)).map V.a) ≫
      eqToHom (congrArg (fun F ↦ F.obj
        ((sheafCompose V.topology (forget CommRingCat)).obj V.S)) sameInverse) ≫
      S.inverse.ringUnderlying.hom

/-- The edge's existing flat-restriction input, formed from the shared corner data.
Source: strict coefficient supplement, normalized restriction
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev EdgeData.input {U V : Corner.{u, w}} (e : EdgeData U V) :
    FlatRingedDiagramInput V.topology U.topology where
  RU := U.R
  SU := U.S
  RV := V.R
  SV := V.S
  aU := U.a
  aV := V.a
  flatU := U.flat
  flatV := V.flat
  R := e.R
  S := e.S
  sameInverse := e.sameInverse
  sameDirect := e.sameDirect
  sameAdjunction := e.sameAdjunction
  coherent := e.coherent

set_option genInjectivity false in
/-- The specified derived adjunction, with the 0FND/0DVC representative normalization.
Source: Stacks 0FND/0DVC and strict coefficient supplement
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
structure NormalizedDerivedAdjunction
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    (L₀ : A ⥤ B) [L₀.Additive] (F₀ : B ⥤ A) [F₀.Additive] (adj₀ : L₀ ⊣ F₀) where
  L : DerivedCategory A ⥤ DerivedCategory B
  F : DerivedCategory B ⥤ DerivedCategory A
  q : DerivedCategory.Q ⋙ L ≅ L₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  η : F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F
  adj : L ⊣ F
  derived : F.IsRightDerivedFunctor η (HomologicalComplex.quasiIso B (.up ℤ))
  computes : ∀ I : CochainComplex B ℤ, I.IsKInjective → IsIso (η.app I)
  transpose : ∀ (P : CochainComplex A ℤ) (I : CochainComplex B ℤ)
    (f : (L₀.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    adj.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
      (q.hom.app P ≫ DerivedCategory.Q.map f) =
    DerivedCategory.Q.map ((adj₀.mapHomologicalComplex (.up ℤ)).homEquiv P I f) ≫ η.app I


/-- The chosen derived termwise operations of an edge with an invertible ring map.
Source: strict coefficient supplement, specified derived termwise adjunctions
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
abbrev DerivedImage {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    {RV : Sheaf K CommRingCat.{u}} {RU : Sheaf H CommRingCat.{u}}
    (e : FlatRingedModuleImage RV RU)
    [HasDerivedCategory.{w} (Index.{u} ⥤ ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RV))]
    [HasDerivedCategory.{w} (Index.{u} ⥤ ringedSiteModules.{u}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj RU))] :=
  NormalizedDerivedAdjunction
    ((Functor.whiskeringRight Index.{u} _ _).obj e.inverse.modules)
    ((Functor.whiskeringRight Index.{u} _ _).obj e.morphism.modules)
    (Adjunction.whiskerRight Index.{u} e.adjunction)


/-- The supplied comparisons have exactly the normalization of the recorded
flat-restriction theorem, including the fixed corner localization factors.
Source: strict coefficient supplement, normalized p and d comparisons
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def EdgeNormalized {U V : Corner.{u, w}}
    (e : EdgeData U V) (R : DerivedImage e.R) (S : DerivedImage e.S)
    (rU : U.Restriction) (rV : V.Restriction)
    (p : S.L ⋙ rU.functor ≅ rV.functor ⋙ R.L)
    (d : S.F ⋙ rV.functor ≅ rU.functor ⋙ R.F) : Prop :=
  ∃ c : FlatRingedDiagramInput.DerivedRestrictionComparison
      (x := e.input) (J := Index.{u}) R.L R.F R.q R.η R.adj S.L S.F S.q S.η S.adj,
    c.maps.rU = rU.functor ∧ c.maps.rV = rV.functor ∧
    HEq c.maps.qU rU.factor ∧ HEq c.maps.qV rV.factor ∧
    HEq p c.maps.b ∧ HEq d c.maps.d

set_option genInjectivity false in
/-- The two normalized natural isomorphisms on the shared restrictions.
Source: strict coefficient supplement, p_u and d_u
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
structure DerivedEdge {U V : Corner.{u, w}}
    (e : EdgeData U V) (R : DerivedImage e.R) (S : DerivedImage e.S)
    (rU : U.Restriction) (rV : V.Restriction) where
  /-- The prescribed inverse-image comparison, on the shared restrictions. -/
  p : S.L ⋙ rU.functor ≅ rV.functor ⋙ R.L
  /-- The prescribed direct-image comparison, on the shared restrictions. -/
  d : S.F ⋙ rV.functor ≅ rU.functor ⋙ R.F
  normalized : EdgeNormalized e R S rU rV p d

set_option genInjectivity false in
/-- A coefficient-normalized ordinary pullback square. The underlying sheaf equation
uniquely specifies the module comparison from the geometric square; its components
are linear morphisms for the given coefficient actions.
Source: Stacks 07A7 and strict coefficient supplement, canonical pullback square
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
structure ModuleSquare
    {CX CY CX' CY' : Type u}
    [SmallCategory CX] [SmallCategory CY] [SmallCategory CX'] [SmallCategory CY']
    {KX : GrothendieckTopology CX} {KY : GrothendieckTopology CY}
    {KX' : GrothendieckTopology CX'} {KY' : GrothendieckTopology CY'}
    {RX : Sheaf KX CommRingCat.{u}} {RY : Sheaf KY CommRingCat.{u}}
    {RX' : Sheaf KX' CommRingCat.{u}} {RY' : Sheaf KY' CommRingCat.{u}}
    (f : FlatRingedModuleImage RY RX) (g : FlatRingedModuleImage RY RY')
    (fp : FlatRingedModuleImage RY' RX') (gp : FlatRingedModuleImage RX RX') where
  geometry : g.morphism.inverse ⋙ fp.morphism.inverse ≅
    f.morphism.inverse ⋙ gp.morphism.inverse
  coefficient : fp.morphism.inverse.map g.inverse.ringUnderlying.hom ≫
      fp.inverse.ringUnderlying.hom =
    geometry.hom.app ((sheafCompose KY (forget CommRingCat)).obj RY) ≫
      gp.morphism.inverse.map f.inverse.ringUnderlying.hom ≫ gp.inverse.ringUnderlying.hom
  modules : g.inverse.modules ⋙ fp.inverse.modules ≅ f.inverse.modules ⋙ gp.inverse.modules
  normalized : ∀ M : ringedSiteModules.{u}
      ((sheafCompose KY (forget₂ CommRingCat RingCat)).obj RY),
    (underlying RX').map (modules.hom.app M) ≫
        gp.inverse.moduleUnderlying.hom.app (f.inverse.modules.obj M) ≫
        gp.morphism.inverse.map (f.inverse.moduleUnderlying.hom.app M) =
      fp.inverse.moduleUnderlying.hom.app (g.inverse.modules.obj M) ≫
        fp.morphism.inverse.map (g.inverse.moduleUnderlying.hom.app M) ≫
        geometry.hom.app ((underlying RY).obj M)


/-- The square comparison on strict diagrams is the specified module comparison
applied termwise. Source: Stacks 07A7, strict coefficient supplement
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def ModuleSquare.diagrams
    {CX CY CX' CY' : Type u}
    [SmallCategory CX] [SmallCategory CY] [SmallCategory CX'] [SmallCategory CY']
    {KX : GrothendieckTopology CX} {KY : GrothendieckTopology CY}
    {KX' : GrothendieckTopology CX'} {KY' : GrothendieckTopology CY'}
    {RX : Sheaf KX CommRingCat.{u}} {RY : Sheaf KY CommRingCat.{u}}
    {RX' : Sheaf KX' CommRingCat.{u}} {RY' : Sheaf KY' CommRingCat.{u}}
    {f : FlatRingedModuleImage RY RX} {g : FlatRingedModuleImage RY RY'}
    {fp : FlatRingedModuleImage RY' RX'} {gp : FlatRingedModuleImage RX RX'}
    (s : ModuleSquare f g fp gp) :=
  (Functor.whiskeringRight Index.{u} _ _).mapIso s.modules

/-- Normalization of an exact-localization square on complexes. This generic form
keeps the four abelian categories opaque while checking the composition formula.
Source: Stacks 04VG and strict coefficient supplement, localization of pullback composition
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def LocalizationSquareNormalized
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{w} C]
    {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{w} D]
    (g₀ : A ⥤ B) [g₀.Additive] (fp₀ : B ⥤ D) [fp₀.Additive]
    (f₀ : A ⥤ C) [f₀.Additive] (gp₀ : C ⥤ D) [gp₀.Additive]
    (θ₀ : g₀ ⋙ fp₀ ≅ f₀ ⋙ gp₀)
    (gL : DerivedCategory A ⥤ DerivedCategory B)
    (fpL : DerivedCategory B ⥤ DerivedCategory D)
    (fL : DerivedCategory A ⥤ DerivedCategory C)
    (gpL : DerivedCategory C ⥤ DerivedCategory D)
    (qg : DerivedCategory.Q ⋙ gL ≅ g₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qfp : DerivedCategory.Q ⋙ fpL ≅ fp₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qf : DerivedCategory.Q ⋙ fL ≅ f₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (qgp : DerivedCategory.Q ⋙ gpL ≅ gp₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (θ : gL ⋙ fpL ≅ fL ⋙ gpL) : Prop :=
  ∀ P : CochainComplex A ℤ,
    fpL.map (qg.hom.app P) ≫ qfp.hom.app ((g₀.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex θ₀ (.up ℤ)).hom.app P) =
      θ.hom.app (DerivedCategory.Q.obj P) ≫ gpL.map (qf.hom.app P) ≫
        qgp.hom.app ((f₀.mapHomologicalComplex (.up ℤ)).obj P)

variable {X Y X' Y' : Corner.{u, w}}
  {f : EdgeData X Y} {g : EdgeData Y' Y}
  {fp : EdgeData X' Y'} {gp : EdgeData X' X}
  {rX : X.Restriction} {rY : Y.Restriction}
  {rX' : X'.Restriction} {rY' : Y'.Restriction}
  {fR : DerivedImage f.R} {fS : DerivedImage f.S}
  {gR : DerivedImage g.R} {gS : DerivedImage g.S}
  {fpR : DerivedImage fp.R} {fpS : DerivedImage fp.S}
  {gpR : DerivedImage gp.R} {gpS : DerivedImage gp.S}

set_option genInjectivity false in
/-- The two specified coefficient squares lie over the same geometric square.
The HEq only transports along the four sameInverse identifications in EdgeData;
it does not impose equality of differently typed module functors.
Source: strict coefficient supplement, specified commutative square
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
structure Square where
  R : ModuleSquare f.R g.R fp.R gp.R
  S : ModuleSquare f.S g.S fp.S gp.S
  sameGeometry : HEq R.geometry S.geometry


/-- The specified derived square and its normalization by termwise pullback composition.
The two equations characterize exact localization of the ordinary canonical squares.
Source: strict coefficient supplement, canonical pullback composition after localization
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def SquareNormalized (s : Square (f := f) (g := g) (fp := fp) (gp := gp))
    (R : gR.L ⋙ fpR.L ≅ fR.L ⋙ gpR.L)
    (S : gS.L ⋙ fpS.L ≅ fS.L ⋙ gpS.L) : Prop :=
  LocalizationSquareNormalized (g.input.inverseR Index.{u}) (fp.input.inverseR Index.{u})
    (f.input.inverseR Index.{u}) (gp.input.inverseR Index.{u}) s.R.diagrams
    gR.L fpR.L fR.L gpR.L gR.q fpR.q fR.q gpR.q R ∧
  LocalizationSquareNormalized (g.input.inverseS Index.{u}) (fp.input.inverseS Index.{u})
    (f.input.inverseS Index.{u}) (gp.input.inverseS Index.{u}) s.S.diagrams
    gS.L fpS.L fS.L gpS.L gS.q fpS.q fS.q gpS.q S

/-- The source comparison b, composed from p_g and d_f exactly as in the node.
Source: strict coefficient supplement, displayed definition of b_Z
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def sourceComparison (df : DerivedEdge f fR fS rX rY) (dg : DerivedEdge g gR gS rY' rY) :
    (fS.F ⋙ gS.L) ⋙ rY'.functor ≅ rX.functor ⋙ (fR.F ⋙ gR.L) :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft fS.F dg.p ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight df.d gR.L ≪≫
    Functor.associator _ _ _

/-- The target comparison d, composed from d_f' and p_g' exactly as in the node.
Source: strict coefficient supplement, displayed definition of d_Z
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange). -/
def targetComparison (dfp : DerivedEdge fp fpR fpS rX' rY') (dgp : DerivedEdge gp gpR gpS rX' rX) :
    (gpS.L ⋙ fpS.F) ⋙ rY'.functor ≅ rX.functor ⋙ (gpR.L ⋙ fpR.F) :=
  Functor.associator _ _ _ ≪≫ isoWhiskerLeft gpS.L dfp.d ≪≫
    (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight dgp.p fpR.F ≪≫
    Functor.associator _ _ _


/-- Flat scalar restriction identifies the canonical pullback composition squares,
their exchange mates as natural transformations on actual derived strict towers,
and the explicitly specified counit transpose.

Source: blueprint main-20261015, completed-exchange-coherence proof, second paragraph,
strict coefficient supplement; Stacks 07A7, remark-base-change
(blueprint: lem-weil-pbc-flat-scalar-tower-exchange).

Proof plan:
1. Apply lem-weil-pbc-flat-ringed-diagram-restriction on all four edges. The recorded
comparison gives the adjunct equation (A) and the natural isomorphisms p and d.
2. Before localization, the coefficient compatibility on each edge identifies the
R-action with the restricted S-action. Along either path the two composite actions
agree by Square.R.coefficient and Square.S.coefficient and the shared geometry.
The normalized ordinary comparison therefore commutes with the square. Apply it
degreewise and use lem-weil-pbc-localization-universal-property to descend and detect
equality. The normalization equations of SquareNormalized give the first conjunct (C).
3. Apply the edge-f adjunct equation to its S-counit, whose adjunct is the identity.
The inverse Hom formula gives rX(epsilonS) p_f inverse L_f(d_f inverse) = epsilonR (K).
4. By def-weil-pbc-adjunction-mate, E_S transposes to thetaS followed by L_g'(epsilonS).
The edge-f' adjunct equation, and pre/postcomposition naturality of that Hom bijection,
transpose the conjugate b inverse; rY'(E_S); d to the composite (T) in the node.
5. Naturality of p_g' moves it past epsilonS. Substitute (C) and cancel the invertible
comparisons. Expanding b gives p_g b inverse = L_g(d_f inverse), yielding (T').
6. Naturality of thetaR moves d_f inverse to the counit. Equation (K) reduces (T')
to thetaR followed by L_g'(epsilonR), the stated explicit transpose. The adjunction
bijection is injective, giving the mate equality. Compose with b to obtain the second
conjunct. Every constituent is a natural transformation of full derived diagram
functors, proving the natural-transformation equality, with no transition, completeness,
cartesianness, reduction-tower, or boundedness condition on Z. -/
theorem flatScalarTowerExchange
    (s : Square (f := f) (g := g) (fp := fp) (gp := gp))
    (df : DerivedEdge f fR fS rX rY) (dg : DerivedEdge g gR gS rY' rY)
    (dfp : DerivedEdge fp fpR fpS rX' rY') (dgp : DerivedEdge gp gpR gpS rX' rX)
    (θR : gR.L ⋙ fpR.L ≅ fR.L ⋙ gpR.L)
    (θS : gS.L ⋙ fpS.L ≅ fS.L ⋙ gpS.L)
    (hθ : SquareNormalized s θR θS) :
    (∀ M : DerivedCategory Y.modulesS,
      rX'.functor.map (θS.hom.app M) ≫ dgp.p.hom.app (fS.L.obj M) ≫
          gpR.L.map (df.p.hom.app M) =
        dfp.p.hom.app (gS.L.obj M) ≫ fpR.L.map (dg.p.hom.app M) ≫
          θR.hom.app (rY.functor.obj M)) ∧
    (whiskerRight (mateEquiv fS.adj fpS.adj
        (TwoSquare.mk _ _ _ _ θS.hom)).natTrans rY'.functor ≫
          (targetComparison dfp dgp).hom =
      (sourceComparison df dg).hom ≫ whiskerLeft rX.functor
        (mateEquiv fR.adj fpR.adj (TwoSquare.mk _ _ _ _ θR.hom)).natTrans) ∧
    (∀ Z : DerivedCategory X.modulesS,
      (fpR.adj.homEquiv _ _).symm
        ((sourceComparison df dg).inv.app Z ≫
          rY'.functor.map ((mateEquiv fS.adj fpS.adj
            (TwoSquare.mk _ _ _ _ θS.hom)).app Z) ≫
          (targetComparison dfp dgp).hom.app Z) =
        θR.hom.app (fR.F.obj (rX.functor.obj Z)) ≫
          gpR.L.map (fR.adj.counit.app (rX.functor.obj Z))) := by
  sorry

end FlatScalarTowerExchange
end CategoryTheory

module

public import Mathlib.CategoryTheory.Whiskering

/-! # Conjugated comparisons and the direct-counit normal form

Source: the agent-formulated categorical calculation supporting Bhatt--Scholze,
Corollary 5.1.6, extracted in lem-weil-boundary-comparison-composition-transport,
steps 3--4; the calculation itself uses Stacks Project, Categories, Tag 0014.
(blueprint: lem-weil-boundary-conjugated-comparison-normal-form)

The two comparisons are actual composites of whiskered natural isomorphisms and
canonical functor associators. The counit is an arbitrary natural transformation
subject to the displayed component square.
-/

@[expose] public section

set_option autoImplicit false

universe vCX vCY vCB vDX vDY vDB uCX uCY uCB uDX uDY uDB

namespace CategoryTheory.BoundaryConjugatedComparison

/-- The comparison Xi, constructed by the four prescribed comparison factors.
Source: agent-formulated calculation supporting Bhatt--Scholze, Corollary 5.1.6,
lem-weil-boundary-comparison-composition-transport, steps 3--4; Stacks Tag 0014.
(blueprint: lem-weil-boundary-conjugated-comparison-normal-form) -/
def rightIso
    {CX : Type uCX} [Category.{vCX} CX] {CY : Type uCY} [Category.{vCY} CY]
    {CB : Type uCB} [Category.{vCB} CB] {DX : Type uDX} [Category.{vDX} DX]
    {DY : Type uDY} [Category.{vDY} DY] {DB : Type uDB} [Category.{vDB} DB]
    {Rf : CY ⥤ CX} {Rg : CB ⥤ CY} {Rc : CB ⥤ CX}
    {Qf : DY ⥤ DX} {Qg : DB ⥤ DY} {Qc : DB ⥤ DX}
    {SX : CX ⥤ DX} {SY : CY ⥤ DY} {SB : CB ⥤ DB}
    (ρf : Rf ⋙ SX ≅ SY ⋙ Qf) (ρg : Rg ⋙ SY ≅ SB ⋙ Qg)
    (ρc : Rc ⋙ SX ≅ SB ⋙ Qc) (θ : Rc ≅ Rg ⋙ Rf) :
    (SB ⋙ Qg) ⋙ Qf ≅ SB ⋙ Qc :=
  Functor.isoWhiskerRight ρg.symm Qf ≪≫ Functor.associator Rg SY Qf ≪≫
    Functor.isoWhiskerLeft Rg ρf.symm ≪≫ (Functor.associator Rg Rf SX).symm ≪≫
    Functor.isoWhiskerRight θ.symm SX ≪≫ ρc

/-- The comparison a, constructed by the four prescribed comparison factors.
Source: agent-formulated calculation supporting Bhatt--Scholze, Corollary 5.1.6,
lem-weil-boundary-comparison-composition-transport, steps 3--4; Stacks Tag 0014.
(blueprint: lem-weil-boundary-conjugated-comparison-normal-form) -/
def leftIso
    {CX : Type uCX} [Category.{vCX} CX] {CY : Type uCY} [Category.{vCY} CY]
    {CB : Type uCB} [Category.{vCB} CB] {DX : Type uDX} [Category.{vDX} DX]
    {DY : Type uDY} [Category.{vDY} DY] {DB : Type uDB} [Category.{vDB} DB]
    {Ff : CX ⥤ CY} {Fg : CY ⥤ CB} {Fc : CX ⥤ CB}
    {Pf : DX ⥤ DY} {Pg : DY ⥤ DB} {Pc : DX ⥤ DB}
    {SX : CX ⥤ DX} {SY : CY ⥤ DY} {SB : CB ⥤ DB}
    (Bf : Ff ⋙ SY ≅ SX ⋙ Pf) (Bg : Fg ⋙ SB ≅ SY ⋙ Pg)
    (Bc : Fc ⋙ SB ≅ SX ⋙ Pc) (α : Ff ⋙ Fg ≅ Fc) :
    (SX ⋙ Pf) ⋙ Pg ≅ SX ⋙ Pc :=
  Functor.isoWhiskerRight Bf.symm Pg ≪≫ Functor.associator Ff SY Pg ≪≫
    Functor.isoWhiskerLeft Ff Bg.symm ≪≫ (Functor.associator Ff Fg SB).symm ≪≫
    Functor.isoWhiskerRight α SB ≪≫ Bc

/-- The prescribed comparison components, inverse cancellation, and counit normal form.
Source: agent-formulated categorical calculation supporting Bhatt--Scholze,
Corollary 5.1.6, lem-weil-boundary-comparison-composition-transport, steps 3--4;
Stacks Project, Categories, Tag 0014 supplies the category laws.
(blueprint: lem-weil-boundary-conjugated-comparison-normal-form)

Proof plan from the node:
1. Naturality of a composite follows by applying the naturality square of each
   factor. Multiplying the naturality square of an isomorphism by its inverses
   proves naturality of the inverse. Whiskering uses functoriality, which also
   shows that functor images of inverse components are inverse.
2. Apply these operations to the chains defining rightIso and leftIso. Their
   components are the displayed four-factor formulas; canonical associators
   have identity components and therefore do not change either formula.
3. At H put r = rho_g, b = rho_f at Rg(H), t = theta, d = rho_c. The arrow
   w = d^{-1} followed by SX(t), b, and Qf(r) is inverse to Xi_H: in both
   products cancel adjacent inverse pairs, using functoriality for the images.
   Uniqueness of the inverse gives w = Xi_H^{-1}. Precompose by d to obtain
   the third displayed equality.
4. At K = Rc(H), expand a_K. Reassociate so that Bc_K, Pc(rho_c,H), and m_H
   are consecutive. The assumed square replaces this subcomposition by
   SB(epsilon_c,H). Combine SB(alpha_K) with it using functoriality to get
   the direct-counit normal form. No relation between alpha and theta is used.
-/
theorem normalForm
    {CX : Type uCX} [Category.{vCX} CX] {CY : Type uCY} [Category.{vCY} CY]
    {CB : Type uCB} [Category.{vCB} CB] {DX : Type uDX} [Category.{vDX} DX]
    {DY : Type uDY} [Category.{vDY} DY] {DB : Type uDB} [Category.{vDB} DB]
    (Ff : CX ⥤ CY) (Fg : CY ⥤ CB) (Fc : CX ⥤ CB)
    (Rf : CY ⥤ CX) (Rg : CB ⥤ CY) (Rc : CB ⥤ CX)
    (Pf : DX ⥤ DY) (Pg : DY ⥤ DB) (Pc : DX ⥤ DB)
    (Qf : DY ⥤ DX) (Qg : DB ⥤ DY) (Qc : DB ⥤ DX)
    (SX : CX ⥤ DX) (SY : CY ⥤ DY) (SB : CB ⥤ DB)
    (ρf : Rf ⋙ SX ≅ SY ⋙ Qf) (ρg : Rg ⋙ SY ≅ SB ⋙ Qg)
    (ρc : Rc ⋙ SX ≅ SB ⋙ Qc)
    (Bf : Ff ⋙ SY ≅ SX ⋙ Pf) (Bg : Fg ⋙ SB ≅ SY ⋙ Pg)
    (Bc : Fc ⋙ SB ≅ SX ⋙ Pc) (α : Ff ⋙ Fg ≅ Fc) (θ : Rc ≅ Rg ⋙ Rf)
    (εc : Rc ⋙ Fc ⟶ 𝟭 CB)
    (m : ∀ H : CB, Pc.obj (Qc.obj (SB.obj H)) ⟶ SB.obj H)
    (hm : ∀ H : CB,
      Bc.hom.app (Rc.obj H) ≫ Pc.map (ρc.hom.app H) ≫ m H = SB.map (εc.app H)) :
    (∀ H : CB, (rightIso ρf ρg ρc θ).hom.app H =
      Qf.map (ρg.inv.app H) ≫ ρf.inv.app (Rg.obj H) ≫
        SX.map (θ.inv.app H) ≫ ρc.hom.app H) ∧
    (∀ G : CX, (leftIso Bf Bg Bc α).hom.app G =
      Pg.map (Bf.inv.app G) ≫ Bg.inv.app (Ff.obj G) ≫
        SB.map (α.hom.app G) ≫ Bc.hom.app G) ∧
    (∀ H : CB, ρc.hom.app H ≫ (rightIso ρf ρg ρc θ).inv.app H =
      SX.map (θ.hom.app H) ≫ ρf.hom.app (Rg.obj H) ≫ Qf.map (ρg.hom.app H)) ∧
    (∀ H : CB,
      (leftIso Bf Bg Bc α).hom.app (Rc.obj H) ≫ Pc.map (ρc.hom.app H) ≫ m H =
        Pg.map (Bf.inv.app (Rc.obj H)) ≫ Bg.inv.app (Ff.obj (Rc.obj H)) ≫
          SB.map (α.hom.app (Rc.obj H) ≫ εc.app H)) := by
  sorry

end CategoryTheory.BoundaryConjugatedComparison

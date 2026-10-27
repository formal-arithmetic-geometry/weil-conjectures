# AlgebraicGeometry.ProEtale.AmbientClopen.UnderivedPasting.Systems.Horizontal

## Reason

The literal system horizontal factor predicate makes the kernel repeatedly compare
category instances inside chosen functors. The complete proof against that presentation
exceeded the 120-second server stop. The problem is conversion, not a missing mathematical
step: the normalization and abstract factor calculation check independently.

Retain the actual categories, functors, units, square maps and arrows in a concrete
`Systems.HorizontalFactorData` record. `horizontalFactorData` constructs every field from
the existing system operations; it chooses no new object. Its smallness argument is a proof.
`HorizontalFactorData.factors` is exactly the two original factor equations, with the same
composition order, quantification and objects. `Systems.Horizontal` now uses this expression
for its second conjunct. The first pasting equation and every binder are unchanged.

The proof transports entire data records between the normalization predicate's cached
smallness witness and the assertion predicate's witness by proof irrelevance. No foundational
module, target signature, existing public signature or mathematical assertion changes.
This assertion-definition change should receive the independent semantic review required
by brief §4. No declaration of `Challenge.lean` mentions these assertion definitions in its
signature; its file is unchanged. The ordinary predicates, vertical system predicate and
identity predicates are unchanged. Empty opens, zero modules and non-flat transitions obey
the same formulas as before; the new representation introduces no hypotheses.

## Old

```lean
def Horizontal (F : FiniteFieldDatum.{u}) : Prop :=
  ∀ (U V T W Z Y : Scheme.{u})
    [U.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of F.k))]
    [QuasiCompact (U ↘ Spec (.of F.k))]
    [V.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of F.k))]
    [QuasiCompact (V ↘ Spec (.of F.k))]
    [T.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of F.k))]
    [QuasiCompact (T ↘ Spec (.of F.k))]
    [W.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))]
    [QuasiCompact (W ↘ Spec (.of F.k))]
    [Z.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of F.k))]
    [QuasiCompact (Z ↘ Spec (.of F.k))]
    [Y.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of F.k))]
    [QuasiCompact (Y ↘ Spec (.of F.k))]
    (k₁ : U ⟶ V) (k₂ : V ⟶ T) (i₁ : W ⟶ Z) (i₂ : Z ⟶ Y)
    (r : U ⟶ W) (p : V ⟶ Z) (q : T ⟶ Y)
    [k₁.IsOver (Spec (.of F.k))]
    [k₂.IsOver (Spec (.of F.k))]
    [i₁.IsOver (Spec (.of F.k))]
    [i₂.IsOver (Spec (.of F.k))]
    [r.IsOver (Spec (.of F.k))]
    [p.IsOver (Spec (.of F.k))]
    [q.IsOver (Spec (.of F.k))]
    [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [QuasiCompact k₁] [QuasiCompact k₂] [QuasiCompact i₁] [QuasiCompact i₂]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k₁ ≫ p = r ≫ i₁) (h₂ : k₂ ≫ q = p ≫ i₂)
    (h : (k₁ ≫ k₂) ≫ q = r ≫ (i₁ ≫ i₂)),
    ((Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (VaryingRing.extension C τ i₁) (VaryingRing.moduleAlpha C τ k₂ p q i₂ h₂)
        ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (VaryingRing.moduleAlpha C τ k₁ r p i₁ h₁) (VaryingRing.extension C τ k₂)
        =
      Functor.whiskerRight (VaryingRing.moduleJComp C τ i₁ i₂).hom (VaryingRing.pull C τ q) ≫
      (VaryingRing.moduleAlpha C τ (k₁ ≫ k₂) r q (i₁ ≫ i₂) h) ≫
      Functor.whiskerLeft (VaryingRing.pull C τ r) (VaryingRing.moduleJComp C τ k₁ k₂).inv ≫
      (Functor.associator _ _ _).inv) ∧
    (∀ M : VaryingRing.Modules C τ W,
      (VaryingRing.pull C τ r).map ((VaryingRing.moduleJAdj C τ i₁).unit.app M) ≫
        (VaryingRing.moduleSquareG C τ k₁ r p i₁ h₁).hom.app ((VaryingRing.extension C τ i₁).obj M)
          ≫
        (VaryingRing.pull C τ k₁).map ((VaryingRing.pull C τ p).map ((VaryingRing.moduleJAdj C τ
          i₂).unit.app ((VaryingRing.extension C τ i₁).obj M))) ≫
        (VaryingRing.pull C τ k₁).map ((VaryingRing.moduleSquareG C τ k₂ p q i₂ h₂).hom.app
          ((VaryingRing.extension C τ i₂).obj ((VaryingRing.extension C τ i₁).obj M))) ≫
        (VaryingRing.pull C τ k₁).map ((VaryingRing.pull C τ k₂).map ((VaryingRing.moduleAlpha C τ
          k₂ p q i₂ h₂).app
          ((VaryingRing.extension C τ i₁).obj M))) =
      (VaryingRing.pull C τ r).map ((VaryingRing.moduleJAdj C τ i₁).unit.app M) ≫
        (VaryingRing.moduleSquareG C τ k₁ r p i₁ h₁).hom.app ((VaryingRing.extension C τ i₁).obj M)
          ≫
        (VaryingRing.pull C τ k₁).map ((VaryingRing.moduleJAdj C τ k₂).unit.app ((VaryingRing.pull C
          τ p).obj ((VaryingRing.extension C τ i₁).obj M)))) ∧
    (∀ M : VaryingRing.Modules C τ W,
      (VaryingRing.pull C τ r).map ((VaryingRing.moduleJAdj C τ i₁).unit.app M) ≫
        (VaryingRing.moduleSquareG C τ k₁ r p i₁ h₁).hom.app ((VaryingRing.extension C τ i₁).obj M)
          ≫
        (VaryingRing.pull C τ k₁).map ((VaryingRing.moduleJAdj C τ k₂).unit.app ((VaryingRing.pull C
          τ p).obj ((VaryingRing.extension C τ i₁).obj M))) ≫
        (VaryingRing.pull C τ k₁).map ((VaryingRing.pull C τ k₂).map ((VaryingRing.extension C τ
          k₂).map
          ((VaryingRing.moduleAlpha C τ k₁ r p i₁ h₁).app M))) =
      (VaryingRing.moduleJAdj C τ k₁).unit.app ((VaryingRing.pull C τ r).obj M) ≫
        (VaryingRing.pull C τ k₁).map ((VaryingRing.moduleJAdj C τ k₂).unit.app
          ((VaryingRing.extension C τ k₁).obj ((VaryingRing.pull C τ r).obj M))))
```

## New

The three new public data definitions and the folded predicate, in the same module:

```lean
section FactorData

universe v w

set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] VaryingRing.moduleJAdj VaryingRing.moduleSquareG

-- This bundle records independent universes for its objects and its morphisms.
set_option linter.checkUnivs false in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Two horizontal squares, retaining the category instances used by their operations.
Source: Stacks Project, Tag 0F7D
(blueprint: lem-sf-ambient-underived-clopen-pasting). -/
structure HorizontalFactorData where
  A : Type w
  B : Type w
  C : Type w
  D : Type w
  E : Type w
  H : Type w
  [catA : Category.{v} A]
  [catB : Category.{v} B]
  [catC : Category.{v} C]
  [catD : Category.{v} D]
  [catE : Category.{v} E]
  [catH : Category.{v} H]
  I : A ⥤ B
  PI : B ⥤ A
  J : B ⥤ E
  PJ : E ⥤ B
  K : C ⥤ D
  PK : D ⥤ C
  L : D ⥤ H
  PL : H ⥤ D
  R : A ⥤ C
  P : B ⥤ D
  Q : E ⥤ H
  etaI : 𝟭 A ⟶ I ⋙ PI
  etaJ : 𝟭 B ⟶ J ⋙ PJ
  etaK : 𝟭 C ⟶ K ⋙ PK
  etaL : 𝟭 D ⟶ L ⋙ PL
  s₁ : PI ⋙ R ⟶ P ⋙ PK
  s₂ : PJ ⋙ P ⟶ Q ⋙ PL
  a₁ : I ⋙ P ⟶ R ⋙ K
  a₂ : J ⋙ Q ⟶ P ⋙ L

/-- The two factor restriction equations of horizontal pasting.
Source: Stacks Project, Tag 0F7D
(blueprint: lem-sf-ambient-underived-clopen-pasting). -/
def HorizontalFactorData.factors (d : HorizontalFactorData.{v, w}) : Prop :=
  letI := d.catA
  letI := d.catB
  letI := d.catC
  letI := d.catD
  letI := d.catE
  letI := d.catH
  (∀ M, d.R.map (d.etaI.app M) ≫ d.s₁.app (d.I.obj M) ≫
    d.PK.map (d.P.map (d.etaJ.app (d.I.obj M))) ≫
    d.PK.map (d.s₂.app (d.J.obj (d.I.obj M))) ≫
    d.PK.map (d.PL.map (d.a₂.app (d.I.obj M))) =
    d.R.map (d.etaI.app M) ≫ d.s₁.app (d.I.obj M) ≫
      d.PK.map (d.etaL.app (d.P.obj (d.I.obj M)))) ∧
  (∀ M, d.R.map (d.etaI.app M) ≫ d.s₁.app (d.I.obj M) ≫
    d.PK.map (d.etaL.app (d.P.obj (d.I.obj M))) ≫
    d.PK.map (d.PL.map (d.L.map (d.a₁.app M))) =
    d.etaK.app (d.R.obj M) ≫ d.PK.map (d.etaL.app (d.K.obj (d.R.obj M))))

/-- The actual functors and units in two horizontal system squares.
The smallness argument records a presentation witness, never a choice of module data.
Source: Stacks Project, Tag 0F7D
(blueprint: lem-sf-ambient-underived-clopen-pasting). -/
def horizontalFactorData
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V T W Z Y : Scheme.{u}}
    (k₁ : U ⟶ V) (k₂ : V ⟶ T) (i₁ : W ⟶ Z) (i₂ : Z ⟶ Y)
    (r : U ⟶ W) (p : V ⟶ Z) (q : T ⟶ Y)
    [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [QuasiCompact k₁] [QuasiCompact k₂] [QuasiCompact i₁] [QuasiCompact i₂]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k₁ ≫ p = r ≫ i₁) (h₂ : k₂ ≫ q = p ≫ i₂)
    (small : ∀ X : Scheme.{u}, EssentiallySmall.{u + 1} (ℕ × X.ProEt)) :
    HorizontalFactorData.{u + 1, u + 2} := by
  let cat (X : Scheme.{u}) : Category (VaryingRing.Modules C τ X) :=
    show Category (SheafOfModules.{u + 1}
      (@SemilinearSections.ring _ _ (small X)
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (@SemilinearSections.systemRing _ _ (VaryingRing.siteSmall X)
          (Scheme.ProEt.topology X)
          (VaryingRing.coefficients C X) (VaryingRing.coefficientTransition C τ X)))) from
      inferInstance
  exact {
    A := VaryingRing.Modules C τ W
    B := VaryingRing.Modules C τ Z
    C := VaryingRing.Modules C τ U
    D := VaryingRing.Modules C τ V
    E := VaryingRing.Modules C τ Y
    H := VaryingRing.Modules C τ T
    catA := cat W
    catB := cat Z
    catC := cat U
    catD := cat V
    catE := cat Y
    catH := cat T
    I := VaryingRing.extension C τ i₁
    PI := VaryingRing.pull C τ i₁
    J := VaryingRing.extension C τ i₂
    PJ := VaryingRing.pull C τ i₂
    K := VaryingRing.extension C τ k₁
    PK := VaryingRing.pull C τ k₁
    L := VaryingRing.extension C τ k₂
    PL := VaryingRing.pull C τ k₂
    R := VaryingRing.pull C τ r
    P := VaryingRing.pull C τ p
    Q := VaryingRing.pull C τ q
    etaI := @Adjunction.unit _ (cat W) _ (cat Z)
      (VaryingRing.extension C τ i₁) (VaryingRing.pull C τ i₁)
      (VaryingRing.moduleJAdj C τ i₁)
    etaJ := @Adjunction.unit _ (cat Z) _ (cat Y)
      (VaryingRing.extension C τ i₂) (VaryingRing.pull C τ i₂)
      (VaryingRing.moduleJAdj C τ i₂)
    etaK := @Adjunction.unit _ (cat U) _ (cat V)
      (VaryingRing.extension C τ k₁) (VaryingRing.pull C τ k₁)
      (VaryingRing.moduleJAdj C τ k₁)
    etaL := @Adjunction.unit _ (cat V) _ (cat T)
      (VaryingRing.extension C τ k₂) (VaryingRing.pull C τ k₂)
      (VaryingRing.moduleJAdj C τ k₂)
    s₁ := @Iso.hom _ (@Functor.category _ (cat Z) _ (cat U))
      (@Functor.comp _ (cat Z) _ (cat W) _ (cat U)
        (VaryingRing.pull C τ i₁) (VaryingRing.pull C τ r))
      (@Functor.comp _ (cat Z) _ (cat V) _ (cat U)
        (VaryingRing.pull C τ p) (VaryingRing.pull C τ k₁))
      (VaryingRing.moduleSquareG C τ k₁ r p i₁ h₁)
    s₂ := @Iso.hom _ (@Functor.category _ (cat Y) _ (cat V))
      (@Functor.comp _ (cat Y) _ (cat Z) _ (cat V)
        (VaryingRing.pull C τ i₂) (VaryingRing.pull C τ p))
      (@Functor.comp _ (cat Y) _ (cat T) _ (cat V)
        (VaryingRing.pull C τ q) (VaryingRing.pull C τ k₂))
      (VaryingRing.moduleSquareG C τ k₂ p q i₂ h₂)
    a₁ := VaryingRing.moduleAlpha C τ k₁ r p i₁ h₁
    a₂ := VaryingRing.moduleAlpha C τ k₂ p q i₂ h₂ }

end FactorData

def Horizontal (F : FiniteFieldDatum.{u}) : Prop :=
  ∀ (U V T W Z Y : Scheme.{u})
    [U.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of F.k))]
    [QuasiCompact (U ↘ Spec (.of F.k))]
    [V.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of F.k))]
    [QuasiCompact (V ↘ Spec (.of F.k))]
    [T.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of F.k))]
    [QuasiCompact (T ↘ Spec (.of F.k))]
    [W.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))]
    [QuasiCompact (W ↘ Spec (.of F.k))]
    [Z.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of F.k))]
    [QuasiCompact (Z ↘ Spec (.of F.k))]
    [Y.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of F.k))]
    [QuasiCompact (Y ↘ Spec (.of F.k))]
    (k₁ : U ⟶ V) (k₂ : V ⟶ T) (i₁ : W ⟶ Z) (i₂ : Z ⟶ Y)
    (r : U ⟶ W) (p : V ⟶ Z) (q : T ⟶ Y)
    [k₁.IsOver (Spec (.of F.k))]
    [k₂.IsOver (Spec (.of F.k))]
    [i₁.IsOver (Spec (.of F.k))]
    [i₂.IsOver (Spec (.of F.k))]
    [r.IsOver (Spec (.of F.k))]
    [p.IsOver (Spec (.of F.k))]
    [q.IsOver (Spec (.of F.k))]
    [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    [IsOpenImmersion i₁] [IsOpenImmersion i₂]
    [QuasiCompact k₁] [QuasiCompact k₂] [QuasiCompact i₁] [QuasiCompact i₂]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k₁ ≫ p = r ≫ i₁) (h₂ : k₂ ≫ q = p ≫ i₂)
    (h : (k₁ ≫ k₂) ≫ q = r ≫ (i₁ ≫ i₂)),
    ((Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (VaryingRing.extension C τ i₁) (VaryingRing.moduleAlpha C τ k₂ p q i₂ h₂)
        ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (VaryingRing.moduleAlpha C τ k₁ r p i₁ h₁) (VaryingRing.extension C τ k₂)
        =
      Functor.whiskerRight (VaryingRing.moduleJComp C τ i₁ i₂).hom (VaryingRing.pull C τ q) ≫
      (VaryingRing.moduleAlpha C τ (k₁ ≫ k₂) r q (i₁ ≫ i₂) h) ≫
      Functor.whiskerLeft (VaryingRing.pull C τ r) (VaryingRing.moduleJComp C τ k₁ k₂).inv ≫
      (Functor.associator _ _ _).inv) ∧
    (horizontalFactorData C τ k₁ k₂ i₁ i₂ r p q h₁ h₂
      @pullIdentity._proof_1).factors
```

## Users

A fresh read-only import/declaration scan on 2026-10-26, using the pure lexer and graph
operations of `tools/leanindex.py` used by `tools/downstream.py --uses`, finds zero downstream
Lean modules and only this module's own textual uses. This avoids writing a repository cache
in the read-only checkout. No module is withdrawn: the DAG parents still need this assertion.
All internal proofs are adapted in the same packet. There are no forced adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.AmbientUnderivedClopenPasting | S1 | Same equations and signatures; constructed data package avoids expensive conversion; all clauses proved. |

## Status

landed 20261026T023957-L-622762 2026-10-26 (merge of deliver/S1/Sheaf.SixFunctors.AmbientUnderivedClopenPasting)

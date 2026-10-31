/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedSmoothTrace
public import WeilConjectures.AlgebraicGeometry.InternalSignedTateTwist
public import WeilConjectures.SixFunctors.CondensedCompactSupportCompositionData

import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SecSmoothPurity.FiniteIntegralCompositionTrace
import WeilConjectures.SecSmoothPurity.FieldCompositionTraceTransport

/-! # Composition of the specified condensed smooth purity maps

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-composition/_section.md,
the purity composite and its counit-preserving identification
(blueprint: sk-prop-sp-composition).

The short names below only package the existing geometric indices and functors.
The support compositor comes from the normalized coherent system. The source comparison
is the existing root-normalized tensor/shift compositor, independently of purity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

attribute [local irreducible] DerivedCategory
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

private theorem counitComparison
    {A B : Type*} [Category A] [Category B]
    {L M : A ⥤ B} {R S : B ⥤ A}
    (a : L ⊣ R) (b : M ⊣ S) (alpha : M ≅ L) :
    ∃ v : R ≅ S,
      (∀ K, M.map (v.hom.app K) ≫ b.counit.app K =
        alpha.hom.app (R.obj K) ≫ a.counit.app K) ∧
      ∀ v' : R ≅ S,
        (∀ K, M.map (v'.hom.app K) ≫ b.counit.app K =
          alpha.hom.app (R.obj K) ≫ a.counit.app K) → v' = v := by
  let v := conjugateIsoEquiv a b alpha
  have hv (K : B) : M.map (v.hom.app K) ≫ b.counit.app K =
      alpha.hom.app (R.obj K) ≫ a.counit.app K :=
    conjugateEquiv_counit a b alpha.hom K
  refine ⟨v, hv, ?_⟩
  intro v' hv'
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply (b.homEquiv _ _).symm.injective
  simpa only [Adjunction.homEquiv_counit] using (hv' K).trans (hv K).symm

private theorem purityComparison
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    {J R : B ⥤ A} {K S : C ⥤ B} {T U : C ⥤ A}
    (a : F ⊣ J) (b : G ⊣ K) (c : H ⊣ T)
    (a' : F ⊣ R) (b' : G ⊣ S) (c' : H ⊣ U)
    (alpha : F ⋙ G ≅ H) (v : U ≅ S ⋙ R)
    (hv : ∀ X, (F ⋙ G).map (v.hom.app X) ≫ (a'.comp b').counit.app X =
      alpha.hom.app (U.obj X) ≫ c'.counit.app X)
    (X : C) (q : T.obj X ⟶ J.obj (K.obj X))
    (ht : alpha.hom.app (T.obj X) ≫ c.counit.app X =
      G.map (F.map q) ≫ G.map (a.counit.app (K.obj X)) ≫ b.counit.app X) :
    (c.rightAdjointUniq c').hom.app X ≫ v.hom.app X =
      q ≫ J.map ((b.rightAdjointUniq b').hom.app X) ≫
        (a.rightAdjointUniq a').hom.app (S.obj X) := by
  apply ((a'.comp b').homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [hv, alpha.hom.naturality_assoc, c.rightAdjointUniq_hom_app_counit, ht]
  simp only [Adjunction.comp_counit_app, Functor.comp_map]
  rw [← G.map_comp_assoc _ _ (b'.counit.app X),
    a.rightAdjointUniq_hom_app_counit]
  rw [← G.map_comp_assoc _ _ (b'.counit.app X)]
  have hA : F.map (J.map ((b.rightAdjointUniq b').hom.app X)) ≫
      a.counit.app (S.obj X) =
      a.counit.app (K.obj X) ≫ (b.rightAdjointUniq b').hom.app X :=
    a.counit_naturality _
  rw [hA, G.map_comp, Category.assoc,
    b.rightAdjointUniq_hom_app_counit]

private def tensorSourceIso
    {A B C : Type*} [Category A] [Category B] [Category C]
    [MonoidalCategory A] [MonoidalCategory B]
    (F : B ⥤ A) [F.Monoidal] (G : C ⥤ B) (H : C ⥤ A)
    (a : H ≅ G ⋙ F) (Lh La Lb : A) (L : B)
    (b : Lh ≅ La ⊗ Lb) (p : F.obj L ≅ La) :
    H ⋙ tensorRight Lh ≅ (G ⋙ tensorRight L) ⋙ (F ⋙ tensorRight Lb) :=
  Functor.isoWhiskerRight a _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft G
      (Functor.isoWhiskerLeft F ((tensoringRight A).mapIso b) ≪≫
        Functor.isoWhiskerLeft F (tensorRightTensor La Lb) ≪≫
        (Functor.associator F (tensorRight La) (tensorRight Lb)).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft F ((tensoringRight A).mapIso p.symm) ≪≫
            Functor.Monoidal.commTensorRight F L) (tensorRight Lb) ≪≫
        Functor.associator (tensorRight L) F (tensorRight Lb)) ≪≫
    (Functor.associator G (tensorRight L) (F ⋙ tensorRight Lb)).symm

private theorem tensorSourceIso_component
    {A B C : Type*} [Category A] [Category B] [Category C]
    [MonoidalCategory A] [MonoidalCategory B]
    (F : B ⥤ A) [F.Monoidal] (G : C ⥤ B) (H : C ⥤ A)
    (a : H ≅ G ⋙ F) (Lh La Lb : A) (L : B)
    (b : Lh ≅ La ⊗ Lb) (p : F.obj L ≅ La) (X : C) :
    (tensorSourceIso F G H a Lh La Lb L b p).hom.app X =
      (tensorIso (a.app X) b ≪≫ (α_ _ _ _).symm ≪≫
        tensorIso (tensorIso (Iso.refl _) p.symm ≪≫
          Functor.Monoidal.μIso F _ _) (Iso.refl _)).hom := by
  simp [tensorSourceIso, MonoidalCategory.tensorHom_def, comp_whiskerRight, Category.assoc,
    ← whisker_exchange_assoc]

namespace AlgebraicGeometry.ProEtale.PurityTransport

private theorem lineCoordinates_unique (ell : ℕ) [Fact ell.Prime]
    (c : Coefficient ell) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)]
    (p q : LinePullCoordinates ell c f) : p = q := by
  have hi : p.integral = q.integral :=
    (integralComparison ell f).unique p.integral_normalized q.integral_normalized
  have hf : p.first = q.first := by
    have hp := p.first_normalized
    rw [hi] at hp
    exact eq_of_heq (hp.trans q.first_normalized.symm)
  have hp : p.power = q.power := by
    funext d
    have hp := p.power_normalized d
    rw [hf] at hp
    exact eq_of_heq (hp.trans (q.power_normalized d).symm)
  cases p
  cases q
  cases hi
  cases hf
  cases hp
  rfl


variable (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
  (hEll : ell ≠ D.p) (c : Coefficient ell)

/-- The source of the fixed normalized purity isomorphism, with its existing membership
proof. Source: the displayed J_a (blueprint: sk-prop-sp-composition). -/
abbrev spCompositionSource (s : SmoothDatum D) : c.ctf ell s.Y.left ⥤ c.ctf ell s.X.left :=
  source ell c s.map s.dim
    (WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c s).source_closed

variable (s : SmoothDatum D) (Z : Over (Spec (.of D.k)))
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of D.k))]
  [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
  (e : ℕ) [SmoothOfRelativeDimension e g] (cg : Compactification g)
  (ch : Compactification (s.map ≫ g))

/-- The second geometric index, with the given map and compactification.
Source: g:Y→Z in the composition statement (blueprint: sk-prop-sp-composition). -/
def spCompositionSecond : SmoothDatum D :=
  { X := s.Y, Y := Z, map := g, dim := e, compactification := cg }

/-- The composite geometric index, retaining any specified compactification of h.
Smooth relative dimensions add. Source: h=gf and m_h=d+e
(blueprint: sk-prop-sp-composition). -/
def spCompositionTotal : SmoothDatum D :=
  { X := s.X, Y := Z, map := s.map ≫ g, dim := s.dim + e, compactification := ch }

/-- The already constructed source compositor. Its Tate coordinates carry their root,
scalar and tensor-power normalization equations. Its derived braiding is the Koszul
braiding, so interchanging the two even shift blocks has sign one.
Source: the displayed source comparison s (blueprint: sk-prop-sp-composition). -/
def spCompositionSourceComponent (p : LinePullCoordinates ell c s.map)
    (K : c.derived ell Z.left) :
    (c.smoothSource ell (s.map ≫ g) (s.dim + e)).obj K ≅
      (c.smoothSource ell s.map s.dim).obj ((c.smoothSource ell g e).obj K) :=
  letI : ∀ x : s.X.left, Invertible (ell : s.X.left.residueField x) :=
    fun x ↦ by
      have hu : IsUnit (ell : s.X.left.residueField x) := by
        simpa only [map_natCast] using
          (primeUnit D ell hEll).map
            ((s.X.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x)
      exact hu.invertible
  sourceComp ell c s.map g s.dim e p K

variable (H : CompactSupportComposition.CoherentData (c.obj.{u} ell) D.k)
  (Rf : ScalarExceptionalAdjoint (c.bundled.{u} ell) s.compactification)
  (Rg : ScalarExceptionalAdjoint (c.bundled.{u} ell) cg)
  (Rh : ScalarExceptionalAdjoint (c.bundled.{u} ell) ch)

set_option maxHeartbeats 1600000 in
-- Comparing the full-subcategory lifts unfolds the three restricted adjunction interfaces.
/-- The precise counit equation fixing the right-adjoint compositor. All arrows here
are the ambient images of the full-subcategory arrows; the inclusion is fully faithful.
The alpha component is exactly the normalized compact-support compositor H.comp.
Source: the first displayed equation (blueprint: sk-prop-sp-composition). -/
def SpCompositionCounit (v : Rh.upper ≅ Rg.upper ⋙ Rf.upper) : Prop :=
  ∀ K : c.ctf ell Z.left,
    (WeilConjectures.PurityWeil.Condensed.supportComposition D H
      (SepFinType.homMk (X := s.X) (Y := s.Y)
        (Over.homMk s.map (comp_over s.map (Spec (.of D.k)))))
      (SepFinType.homMk (X := s.Y) (Y := Z)
        (Over.homMk g (comp_over g (Spec (.of D.k))))) s.compactification cg ch).hom.app
        ((inclusion ell c s.X.left).obj (Rh.upper.obj K)) ≫
      (Rh.restrictedAdjunction.counit.app K).hom =
    (Rg.lower.map (Rf.lower.map (v.hom.app K))).hom ≫
      (Rg.lower.map (Rf.restrictedAdjunction.counit.app (Rg.upper.obj K))).hom ≫
      (Rg.restrictedAdjunction.counit.app K).hom

set_option maxHeartbeats 3200000 in
-- The coefficient-transpose proof unfolds large derived functor expressions.
/-- Composition of the fixed purity maps, with the unique counit-preserving exceptional
compositor and the independently specified source compositor.
Source: latest blueprint sk-prop-sp-composition/_section.md, both displayed equations
(blueprint: sk-prop-sp-composition).

Proof, following the four DAG steps.
1. Compose the exceptional adjunctions (def-weil-pbc-composite-adjunction) and
transport along the support compositor alpha of H (sk-thm-sf-comp-composition): the
conjugate right-adjoint equivalence gives v with the counit equation, and injectivity
of the adjunction Hom equivalence gives its uniqueness (det-sp-unique-right-adjoint).
2. The root-normalized coordinates p are those of def-pur-transport-line-pullback; they
are unique (`lineCoordinates_unique`). Pullback composition, the monoidal tensorator of
derived pullback, tensor-power concatenation and the even Koszul braiding give w
(prop-sfb-module-left-derived-upper-star-comp, lem-sfb-derived-pullback-strong-monoidal,
sk-def-sp-tate-twist, lem-pur-derived-tensor-additive-constraints); its component is
sourceComp, including either dimension zero.
3. The normalized smooth counit equation (*) (def-pur-normalized-composition-trace)
holds for finite and integral coefficients by lem-pur-finite-integral-composition-trace
and for rational and closure coefficients by lem-pur-field-composition-trace-transport.
4. Transpose the two purity composites under the composite adjunction: the counit
equation of v and (*) identify their transposes, so injectivity of the adjunction
Hom bijection gives the stated purity equality in every coefficient case.
-/
theorem smoothPurity_composition :
    ∃ p : LinePullCoordinates ell c s.map,
    ∃ v : Rh.upper ≅ Rg.upper ⋙ Rf.upper,
      SpCompositionCounit ell D c s Z g cg ch H Rf Rg Rh v ∧
      (∀ v' : Rh.upper ≅ Rg.upper ⋙ Rf.upper,
        SpCompositionCounit ell D c s Z g cg ch H Rf Rg Rh v' → v' = v) ∧
      ∃ w : spCompositionSource ell D hEll c (spCompositionTotal D s Z g e ch) ≅
          spCompositionSource ell D hEll c (spCompositionSecond D s Z g e cg) ⋙
            spCompositionSource ell D hEll c s,
        (∀ K : c.ctf ell Z.left,
          (w.hom.app K).hom =
            (spCompositionSourceComponent ell D hEll c s Z g e p K.obj).hom) ∧
        ∀ K : c.ctf ell Z.left,
          (WeilConjectures.PurityWeil.Condensed.canonicalPurity ell D hEll c
            (spCompositionTotal D s Z g e ch) Rh).hom.app K ≫ v.hom.app K =
          w.hom.app K ≫
            (spCompositionSource ell D hEll c s).map
              ((WeilConjectures.PurityWeil.Condensed.canonicalPurity ell D hEll c
                (spCompositionSecond D s Z g e cg) Rg).hom.app K) ≫
            (WeilConjectures.PurityWeil.Condensed.canonicalPurity ell D hEll c s Rf).hom.app
              (Rg.upper.obj K) := by
  classical
  letI : ∀ x : s.X.left, Invertible (ell : s.X.left.residueField x) :=
    fun x ↦ (by
      simpa only [map_natCast] using (primeUnit D ell hEll).map
        ((s.X.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
          IsUnit (ell : s.X.left.residueField x)).invertible
  letI : ∀ x : s.Y.left, Invertible (ell : s.Y.left.residueField x) :=
    fun x ↦ (by
      simpa only [map_natCast] using (primeUnit D ell hEll).map
        ((s.Y.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
          IsUnit (ell : s.Y.left.residueField x)).invertible
  obtain ⟨p⟩ := linePullCoordinates_nonempty ell c s.map
  let alpha : Rf.lower ⋙ Rg.lower ≅ Rh.lower := NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _
      ((WeilConjectures.PurityWeil.Condensed.supportComposition D H
        (SepFinType.homMk (X := s.X) (Y := s.Y)
          (Over.homMk s.map (comp_over s.map (Spec (.of D.k)))))
        (SepFinType.homMk (X := s.Y) (Y := Z)
          (Over.homMk g (comp_over g (Spec (.of D.k)))))
        s.compactification cg ch).app ((inclusion ell c s.X.left).obj M)))
    (fun m ↦ ObjectProperty.hom_ext _
      ((WeilConjectures.PurityWeil.Condensed.supportComposition D H
        (SepFinType.homMk (X := s.X) (Y := s.Y)
          (Over.homMk s.map (comp_over s.map (Spec (.of D.k)))))
        (SepFinType.homMk (X := s.Y) (Y := Z)
          (Over.homMk g (comp_over g (Spec (.of D.k)))))
        s.compactification cg ch).hom.naturality
          ((inclusion ell c s.X.left).map m)))
  obtain ⟨v, hv, hu⟩ := counitComparison Rh.restrictedAdjunction
    (Rf.restrictedAdjunction.comp Rg.restrictedAdjunction) alpha
  have hv' : SpCompositionCounit ell D c s Z g cg ch H Rf Rg Rh v := by
    intro K
    simpa [alpha, Functor.comp_map, Adjunction.comp_counit_app] using
      congrArg (fun t ↦ t.hom) (hv K).symm
  have hu' (v' : Rh.upper ≅ Rg.upper ⋙ Rf.upper)
      (h : SpCompositionCounit ell D c s Z g cg ch H Rf Rg Rh v') : v' = v := by
    apply hu v'
    intro K
    apply ObjectProperty.hom_ext
    simpa [alpha, Functor.comp_map, Adjunction.comp_counit_app] using (h K).symm
  let af := WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c s
  let sg := spCompositionSecond D s Z g e cg
  let sh := spCompositionTotal D s Z g e ch
  let ag := WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c sg
  let ah := WeilConjectures.PurityWeil.Condensed.normalizedFamily ell D hEll c sh
  have htrace : ∃ p : LinePullCoordinates ell c s.map,
      ∀ K : c.ctf ell Z.left,
        alpha.hom.app ((spCompositionSource ell D hEll c sh).obj K) ≫
            ah.adjunction.counit.app K =
          Rg.lower.map (Rf.lower.map (ObjectProperty.homMk
            (spCompositionSourceComponent ell D hEll c s Z g e p K.obj).hom)) ≫
            Rg.lower.map (af.adjunction.counit.app
              ((spCompositionSource ell D hEll c sg).obj K)) ≫
            ag.adjunction.counit.app K := by
    have hi := finiteIntegralCompositionTrace ell D hEll
    have hf := fieldCompositionTraceTransport ell D hEll hi.2.2
    have hc : NormalizedCompositionTrace ell D hEll c :=
      match c with
      | .finite A fin n hA => hi.1 A fin n hA
      | .integers => hi.2.1
      | .integral E => hi.2.2 E
      | .rationals => hf.1
      | .rational E => hf.2.1 E
      | .closure => hf.2.2
    obtain ⟨p, hp⟩ := hc s Z g e cg ch H
    refine ⟨p, ?_⟩
    intro K
    apply ObjectProperty.hom_ext
    exact hp K
  obtain ⟨p', hp⟩ := htrace
  have heq : p' = p := lineCoordinates_unique ell c s.map p' p
  subst p'
  letI := _root_.DerivedCategory.braidedCategory'
    (Mod (Sheaf (ProEt.topology s.X.left) Ab.{u + 1})
      (condensedRingObj (c.obj ell) s.X.left))
  let W := tensorSourceIso
    (actualPull (c.obj ell) s.map) (actualPull (c.obj ell) g)
    (actualPull (c.obj ell) (s.map ≫ g))
    (CondensedRing.leftDerivedUpperStarComp (c.obj ell) s.map g)
    (c.derivedLine ell s.X.left (s.dim + e))
    (c.derivedLine ell s.X.left e) (c.derivedLine ell s.X.left s.dim)
    (c.derivedLine ell s.Y.left e)
    ((derivedProduct ell c s.X.left s.dim e).symm ≪≫ β_ _ _) (p.derived ell e)
  let w : spCompositionSource ell D hEll c sh ≅
      spCompositionSource ell D hEll c sg ⋙ spCompositionSource ell D hEll c s :=
    NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (W.app K.obj))
      (fun m ↦ ObjectProperty.hom_ext _ (W.hom.naturality m.hom))
  have hw (K : c.ctf ell Z.left) : (w.hom.app K).hom =
      (spCompositionSourceComponent ell D hEll c s Z g e p K.obj).hom := by
    exact tensorSourceIso_component _ _ _ _ _ _ _ _ _ _ K.obj
  refine ⟨p, v, hv', hu', w, hw, ?_⟩
  intro K
  have hq : w.hom.app K = ObjectProperty.homMk
      (spCompositionSourceComponent ell D hEll c s Z g e p K.obj).hom := by
    exact ObjectProperty.hom_ext _ (hw K)
  rw [hq]
  exact purityComparison af.adjunction ag.adjunction ah.adjunction
    Rf.restrictedAdjunction Rg.restrictedAdjunction Rh.restrictedAdjunction
    alpha v hv K _ (hp K)

end AlgebraicGeometry.ProEtale.PurityTransport

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

-- Definition owner: def-sf-finite-exceptional-compositor-maps.
public import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalCompositor
import WeilConjectures.AlgebraicGeometry.FiniteCompactSupportCoefficientSquare

/-! # Finite coefficient compatibility of exceptional composition

Source: current blueprint, Verdier exchange, final compatibility sentence, expanded
into the compact-support coefficient square and its two counit transposes
(blueprint: lem-sf-finite-exceptional-compositor-coefficients).

The scalar functors and comparisons below are presentations of the specified derived
extension and proper/open coefficient mates. Their normalization equations retain the
actual maps; no compatibility with geometric composition is assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteExceptionalCompositorCoefficients
open ConstructibleExceptionalCoefficients ConstructibleExceptionalCompositor

attribute [instance] ConstructibleExceptionalCoefficients.Scalar.commShift

/-- The three finite coefficient maps in the statement: a positive quotient, a
possibly ramified finite extension at its retained level en, or that extension
followed by any positive quotient. Equality in the last constructor is equality
of the actual ring-sheaf maps. Source: Verdier exchange, finite coefficient clause
(blueprint: lem-sf-finite-exceptional-compositor-coefficients). -/
inductive FiniteChange (l : ℕ) [Fact l.Prime] :
    {s t : RingStage.{u} l} →
      PurCompactSupport.Change (s.coefficients l) (t.coefficients l) → Prop
  | quotient (E : FieldStage.{u} l) (n m : ℕ+) (h : (m : ℕ) ≤ n) :
      FiniteChange l (s := .finite E n) (t := .finite E m)
        (PurCompactSupport.finiteQuotientChange l E.carrier n m n.pos m.pos h)
  | extension (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (n : ℕ+) :
      FiniteChange l (s := .finite E n)
        (t := .finite L ⟨e * n, Nat.mul_pos e.pos n.pos⟩)
        (PurCompactSupport.finiteChange l E.carrier L.carrier i e he e.pos n n.pos)
  | extensionQuotient (E L : FieldStage.{u} l) (i : E.carrier →ₐ[Padic l] L.carrier)
      (e : ℕ+) (he : PurCompactSupport.Ramification l E.carrier L.carrier i e)
      (n m : ℕ+) (hm : (m : ℕ) ≤ e * n)
      (a : PurCompactSupport.Change ((RingStage.finite E n).coefficients l)
        ((RingStage.finite L m).coefficients l))
      (h : ∀ T : Scheme.{u},
        (PurCompactSupport.finiteChange l E.carrier L.carrier i e he e.pos n n.pos).map T ≫
          (PurCompactSupport.finiteQuotientChange l L.carrier (e * n) m
            (Nat.mul_pos e.pos n.pos) m.pos hm).map T = a.map T) :
      FiniteChange l (s := .finite E n) (t := .finite L m) a

section Formulas
variable {D : FiniteFieldDatum.{u}} (B : D.CoefficientDatum)
  {X Y Z : Scheme.{u}} {s t : Stage.{u} B.l}
  (A : Operation.{u} B.l B.Qbar X Y s) (G : Operation.{u} B.l B.Qbar Y Z s)
  (H : Operation.{u} B.l B.Qbar X Z s)
  (A' : Operation.{u} B.l B.Qbar X Y t) (G' : Operation.{u} B.l B.Qbar Y Z t)
  (H' : Operation.{u} B.l B.Qbar X Z t)
  (TX : C.{u} B.l B.Qbar X s ⥤ C.{u} B.l B.Qbar X t)
  (TY : C.{u} B.l B.Qbar Y s ⥤ C.{u} B.l B.Qbar Y t)
  (TZ : C.{u} B.l B.Qbar Z s ⥤ C.{u} B.l B.Qbar Z t)
  [TX.CommShift ℤ] [TY.CommShift ℤ] [TZ.CommShift ℤ]
  (df : Comparison.{u} B.l B.Qbar A A' TX TY)
  (dg : Comparison.{u} B.l B.Qbar G G' TY TZ)
  (dx : Comparison.{u} B.l B.Qbar H H' TX TZ)
  (alpha : A.F ⋙ G.F ≅ H.F) (alpha' : A'.F ⋙ G'.F ≅ H'.F)

/-- The first side b_x C_X(c_A). Source: finite exceptional composition display
(blueprint: lem-sf-finite-exceptional-compositor-coefficients). -/
def leftMap (L : C.{u} B.l B.Qbar Z s) :
    TX.obj (A.G.obj (G.G.obj L)) ⟶ H'.G.obj (TZ.obj L) :=
  TX.map ((exceptionalIso B A G H alpha).hom.app L) ≫ dx.b.hom.app L

/-- The second side c_B G_f(b_g) b_f. Source: finite exceptional composition display
(blueprint: lem-sf-finite-exceptional-compositor-coefficients). -/
def rightMap (L : C.{u} B.l B.Qbar Z s) :
    TX.obj (A.G.obj (G.G.obj L)) ⟶ H'.G.obj (TZ.obj L) :=
  df.b.hom.app (G.G.obj L) ≫ A'.G.map (dg.b.hom.app L) ≫
    (exceptionalIso B A' G' H' alpha').hom.app (TZ.obj L)

/-- The common transpose: inverse alpha_B, inverse pasted q, then C_Z(beta_A).
The composite adjunction counit is exactly F_g(epsilon_f) followed by epsilon_g.
Source: finite exceptional composition, more precise transpose display
(blueprint: lem-sf-finite-exceptional-compositor-coefficients). -/
def commonTranspose (L : C.{u} B.l B.Qbar Z s) :
    H'.F.obj (TX.obj (A.G.obj (G.G.obj L))) ⟶ TZ.obj L :=
  alpha'.inv.app (TX.obj (A.G.obj (G.G.obj L))) ≫
    G'.F.map (df.q.inv.app (A.G.obj (G.G.obj L))) ≫
    dg.q.inv.app (A.F.obj (A.G.obj (G.G.obj L))) ≫
    TZ.map ((A.adjunction.comp G.adjunction).counit.app L)

/-- The component square and both explicit inverse Hom transposes. Quantification over
all L makes this equality of natural transformations. Source: both displays in the
finite coefficient compositor statement
(blueprint: lem-sf-finite-exceptional-compositor-coefficients). -/
def Compatibility : Prop :=
  ∀ L : C.{u} B.l B.Qbar Z s,
    leftMap B A G H H' TX TZ dx alpha L =
      rightMap B A G A' G' H' TX TY TZ df dg alpha' L ∧
    (H'.adjunction.homEquiv (TX.obj (A.G.obj (G.G.obj L))) (TZ.obj L)).symm
        (leftMap B A G H H' TX TZ dx alpha L) =
      commonTranspose B A G A' G' H' TX TY TZ df dg alpha' L ∧
    (H'.adjunction.homEquiv (TX.obj (A.G.obj (G.G.obj L))) (TZ.obj L)).symm
        (rightMap B A G A' G' H' TX TY TZ df dg alpha' L) =
      commonTranspose B A G A' G' H' TX TY TZ df dg alpha' L

private theorem comparison_counit (L : C.{u} B.l B.Qbar Z s) :
    H'.F.map (dx.b.hom.app L) ≫ H'.adjunction.counit.app (TZ.obj L) =
      dx.q.inv.app (H.G.obj L) ≫ TZ.map (H.adjunction.counit.app L) := by
  rw [← dx.counit L]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

private theorem compositor_counit (L : C.{u} B.l B.Qbar Z s) :
    H.F.map ((exceptionalIso B A G H alpha).hom.app L) ≫ H.adjunction.counit.app L =
      alpha.inv.app (A.G.obj (G.G.obj L)) ≫
        (A.adjunction.comp G.adjunction).counit.app L := by
  simpa only [exceptionalIso, conjugateIsoEquiv_apply_hom, Iso.symm_hom, Functor.comp_obj] using
    conjugateEquiv_counit (A.adjunction.comp G.adjunction) H.adjunction alpha.inv L

private theorem compositor_transpose
    {K : C.{u} B.l B.Qbar X s} (L : C.{u} B.l B.Qbar Z s)
    (v : K ⟶ A.G.obj (G.G.obj L)) :
    (H.adjunction.homEquiv K L).symm
        (v ≫ (exceptionalIso B A G H alpha).hom.app L) =
      alpha.inv.app K ≫ ((A.adjunction.comp G.adjunction).homEquiv K L).symm v := by
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit,
    compositor_counit B A G H alpha L]
  change H.F.map v ≫ alpha.inv.app _ ≫ _ = _
  rw [alpha.inv.naturality_assoc]
  simp only [Adjunction.homEquiv_counit, Functor.comp_map]

private theorem right_transpose (L : C.{u} B.l B.Qbar Z s) :
    (H'.adjunction.homEquiv (TX.obj (A.G.obj (G.G.obj L))) (TZ.obj L)).symm
        (rightMap B A G A' G' H' TX TY TZ df dg alpha' L) =
      commonTranspose B A G A' G' H' TX TY TZ df dg alpha' L := by
  rw [rightMap, ← Category.assoc,
    compositor_transpose B A' G' H' alpha' (TZ.obj L)]
  rw [Adjunction.comp_homEquiv]
  change alpha'.inv.app _ ≫ (G'.adjunction.homEquiv _ _).symm
    ((A'.adjunction.homEquiv _ _).symm
      (df.b.hom.app _ ≫ A'.G.map (dg.b.hom.app L))) = _
  rw [Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm]
  have hf : (A'.adjunction.homEquiv _ _).symm (df.b.hom.app (G.G.obj L)) =
      df.q.inv.app (A.G.obj (G.G.obj L)) ≫
        TY.map (A.adjunction.counit.app (G.G.obj L)) := by
    rw [Adjunction.homEquiv_counit]
    exact comparison_counit B A A' TX TY df (G.G.obj L)
  have hg : (G'.adjunction.homEquiv _ _).symm (dg.b.hom.app L) =
      dg.q.inv.app (G.G.obj L) ≫ TZ.map (G.adjunction.counit.app L) := by
    rw [Adjunction.homEquiv_counit]
    exact comparison_counit B G G' TY TZ dg L
  dsimp only [Functor.comp_obj] at hf hg ⊢
  rw [hf, hg]
  simp only [Functor.map_comp, Category.assoc]
  have hn := dg.q.inv.naturality (A.adjunction.counit.app (G.G.obj L))
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [commonTranspose, ← TZ.map_comp, Adjunction.comp_counit_app]

private theorem left_transpose
    (h : LeftCoefficientEquation B A A' G G' H H' TX TY TZ df.q dg.q dx.q alpha alpha')
    (L : C.{u} B.l B.Qbar Z s) :
    (H'.adjunction.homEquiv (TX.obj (A.G.obj (G.G.obj L))) (TZ.obj L)).symm
        (leftMap B A G H H' TX TZ dx alpha L) =
      commonTranspose B A G A' G' H' TX TY TZ df dg alpha' L := by
  let K := A.G.obj (G.G.obj L)
  have hi := congrArg Iso.inv
    (show TZ.mapIso (alpha.app K) ≪≫ dx.q.app K =
      dg.q.app (A.F.obj K) ≪≫ G'.F.mapIso (df.q.app K) ≪≫ alpha'.app (TX.obj K) from
        Iso.ext (h K))
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at hi
  rw [leftMap, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_counit, comparison_counit B H H' TX TZ dx L]
  have hn := dx.q.inv.naturality ((exceptionalIso B A G H alpha).hom.app L)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  rw [← TZ.map_comp, compositor_counit B A G H alpha L, TZ.map_comp]
  simp only [commonTranspose]
  simpa only [Category.assoc] using congrArg
    (fun v ↦ v ≫ TZ.map ((A.adjunction.comp G.adjunction).counit.app L)) hi

private theorem compatibility_of_left
    (h : LeftCoefficientEquation B A A' G G' H H' TX TY TZ df.q dg.q dx.q alpha alpha') :
    Compatibility B A G H A' G' H' TX TY TZ df dg dx alpha alpha' := by
  intro L
  have hl := left_transpose B A G H A' G' H' TX TY TZ df dg dx alpha alpha' h L
  have hr := right_transpose B A G A' G' H' TX TY TZ df dg alpha' L
  refine ⟨?_, hl, hr⟩
  exact (H'.adjunction.homEquiv _ _).symm.injective (hl.trans hr.symm)

end Formulas

/-- Finite quotient and ramified coefficient changes preserve canonical exceptional
composition, with the displayed common counit transpose. All operations are those of
the recorded constructible systems. Shared scalar presentations and normalized q
presentations merely make the common coefficient functors literal at the three vertices.
Source: current blueprint, Verdier exchange, final compatibility sentence
(blueprint: lem-sf-finite-exceptional-compositor-coefficients).

Proof plan:
1. On the actual finite-Tor pro-etale categories establish the LEFT square
   C_Z(alpha_A) q_x = q_g F_g(q_f) alpha_B. For quotients this is
   lem-sf-compact-coefficient-composition. For retained finite-free extension it is
   lem-coef-finite-free-compact-composition. For extension followed by quotient,
   paste these squares using the tensor associators and the coefficient cocycle of
   lem-sf-constructible-exceptional-adjunction-coefficients. Naturality cancels the
   intermediate factors. The normalization equations below identify precisely these
   canonical maps, not arbitrary isomorphisms. No flat quotient is used.
2. The composite adjunction has counit beta_A = F_g(epsilon_f) epsilon_g, by
   def-weil-pbc-composite-adjunction. Conjugation of inverse alpha_A gives
   F_x(c_A) epsilon_x = alpha_A inverse beta_A, by
   def-weil-pbc-adjunction-conjugate and def-weil-pbc-adjunction-mate. Likewise at B.
3. Transpose leftMap under F_x,B adjoint G_x,B. Its counit normalization and
   naturality of inverse q_x give C_Z(F_x(c_A) epsilon_x) q_x inverse, in mathematical
   composition order. Substitute Step 2 and the inverse of Step 1 to obtain exactly
   commonTranspose.
4. Transpose rightMap. Substitute Step 2 at B and naturality of inverse alpha_B.
   Naturality of epsilon_f,B moves b_g past it. Apply the counit equations first
   for f, then for g. Naturality of inverse q_g at epsilon_f,A leaves inverse
   pasted q followed by C_Z(beta_A). This is the same commonTranspose.
5. The adjunction Hom equivalence is injective, so the maps agree. Every factor is
   natural on the finite-Tor categories; hence component equality is natural equality.
   Positive levels retain the identity quotient, identity scheme maps, zero objects,
   and ramified level en with every subsequent positive quotient.
-/
theorem finiteExceptionalCompositorCoefficients
    {D : FiniteFieldDatum.{u}} (B : D.CoefficientDatum)
    {X Y Z : SixFunctorSpace D}
    [IsSeparated X.obj.hom] [IsSeparated Y.obj.hom] [IsSeparated Z.obj.hom]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (P : System.{u} B.l B.Qbar D B.different (f := f.hom.left))
    (Q : System.{u} B.l B.Qbar D B.different (f := g.hom.left))
    (R : System.{u} B.l B.Qbar D B.different (f := (f ≫ g).hom.left))
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cx : Compactification (f ≫ g).hom.left)
    (E L : FieldStage.{u} B.l) (n m : ℕ+)
    (S : SixFunctorOperationDatum D B E.carrier n n.pos)
    (S' : SixFunctorOperationDatum D B L.carrier m m.pos)
    (a : PurCompactSupport.Change ((RingStage.finite E n).coefficients B.l)
      ((RingStage.finite L m).coefficients B.l))
    (_ha : FiniteChange B.l (s := .finite E n) (t := .finite L m) a)
    (TX : Scalar.{u} B.l B.Qbar a X.obj.left) (TY : Scalar.{u} B.l B.Qbar a Y.obj.left)
    (TZ : Scalar.{u} B.l B.Qbar a Z.obj.left)
    (df : @Comparison.{u} B.l _ B.Qbar _ _ _ X.obj.left Y.obj.left
      (.finite E n) (.finite L m) (P.ring.operation cf (.finite E n))
      (P.ring.operation cf (.finite L m)) TX.functor TY.functor
      TX.commShift TY.commShift)
    (dg : @Comparison.{u} B.l _ B.Qbar _ _ _ Y.obj.left Z.obj.left
      (.finite E n) (.finite L m) (Q.ring.operation cg (.finite E n))
      (Q.ring.operation cg (.finite L m)) TY.functor TZ.functor
      TY.commShift TZ.commShift)
    (dx : @Comparison.{u} B.l _ B.Qbar _ _ _ X.obj.left Z.obj.left
      (.finite E n) (.finite L m) (R.ring.operation cx (.finite E n))
      (R.ring.operation cx (.finite L m)) TX.functor TZ.functor
      TX.commShift TZ.commShift)
    (_hf : QNormalized.{u} B.l B.Qbar cf a TX TY
      (P.ring.left cf (.finite E n)) (P.ring.left cf (.finite L m)) df)
    (_hg : QNormalized.{u} B.l B.Qbar cg a TY TZ
      (Q.ring.left cg (.finite E n)) (Q.ring.left cg (.finite L m)) dg)
    (_hx : QNormalized.{u} B.l B.Qbar cx a TX TZ
      (R.ring.left cx (.finite E n)) (R.ring.left cx (.finite L m)) dx) :
    @Compatibility D B X.obj.left Y.obj.left Z.obj.left (.finite E n) (.finite L m)
      (P.ring.operation cf (.finite E n)) (Q.ring.operation cg (.finite E n))
      (R.ring.operation cx (.finite E n)) (P.ring.operation cf (.finite L m))
      (Q.ring.operation cg (.finite L m)) (R.ring.operation cx (.finite L m))
      TX.functor TY.functor TZ.functor TX.commShift TY.commShift TZ.commShift df dg dx
      (finiteAlpha B f g P Q R E n S cf cg cx)
      (finiteAlpha B f g P Q R L m S' cf cg cx) := by
  have ha : Allowed B.l (s := .finite E n) (t := .finite L m) a := by
    cases _ha with
    | quotient E n m h => exact .quotient E n m h
    | extension E L i e he n => exact .ramified E L i e he n
    | extensionQuotient E L i e he n m hm a h =>
      exact .comp _ _ _ h (.ramified E L i e he n)
        (.quotient L ⟨e * n, Nat.mul_pos e.pos n.pos⟩ m hm)
  apply @compatibility_of_left D B X.obj.left Y.obj.left Z.obj.left
    (.finite E n) (.finite L m)
    (P.ring.operation cf (.finite E n)) (Q.ring.operation cg (.finite E n))
    (R.ring.operation cx (.finite E n)) (P.ring.operation cf (.finite L m))
    (Q.ring.operation cg (.finite L m)) (R.ring.operation cx (.finite L m))
    TX.functor TY.functor TZ.functor TX.commShift TY.commShift TZ.commShift df dg dx
    (finiteAlpha B f g P Q R E n S cf cg cx)
    (finiteAlpha B f g P Q R L m S' cf cg cx)
  exact FiniteCompactSupportCoefficientSquare.finiteCompactSupportCoefficientSquare
    B f g P Q R cf cg cx E L n m S S' a ha TX TY TZ df dg dx _hf _hg _hx

end WeilConjectures.FiniteExceptionalCompositorCoefficients

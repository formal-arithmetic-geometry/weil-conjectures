/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.SystemProjectionFormula.SystemProjectionFormulaMaps
public import WeilConjectures.SixFunctors.FiniteAdjunctionDiagram.FiniteAdjunctionDiagramRealization
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralCompactificationSystemRealization
public import WeilConjectures.Compactification.Triangle
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.CharP.Algebra
import WeilConjectures.SmoothPurity.IntegralSystemRealization.SystemPullbackCompositorEvaluation
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.SystemProperOpenSupport
import WeilConjectures.SmoothPurity.SystemProjectionFormula.SystemProjectionChangeCompatibility
import WeilConjectures.SmoothPurity.SystemProjectionFormula.SystemProjectionTriangleCompatibility

/-! # Projection composition before the total inverse limit

Source: main-20261015, fix-prop-projection-formula.proof.md, the composition and
same-projection-map sentences; Stacks 0F7J and 0B56
(blueprint: lem-pur-system-level-projection-formula-coherence).

The compact-support compositor is the existing graph-refinement word, not a lift
chosen from its finite evaluations. The intrinsic proper/open mate fixes all comparison factors
before evaluation. Level n means exponent n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.IntegralSystemRealization
namespace WeilConjectures.SystemProjectionFormula

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The residue-field prime is a unit by transport of the fixed base-field unit.
This supplies finite tensor APIs without adding an invertibility hypothesis.
Source: finite-field coefficient convention; Stacks 03QO
(blueprint: lem-pur-system-level-projection-formula-coherence). -/
@[instance_reducible] def residueInvertible (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (W : Scheme.{u}) (t : W ⟶ Spec (.of D.k)) (x : W) :
    Invertible (l : W.residueField x) :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  letI : Fact D.p.Prime := ⟨D.prime⟩
  letI : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans (D.card_base.trans D.cardinality_eq))
  letI : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let φ := ((Scheme.ΓSpecIso (.of D.k)).inv ≫ t.appTop ≫ W.Γevaluation x).hom
  (Eq.mp (congrArg IsUnit (map_natCast φ l))
    ((isUnit_iff_ne_zero.mpr
      (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : l.Prime) hl.symm)).map φ)).invertible

/-- Finite inverse-image composition descended from the specified ordinary comparison.
Source: Stacks 03D2, 07A7
(blueprint: lem-pur-system-level-projection-formula-coherence). -/
def finitePullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    finiteDerivedPullback l E n (f ≫ g) ≅
      finiteDerivedPullback l E n g ⋙ finiteDerivedPullback l E n f :=
  sfIntrinsicDerivedPullbackComp (Padic.coefficientExtensionRing l E (n + 1)) f g

/-- The finite projection mate formed from the actual finite counit.
Source: def-exchange-projection; Stacks 0B56
(blueprint: lem-pur-system-level-projection-formula-coherence). -/
def finiteProperProjection (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (tX : X ⟶ Spec (.of D.k)) (tY : Y ⟶ Spec (.of D.k)) (n : ℕ)
    (M : normalizedDVRDerived l E X n) (N : normalizedDVRDerived l E Y n) :=
  letI := residueInvertible l D hl X tX
  letI := residueInvertible l D hl Y tY
  ((finiteAdj l E f n).homEquiv _ _)
    ((canonicalFinitePullbackTensor l E f n
      ((proEtaleConstantDerivedDirectImage f
        (Padic.coefficientExtensionRing l E (n + 1))).obj M) N).hom ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom ((finiteAdj l E f n).counit.app M) (𝟙 _)))

/-- The inverse open tensor map fixed by the actual finite open-adjunction unit.
Source: Stacks 03DI, 0E8I; def-exchange-projection
(blueprint: lem-pur-system-level-projection-formula-coherence). -/
def finiteOpenTensorInv (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (tX : X ⟶ Spec (.of D.k)) (tY : Y ⟶ Spec (.of D.k)) (n : ℕ)
    (M : normalizedDVRDerived l E X n) (N : normalizedDVRDerived l E Y n) :=
  letI := residueInvertible l D hl X tX
  letI := residueInvertible l D hl Y tY
  ((finiteOpenAdj l E j n).homEquiv _ _).symm
    ((finiteIntrinsicDerivedTensor l E X n).map
      (Prod.mkHom ((finiteOpenAdj l E j n).unit.app M) (𝟙 _)) ≫
        (canonicalFinitePullbackTensor l E j n
          (((sfIntrinsicExtensionByZero j
            (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory).obj M) N).inv)

/-- The specified finite compactification projection, proper counit then open tensor
and pullback composition. InverseOnDomain is used only at the invertible open tensor.
Source: def-exchange-projection; Stacks 0B56, 0E8I
(blueprint: lem-pur-system-level-projection-formula-coherence). -/
def finiteProjection (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (tX : X ⟶ Spec (.of D.k)) (tY : Y ⟶ Spec (.of D.k)) (n : ℕ)
    (M : normalizedDVRDerived l E X n) (N : normalizedDVRDerived l E Y n) :=
  finiteProperProjection l E D hl c.g (c.g ≫ tY) tY n
      (((sfIntrinsicExtensionByZero c.i
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory).obj M) N ≫
    (proEtaleConstantDerivedDirectImage c.g
      (Padic.coefficientExtensionRing l E (n + 1))).map
      (inverseOnDomain
        (finiteOpenTensorInv l E D hl c.i tX (c.g ≫ tY) n M
          ((finiteDerivedPullback l E n c.g).obj N))) ≫
    (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
      ((finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom (𝟙 M) (((finitePullComp l E c.i c.g n).symm ≪≫
          eqToIso (congrArg (finiteDerivedPullback l E n) c.comm.symm)).hom.app N)))

/-- The canonical finite evaluation of compact support, in the unchanged intrinsic
module coordinates. Source: Zheng 4.10, Stacks 07A4
(blueprint: lem-pur-system-level-projection-formula-coherence). -/
abbrev evaluateSupport (o : Operations l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) := supportEvaluation l E o c n

private theorem projection_natural_aux (o : Operations l E) (c : Compositors l E o)
    (a : OpenComparisons l E o c)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (d : Compactification f)
    {M M' : System l E X} {N N' : System l E Y} (v : M ⟶ M') (w : N ⟶ N') :
    (calculus l E Y).systemClosed.tensor.map
        (Prod.mkHom ((support l E o d).map v) w) ≫ projection l E o c a d M' N' =
      projection l E o c a d M N ≫
        (support l E o d).map ((calculus l E X).systemClosed.tensor.map
          (Prod.mkHom v ((pull l E f).map w))) := by
  have hpi := (Functor.uncurry.map (properProjection l E o d.g)).naturality
    (Prod.mkHom ((Operations.shriek l E o d.i).map v) w)
  have hd := (a.projection d.i).hom.naturality
    (Prod.mkHom v ((pull l E d.g).map w))
  have hp := ((c.pullComp d.i d.g).inv ≫
    eqToHom (congrArg (pull l E) d.comm.symm)).naturality w
  have hpi' : (calculus l E Y).systemClosed.tensor.map
      (Prod.mkHom ((Operations.push l E o d.g).map
        ((Operations.shriek l E o d.i).map v)) w) ≫
      ((properProjection l E o d.g).app ((Operations.shriek l E o d.i).obj M')).app N' =
    ((properProjection l E o d.g).app ((Operations.shriek l E o d.i).obj M)).app N ≫
      (Operations.push l E o d.g).map ((calculus l E d.Z).systemClosed.tensor.map
        (Prod.mkHom ((Operations.shriek l E o d.i).map v) ((pull l E d.g).map w))) := by
    simpa [Functor.uncurry_obj_map, Functor.curryObj, ← Functor.map_comp] using hpi
  dsimp only [openTensorLeft, openTensorRight, Functor.comp_map, Functor.prod_map,
    Functor.id_map] at hd
  simp only [NatTrans.comp_app, eqToHom_app, Functor.comp_map] at hp
  dsimp only [projection, compactificationProjection, support, Functor.comp_map]
  rw [reassoc_of% hpi']
  simp only [Category.assoc, ← Functor.map_comp]
  congr 1
  apply congrArg (Operations.push l E o d.g).map
  rw [reassoc_of% hd]
  simp only [← Functor.map_comp]
  congr 1
  apply congrArg (Operations.shriek l E o d.i).map
  congr 1
  ext
  · simp
  · exact hp

private theorem inverseOnDomain_eq {C : Type v} [Category.{w} C]
    [HasZeroMorphisms C] {K M : C} (b : K ⟶ M) [IsIso b] :
    inverseOnDomain b = inv b := by
  simp only [inverseOnDomain, dif_pos (inferInstance : IsIso b)]

section EvaluationProofs

attribute [local irreducible] HasDerivedCategory.standard Scheme.residueField
  CategoryTheory.Functor.leftAdjoint

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true

private theorem inverse_square
    {C : Type*} [Category C] [HasZeroMorphisms C] {A B P Q : C}
    (e : A ≅ B) (a : A ⟶ Q) (b : B ⟶ P) (v : P ⟶ Q) [IsIso v]
    (h : e.inv ≫ a = b ≫ v) : e.hom ≫ b = a ≫ inverseOnDomain v := by
  rw [inverseOnDomain_eq]
  apply (asIso v).eq_comp_inv.mpr
  rw [asIso_hom, Category.assoc, ← h, Iso.hom_inv_id_assoc]

private theorem tensor_pair_exchange
    {C D : Type*} [Category C] [Category D] (T : C × C ⥤ D)
    {A A₁ A₂ A₃ B B₁ B₂ : C}
    (a : A ⟶ A₁) (c : A₁ ⟶ A₂) (e : A₂ ⟶ A₃)
    (d : B ⟶ B₁) (f : B₁ ⟶ B₂) :
    T.map (Prod.mkHom a (𝟙 B)) ≫ T.map (Prod.mkHom c d) ≫
      T.map (Prod.mkHom e f) =
    T.map (Prod.mkHom (𝟙 A) (d ≫ f)) ≫
      T.map (Prod.mkHom (a ≫ c ≫ e) (𝟙 B₂)) := by
  simp only [← T.map_comp, prod_comp, Prod.mkHom,
    Category.id_comp, Category.comp_id]

private theorem tensor_right_transport
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (T : C × C ⥤ C) (t : D × D ⥤ D)
    (e : T ⋙ F ≅ (F.prod F) ⋙ t)
    (M : C) {N N' : C} {Q₀ Q : D} (w : N ⟶ N')
    (b : F.obj N' ⟶ Q) (d : F.obj N ⟶ Q₀) (q : Q₀ ⟶ Q)
    (h : F.map w ≫ b = d ≫ q) :
    F.map (T.map (Prod.mkHom (𝟙 M) w)) ≫ e.hom.app (M, N') ≫
      t.map (Prod.mkHom (𝟙 (F.obj M)) b) =
    (e.hom.app (M, N) ≫ t.map (Prod.mkHom (𝟙 (F.obj M)) d)) ≫
      t.map (Prod.mkHom (𝟙 (F.obj M)) q) := by
  have hn := e.hom.naturality (Prod.mkHom (𝟙 M) w)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  erw [reassoc_of% hn, Category.assoc]
  simp only [← t.map_comp, prod_comp, Prod.mkHom,
    Category.comp_id, h]
  erw [F.map_id]

private theorem paste_support_word
    {Xs Zs Ys Xf Zf Yf : Type*}
    [Category Xs] [Category Zs] [Category Ys]
    [Category Xf] [Category Zf] [Category Yf]
    (F : Xs ⥤ Xf) (G : Zs ⥤ Zf) (H : Ys ⥤ Yf)
    (Js : Xs ⥤ Zs) (Rs : Zs ⥤ Ys) (Jf : Xf ⥤ Zf) (Rf : Zf ⥤ Yf)
    (ej : Js ⋙ G ≅ F ⋙ Jf) (er : Rs ⋙ H ≅ G ⋙ Rf)
    {U T : Xs} {V : Zs} {W : Ys} {A B : Xf} {CZ : Zf} {CY L : Yf}
    (pp : W ⟶ Rs.obj V) (dd : V ⟶ Js.obj U) (vv : U ⟶ T)
    (af : F.obj T ⟶ B) (ai : F.obj U ⟶ A) (bb : A ⟶ B)
    (middle : G.obj V ⟶ CZ) (delta : CZ ⟶ Jf.obj A)
    (r1 : H.obj W ⟶ L) (r2 : L ⟶ CY) (pi : CY ⟶ Rf.obj CZ)
    (hp : H.map pp ≫ er.hom.app V ≫ Rf.map middle = r1 ≫ r2 ≫ pi)
    (ho : G.map dd ≫ ej.hom.app U ≫ Jf.map ai = middle ≫ delta)
    (ht : F.map vv ≫ af = ai ≫ bb) :
    H.map (pp ≫ Rs.map (dd ≫ Js.map vv)) ≫
      (er.hom.app (Js.obj T) ≫ Rf.map (ej.hom.app T)) ≫
      (Jf ⋙ Rf).map af =
    r1 ≫ r2 ≫ (pi ≫ Rf.map delta ≫ (Jf ⋙ Rf).map bb) := by
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc]
  have hr := er.hom.naturality dd
  have hr2 := er.hom.naturality (Js.map vv)
  dsimp only [Functor.comp_map] at hr hr2
  have hj := ej.hom.naturality vv
  dsimp only [Functor.comp_map] at hj
  rw [reassoc_of% hr2, reassoc_of% hr]
  rw [← Rf.map_comp_assoc (G.map (Js.map vv)) (ej.hom.app T), hj]
  simp only [Rf.map_comp, Category.assoc]
  rw [← Rf.map_comp (Jf.map (F.map vv)) (Jf.map af),
    ← Jf.map_comp, ht, Jf.map_comp, Rf.map_comp]
  rw [← Rf.map_comp_assoc (G.map dd) (ej.hom.app U),
    ← Rf.map_comp_assoc (G.map dd ≫ ej.hom.app U) (Jf.map ai),
    Category.assoc (G.map dd) (ej.hom.app U) (Jf.map ai), ho]
  simp only [Rf.map_comp, Category.assoc]
  rw [reassoc_of% hp]

private theorem transpose_evaluation
    {C D c d : Type*} [Category C] [Category D] [Category c] [Category d]
    {F : C ⥤ c} {G : D ⥤ d} {L : C ⥤ D} {R : D ⥤ C}
    {Lf : c ⥤ d} {Rf : d ⥤ c} (adj : L ⊣ R) (af : Lf ⊣ Rf)
    (el : L ⋙ G ≅ F ⋙ Lf) (er : R ⋙ F ≅ G ⋙ Rf)
    (hu : ∀ A : C, F.map (adj.unit.app A) ≫ er.hom.app (L.obj A) ≫
      Rf.map (el.hom.app A) = af.unit.app (F.obj A))
    {A : C} {B : D} (h : L.obj A ⟶ B) :
    F.map ((adj.homEquiv _ _) h) ≫ er.hom.app B =
      (af.homEquiv _ _) (el.inv.app A ≫ G.map h) := by
  erw [adj.homEquiv_unit, af.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hn := er.hom.naturality h
  dsimp only [Functor.comp_map] at hn
  erw [hn]
  have he : F.map (adj.unit.app A) ≫ er.hom.app (L.obj A) =
      af.unit.app (F.obj A) ≫ Rf.map (el.inv.app A) := by
    erw [← hu A]
    have hi := (Rf.mapIso (el.app A)).hom_inv_id
    change Rf.map (el.hom.app A) ≫ Rf.map (el.inv.app A) = 𝟙 _ at hi
    simp only [Category.assoc, hi]
    erw [Category.comp_id]
  erw [← Category.assoc, he, Category.assoc]

private theorem proper_mate_evaluation
    {X Y x y : Type*} [Category X] [Category Y] [Category x] [Category y]
    {P : Y ⥤ X} {R : X ⥤ Y} {p : y ⥤ x} {r : x ⥤ y}
    (adj : P ⊣ R) (af : p ⊣ r) (F : X ⥤ x) (G : Y ⥤ y)
    (TX : X × X ⥤ X) (TY : Y × Y ⥤ Y) (tx : x × x ⥤ x) (ty : y × y ⥤ y)
    (ep : P ⋙ F ≅ G ⋙ p) (er : R ⋙ G ≅ F ⋙ r)
    (ex : TX ⋙ F ≅ (F.prod F) ⋙ tx) (ey : TY ⋙ G ≅ (G.prod G) ⋙ ty)
    (mus : TY ⋙ P ≅ (P.prod P) ⋙ TX) (muf : ty ⋙ p ≅ (p.prod p) ⋙ tx)
    (hu : ∀ A : Y, G.map (adj.unit.app A) ≫ er.hom.app (P.obj A) ≫
      r.map (ep.hom.app A) = af.unit.app (G.obj A))
    (hc : ∀ A : X, ep.hom.app (R.obj A) ≫ p.map (er.hom.app A) ≫
      af.counit.app (F.obj A) = F.map (adj.counit.app A))
    (hmu : ∀ A B : Y, F.map (mus.hom.app (A, B)) ≫
      ex.hom.app (P.obj A, P.obj B) ≫
      tx.map (Prod.mkHom (ep.hom.app A) (ep.hom.app B)) =
      ep.hom.app (TY.obj (A, B)) ≫ p.map (ey.hom.app (A, B)) ≫
      muf.hom.app (G.obj A, G.obj B))
    (M : X) (N : Y) (m : x) (em : F.obj M ≅ m)
    (pi : TY.obj (R.obj M, N) ⟶ R.obj (TX.obj (M, P.obj N)))
    (hpi : (adj.homEquiv _ _).symm pi = mus.hom.app (R.obj M, N) ≫
      TX.map (Prod.mkHom (adj.counit.app M) (𝟙 _))) :
    G.map pi ≫ er.hom.app (TX.obj (M, P.obj N)) ≫
      r.map (ex.hom.app (M, P.obj N) ≫ tx.map (Prod.mkHom em.hom (ep.hom.app N))) =
    ey.hom.app (R.obj M, N) ≫
      ty.map (Prod.mkHom (er.hom.app M ≫ r.map em.hom) (𝟙 _)) ≫
      (af.homEquiv _ _) (muf.hom.app (r.obj m, G.obj N) ≫
        tx.map (Prod.mkHom (af.counit.app m) (𝟙 _))) := by
  have hs : pi = (adj.homEquiv _ _)
      (mus.hom.app (R.obj M, N) ≫
        TX.map (Prod.mkHom (adj.counit.app M) (𝟙 _))) :=
    ((adj.homEquiv _ _).apply_symm_apply pi).symm.trans
      (congrArg (adj.homEquiv _ _) hpi)
  erw [hs]
  dsimp only [Functor.id_obj, Functor.comp_obj]
  erw [reassoc_of% (transpose_evaluation adj af ep er hu _)]
  erw [← af.homEquiv_naturality_right]
  simp only [← Category.assoc]
  erw [← af.homEquiv_naturality_left
    (ey.hom.app (R.obj M, N) ≫
      ty.map (Prod.mkHom (er.hom.app M ≫ r.map em.hom) (𝟙 _)))]
  congr 1
  simp only [Functor.map_comp, Category.assoc]
  have hn := ex.hom.naturality
    (Prod.mkHom (adj.counit.app M) (𝟙 (P.obj N)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  erw [reassoc_of% hn]
  have hce : F.map (adj.counit.app M) ≫ em.hom =
      ep.hom.app (R.obj M) ≫ p.map (er.hom.app M ≫ r.map em.hom) ≫
        af.counit.app m := by
    simp only [Functor.map_comp, Category.assoc]
    erw [af.counit_naturality em.hom, ← hc M]
    simp only [Category.assoc]
  have hm : tx.map (Prod.mkHom (F.map (adj.counit.app M)) (F.map (𝟙 (P.obj N)))) ≫
      tx.map (Prod.mkHom em.hom (ep.hom.app N)) =
    tx.map (Prod.mkHom (ep.hom.app (R.obj M)) (ep.hom.app N)) ≫
      tx.map (Prod.mkHom (p.map (er.hom.app M ≫ r.map em.hom)) (𝟙 _)) ≫
        tx.map (Prod.mkHom (af.counit.app m) (𝟙 _)) := by
    simp only [← tx.map_comp]
    congr 1
    ext <;> simp [hce]
  erw [hm, reassoc_of% (hmu (R.obj M) N)]
  erw [reassoc_of% (ep.inv_hom_id_app (TY.obj (R.obj M, N)))]
  have hl := muf.hom.naturality
    (Prod.mkHom (er.hom.app M ≫ r.map em.hom) (𝟙 (G.obj N)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hl
  erw [reassoc_of% hl]
  erw [p.map_id]
  rfl

/-- The bifunctor isomorphism whose components are canonicalFinitePullbackTensor.
This only exposes naturality of the existing specified finite comparison.
Source: Stacks 07A4 (blueprint: lem-pur-system-level-projection-formula-coherence). -/
private def finite_tensor_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    finiteIntrinsicDerivedTensor l E Y n ⋙ finiteDerivedPullback l E n f ≅
      ((finiteDerivedPullback l E n f).prod (finiteDerivedPullback l E n f)) ⋙
        finiteIntrinsicDerivedTensor l E X n := by
  letI addIntrinsic : (sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) f).Additive :=
    sfIntrinsicPullback_additive (finiteCoefficientRing l E (n + 1)) f
  letI limitsIntrinsic :=
    sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) f
  letI colimitsIntrinsic :=
    sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) f
  letI addRinged := proEtaleRingModulePullback_additive f
    (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)
  letI limitsRinged := proEtaleRingModulePullback_preservesFiniteLimits f
    (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)
  letI colimitsRinged := proEtaleRingModulePullback_preservesFiniteColimits f
    (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)
  let e := @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _ _ _
    addRinged addIntrinsic limitsRinged colimitsRinged limitsIntrinsic colimitsIntrinsic
    (pullbackTensorFiniteRealization l E f n)
  exact Functor.isoWhiskerLeft _ e.symm ≪≫
    Functor.isoWhiskerRight (pullbackTensorFiniteModelIso l E Y n).symm _ ≪≫
    proEtaleCanonicalTensorComparison f
      (integralCoefficientCommRingSheaf l E Y n)
      (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)
      (pullbackTensorFiniteModel l E Y n) (pullbackTensorFiniteModel l E X n) ≪≫
    Functor.isoWhiskerLeft _ (pullbackTensorFiniteModelIso l E X n) ≪≫
    Functor.isoWhiskerRight (NatIso.prod e e) _

private theorem finite_tensor_comparison_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : normalizedDVRDerived l E Y n) (N : normalizedDVRDerived l E Y n) :
    (finite_tensor_comparison l E f n).hom.app (M, N) =
      (canonicalFinitePullbackTensor l E f n M N).hom := by
  rfl

private theorem finite_tensor_comparison_inv_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M : normalizedDVRDerived l E Y n) (N : normalizedDVRDerived l E Y n) :
    (finite_tensor_comparison l E f n).inv.app (M, N) =
      (canonicalFinitePullbackTensor l E f n M N).inv := by
  rfl

attribute [local irreducible] canonicalFinitePullbackTensor finite_tensor_comparison
  pullbackTensorDerivedEvaluation pullbackTensorSystemComparison
  CategoryTheory.Functor.mapDerivedCategory

private theorem proper_projection_transpose (o : Operations l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : System l E X) (N : System l E Y) :
    ((o.direct f).adj.homEquiv _ _).symm
        (((properProjection l E o f).app M).app N) =
      (pullbackTensorSystemComparison l E f).hom.app ((Operations.push l E o f).obj M, N) ≫
        (calculus l E X).systemClosed.tensor.map
          (Prod.mkHom ((o.direct f).adj.counit.app M) (𝟙 _)) := by
  simpa [properProjection, Functor.curryObj] using
    (o.direct f).adj.homEquiv_symm_rightAdjointProjectionMap_app_app
      (T_C := Functor.curry.obj (calculus l E X).systemClosed.tensor)
      (T_D := Functor.curry.obj (calculus l E Y).systemClosed.tensor)
      (Functor.curry.mapIso (pullbackTensorSystemComparison l E f) ≪≫
        Functor.curryObjProdComp (pull l E f) (pull l E f)
          (calculus l E X).systemClosed.tensor).hom M N

attribute [local irreducible] properProjection

private theorem proper_projection_evaluation (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (tX : X ⟶ Spec (.of D.k)) (tY : Y ⟶ Spec (.of D.k)) (n : ℕ)
    (M : System l E X) (N : System l E Y)
    (Mₙ : normalizedDVRDerived l E X n)
    (eM : (coefficientSequenceDerivedEvaluation l E X n).obj M ≅ Mₙ) :
    (coefficientSequenceDerivedEvaluation l E Y n).map
        (((properProjection l E o f).app M).app N) ≫
      ((o.evaluation f).evaluation n).hom.app
        ((calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj N)) ≫
      (proEtaleConstantDerivedDirectImage f
        (Padic.coefficientExtensionRing l E (n + 1))).map
        (((calculus l E X).evaluationTensor n).hom.app (M, (pull l E f).obj N) ≫
          (finiteIntrinsicDerivedTensor l E X n).map
            (Prod.mkHom eM.hom ((pullbackTensorDerivedEvaluation l E f n).hom.app N))) =
    ((calculus l E Y).evaluationTensor n).hom.app ((Operations.push l E o f).obj M, N) ≫
      (finiteIntrinsicDerivedTensor l E Y n).map
        (Prod.mkHom ((((o.evaluation f).evaluation n).hom.app M) ≫
          (proEtaleConstantDerivedDirectImage f
            (Padic.coefficientExtensionRing l E (n + 1))).map eM.hom) (𝟙 _)) ≫
      finiteProperProjection l E D hl f tX tY n
        Mₙ ((coefficientSequenceDerivedEvaluation l E Y n).obj N) := by
  let := residueInvertible l D hl X tX
  let := residueInvertible l D hl Y tY
  let EX := coefficientSequenceDerivedEvaluation l E X n
  let EY := coefficientSequenceDerivedEvaluation l E Y n
  let P : normalizedDVRDerived l E Y n ⥤ normalizedDVRDerived l E X n :=
    finiteDerivedPullback l E n f
  let R : normalizedDVRDerived l E X n ⥤ normalizedDVRDerived l E Y n :=
    proEtaleConstantDerivedDirectImage f (Padic.coefficientExtensionRing l E (n + 1))
  let TX := (calculus l E X).systemClosed.tensor
  let tXₙ : normalizedDVRDerived l E X n × normalizedDVRDerived l E X n ⥤
      normalizedDVRDerived l E X n := finiteIntrinsicDerivedTensor l E X n
  let tYₙ : normalizedDVRDerived l E Y n × normalizedDVRDerived l E Y n ⥤
      normalizedDVRDerived l E Y n := finiteIntrinsicDerivedTensor l E Y n
  let ep : pull l E f ⋙ EX ≅ EY ⋙ P := pullbackTensorDerivedEvaluation l E f n
  let er : Operations.push l E o f ⋙ EY ≅ EX ⋙ R := (o.evaluation f).evaluation n
  let ex : TX ⋙ EX ≅ (EX.prod EX) ⋙ tXₙ := (calculus l E X).evaluationTensor n
  let ey : (calculus l E Y).systemClosed.tensor ⋙ EY ≅ (EY.prod EY) ⋙ tYₙ :=
    (calculus l E Y).evaluationTensor n
  let TY := (calculus l E Y).systemClosed.tensor
  have h := proper_mate_evaluation (o.direct f).adj (finiteAdj l E f n)
    EX EY TX TY tXₙ tYₙ ep er ex ey
    (pullbackTensorSystemComparison l E f) (finite_tensor_comparison l E f n)
    ((o.evaluation f).unit n) ((o.evaluation f).counit n)
    (by
      intro A B
      erw [finite_tensor_comparison_app]
      exact pullbackTensorSystemComparison_evaluation l E f n A B)
    M N Mₙ eM (((properProjection l E o f).app M).app N)
    (proper_projection_transpose l E o f M N)
  erw [finite_tensor_comparison_app] at h
  dsimp only [finiteProperProjection]
  exact h

private theorem open_unit_evaluation (o : Operations l E)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) (M : System l E X) :
    (coefficientSequenceDerivedEvaluation l E X n).map
        ((o.extension j).adj.unit.app M) ≫
      (pullbackTensorDerivedEvaluation l E j n).hom.app
        ((Operations.shriek l E o j).obj M) ≫
      (finiteDerivedPullback l E n j).map
        (((o.openEvaluation j).evaluation n).hom.app M) =
    (finiteOpenAdj l E j n).unit.app
      ((coefficientSequenceDerivedEvaluation l E X n).obj M) := by
  have h := unit_mateEquiv_symm (o.extension j).adj (finiteOpenAdj l E j n)
    (TwoSquare.mk _ _ _ _ (pullbackTensorDerivedEvaluation l E j n).hom) M
  change _ = (finiteOpenAdj l E j n).unit.app _ ≫
    (finiteDerivedPullback l E n j).map
      ((((mateEquiv (o.extension j).adj (finiteOpenAdj l E j n)).symm
        (pullbackTensorDerivedEvaluation l E j n).hom)).app M) at h
  erw [(o.openEvaluation j).transpose n] at h
  change (coefficientSequenceDerivedEvaluation l E X n).map
      ((o.extension j).adj.unit.app M) ≫
      (pullbackTensorDerivedEvaluation l E j n).hom.app
        ((Operations.shriek l E o j).obj M) =
    (finiteOpenAdj l E j n).unit.app
      ((coefficientSequenceDerivedEvaluation l E X n).obj M) ≫
      (finiteDerivedPullback l E n j).map
        (((o.openEvaluation j).evaluation n).inv.app M) at h
  erw [reassoc_of% h]
  have hi := ((finiteDerivedPullback l E n j).mapIso
    (((o.openEvaluation j).evaluation n).app M)).inv_hom_id
  change (finiteDerivedPullback l E n j).map
      (((o.openEvaluation j).evaluation n).inv.app M) ≫
      (finiteDerivedPullback l E n j).map
        (((o.openEvaluation j).evaluation n).hom.app M) = 𝟙 _ at hi
  erw [Category.assoc, hi, Category.comp_id]

private theorem open_projection_evaluation (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (o : Operations l E) (c : Compositors l E o) (a : OpenComparisons l E o c)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (tX : X ⟶ Spec (.of D.k)) (tY : Y ⟶ Spec (.of D.k)) (n : ℕ)
    (M : System l E X) (N : System l E Y)
    (Nₙ : normalizedDVRDerived l E Y n)
    (eN : (coefficientSequenceDerivedEvaluation l E Y n).obj N ≅ Nₙ) :
    (coefficientSequenceDerivedEvaluation l E Y n).map
        ((a.projection j).hom.app (M, N)) ≫
      ((o.openEvaluation j).evaluation n).hom.app
        ((calculus l E X).systemClosed.tensor.obj (M, (pull l E j).obj N)) ≫
      (sfIntrinsicExtensionByZero j
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.map
        (((calculus l E X).evaluationTensor n).hom.app (M, (pull l E j).obj N) ≫
          (finiteIntrinsicDerivedTensor l E X n).map
            (Prod.mkHom (𝟙 _) ((pullbackTensorDerivedEvaluation l E j n).hom.app N ≫
              (finiteDerivedPullback l E n j).map eN.hom))) =
    ((calculus l E Y).evaluationTensor n).hom.app ((Operations.shriek l E o j).obj M, N) ≫
      (finiteIntrinsicDerivedTensor l E Y n).map
        (Prod.mkHom (((o.openEvaluation j).evaluation n).hom.app M) eN.hom) ≫
      inverseOnDomain (finiteOpenTensorInv l E D hl j tX tY n
        ((coefficientSequenceDerivedEvaluation l E X n).obj M)
        Nₙ) := by
  let := residueInvertible l D hl X tX
  let := residueInvertible l D hl Y tY
  let EX := coefficientSequenceDerivedEvaluation l E X n
  let EY := coefficientSequenceDerivedEvaluation l E Y n
  let P : normalizedDVRDerived l E Y n ⥤ normalizedDVRDerived l E X n :=
    finiteDerivedPullback l E n j
  let J : normalizedDVRDerived l E X n ⥤ normalizedDVRDerived l E Y n :=
    (sfIntrinsicExtensionByZero j
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory
  let TX := (calculus l E X).systemClosed.tensor
  let TY := (calculus l E Y).systemClosed.tensor
  let tx : normalizedDVRDerived l E X n × normalizedDVRDerived l E X n ⥤
      normalizedDVRDerived l E X n := finiteIntrinsicDerivedTensor l E X n
  let ty : normalizedDVRDerived l E Y n × normalizedDVRDerived l E Y n ⥤
      normalizedDVRDerived l E Y n := finiteIntrinsicDerivedTensor l E Y n
  let ep : pull l E j ⋙ EX ≅ EY ⋙ P := pullbackTensorDerivedEvaluation l E j n
  let ej : Operations.shriek l E o j ⋙ EY ≅ EX ⋙ J := (o.openEvaluation j).evaluation n
  let ex : TX ⋙ EX ≅ (EX.prod EX) ⋙ tx := (calculus l E X).evaluationTensor n
  let ey : TY ⋙ EY ≅ (EY.prod EY) ⋙ ty := (calculus l E Y).evaluationTensor n
  let A := TX.obj (M, (pull l E j).obj N)
  let B := TY.obj ((Operations.shriek l E o j).obj M, N)
  let aa := ex.hom.app (M, (pull l E j).obj N) ≫
    tx.map (Prod.mkHom (𝟙 _) (ep.hom.app N ≫ P.map eN.hom))
  let bb := ey.hom.app ((Operations.shriek l E o j).obj M, N) ≫
    ty.map (Prod.mkHom (ej.hom.app M) eN.hom)
  let v := finiteOpenTensorInv l E D hl j tX tY n (EX.obj M) Nₙ
  have hinv : EY.map ((a.projection j).inv.app (M, N)) ≫ bb =
      ej.hom.app A ≫ J.map aa ≫ v := by
    apply (cancel_epi (ej.inv.app A)).mp
    have hi := ej.inv_hom_id_app A
    erw [reassoc_of% hi]
    apply ((finiteOpenAdj l E j n).homEquiv _ _).injective
    erw [← Category.assoc, (finiteOpenAdj l E j n).homEquiv_naturality_right]
    erw [← transpose_evaluation (o.extension j).adj (finiteOpenAdj l E j n)
      ej ep (open_unit_evaluation l E o j n)]
    erw [(finiteOpenAdj l E j n).homEquiv_naturality_left]
    dsimp only [v, finiteOpenTensorInv]
    erw [Equiv.apply_symm_apply, a.projection_transpose]
    erw [EX.map_comp]
    simp only [Category.assoc]
    dsimp only [bb]
    erw [P.map_comp]
    have hmu : EX.map ((pullbackTensorSystemComparison l E j).inv.app
          ((Operations.shriek l E o j).obj M, N)) ≫ ep.hom.app B ≫
          P.map (ey.hom.app ((Operations.shriek l E o j).obj M, N)) =
        ex.hom.app ((pull l E j).obj ((Operations.shriek l E o j).obj M),
          (pull l E j).obj N) ≫
        tx.map (Prod.mkHom
          (ep.hom.app ((Operations.shriek l E o j).obj M)) (ep.hom.app N)) ≫
        (canonicalFinitePullbackTensor l E j n (EY.obj
          ((Operations.shriek l E o j).obj M)) (EY.obj N)).inv := by
      apply (cancel_epi (EX.map ((pullbackTensorSystemComparison l E j).hom.app
        ((Operations.shriek l E o j).obj M, N)))).mp
      have hcancel := (EX.mapIso ((pullbackTensorSystemComparison l E j).app
        ((Operations.shriek l E o j).obj M, N))).hom_inv_id
      change EX.map ((pullbackTensorSystemComparison l E j).hom.app
          ((Operations.shriek l E o j).obj M, N)) ≫
        EX.map ((pullbackTensorSystemComparison l E j).inv.app
          ((Operations.shriek l E o j).obj M, N)) = 𝟙 _ at hcancel
      erw [← Category.assoc, hcancel, Category.id_comp]
      erw [reassoc_of% (pullbackTensorSystemComparison_evaluation l E j n
        ((Operations.shriek l E o j).obj M) N)]
      repeat erw [Category.assoc]
      erw [(canonicalFinitePullbackTensor l E j n
        (EY.obj ((Operations.shriek l E o j).obj M)) (EY.obj N)).hom_inv_id,
        Category.comp_id]
      rfl
    erw [Category.assoc, reassoc_of% hmu]
    have hn := ex.hom.naturality
      (Prod.mkHom ((o.extension j).adj.unit.app M) (𝟙 ((pull l E j).obj N)))
    dsimp only [Functor.comp_map, Functor.prod_map] at hn
    erw [Category.assoc, reassoc_of% hn]
    have hf := (finite_tensor_comparison l E j n).inv.naturality
      (Prod.mkHom (ej.hom.app M) eN.hom)
    dsimp only [Functor.comp_map, Functor.prod_map] at hf
    simp only [finite_tensor_comparison_inv_app] at hf
    repeat erw [Category.assoc]
    erw [← hf]
    dsimp only [aa]
    erw [EX.map_id]
    erw [reassoc_of% (tensor_pair_exchange tx
      (EX.map ((o.extension j).adj.unit.app M))
      (ep.hom.app ((Operations.shriek l E o j).obj M))
      (P.map (ej.hom.app M)) (ep.hom.app N) (P.map eN.hom))]
    erw [open_unit_evaluation l E o j n M]
    rfl
  let aaIso := ex.app (M, (pull l E j).obj N) ≪≫
    tx.mapIso (Iso.prod (Iso.refl (EX.obj M)) (ep.app N ≪≫ P.mapIso eN))
  let bbIso := ey.app ((Operations.shriek l E o j).obj M, N) ≪≫
    ty.mapIso (Iso.prod (ej.app M) eN)
  have ha : IsIso aa := by
    exact (show IsIso aaIso.hom from inferInstance)
  have hb : IsIso bb := by
    exact (show IsIso bbIso.hom from inferInstance)
  have hd : IsIso (EY.map ((a.projection j).inv.app (M, N))) := by
    exact (show IsIso (EY.mapIso ((a.projection j).app (M, N)).symm).hom from
      inferInstance)
  have : IsIso (ej.hom.app A ≫ J.map aa ≫ v) := by
    rw [← hinv]
    exact IsIso.comp_isIso' hd hb
  have : IsIso (J.map aa ≫ v) := IsIso.of_isIso_comp_left (ej.hom.app A) _
  have hv : IsIso v := IsIso.of_isIso_comp_left (J.map aa) v
  have hforward := @inverse_square _ _ _ _ _ _ _
    (EY.mapIso ((a.projection j).app (M, N)))
    bb (ej.hom.app A ≫ J.map aa) v hv (hinv.trans (Category.assoc _ _ _).symm)
  dsimp only [EX, EY, J, aa, bb, ex, ey, ep, ej, A, TX, TY, P, tx, ty, v] at hforward
  erw [Category.assoc] at hforward
  exact hforward

private theorem pullback_evaluation_congr
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (n : ℕ) (N : System l E Y) :
    (coefficientSequenceDerivedEvaluation l E X n).map
        (eqToHom (congrArg (fun f ↦ (pull l E f).obj N) h)) ≫
      (pullbackTensorDerivedEvaluation l E g n).hom.app N =
    (pullbackTensorDerivedEvaluation l E f n).hom.app N ≫
      (eqToIso (congrArg (finiteDerivedPullback l E n) h)).hom.app
        ((coefficientSequenceDerivedEvaluation l E Y n).obj N) := by
  subst g
  simp only [eqToHom_refl, eqToIso_refl, Iso.refl_hom]
  erw [(coefficientSequenceDerivedEvaluation l E X n).map_id, Category.id_comp]
  exact (Category.comp_id ((pullbackTensorDerivedEvaluation l E f n).hom.app N)).symm

private theorem evaluateSupport_hom_app (o : Operations l E)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (cf : Compactification f) (n : ℕ)
    (M : System l E X) :
    (evaluateSupport l E o cf n).hom.app M =
      ((o.evaluation cf.g).evaluation n).hom.app ((Operations.shriek l E o cf.i).obj M) ≫
        (proEtaleConstantDerivedDirectImage cf.g
          (Padic.coefficientExtensionRing l E (n + 1))).map
          (((o.openEvaluation cf.i).evaluation n).hom.app M) := by
  simp only [evaluateSupport, supportEvaluation, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
  erw [Category.comp_id]
  rfl

end EvaluationProofs

section SupportIsoProofs
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] refinement change triangleWord compositorAlong
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  Compactification.Triangle.ofHasCompactification

end SupportIsoProofs

set_option backward.isDefEq.respectTransparency true in
private theorem paste_compositor_cast
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' : C} {P Q U V : D} (a : A ⟶ B) (b : B ⟶ C')
    (e : F.obj C' ⟶ Q) (d : F.obj B ⟶ P) (r : F.obj A ⟶ U)
    (s : U ⟶ V) (t : V ⟶ P) (u : P ⟶ Q) (q : V ⟶ Q)
    (hb : F.map b ≫ e = d ≫ u) (ha : F.map a ≫ d = r ≫ s ≫ t)
    (hq : q = t ≫ u) : F.map (a ≫ b) ≫ e = r ≫ s ≫ q := by
  calc
    F.map (a ≫ b) ≫ e = F.map a ≫ F.map b ≫ e := F.map_comp_assoc _ _ _
    _ = F.map a ≫ (d ≫ u) := congrArg (fun k ↦ F.map a ≫ k) hb
    _ = (F.map a ≫ d) ≫ u := (Category.assoc _ _ _).symm
    _ = (r ≫ s ≫ t) ≫ u := congrArg (fun k ↦ k ≫ u) ha
    _ = r ≫ s ≫ (t ≫ u) := by simp only [Category.assoc]
    _ = r ≫ s ≫ q := congrArg (fun k ↦ r ≫ s ≫ k) hq.symm

section Geometry
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (o : Operations l E) (z : Realizations l E D o)
  {X Y Z : Scheme.{u}}
  [overX : X.Over (Spec (.of D.k))] [overY : Y.Over (Spec (.of D.k))]
  [overZ : Z.Over (Spec (.of D.k))]
  [sepX : IsSeparated (X ↘ Spec (.of D.k))] [sepY : IsSeparated (Y ↘ Spec (.of D.k))]
  [sepZ : IsSeparated (Z ↘ Spec (.of D.k))]
  [ftX : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [qcX : QuasiCompact (X ↘ Spec (.of D.k))]
  [ftY : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [qcY : QuasiCompact (Y ↘ Spec (.of D.k))]
  [ftZ : LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
  [qcZ : QuasiCompact (Z ↘ Spec (.of D.k))]
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [overF : f.IsOver (Spec (.of D.k))] [overG : g.IsOver (Spec (.of D.k))]
  [sepF : IsSeparated f] [ftF : LocallyOfFiniteType f] [QuasiCompact f]
  [sepG : IsSeparated g] [ftG : LocallyOfFiniteType g] [QuasiCompact g]

section ProjectionEvaluation

attribute [local irreducible] properProjection finiteProperProjection finiteOpenTensorInv
  pullbackTensorDerivedEvaluation pullbackTensorSystemComparison
  canonicalFinitePullbackTensor CategoryTheory.Functor.mapDerivedCategory
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint

set_option backward.isDefEq.respectTransparency true in
set_option backward.defeqAttrib.useBackward true in
set_option linter.unusedSectionVars false in
include D hl overX overY sepX sepY ftX qcX ftY qcY overF sepF ftF in
/-- Evaluation is exactly the specified finite projection, with the fixed tensor,
compact-support and pullback comparisons on its two endpoints.
Source: def-exchange-projection; Zheng 4.10 and Stacks 0B56
(blueprint: lem-pur-system-level-projection-formula-coherence).
Proof: transpose the proper projection using the recorded evaluation-adjunction
unit, identify its tensor comparison by pullbackTensorSystemComparison_evaluation,
and use the recorded counit equation. Transpose the inverse open tensor map by
the open-evaluation mate equation and its unit formula. Its finite inverse is
invertible by transport of the given system open-projection isomorphism.
Naturality of the evaluation tensor comparison and
systemPullbackCompositorEvaluation identify the last pullback compositor and
its equality cast. Paste the proper, open and pullback squares using the
specified compact-support evaluation comparison. The argument works on all
system inputs, retaining the quotient transitions and the specified endpoints. -/
theorem projection_evaluation (cf : Compactification f) (n : ℕ)
    (M : System l E X) (N : System l E Y)
    (_hM : FiniteAdjunctionDiagram.domain l E X M)
    (_hN : FiniteAdjunctionDiagram.domain l E Y N) :
    (coefficientSequenceDerivedEvaluation l E Y n).map
        (projection l E o z.compositors z.openComparisons cf M N) ≫
      (evaluateSupport l E o cf n).hom.app
        ((calculus l E X).systemClosed.tensor.obj (M, (pull l E f).obj N)) ≫
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) cf).map
        (((calculus l E X).evaluationTensor n).hom.app (M, (pull l E f).obj N) ≫
          (finiteIntrinsicDerivedTensor l E X n).map
            (Prod.mkHom (𝟙 _) ((pullbackTensorDerivedEvaluation l E f n).hom.app N))) =
    ((calculus l E Y).evaluationTensor n).hom.app ((support l E o cf).obj M, N) ≫
      (finiteIntrinsicDerivedTensor l E Y n).map
        (Prod.mkHom ((evaluateSupport l E o cf n).hom.app M) (𝟙 _)) ≫
      finiteProjection l E D hl cf (X ↘ Spec (.of D.k)) (Y ↘ Spec (.of D.k)) n
        ((coefficientSequenceDerivedEvaluation l E X n).obj M)
        ((coefficientSequenceDerivedEvaluation l E Y n).obj N) := by
  -- Use one expression for the factored morphism before comparing its pullback functors.
  rcases cf with ⟨W, pg, oi, h, hp, hi⟩
  subst f
  let := hp
  let := hi
  let cf : Compactification (oi ≫ pg) := ⟨W, pg, oi, rfl, hp, hi⟩
  let := residueInvertible l D hl X (X ↘ Spec (.of D.k))
  let := residueInvertible l D hl Y (Y ↘ Spec (.of D.k))
  let := residueInvertible l D hl cf.Z (cf.g ≫ (Y ↘ Spec (.of D.k)))
  let EX := coefficientSequenceDerivedEvaluation l E X n
  let EY := coefficientSequenceDerivedEvaluation l E Y n
  let EZ := coefficientSequenceDerivedEvaluation l E cf.Z n
  let TX := (calculus l E X).systemClosed.tensor
  let tx : normalizedDVRDerived l E X n × normalizedDVRDerived l E X n ⥤
      normalizedDVRDerived l E X n := finiteIntrinsicDerivedTensor l E X n
  let Pi : normalizedDVRDerived l E cf.Z n ⥤ normalizedDVRDerived l E X n :=
    finiteDerivedPullback l E n cf.i
  let J : normalizedDVRDerived l E X n ⥤ normalizedDVRDerived l E cf.Z n :=
    (sfIntrinsicExtensionByZero cf.i
      (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory
  let R : normalizedDVRDerived l E cf.Z n ⥤ normalizedDVRDerived l E Y n :=
    proEtaleConstantDerivedDirectImage cf.g (Padic.coefficientExtensionRing l E (n + 1))
  let ex : TX ⋙ EX ≅ (EX.prod EX) ⋙ tx := (calculus l E X).evaluationTensor n
  let epg := pullbackTensorDerivedEvaluation l E cf.g n
  let epi : pull l E cf.i ⋙ EX ≅ EZ ⋙ Pi :=
    pullbackTensorDerivedEvaluation l E cf.i n
  let epf := pullbackTensorDerivedEvaluation l E (oi ≫ pg) n
  let w := (z.compositors.pullComp cf.i cf.g).inv.app N ≫
    eqToHom (congrArg (fun g : X ⟶ Y ↦ (pull l E g).obj N) cf.comm.symm)
  let v := TX.map (Prod.mkHom (𝟙 M) w)
  let q := ((finitePullComp l E cf.i cf.g n).symm ≪≫
    eqToIso (congrArg (finiteDerivedPullback l E n) cf.comm.symm)).hom.app (EY.obj N)
  have hcomp : EX.map w ≫ epf.hom.app N =
      epi.hom.app ((pull l E cf.g).obj N) ≫ Pi.map (epg.hom.app N) ≫ q := by
    exact paste_compositor_cast EX
      ((z.compositors.pullComp cf.i cf.g).inv.app N)
      (eqToHom (congrArg (fun g : X ⟶ Y ↦ (pull l E g).obj N) cf.comm.symm))
      (epf.hom.app N) ((pullbackTensorDerivedEvaluation l E (cf.i ≫ cf.g) n).hom.app N)
      (epi.hom.app ((pull l E cf.g).obj N)) (Pi.map (epg.hom.app N))
      ((sfIntrinsicDerivedPullbackComp (Padic.coefficientExtensionRing l E (n + 1))
        cf.i cf.g).inv.app (EY.obj N))
      ((eqToIso (congrArg (finiteDerivedPullback l E n) cf.comm.symm)).hom.app (EY.obj N))
      q (pullback_evaluation_congr l E cf.comm.symm n N)
      (systemPullbackCompositorEvaluation l E o z.compositors cf.i cf.g n N) (by rfl)
  have htransport := tensor_right_transport EX TX tx ex M w (epf.hom.app N)
    (epi.hom.app ((pull l E cf.g).obj N) ≫ Pi.map (epg.hom.app N)) q
    (hcomp.trans (Category.assoc _ _ _).symm)
  have hproper := proper_projection_evaluation l E D hl o cf.g
    (cf.g ≫ (Y ↘ Spec (.of D.k))) (Y ↘ Spec (.of D.k)) n
    ((Operations.shriek l E o cf.i).obj M) N (J.obj (EX.obj M))
    (((o.openEvaluation cf.i).evaluation n).app M)
  have hopen := open_projection_evaluation l E D hl o z.compositors z.openComparisons cf.i
    (X ↘ Spec (.of D.k)) (cf.g ≫ (Y ↘ Spec (.of D.k))) n
    M ((pull l E cf.g).obj N) ((finiteDerivedPullback l E n cf.g).obj (EY.obj N))
    (epg.app N)
  let Js := Operations.shriek l E o cf.i
  let Rs := Operations.push l E o cf.g
  let pp : (calculus l E Y).systemClosed.tensor.obj (Rs.obj (Js.obj M), N) ⟶
      Rs.obj ((calculus l E cf.Z).systemClosed.tensor.obj
        (Js.obj M, (pull l E cf.g).obj N)) :=
    ((properProjection l E o cf.g).app (Js.obj M)).app N
  let dd : (calculus l E cf.Z).systemClosed.tensor.obj
      (Js.obj M, (pull l E cf.g).obj N) ⟶
      Js.obj (TX.obj (M, (pull l E cf.i).obj ((pull l E cf.g).obj N))) :=
    (z.openComparisons.projection cf.i).hom.app (M, (pull l E cf.g).obj N)
  have hpaste := paste_support_word EX EZ EY Js Rs J R
    ((o.openEvaluation cf.i).evaluation n) ((o.evaluation cf.g).evaluation n)
    pp dd v
    (ex.hom.app (M, (pull l E (oi ≫ pg)).obj N) ≫
      tx.map (Prod.mkHom (𝟙 _) (epf.hom.app N)))
    (ex.hom.app (M, (pull l E cf.i).obj ((pull l E cf.g).obj N)) ≫
      tx.map (Prod.mkHom (𝟙 _)
        (epi.hom.app ((pull l E cf.g).obj N) ≫ Pi.map (epg.hom.app N))))
    (tx.map (Prod.mkHom (𝟙 _) q))
    _ _ _ _ _ hproper (hopen.trans (Category.assoc _ _ _).symm)
    htransport
  simp only [evaluateSupport_hom_app]
  dsimp only [projection, compactificationProjection, finiteProjection,
    sfAmbientCompactSupportCandidate, Functor.comp_map]
  exact hpaste

end ProjectionEvaluation

-- Retain the geometric parameters of the existing public interface.
set_option linter.unusedSectionVars false in
include D hl overX overY sepX sepY ftX qcX ftY qcY overF sepF ftF in
/-- Joint naturality of the specified projection on the full normalized finite-Tor
constructible domain. Source: main-20261015, fix-prop-projection-formula.proof.md,
same-projection-map sentence; Stacks 0B56
(blueprint: lem-pur-system-level-projection-formula-coherence).
Proof: uncurry the proper projection natural transformation and apply its
naturality to the pair consisting of open extension of v and w. Apply naturality
of the open tensor comparison to v and pullback of w. Finally use naturality
of the inverse pullback compositor followed by the compactification equality
cast. Functoriality of tensor, open extension and proper direct image combines
these three squares. The argument works on all systems and retains the chosen
compactification; no finite-Tor or constructibility closure theorem is needed. -/
theorem projection_natural (c : Compactification f)
    (M M' : System l E X) (N N' : System l E Y)
    (_hM : FiniteAdjunctionDiagram.domain l E X M)
    (_hM' : FiniteAdjunctionDiagram.domain l E X M')
    (_hN : FiniteAdjunctionDiagram.domain l E Y N)
    (_hN' : FiniteAdjunctionDiagram.domain l E Y N')
    (v : M ⟶ M') (w : N ⟶ N') :
    (calculus l E Y).systemClosed.tensor.map
        (Prod.mkHom ((support l E o c).map v) w) ≫
      projection l E o z.compositors z.openComparisons c M' N' =
    projection l E o z.compositors z.openComparisons c M N ≫
      (support l E o c).map ((calculus l E X).systemClosed.tensor.map
        (Prod.mkHom v ((pull l E f).map w))) := by
  exact projection_natural_aux l E o z.compositors z.openComparisons c v w

attribute [local irreducible] projection compactificationProjection change triangleWord
  compositorAlong

include D hl overX overY overZ sepX sepY sepZ ftX qcX ftY qcY ftZ qcZ
  overF overG sepF sepG ftF ftG in
include D hl overX overY overZ sepX sepY sepZ ftX qcX ftY qcY ftZ qcZ
  overF overG sepF sepG ftF ftG in
end Geometry
end WeilConjectures.SystemProjectionFormula

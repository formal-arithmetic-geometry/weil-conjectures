module

public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.ScalarLocalizationCoefficientActions
public import Sheaf.CategoryTheory.ScalarLocalization
public import Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.CategoryTheory.ScalarLocalizationTriangulated
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.StupidTailHomShortExact
import all WeilConjectures.Algebra.Homology.SingleDegreeExactTermHomQuasiIso

/-!
# Localized internal Hom for a bounded source

Source: Stacks Project, Tags 0A8X and 08JC; Derived Categories, Tags 0152,
05R6 and 014A; the finite-tail argument in the proof of perfect dualizability.
(blueprint: lem-sf-localized-bounded-hom-comparison).

The short complexes below use the canonical stupid-filtration inclusion and
projection, and the actual postcomposition maps. The single-term source-shift
isomorphism is normalized on every product component.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.LocalizedBoundedHom

private abbrev Modules {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) :=
  SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

private abbrev Complex {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) := CochainComplex (Modules R) ℤ

-- Use the projection API rather than reducing the chosen bifunctor construction.
attribute [local irreducible] homComplexFunctor homComplexπ

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})

/-- Postcomposition in the ordinary internal Hom complex.
Source: Stacks 0A8X (blueprint: lem-sf-localized-bounded-hom-comparison). -/
def comparison
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    {M N : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ} (f : M ⟶ N) :
    homComplex.{u, u, u, u} (R := R) P M ⟶ homComplex.{u, u, u, u} (R := R) P N :=
  ((homComplexFunctor.{u, u, u, u} (R := R)).obj (op P)).map f

variable
  (P : CochainComplex (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (r : ℤ)
  (V : CochainComplex (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)

/-- Precomposition with the canonical quotient and inclusion has zero composite.
Source: Stacks 08JC (blueprint: lem-sf-localized-bounded-hom-comparison).
Proof: the quotient kills the next stupid tail. Contravariant functoriality
of the Hom complex identifies the composite with precomposition by zero,
which is zero on every product factor. -/
theorem row_zero :
    ((homComplexFunctor.{u, u, u, u} (R := R)).map
      (P.shortComplexStupidFiltrationGE r (r + 1) rfl).g.op).app V ≫
    ((homComplexFunctor.{u, u, u, u} (R := R)).map
      (P.shortComplexStupidFiltrationGE r (r + 1) rfl).f.op).app V = 0 := by
  let F := (homComplexFunctor (R := R)).flip.obj V
  let : F.PreservesZeroMorphisms := homComplex_preservesZero V
  change F.map _ ≫ F.map _ = 0
  rw [← F.map_comp, ← op_comp, ShortComplex.zero, op_zero, F.map_zero]

/-- The canonical Hom row obtained from a stupid-tail source sequence.
Source: Stacks 08JC (blueprint: lem-sf-localized-bounded-hom-comparison). -/
def row : ShortComplex (CochainComplex (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) :=
  ShortComplex.mk
    (((homComplexFunctor.{u, u, u, u} (R := R)).map
      (P.shortComplexStupidFiltrationGE r (r + 1) rfl).g.op).app V)
    (((homComplexFunctor.{u, u, u, u} (R := R)).map
      (P.shortComplexStupidFiltrationGE r (r + 1) rfl).f.op).app V)
    (row_zero R P r V)

/-- The canonical Hom rows are short exact without projective source terms.
Source: Stacks 08JC (blueprint: lem-sf-localized-bounded-hom-comparison).
Proof: in degree q separate the product indexed by source degrees into its
factor at r and the factors at least r+1; factors below r are zero. The
canonical maps are the first-factor inclusion and complementary projection.
They give a splitting in every degree, hence a short exact row of complexes.
The source differentials need not preserve these degreewise splittings. -/
theorem row_shortExact : (row R P r V).ShortExact := by
  let F := (homComplexFunctor (R := R)).flip.obj V
  let : F.PreservesZeroMorphisms := homComplex_preservesZero V
  exact homComplex_degreewise_split
    (P.shortComplexStupidFiltrationGE r (r + 1) rfl)
    (P.shortComplexStupidFiltrationGESplitting r (r + 1) rfl) V

variable {M N : CochainComplex (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ} (f : M ⟶ N)

/-- Postcomposition commutes with both canonical source precompositions.
Source: Stacks 0A8X, 08JC (blueprint: lem-sf-localized-bounded-hom-comparison).
Proof: on each product component both sides are the same composition of
the source map, the component of a homogeneous map, and the component of f.
Associativity gives both equalities, including at the zero source degrees. -/
theorem row_comm :
    comparison R ((P.shortComplexStupidFiltrationGE r (r + 1) rfl).X₃) f ≫
        (row R P r N).f =
      (row R P r M).f ≫
        comparison R ((P.shortComplexStupidFiltrationGE r (r + 1) rfl).X₂) f ∧
    comparison R ((P.shortComplexStupidFiltrationGE r (r + 1) rfl).X₂) f ≫
        (row R P r N).g =
      (row R P r M).g ≫
        comparison R ((P.shortComplexStupidFiltrationGE r (r + 1) rfl).X₁) f := by
  constructor
  · exact (((homComplexFunctor (R := R)).map
      (P.shortComplexStupidFiltrationGE r (r + 1) rfl).g.op).naturality f)
  · exact (((homComplexFunctor (R := R)).map
      (P.shortComplexStupidFiltrationGE r (r + 1) rfl).f.op).naturality f)

/-- The three actual comparisons form a morphism of the canonical Hom rows.
Source: Stacks 08JC (blueprint: lem-sf-localized-bounded-hom-comparison). -/
def rowMap : row R P r M ⟶ row R P r N where
  τ₁ := comparison R ((P.shortComplexStupidFiltrationGE r (r + 1) rfl).X₃) f
  τ₂ := comparison R ((P.shortComplexStupidFiltrationGE r (r + 1) rfl).X₂) f
  τ₃ := comparison R ((P.shortComplexStupidFiltrationGE r (r + 1) rfl).X₁) f
  comm₁₂ := (row_comm R P r f).1
  comm₂₃ := (row_comm R P r f).2

private lemma normalized_projection {B : Type*} [Category* B]
    {A A' D D' E E' : B} (d : A ⟶ A') (p : A ⟶ D) (p' : A' ⟶ D')
    (a : D ⟶ D') (e : D ⟶ E) (e' : D' ⟶ E') (b : E ⟶ E')
    (hd : d ≫ p' = p ≫ a) (he : a ≫ e' = e ≫ b) :
    d ≫ (p' ≫ e') = (p ≫ e) ≫ b := by
  rw [← Category.assoc, hd, Category.assoc, he, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem signed_shift_of_projections
    {B D : Type*} [Category* B] [Preadditive B] [Category* D]
    (H : ℤ → D ⥤ CochainComplex B ℤ) (Y : D → ℤ → B)
    (p : ∀ k W n q, (_h : k + n = q) → (((H k).obj W).X n ⟶ Y W q))
    (hp : ∀ k W n q h, IsIso (p k W n q h))
    (d : ∀ W q q', Y W q ⟶ Y W q')
    (hd : ∀ k W n m q q' (_h : n + 1 = m) (hq : k + n = q) (hq' : k + m = q'),
      ((H k).obj W).d n m ≫ p k W m q' hq' = p k W n q hq ≫ d W q q')
    (b : ∀ {W W'}, (W ⟶ W') → ∀ q, Y W q ⟶ Y W' q)
    (hb : ∀ k {W W'} (g : W ⟶ W') n q h,
      ((H k).map g).f n ≫ p k W' n q h = p k W n q h ≫ b g q) (r : ℤ) :
    ∃ η : ∀ W, ((H 0).obj W)⟦r⟧ ≅ (H r).obj W,
      (∀ W n,
        (CochainComplex.shiftFunctorObjXIso ((H 0).obj W) r n (n + r) rfl).inv ≫
          (η W).hom.f n ≫ p r W n (r + n) rfl =
            (r * n).negOnePow • p 0 W (n + r) (r + n) (by omega)) ∧
      (∀ {W W'} (g : W ⟶ W'),
        (shiftFunctor _ r).map ((H 0).map g) ≫ (η W').hom =
          (η W).hom ≫ (H r).map g) := by
  classical
  have instances (k : ℤ) (W : D) (n q : ℤ) (h : k + n = q) :
      IsIso (p k W n q h) := hp k W n q h
  let := instances
  let e (W : D) (n : ℤ) : ((H 0).obj W).X (n + r) ≅ ((H r).obj W).X n :=
    asIso (p 0 W (n + r) (r + n) (by omega)) ≪≫
      ((r * n).negOnePow • (asIso (p r W n (r + n) rfl)).symm)
  have he (W : D) (n : ℤ) :
      (e W n).hom ≫ p r W n (r + n) rfl =
        (r * n).negOnePow • p 0 W (n + r) (r + n) (by omega) := by
    dsimp only [e, Iso.trans_hom, Preadditive.smul_iso_hom, Iso.symm_hom,
      asIso_hom, asIso_inv]
    simp only [Linear.units_smul_comp, Category.assoc, Linear.comp_units_smul,
      IsIso.inv_hom_id, Category.comp_id]
  have hc (W : D) (n m : ℤ) (hnm : n + 1 = m) :
      (e W n).hom ≫ ((H r).obj W).d n m =
        (((H 0).obj W)⟦r⟧).d n m ≫ (e W m).hom := by
    apply (cancel_mono (p r W m (r + m) rfl)).mp
    rw [Category.assoc, hd r W n m (r + n) (r + m) hnm rfl rfl,
      ← Category.assoc, he]
    conv_rhs => rw [Category.assoc, he]
    dsimp only [CochainComplex.shiftFunctor_obj_d']
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul]
    rw [hd 0 W (n + r) (m + r) (r + n) (r + m) (by omega) (by omega) (by omega)]
    have hs : (r * m).negOnePow * r.negOnePow = (r * n).negOnePow := by
      rw [← Int.negOnePow_add]
      have hh : r * m + r = r * n + r + r := by subst m; ring
      rw [hh, Int.negOnePow_add, Int.negOnePow_add, mul_assoc, Int.units_mul_self, mul_one]
    rw [hs]
  let η (W : D) : ((H 0).obj W)⟦r⟧ ≅ (H r).obj W :=
    HomologicalComplex.Hom.isoOfComponents (e W) (hc W)
  refine ⟨η, ?_, ?_⟩
  · intro W n
    simpa only [η, HomologicalComplex.Hom.isoOfComponents,
      CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv, Category.id_comp] using he W n
  · intro W W' g
    apply HomologicalComplex.hom_ext
    intro n
    apply (cancel_mono (p r W' n (r + n) rfl)).mp
    change (((H 0).map g).f (n + r) ≫ (e W' n).hom) ≫ p r W' n (r + n) rfl =
      ((e W n).hom ≫ ((H r).map g).f n) ≫ p r W' n (r + n) rfl
    rw [Category.assoc, he, Linear.comp_units_smul, hb 0 g (n + r) (r + n) (by omega)]
    rw [Category.assoc, hb r g n (r + n) rfl, ← Category.assoc, he, Linear.units_smul_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem single_source_shift
    {B : Type*} [Category* B] [Preadditive B] [HasZeroObject B]
    (H : B → B → B)
    (map : ∀ {A A' D D' : B}, (A' ⟶ A) → (D ⟶ D') → (H A D ⟶ H A' D'))
    (map_id : ∀ A D, map (𝟙 A) (𝟙 D) = 𝟙 (H A D))
    (map_comp : ∀ {A A' A'' D D' D'' : B}
      (a : A' ⟶ A) (a' : A'' ⟶ A') (b : D ⟶ D') (b' : D' ⟶ D''),
      map a b ≫ map a' b' = map (a' ≫ a) (b ≫ b'))
    (map_zero : ∀ {A A' D : B}, map (0 : A' ⟶ A) (𝟙 D) = 0)
    (F : (CochainComplex B ℤ)ᵒᵖ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (π : ∀ L W : CochainComplex B ℤ, ∀ n p q,
      (_h : p + n = q) → (((F.obj (op L)).obj W).X n ⟶ H (L.X p) (W.X q)))
    (hlim : ∀ L W n, IsLimit (Fan.mk (((F.obj (op L)).obj W).X n)
      (fun p ↦ π L W n p (p + n) rfl)))
    (hd : ∀ L W n m p q q' p' (_hnm : n + 1 = m) (hpq : p + m = q)
      (hq' : p + n = q') (hp' : p' + n = q),
      ((F.obj (op L)).obj W).d n m ≫ π L W m p q hpq =
        π L W n p q' hq' ≫ map (𝟙 (L.X p)) (W.d q' q) -
          n.negOnePow • (π L W n p' q hp' ≫ map (L.d p p') (𝟙 _)))
    (hm : ∀ L {W W'} (g : W ⟶ W') n p q h,
      ((F.obj (op L)).map g).f n ≫ π L W' n p q h =
        π L W n p q h ≫ map (𝟙 (L.X p)) (g.f q))
    (S : ℤ → CochainComplex B ℤ) (X : B) (e : ∀ k, (S k).X k ≅ X)
    (hz : ∀ k p, p ≠ k → IsZero ((S k).X p))
    (hS : ∀ k p p', (S k).d p p' = 0) (r : ℤ) :
    ∃ η : ∀ W, ((F.obj (op (S 0))).obj W)⟦r⟧ ≅ (F.obj (op (S r))).obj W,
      (∀ W n,
        (CochainComplex.shiftFunctorObjXIso ((F.obj (op (S 0))).obj W)
          r n (n + r) rfl).inv ≫ (η W).hom.f n ≫
            π (S r) W n r (r + n) rfl ≫ map (e r).inv (𝟙 _) =
        (r * n).negOnePow •
          (π (S 0) W (n + r) 0 (r + n) (by omega) ≫ map (e 0).inv (𝟙 _))) ∧
      (∀ W W' (g : W ⟶ W'),
        (shiftFunctor _ r).map ((F.obj (op (S 0))).map g) ≫ (η W').hom =
          (η W).hom ≫ (F.obj (op (S r))).map g) := by
  classical
  have comm {A A' D D' : B} (a : A' ⟶ A) (b : D ⟶ D') :
      map (𝟙 A) b ≫ map a (𝟙 D') = map a (𝟙 D) ≫ map (𝟙 A') b := by
    simp only [map_comp, Category.id_comp, Category.comp_id]
  let p k W n q (h : k + n = q) := π (S k) W n k q h ≫ map (e k).inv (𝟙 _)
  have hp k W n q h : IsIso (p k W n q h) := by
    subst q
    have hpπ : IsIso (π (S k) W n k (k + n) rfl) := by
      apply CategoryTheory.fan_projection_isIso (hlim (S k) W n) k
      intro j hj
      rw [IsZero.iff_id_eq_zero, ← map_id]
      rw [(hz k j hj).eq_of_src (𝟙 _) 0, map_zero]
    have hpe : IsIso (map (e k).inv (𝟙 (W.X (k + n)))) := by
      refine ⟨⟨map (e k).hom (𝟙 _), ?_, ?_⟩⟩
      · simp only [map_comp, Category.id_comp, Iso.hom_inv_id, map_id]
      · simp only [map_comp, Category.id_comp, Iso.inv_hom_id, map_id]
    exact inferInstanceAs (IsIso (π (S k) W n k (k + n) rfl ≫ _))
  have hp_d k W n m q q' (h : n + 1 = m) hq hq' :
      ((F.obj (op (S k))).obj W).d n m ≫ p k W m q' hq' =
        p k W n q hq ≫ map (𝟙 X) (W.d q q') := by
    apply normalized_projection
    · simpa only [hS, map_zero, comp_zero, smul_zero, sub_zero] using
        hd (S k) W n m k q' q (k + 1) h hq' hq (by omega)
    · exact comm (e k).inv (W.d q q')
  have hp_m k {W W'} (g : W ⟶ W') n q h :
      ((F.obj (op (S k))).map g).f n ≫ p k W' n q h =
        p k W n q h ≫ map (𝟙 X) (g.f q) := by
    exact normalized_projection _ _ _ _ _ _ _ (hm (S k) g n k q h)
      (comm (e k).inv (g.f q))
  obtain ⟨η, he, hn⟩ := signed_shift_of_projections
    (fun k ↦ F.obj (op (S k))) (fun W q ↦ H X (W.X q)) p hp
    (fun W q q' ↦ map (𝟙 X) (W.d q q')) hp_d
    (fun g q ↦ map (𝟙 X) (g.f q)) hp_m r
  refine ⟨η, ?_, ?_⟩
  · exact he
  · intro W W' g
    exact hn g

/-- The signed single-term source-shift identification, natural in the target.
The degree-q component multiplies by exactly (-1)^(r*q).
Source: Stacks 0A8X (blueprint: lem-sf-localized-bounded-hom-comparison).
Proof: identify the sole nonzero source term in degree r with the degree-zero
source term. The shifted Hom differential has coefficient (-1)^r on target
postcomposition; the Hom from the source in degree r has coefficient one.
Multiplication by s_q=(-1)^(r*q) intertwines them because
s_(q+1)*(-1)^r=s_q. Its square is one, so it is an isomorphism.
Postcomposition by every target chain map commutes with the same sign and
the reindexing, giving a natural isomorphism, for all integer r and q. -/
theorem signed_single_shift
    (X : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    ∃ η : ∀ W : CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ,
      (homComplex.{u, u, u, u} (R := R)
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj X) W)⟦r⟧ ≅
        homComplex.{u, u, u, u} (R := R)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) r).obj X) W,
      (∀ (W : CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (q : ℤ),
        (CochainComplex.shiftFunctorObjXIso
          (homComplex.{u, u, u, u} (R := R)
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj X) W)
          r q (q + r) rfl).inv ≫ (η W).hom.f q ≫
          homComplexπ.{u, u, u, u} (R := R)
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) r).obj X)
            W q r (r + q) rfl ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) r X).inv (𝟙 _) =
        (r * q).negOnePow •
          (homComplexπ.{u, u, u, u} (R := R)
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj X)
            W (q + r) 0 (r + q) (by omega) ≫
          SheafOfModules.homObjMap (R := R)
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv (𝟙 _))) ∧
      (∀ (W W' : CochainComplex (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (g : W ⟶ W'),
        (shiftFunctor _ r).map (comparison R
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj X) g) ≫ (η W').hom =
          (η W).hom ≫ comparison R
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) r).obj X) g) := by
  exact single_source_shift
    (fun A B ↦ SheafOfModules.homObj.{u, u, u, u} (R := R) A B)
    (fun a b ↦ SheafOfModules.homObjMap.{u, u, u, u} (R := R) a b)
    (fun A B ↦ SheafOfModules.homObjMap_id (R := R) (M := A) (N := B))
    (fun a a' b b' ↦ SheafOfModules.homObjMap_comp_homObjMap a a' b b')
    (fun {_ _ _} ↦ homMap_zero) (homComplexFunctor (R := R))
    (homComplexπ (R := R)) (homComplexIsLimit (R := R))
    (homComplex_d_π (R := R))
    (fun L {_ _} g n p q h ↦ homComplexFunctor_obj_map_f_π (L := L) g n p q h)
    (fun k ↦ (HomologicalComplex.single _ (.up ℤ) k).obj X) X
    (fun k ↦ HomologicalComplex.singleObjXSelf (.up ℤ) k X)
    (fun k p hp ↦ HomologicalComplex.isZero_single_obj_X (.up ℤ) k X p hp)
    (fun k p p' ↦ HomologicalComplex.single_obj_d (.up ℤ) k X p p') r

variable [HasDerivedCategory.{w}
  (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]

/-- The induced morphism of canonical distinguished triangles, including its
connecting square. Source: Stacks 0152
(blueprint: lem-sf-localized-bounded-hom-comparison). -/
def triangleMap :
    DerivedCategory.triangleOfSES (row_shortExact R P r M) ⟶
      DerivedCategory.triangleOfSES (row_shortExact R P r N) :=
  DerivedCategory.triangleOfSES.map
    (row_shortExact R P r M) (row_shortExact R P r N) (rowMap R P r f)

/-- Both canonical Hom triangles are distinguished and their connecting square
is the natural square for the three comparisons.
Source: Stacks 0152 (blueprint: lem-sf-localized-bounded-hom-comparison).
Proof: apply the derived-category short-exact-sequence triangle construction
to the two canonical rows and their specified morphism. Its natural connecting
map gives the displayed equality, rather than an unspecified triangle filler. -/
theorem triangles :
    DerivedCategory.triangleOfSES (row_shortExact R P r M) ∈ distTriang _ ∧
    DerivedCategory.triangleOfSES (row_shortExact R P r N) ∈ distTriang _ ∧
    DerivedCategory.triangleOfSESδ (row_shortExact R P r M) ≫
        (DerivedCategory.Q.map (rowMap R P r f).τ₁)⟦(1 : ℤ)⟧' =
      DerivedCategory.Q.map (rowMap R P r f).τ₃ ≫
        DerivedCategory.triangleOfSESδ (row_shortExact R P r N) := by
  exact ⟨DerivedCategory.triangleOfSES_distinguished _,
    DerivedCategory.triangleOfSES_distinguished _,
    DerivedCategory.triangleOfSESδ_naturality _ _ (rowMap R P r f)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem bounded_comparison
    {E : Type*} [Category* E] [Preadditive E] [HasZeroObject E] [HasShift E ℤ]
    [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
    (Q : DerivedCategory (Modules R) ⥤ E)
    [Q.CommShift ℤ] [Q.IsTriangulated]
    (b₀ b₁ : ℤ)
    (hsupport : ∀ n : ℤ, n < b₀ ∨ b₁ < n → IsZero (P.X n))
    (hterms : ∀ n : ℤ, b₀ ≤ n → n ≤ b₁ →
      IsIso ((DerivedCategory.Q ⋙ Q).map (comparison R
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj (P.X n)) f))) :
    IsIso ((DerivedCategory.Q ⋙ Q).map (comparison R P f)) := by
  classical
  let B := Modules R
  let F := (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B) ⋙ Q
  have transport {X Y X' Y' : E}
      (g : X ⟶ Y) (g' : X' ⟶ Y') (i : X ≅ X') (j : Y ≅ Y')
      (h : g ≫ j.hom = i.hom ≫ g') : IsIso g ↔ IsIso g' :=
    Arrow.isIso_iff_isIso_of_isIso (Arrow.isoMk i j h.symm).hom
  have source (L L' : CochainComplex B ℤ) (e : L ≅ L')
      (h : IsIso (F.map (comparison R L' f))) :
      IsIso (F.map (comparison R L f)) := by
    let α := asIso ((homComplexFunctor (R := R)).map e.hom.op)
    exact (transport _ _ (F.mapIso (α.app M)) (F.mapIso (α.app N))
      (by simpa only [Functor.map_comp, Functor.mapIso_hom, α, Iso.app_hom,
          asIso_hom, comparison] using
        (congrArg (fun g ↦ F.map g)
          (((homComplexFunctor (R := R)).map e.hom.op).naturality f)))).mp h
  have zero (L : CochainComplex B ℤ) (hL : IsZero L) :
      IsIso (F.map (comparison R L f)) := by
    have hH (W : CochainComplex B ℤ) : IsZero (homComplex (R := R) L W) := by
      let G := (homComplexFunctor (R := R)).flip.obj W
      let : G.PreservesZeroMorphisms := homComplex_preservesZero W
      exact G.map_isZero hL.op
    have : IsIso (comparison R L f) := (hH M).isIso (hH N) _
    infer_instance
  have single (k : ℤ) (hk₀ : b₀ ≤ k) (hk₁ : k ≤ b₁) :
      IsIso (F.map (comparison R
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) k).obj (P.X k)) f)) := by
    let G := (HomologicalComplex.single B (ComplexShape.up ℤ) 0).obj (P.X k)
    have hG : IsIso (F.map (comparison R G f)) := hterms k hk₀ hk₁
    let := hG
    have hshift : IsIso (F.map ((shiftFunctor _ k).map (comparison R G f))) := by
      exact (transport _ _ ((F.commShiftIso k).app _) ((F.commShiftIso k).app _)
        ((F.commShiftIso k).hom.naturality (comparison R G f))).mpr
          (by change IsIso ((shiftFunctor _ k).map (F.map (comparison R G f)))
              infer_instance)
    obtain ⟨η, _, hη⟩ := signed_single_shift R k (P.X k)
    exact (transport _ _ (F.mapIso (η M)) (F.mapIso (η N))
      (by simpa only [Functor.map_comp, Functor.mapIso_hom, G] using
        (congrArg (fun g ↦ F.map g) (hη M N f)))).mp hshift
  let T (k : ℤ) : CochainComplex B ℤ := P.stupidFiltrationGE.obj (op k)
  have zero_tail (k : ℤ) (hk : b₁ < k) : IsZero (T k) := by
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro n
    have hn : IsZero ((T k).X n) := by
      by_cases hkn : k ≤ n
      · obtain ⟨i, hi⟩ := Int.le.dest hkn
        have he : (ComplexShape.embeddingUpIntGE k).f i = n := by
          simpa using hi
        exact (hsupport n (Or.inr (by omega))).of_iso (P.stupidTruncXIso _ he)
      · exact P.isZero_stupidTrunc_X _ n
          ((ComplexShape.notMem_range_embeddingUpIntGE_iff k n).mpr (by omega))
    exact hn.eq_of_src _ _
  have tails : ∀ k : ℤ, k ≤ b₁ + 1 → b₀ ≤ k →
      IsIso (F.map (comparison R (T k) f)) := by
    apply Int.leInductionDown
    · intro _
      exact zero _ (zero_tail _ (by omega))
    · intro k hk ih hlow
      have hfirst := single (k - 1) hlow (by omega)
      have hthird : IsIso (F.map (comparison R (T ((k - 1) + 1)) f)) := by
        rw [show k - 1 + 1 = k by omega]
        exact ih (by omega)
      let φ := Q.mapTriangle.map (triangleMap R P (k - 1) f)
      exact Pretriangulated.isIso₂_of_isIso₁₃ φ
        (Q.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished _))
        (Q.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished _)) hfirst hthird
  by_cases hbounds : b₀ ≤ b₁ + 1
  · have ht := tails b₀ hbounds le_rfl
    have hι : IsIso (P.ιStupidTrunc (ComplexShape.embeddingUpIntGE b₀)) := by
      have components : ∀ n : ℤ,
          IsIso ((P.ιStupidTrunc (ComplexShape.embeddingUpIntGE b₀)).f n) := by
        intro n
        by_cases hn : b₀ ≤ n
        · obtain ⟨i, hi⟩ := Int.le.dest hn
          exact P.isIso_ιStupidTrunc_f _ (i := i) (by simpa using hi)
        · exact (P.isZero_stupidTrunc_X _ n
            ((ComplexShape.notMem_range_embeddingUpIntGE_iff b₀ n).mpr (by omega))).isIso
            (hsupport n (Or.inl (by omega))) _
      let := components
      exact HomologicalComplex.Hom.isIso_of_components _
    exact source P (T b₀) (asIso (P.ιStupidTrunc _)).symm ht
  · apply zero P
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro n
    exact (hsupport n (by omega)).eq_of_src _ _



variable (A : Type v) [CommRing A]
  (a : A →+* RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) (t : A)

set_option linter.unusedVariables false in
/-- The canonical triangle morphism stays a morphism of distinguished triangles
after scalar localization, with its connecting square commuting. The structural
instances describe any exact triangulated enhancement of the specified scalar
localization, whose existence is supplied by scalar localization triangulatedness.
Source: Stacks 05R6 (blueprint: lem-sf-localized-bounded-hom-comparison).
Proof: apply the exact localization functor to the canonical distinguished
triangles and their canonical morphism. Its commutation with shift identifies
the third square with the displayed equality. Functoriality preserves the
other two squares. The coefficient action is the given A-algebra action. -/
theorem localized_triangles :
    (fun [linearInst : Linear A (DerivedCategory (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))] ↦
      ∀ [HasZeroObject (ScalarLocalization A (DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t)]
        [HasShift (ScalarLocalization A (DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t) ℤ]
        [∀ n : ℤ, (shiftFunctor (ScalarLocalization A (DerivedCategory
          (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t)
            n).Additive]
        [Pretriangulated (ScalarLocalization A (DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t)]
        [(ScalarLocalization.localization A (DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t).CommShift ℤ]
        [(ScalarLocalization.localization A (DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t).IsTriangulated],
      (ScalarLocalization.localization A (DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t).mapTriangle.obj
          (DerivedCategory.triangleOfSES (row_shortExact R P r M)) ∈ distTriang _ ∧
      (ScalarLocalization.localization A (DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t).mapTriangle.obj
          (DerivedCategory.triangleOfSES (row_shortExact R P r N)) ∈ distTriang _ ∧
      ((ScalarLocalization.localization A (DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t).mapTriangle.obj
          (DerivedCategory.triangleOfSES (row_shortExact R P r M))).mor₃ ≫
          ((ScalarLocalization.localization A (DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t).map
            (DerivedCategory.Q.map (rowMap R P r f).τ₁))⟦(1 : ℤ)⟧' =
        (ScalarLocalization.localization A (DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t).map
            (DerivedCategory.Q.map (rowMap R P r f).τ₃) ≫
          ((ScalarLocalization.localization A (DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t).mapTriangle.obj
            (DerivedCategory.triangleOfSES (row_shortExact R P r N))).mor₃)
      (linearInst := scalarLocalizationDerivedLinear A R a) := by
  let := scalarLocalizationDerivedLinear A R a
  intro z s add tri comm exactInst
  let Q := ScalarLocalization.localization A (DerivedCategory (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t
  exact ⟨Q.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished _),
    Q.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished _),
    (Q.mapTriangle.map (triangleMap R P r f)).comm₃⟩

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- Finite-tail devissage of the localized ordinary internal Hom comparison.
Source: Stacks 08JC, 0152, 05R6, 014A and the finite-tail argument for perfect
dualizability (blueprint: lem-sf-localized-bounded-hom-comparison).
Proof: the canonical source sequence for each stupid tail is degreewise split.
Applying Hom into M and N gives the canonical short exact rows and their
postcomposition morphism. The natural short-exact-sequence construction gives
distinguished derived triangles, with the connecting square commuting. Scalar
localization is exact for the canonical A-action, so preserves these triangles
and their morphism. The signed source-shift isomorphism identifies the comparison
for the term in degree r with the r-shift of its degree-zero comparison; its
component in degree q multiplies by (-1)^(r*q), naturally in the target map.
Thus the first comparison of each tail triangle is invertible. Downward induction
from the zero tail in degree b+1, using two-out-of-three for triangle morphisms,
gives invertibility at a, where the tail is P. If b<a all terms of P are zero;
the comparison is then between zero Hom complexes and is invertible. The same
argument includes P=0. No quasi-isomorphism hypothesis on f or projectivity
hypothesis on the terms of P is used. -/
theorem isIso_comparison :
    (fun [linearInst : Linear A (DerivedCategory (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))] ↦
      ∀ (b₀ b₁ : ℤ)
        (hsupport : ∀ n : ℤ, n < b₀ ∨ b₁ < n → IsZero (P.X n))
        (hterms : ∀ n : ℤ, b₀ ≤ n → n ≤ b₁ →
          IsIso ((ScalarLocalization.localization A (DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t).map
            (DerivedCategory.Q.map
            (comparison R ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
              (P.X n)) f)))),
      IsIso ((ScalarLocalization.localization A (DerivedCategory (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))) t).map
        (DerivedCategory.Q.map (comparison R P f))))
      (linearInst := scalarLocalizationDerivedLinear A R a) := by
  classical
  let := scalarLocalizationCoefficientLinear A R a
  let := scalarLocalizationDerivedLinear A R a
  let B := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let D := DerivedCategory B
  obtain ⟨z, hz⟩ := ScalarLocalization.exists_triangulated_scalarLocalization A D t
  let := z
  obtain ⟨s, hs⟩ := hz
  let := s
  obtain ⟨_, add, hadd⟩ := hs
  let := add
  obtain ⟨comm, hcomm⟩ := hadd
  let := comm
  obtain ⟨_, tri, htri⟩ := hcomm
  let := tri
  obtain ⟨_, exactInst, _⟩ := htri
  let := exactInst
  let Q := ScalarLocalization.localization A D t
  intro b₀ b₁ hsupport hterms
  exact bounded_comparison R P f Q b₀ b₁ hsupport hterms

end CategoryTheory.LocalizedBoundedHom

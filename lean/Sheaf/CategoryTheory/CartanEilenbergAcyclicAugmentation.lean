/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.CategoryTheory.GrothendieckComposablePair
public import Sheaf.CategoryTheory.CartanEilenbergPresentation
import Sheaf.CategoryTheory.CartanEilenbergAugmentationQuasiIso
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import Mathlib.Algebra.Homology.TotalComplexSymmetry

/-! # CartanEilenbergAcyclicAugmentation

Source: Stacks Project, Derived Categories, Tags 015N and 015K.
(blueprint: lem-sp-ce-acyclic-augmentation).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private noncomputable def totalAugmentation
    {C : Type uC} [Category.{vC} C] [Abelian C]
    (K : CochainComplex C ℤ)
    (D : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [D.HasTotal (ComplexShape.up ℤ)]
    (b : ∀ n : ℤ, K.X n ⟶ (D.X n).X 0)
    (hz : ∀ n : ℤ, b n ≫ (D.X n).d 0 1 = 0)
    (hc : ∀ i j : ℤ, K.d i j ≫ b j = b i ≫ (D.d i j).f 0) :
    K ⟶ D.total (ComplexShape.up ℤ) where
  f n := b n ≫ D.ιTotal (ComplexShape.up ℤ) n 0 n (add_zero n)
  comm' i j hij := by
    obtain rfl : j = i + 1 := hij.symm
    simp only [HomologicalComplex₂.total_d, Category.assoc, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rw [D.d₁_eq (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)
      0 (i + 1) (add_zero (i + 1)),
      D.d₂_eq (ComplexShape.up ℤ) i
        (show (ComplexShape.up ℤ).Rel 0 1 from rfl) (i + 1) rfl]
    simp only [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (i, 0) = 1 from rfl,
      one_smul, Linear.comp_units_smul, ← Category.assoc,
      hz, zero_comp, smul_zero, add_zero, hc]

private noncomputable def mappedColumnAugmentation
    {B : Type uB} [Category.{vB} B] [Abelian B]
    {C : Type uC} [Category.{vC} C] [Abelian C]
    (G : B ⥤ C) [G.Additive] (K : CochainComplex B ℤ)
    (I : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (e : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I) :
    ((CochainComplex.single₀ C).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      ((G.mapHomologicalComplex (ComplexShape.up ℕ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I :=
  (NatIso.mapHomologicalComplex
      (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).symm
      (ComplexShape.up ℤ)).hom.app K ≫
    ((G.mapHomologicalComplex (ComplexShape.up ℕ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map e

private theorem mappedColumnAugmentation_f_zero
    {B : Type uB} [Category.{vB} B] [Abelian B]
    {C : Type uC} [Category.{vC} C] [Abelian C]
    (G : B ⥤ C) [G.Additive] (K : CochainComplex B ℤ)
    (I : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (e : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I) (n : ℤ) :
    ((mappedColumnAugmentation G K I e).f n).f 0 = G.map ((e.f n).f 0) := by
  dsimp only [mappedColumnAugmentation]
  simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_hom_app_f,
    Iso.symm_hom, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    CochainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv, Category.id_comp]
  change G.map (𝟙 (K.X n)) ≫ G.map ((e.f n).f 0) = _
  rw [G.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
private noncomputable def columnTotalAugmentation
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    (K : CochainComplex C ℤ)
    (I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (e : ((CochainComplex.single₀ C).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I) :
    K ⟶ ((CartanEilenbergPresentation.mappedFunctor (𝟭 C)).obj I).total
      (ComplexShape.up ℤ) := by
  let D := (CartanEilenbergPresentation.mappedFunctor (𝟭 C)).obj I
  let b := fun n : ℤ ↦ (e.f n).f 0 ≫
    (HomologicalComplex.extendXIso (I.X n) ComplexShape.embeddingUpNat
      (i := 0) (i' := 0) rfl).inv
  exact totalAugmentation K D b (by
    intro n
    change ((e.f n).f 0 ≫ _) ≫ ((I.X n).extend ComplexShape.embeddingUpNat).d 0 1 = 0
    rw [HomologicalComplex.extend_d_eq (I.X n) ComplexShape.embeddingUpNat
      (i := 0) (j := 1) (i' := 0) (j' := 1) rfl rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, (e.f n).comm 0 1]
    change (((CochainComplex.single₀ C).obj (K.X n)).d 0 1 ≫ _) ≫ _ = 0
    rw [HomologicalComplex.single_obj_d, zero_comp, zero_comp]) (by
    intro i j
    change K.d i j ≫ ((e.f j).f 0 ≫ _) =
      ((e.f i).f 0 ≫ _) ≫ (HomologicalComplex.extendMap (I.d i j)
        ComplexShape.embeddingUpNat).f 0
    rw [HomologicalComplex.extendMap_f (I.d i j) ComplexShape.embeddingUpNat
      (i := 0) (i' := 0) rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    have h := congrArg (fun f ↦ f.f 0) (e.comm i j)
    simpa only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_obj_d,
      CochainComplex.single₀_map_f_zero, Category.assoc] using h.symm =≫
      (HomologicalComplex.extendXIso (I.X j) ComplexShape.embeddingUpNat
        (i := 0) (i' := 0) rfl).inv)

private theorem columnTotalAugmentation_naturality
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    {K L : CochainComplex C ℤ}
    {I J : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ)}
    (e : ((CochainComplex.single₀ C).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (e' : ((CochainComplex.single₀ C).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      L ⟶ J)
    (β : K ⟶ L) (α : I ⟶ J)
    (h : ∀ n : ℤ, (e.f n).f 0 ≫ (α.f n).f 0 = β.f n ≫ (e'.f n).f 0) :
    β ≫ columnTotalAugmentation L J e' = columnTotalAugmentation K I e ≫
      HomologicalComplex₂.total.map
        ((CartanEilenbergPresentation.mappedFunctor (𝟭 C)).map α) (ComplexShape.up ℤ) := by
  ext n
  dsimp only [columnTotalAugmentation, totalAugmentation, HomologicalComplex.comp_f]
  rw [Category.assoc, Category.assoc, HomologicalComplex₂.ιTotal_map]
  change β.f n ≫ (e'.f n).f 0 ≫ _ =
    ((e.f n).f 0 ≫ _) ≫ (HomologicalComplex.extendMap (α.f n)
      ComplexShape.embeddingUpNat).f 0 ≫ _
  rw [HomologicalComplex.extendMap_f (α.f n) ComplexShape.embeddingUpNat
    (i := 0) (i' := 0) rfl]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (β.f n), ← h, Category.assoc]

private theorem columnTotalAugmentation_quasiIso
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    (K : CochainComplex C ℤ)
    (I : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (e : ((CochainComplex.single₀ C).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (hbelow : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s))
    (hrows : ∀ s : ℤ, QuasiIso (e.f s)) :
    QuasiIso (columnTotalAugmentation K I e) := by
  let D := (CartanEilenbergPresentation.mappedFunctor (𝟭 C)).obj I
  let aug := columnTotalAugmentation K I e ≫ (D.totalFlipIso (ComplexShape.up ℤ)).inv
  have haug (n : ℤ) : aug.f n = (e.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 C).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      D.flip.ιTotal (ComplexShape.up ℤ) 0 n n (zero_add n) := by
    dsimp [aug, columnTotalAugmentation, totalAugmentation]
    rw [Category.assoc, HomologicalComplex₂.ιTotal_totalFlipIso_f_inv]
    simp [ComplexShape.σ]
    rfl
  have hq := Functor.cartanEilenberg_augmentation_quasiIso K I e hbelow hrows aug haug
  have : QuasiIso aug := hq
  exact quasiIso_of_comp_right
    (columnTotalAugmentation K I e) (D.totalFlipIso (ComplexShape.up ℤ)).inv

private theorem mapExtendIso_inv_f
    {B : Type uB} [Category.{vB} B] [Abelian B]
    {C : Type uC} [Category.{vC} C] [Abelian C]
    (G : B ⥤ C) [G.Additive] (K : CochainComplex B ℕ) (n : ℕ) :
    (K.mapExtendIso ComplexShape.embeddingUpNat G).inv.f (n : ℤ) =
      (HomologicalComplex.extendXIso
        ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
        ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom ≫
      G.map (K.extendXIso ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).inv := by
  simp only [HomologicalComplex.mapExtendIso, HomologicalComplex.Hom.isoOfComponents_inv_f,
    HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso.hom, eqToIso.inv,
    eqToHom_map, eqToHom_trans]
  rw [HomologicalComplex.mapExtendX_hom_eq K G
    (ComplexShape.embeddingUpNat.r_eq_some (i := n) (i' := (n : ℤ)) rfl)]
  rfl

/-- The common augmentation into vertical-degree-zero total summands is natural
and a quasi-isomorphism under the injective acyclicity assumption. Its prescribed
components determine the map uniquely: in negative degrees the source is zero.
Source: Stacks Project, Derived Categories, Tags 015N and 015K.
(blueprint: lem-sp-ce-acyclic-augmentation).

Proof: In nonnegative degree n take the component displayed below, inserting the
mapped common augmentation into the (n,0) total summand. In negative degrees use
the unique map from the zero source. The horizontal differential equation is the
bicomplex augmentation square; the vertical differential kills the augmentation,
so the signed vertical total differential contributes zero. The comparison square
follows degreewise from comm_e and functoriality of extension and total inclusions;
negative source terms are zero. Each column resolves F(J^p) with injective terms.
Since J^p is injective, applying G gives zero positive column cohomology and
degree-zero cohomology GF(J^p), compatibly with the augmentation. Filter the cone
of the augmentation by horizontal degree. The resulting column complexes are
acyclic. The double complex has first-quadrant support, making the filtration
finite in every total degree. The column spectral sequence therefore has zero
abutment. The augmentation cone is acyclic, which is exactly that a is a
quasi-isomorphism. This argument includes degree zero and zero objects. -/
theorem exists_cartanEilenberg_acyclic_augmentation
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
    {C : Type uC} [Category.{vC} C] [Abelian C] [IsGrothendieckAbelian.{vC} C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (hFG : (⟨F, G⟩ : GrothendieckComposablePair A B C).SendsInjectivesToAcyclics) :
    ∃ a : ∀ P : CartanEilenbergPresentation F,
        (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex).extend
          ComplexShape.embeddingUpNat ⟶ P.total G,
      (∀ P : CartanEilenbergPresentation F, (∀ n : ℕ, (a P).f (n : ℤ) =
            (HomologicalComplex.extendXIso
              (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).obj P.J.cocomplex)
              ComplexShape.embeddingUpNat (rfl : (n : ℤ) = n)).hom ≫
            G.map (F.map (P.J.cocomplex.extendXIso ComplexShape.embeddingUpNat
              (rfl : (n : ℤ) = n)).inv ≫ (P.e.f (n : ℤ)).f 0) ≫
            (HomologicalComplex.extendXIso
              ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj (P.I.X (n : ℤ)))
              ComplexShape.embeddingUpNat (rfl : (0 : ℤ) = 0)).inv ≫
            HomologicalComplex₂.ιTotalOrZero
              ((CartanEilenbergPresentation.mappedFunctor G).obj P.I)
              (ComplexShape.up ℤ) (n : ℤ) 0 (n : ℤ))) ∧
      (∀ P : CartanEilenbergPresentation F, QuasiIso (a P)) ∧
      (∀ (P Q : CartanEilenbergPresentation F) (c : P.Comparison Q),
        HomologicalComplex.extendMap
            (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).map c.β)
            ComplexShape.embeddingUpNat ≫ a Q =
          a P ≫ HomologicalComplex₂.total.map
            ((CartanEilenbergPresentation.mappedFunctor G).map c.α)
            (ComplexShape.up ℤ)) := by
  let K := fun P : CartanEilenbergPresentation F ↦
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (P.J.cocomplex.extend ComplexShape.embeddingUpNat)
  let L := fun P : CartanEilenbergPresentation F ↦
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (K P)
  let I := fun P : CartanEilenbergPresentation F ↦
    ((G.mapHomologicalComplex (ComplexShape.up ℕ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P.I
  let e := fun P : CartanEilenbergPresentation F ↦
    mappedColumnAugmentation G (K P) P.I P.e
  let b := fun P : CartanEilenbergPresentation F ↦
    columnTotalAugmentation (L P) (I P) (e P)
  let t := fun P : CartanEilenbergPresentation F ↦
    P.J.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (F ⋙ G)
  let a := fun P : CartanEilenbergPresentation F ↦ (t P).inv ≫ b P
  refine ⟨a, ?_, ?_, ?_⟩
  · intro P n
    dsimp only [a, b, t, columnTotalAugmentation, totalAugmentation, e,
      HomologicalComplex.comp_f]
    rw [mappedColumnAugmentation_f_zero, mapExtendIso_inv_f]
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
    rw [HomologicalComplex₂.ιTotalOrZero_eq
      ((CartanEilenbergPresentation.mappedFunctor G).obj P.I)
      (ComplexShape.up ℤ) (n : ℤ) 0 (n : ℤ) (add_zero (n : ℤ))]
    rfl
  · intro P
    have hcol (s : ℤ) : QuasiIso ((e P).f s) := by
      have : QuasiIso (P.e.f s) := P.column_quasiIso s
      have hK (q : ℕ) : G.rightAcyclic
          (((((CochainComplex.single₀ B).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (K P)).X s).X q) := by
        by_cases hq : q = 0
        · subst q
          change G.rightAcyclic (F.obj
            ((P.J.cocomplex.extend ComplexShape.embeddingUpNat).X s))
          have : Injective ((P.J.cocomplex.extend ComplexShape.embeddingUpNat).X s) :=
            inferInstance
          exact fun q ↦ hFG _ (q + 1) (by omega)
        · exact G.rightAcyclic.prop_of_isZero
            (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
              ((K P).X s) q hq)
      have hI (q : ℕ) : G.rightAcyclic ((P.I.X s).X q) := by
        have : Injective ((P.I.X s).X q) := P.term_injective s q
        exact Functor.rightAcyclic_of_injective _
      have := G.quasiIso_map_of_rightAcyclic_nat (P.e.f s) hK hI
      change QuasiIso
        ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.app
          ((K P).X s) ≫ (G.mapHomologicalComplex (ComplexShape.up ℕ)).map (P.e.f s))
      infer_instance
    have hb : QuasiIso (b P) := columnTotalAugmentation_quasiIso (L P) (I P) (e P)
      ⟨0, fun s hs ↦ (G.mapHomologicalComplex (ComplexShape.up ℕ)).map_isZero
        (P.zero_neg s hs)⟩ hcol
    exact quasiIso_comp (t P).inv (b P)
  · intro P Q c
    let β := ((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap c.β ComplexShape.embeddingUpNat)
    let α := ((G.mapHomologicalComplex (ComplexShape.up ℕ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map c.α
    have hb : β ≫ b Q = b P ≫ HomologicalComplex₂.total.map
        ((CartanEilenbergPresentation.mappedFunctor G).map c.α) (ComplexShape.up ℤ) := by
      apply columnTotalAugmentation_naturality (e P) (e Q) β α
      intro n
      dsimp only [e]
      rw [mappedColumnAugmentation_f_zero, mappedColumnAugmentation_f_zero]
      change G.map ((P.e.f n).f 0) ≫ G.map ((c.α.f n).f 0) =
        G.map (F.map ((HomologicalComplex.extendMap c.β
          ComplexShape.embeddingUpNat).f n)) ≫ G.map ((Q.e.f n).f 0)
      rw [← G.map_comp, ← G.map_comp]
      exact congrArg G.map (c.comm_e n)
    have ht : (t P).hom ≫ HomologicalComplex.extendMap
        (((F ⋙ G).mapHomologicalComplex (ComplexShape.up ℕ)).map c.β)
        ComplexShape.embeddingUpNat = β ≫ (t Q).hom := by
      ext n
      exact (HomologicalComplex.mapExtensIso_hom_f_naturality c.β
        ComplexShape.embeddingUpNat (F ⋙ G) n).symm
    apply (cancel_epi (t P).hom).mp
    dsimp only [a]
    simp only [Category.assoc]
    rw [← Category.assoc (t P).hom, ht]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hb


end CategoryTheory

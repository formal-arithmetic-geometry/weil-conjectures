/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Adjunction.Parametrized
public import Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.Algebra.Homology.BifunctorHomComplex
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # External Hom-complex currying with the row differential

Source: Stacks, More on Algebra, Tag 0A5Y (Lemma compose), with the external
parametrized-adjunction generalization and row convention of the DAG statement.
(blueprint: lem-sf-kflat-bifunctor-chain-currying)
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CochainComplex

open HomComplex

section Construction

variable {A : Type u} [Category.{v} A] [Abelian A]
  {F : A ⥤ A ⥤ A} {H : Aᵒᵖ ⥤ A ⥤ A}
  [∀ X : A, (F.obj X).Additive] (adj : F ⊣₂ H)

private noncomputable def untranspose (X Y Z : A) :
    (Y ⟶ (H.obj (op X)).obj Z) ≃+ ((F.obj X).obj Y ⟶ Z) :=
  ((adj.adj X).homAddEquiv Y Z).symm

private lemma untranspose_units (X Y Z : A) (e : ℤˣ)
    (a : Y ⟶ (H.obj (op X)).obj Z) :
    untranspose adj X Y Z (e • a) = e • untranspose adj X Y Z a := by
  simp only [Units.smul_def, map_zsmul]

private lemma untranspose_one {X X' Y Z : A} (g : X' ⟶ X)
    (a : Y ⟶ (H.obj (op X)).obj Z) :
    untranspose adj X' Y Z (a ≫ (H.map g.op).app Z) =
      (F.map g).app Y ≫ untranspose adj X Y Z a :=
  adj.homEquiv_symm_naturality_one g a

private lemma untranspose_two {X Y Y' Z : A} (f : Y' ⟶ Y)
    (a : Y ⟶ (H.obj (op X)).obj Z) :
    untranspose adj X Y' Z (f ≫ a) =
      (F.obj X).map f ≫ untranspose adj X Y Z a :=
  adj.homEquiv_symm_naturality_two f a

private lemma untranspose_three {X Y Z Z' : A} (t : Z ⟶ Z')
    (a : Y ⟶ (H.obj (op X)).obj Z) :
    untranspose adj X Y Z' (a ≫ (H.obj (op X)).map t) =
      untranspose adj X Y Z a ≫ t :=
  adj.homEquiv_symm_naturality_three t a

variable [HasCountableProducts A] [HasCountableCoproducts A]
  [F.Additive] [H.Additive] [∀ X : Aᵒᵖ, (H.obj X).Additive]

private noncomputable def curryTo (K L M : CochainComplex A ℤ) (r : ℤ) :
    Cochain K (bifunctorHomObj H L M) r →+
      Cochain (HomologicalComplex.mapBifunctor K L F.flip (.up ℤ)) M r where
  toFun α := Cochain.mk fun n t hnt ↦ HomologicalComplex.mapBifunctorDesc
    (fun p q hn ↦ (q * (p + r)).negOnePow •
      untranspose adj (L.X q) (K.X p) (M.X t)
        (α.v p (p + r) rfl ≫ bifunctorHomπ H L M (p + r) q t (by
          change p + q = n at hn
          omega)))
  map_zero' := by
    apply Cochain.ext
    intro n t hnt
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hn
    change p + q = n at hn
    simp
  map_add' α α' := by
    apply Cochain.ext
    intro n t hnt
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hn
    change p + q = n at hn
    simp [Preadditive.add_comp, smul_add]

private lemma curryTo_ι (K L M : CochainComplex A ℤ) (r : ℤ)
    (α : Cochain K (bifunctorHomObj H L M) r)
    (p q s n t : ℤ) (hp : p + r = s) (hn : p + q = n)
    (ht : q + s = t) (hnt : n + r = t) :
    HomologicalComplex.ιMapBifunctor K L F.flip (.up ℤ) p q n hn ≫
        (curryTo adj K L M r α).v n t hnt =
      (q * s).negOnePow • untranspose adj (L.X q) (K.X p) (M.X t)
        (α.v p s hp ≫ bifunctorHomπ H L M s q t ht) := by
  subst s
  simp only [curryTo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Cochain.mk_v,
    HomologicalComplex.ι_mapBifunctorDesc]

private noncomputable def curryFrom (K L M : CochainComplex A ℤ) (r : ℤ)
    (β : Cochain (HomologicalComplex.mapBifunctor K L F.flip (.up ℤ)) M r) :
    Cochain K (bifunctorHomObj H L M) r :=
  Cochain.mk fun p s hp ↦ bifunctorHomLift H L M s fun q t ht ↦
    (untranspose adj (L.X q) (K.X p) (M.X t)).symm
      ((q * s).negOnePow •
        (HomologicalComplex.ιMapBifunctor K L F.flip (.up ℤ) p q (p + q) rfl ≫
          β.v (p + q) t (by omega)))

private lemma curryFrom_π (K L M : CochainComplex A ℤ) (r : ℤ)
    (β : Cochain (HomologicalComplex.mapBifunctor K L F.flip (.up ℤ)) M r)
    (p q s n t : ℤ) (hp : p + r = s) (hn : p + q = n)
    (ht : q + s = t) (hnt : n + r = t) :
    (curryFrom adj K L M r β).v p s hp ≫ bifunctorHomπ H L M s q t ht =
      (untranspose adj (L.X q) (K.X p) (M.X t)).symm
        ((q * s).negOnePow •
          (HomologicalComplex.ιMapBifunctor K L F.flip (.up ℤ) p q n hn ≫
            β.v n t hnt)) := by
  subst n
  simp only [curryFrom, Cochain.mk_v, bifunctorHomLift_π]

private noncomputable def curryEquiv (K L M : CochainComplex A ℤ) (r : ℤ) :
    Cochain K (bifunctorHomObj H L M) r ≃+
      Cochain (HomologicalComplex.mapBifunctor K L F.flip (.up ℤ)) M r where
  toFun := curryTo adj K L M r
  invFun := curryFrom adj K L M r
  left_inv α := by
    apply Cochain.ext
    intro p s hp
    apply bifunctorHomObj_hom_ext
    intro q t ht
    rw [curryFrom_π adj K L M r _ p q s (p + q) t hp rfl ht (by omega),
      curryTo_ι adj K L M r α p q s (p + q) t hp rfl ht (by omega), smul_smul,
      Int.units_mul_self, one_smul, AddEquiv.symm_apply_apply]
  right_inv β := by
    apply Cochain.ext
    intro n t hnt
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hn
    change p + q = n at hn
    rw [curryTo_ι adj K L M r _ p q (p + r) n t rfl hn (by omega) hnt,
      curryFrom_π adj K L M r β p q (p + r) n t rfl hn (by omega) hnt,
      AddEquiv.apply_symm_apply, smul_smul, Int.units_mul_self, one_smul]
  map_add' := (curryTo adj K L M r).map_add

omit [HasCountableProducts A] in
private lemma total_d (K L : CochainComplex A ℤ) (p q n n' : ℤ)
    (hn : p + q = n) (hn' : n + 1 = n') :
    HomologicalComplex.ιMapBifunctor K L F.flip (.up ℤ) p q n hn ≫
        (HomologicalComplex.mapBifunctor K L F.flip (.up ℤ)).d n n' =
      (F.obj (L.X q)).map (K.d p (p + 1)) ≫
          HomologicalComplex.ιMapBifunctor K L F.flip (.up ℤ) (p + 1) q n' (by
            change p + 1 + q = n'; omega) +
        p.negOnePow • ((F.map (L.d q (q + 1))).app (K.X p) ≫
          HomologicalComplex.ιMapBifunctor K L F.flip (.up ℤ) p (q + 1) n' (by
            change p + (q + 1) = n'; omega)) := by
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq (i₁' := p + 1) _ _ _ _ (by simp) q n' (by
      change p + 1 + q = n'; omega),
    HomologicalComplex.mapBifunctor.d₂_eq (i₂' := q + 1) _ _ _ _ p (by simp) n' (by
      change p + (q + 1) = n'; omega)]
  change (1 : ℤˣ) • _ + p.negOnePow • _ = _
  simp only [one_smul, Functor.flip_map_app, Functor.flip_obj_map]

private lemma curryTo_delta (K L M : CochainComplex A ℤ) (r : ℤ)
    (α : Cochain K (bifunctorHomObj H L M) r) :
    curryTo adj K L M (r + 1) (δ r (r + 1) α) =
      δ r (r + 1) (curryTo adj K L M r α) := by
  apply Cochain.ext
  intro n t hnt
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hn
  change p + q = n at hn
  rw [curryTo_ι adj K L M (r + 1) _ p q (p + (r + 1)) n t rfl hn (by omega) hnt,
    δ_v r (r + 1) rfl α p (p + (r + 1)) rfl (p + r) (p + 1) (by omega) rfl,
    δ_v r (r + 1) rfl _ n t hnt (t - 1) (n + 1) rfl rfl]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc]
  rw [bifunctorHomObj_d_π H L M (p + r) (p + (r + 1)) q t (by omega)
    (t - 1) (q + 1) (by omega) (by omega)]
  rw [reassoc_of% (total_d (F := F) K L p q n (n + 1) hn rfl)]
  simp only [Preadditive.comp_sub, Preadditive.add_comp,
    Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
    map_add, map_sub, untranspose_units, smul_add, smul_sub, smul_smul]
  simp only [← Category.assoc]
  rw [untranspose_three, untranspose_one]
  simp only [Category.assoc]
  rw [untranspose_two adj (K.d p (p + 1))
    (α.v (p + 1) (p + (r + 1)) (by omega) ≫
      bifunctorHomπ H L M (p + (r + 1)) q t (by omega))]
  rw [reassoc_of% (curryTo_ι adj K L M r α p q (p + r) n (t - 1) rfl hn
      (by omega) (by omega)),
    curryTo_ι adj K L M r α (p + 1) q (p + (r + 1)) (n + 1) t (by omega) (by omega)
      (by omega) (by omega),
    curryTo_ι adj K L M r α p (q + 1) (p + r) (n + 1) t rfl (by omega)
      (by omega) (by omega)]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul, smul_smul,
    ← Int.negOnePow_add]
  have hM : (q * (p + (r + 1)) + q).negOnePow = (q * (p + r)).negOnePow := by
    exact (Int.negOnePow_eq_iff _ _).2 ⟨q, by ring⟩
  have hK : (q * (p + (r + 1)) + (r + 1)).negOnePow =
      (r + 1 + q * (p + (r + 1))).negOnePow := by congr 1; ring
  have hL : (r + 1 + p + (q + 1) * (p + r)).negOnePow =
      -(q * (p + r)).negOnePow := by
    rw [← Int.negOnePow_succ]
    exact (Int.negOnePow_eq_iff _ _).2 ⟨p + r, by ring⟩
  rw [hM, hK, hL]
  simp only [Units.neg_smul]
  abel

private noncomputable def curryIso (K L M : CochainComplex A ℤ) :
    HomComplex K (bifunctorHomObj H L M) ≅
      HomComplex (HomologicalComplex.mapBifunctor K L F.flip (.up ℤ)) M :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r ↦ (curryEquiv adj K L M r).toAddCommGrpIso) (by
      intro r r' hrr'
      obtain rfl : r' = r + 1 := hrr'.symm
      apply ConcreteCategory.hom_ext
      intro α
      exact (curryTo_delta adj K L M r α).symm)

private lemma curryIso_hom_apply (K L M : CochainComplex A ℤ) (r : ℤ)
    (α : Cochain K (bifunctorHomObj H L M) r) :
    ((curryIso adj K L M).hom.f r) α = curryTo adj K L M r α := rfl

private lemma curryIso_inv_apply (K L M : CochainComplex A ℤ) (r : ℤ)
    (β : Cochain (HomologicalComplex.mapBifunctor K L F.flip (.up ℤ)) M r) :
    ((curryIso adj K L M).inv.f r) β = curryFrom adj K L M r β := rfl

private lemma curryTo_naturality
    (K K' L L' M M' : CochainComplex A ℤ)
    (f : K' ⟶ K) (g : L' ⟶ L) (t : M ⟶ M') (r : ℤ)
    (α : Cochain K (bifunctorHomObj H L M) r) :
    curryTo adj K' L' M' r
        ((Cochain.ofHom f).comp
          (α.comp (Cochain.ofHom
            (bifunctorHomMapLeft g ≫ bifunctorHomMapRight t)) (add_zero r))
          (zero_add r)) =
      ((Cochain.ofHom
        (HomologicalComplex.mapBifunctorMap f g F.flip (.up ℤ))).comp
          (curryTo adj K L M r α) (zero_add r)).comp
        (Cochain.ofHom t) (add_zero r) := by
  apply Cochain.ext
  intro n b hnb
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hn
  change p + q = n at hn
  rw [curryTo_ι adj K' L' M' r _ p q (p + r) n b rfl hn (by omega) hnb]
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    HomologicalComplex.comp_f, Category.assoc, bifunctorHomMapRight_f_π,
    bifunctorHomMapLeft_f_π_assoc]
  rw [untranspose_two]
  simp only [← Category.assoc]
  rw [untranspose_three, untranspose_one]
  simp only [HomologicalComplex.ι_mapBifunctorMap, Category.assoc]
  rw [reassoc_of% (curryTo_ι adj K L M r α p q (p + r) n b rfl hn (by omega) hnb)]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul,
    Functor.flip_map_app, Functor.flip_obj_map]

omit [HasCountableProducts A] [HasCountableCoproducts A] in
private lemma zero_cocycle_iff (X Y : CochainComplex A ℤ) (z : Cochain X Y 0) :
    δ 0 1 z = 0 ↔ ∃ f : X ⟶ Y, Cochain.ofHom f = z := by
  constructor
  · intro hz
    exact ⟨Cocycle.homOf (Cocycle.mk z 1 rfl hz), by simp⟩
  · rintro ⟨f, rfl⟩
    exact δ_ofHom f

omit [HasCountableProducts A] [HasCountableCoproducts A] in
private lemma homotopy_iff (X Y : CochainComplex A ℤ) (u v : X ⟶ Y)
    (h : Cochain X Y (-1)) :
    δ (-1) 0 h = Cochain.ofHom u - Cochain.ofHom v ↔
      ∀ p : ℤ, h.v p (p - 1) (sub_eq_add_neg p 1).symm ≫ Y.d (p - 1) p +
        X.d p (p + 1) ≫ h.v (p + 1) p (by omega) = u.f p - v.f p := by
  constructor
  · intro hh p
    simpa only [δ_v (-1) 0 (by omega) h p p (add_zero p) (p - 1) (p + 1) rfl rfl,
      Int.negOnePow_zero, one_smul, Cochain.sub_v, Cochain.ofHom_v]
      using Cochain.congr_v hh p p (add_zero p)
  · intro hh
    apply Cochain.ext₀
    intro p
    simpa only [δ_v (-1) 0 (by omega) h p p (add_zero p) (p - 1) (p + 1) rfl rfl,
      Int.negOnePow_zero, one_smul, Cochain.sub_v, Cochain.ofHom_v] using hh p

omit [HasCountableProducts A] [HasCountableCoproducts A] in
private lemma preserves_homotopy {X Y X' Y' : CochainComplex A ℤ}
    (φ : HomComplex X Y ⟶ HomComplex X' Y')
    (u v : Cochain X Y 0) (h : Cochain X Y (-1))
    (hh : δ (-1) 0 h = u - v) :
    δ (-1) 0 ((φ.f (-1)) h) = (φ.f 0) u - (φ.f 0) v := by
  have he := ConcreteCategory.congr_hom (φ.comm (-1) 0) h
  change δ (-1) 0 ((φ.f (-1)) h) = (φ.f 0) (δ (-1) 0 h) at he
  rw [he, hh]
  exact map_sub (φ.f 0).hom u v

end Construction

/-- Signed external currying for arbitrary integer cochain complexes.

Source: Stacks, More on Algebra, Tag 0A5Y (Lemma compose); the external
parametrized-adjunction generalization uses the row convention of
`bifunctorHomObj` and the left-first total of `F.flip`.
(blueprint: lem-sf-kflat-bifunctor-chain-currying)

Proof: (1) Use the inverse adjunction transpose, expressed by the counit; it is
additive and natural in all three variables. (2) The product projections give
the row differential; its square vanishes by the two complex identities and
naturality of H. (3) The coproduct inclusions give the total differential; its
mixed terms cancel with coefficients (-1)^(p+1) and (-1)^p. (4) The external
Hom differential squares to zero by bilinearity and the complex identities.
(5) Apply the inverse transpose componentwise with sign (-1)^(q*(p+r)); use
the coproduct universal property. The inverse transposes the same signed
components and assembles them by the product universal property. These are
inverse additive maps since the square of the sign is one; the component
formula also gives uniqueness. (6) After inverse transpose, the three terms
of the source differential are (-1)^q*(x-y)-(-1)^r*z, where x is the target
differential term, y the L differential term and z the K differential term.
(7) On the total side the coefficients are e(p,q,r), -(-1)^r*e(p+1,q,r),
and -(-1)^(r+p)*e(p,q+1,r). The parity identities in the node identify these
with the coefficients from step 6 multiplied by e(p,q,r+1). Thus E commutes
with differentials. (8) Invert this identity to obtain the inverse chain
identity. (9) Transpose naturality and the universal properties prove the
simultaneous contravariant naturality in K,L and covariance in M; invertibility
also gives inverse naturality. (10) In degree zero the cocycle equation is
exactly the chain-map equation; in degree minus one the coboundary equation is
the degreewise homotopy equation. Apply the chain identity and additivity to
transport that equation in both directions. -/
theorem exists_bifunctorChainCurrying
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasCountableProducts A] [HasCountableCoproducts A]
    (F : A ⥤ A ⥤ A) (H : Aᵒᵖ ⥤ A ⥤ A)
    [F.Additive] [∀ X : A, (F.obj X).Additive]
    [H.Additive] [∀ X : Aᵒᵖ, (H.obj X).Additive]
    (adj : F ⊣₂ H) :
    ∃ E : ∀ K L M : CochainComplex A ℤ,
      HomComplex K (bifunctorHomObj H L M) ≅
        HomComplex (HomologicalComplex.mapBifunctor K L F.flip (.up ℤ)) M,
      (∀ (K L M : CochainComplex A ℤ) (r : ℤ)
        (α : Cochain K (bifunctorHomObj H L M) r)
        (p q s n t : ℤ) (hp : p + r = s) (hn : p + q = n)
        (ht : q + s = t) (hnt : n + r = t),
        HomologicalComplex.ιMapBifunctor K L F.flip (.up ℤ) p q n hn ≫
          (((E K L M).hom.f r) α).v n t hnt =
        (q * s).negOnePow •
          ((F.obj (L.X q)).map (α.v p s hp ≫ bifunctorHomπ H L M s q t ht) ≫
            (adj.adj (L.X q)).counit.app (M.X t))) ∧
      (∀ (K L M : CochainComplex A ℤ) (r : ℤ)
        (β : Cochain (HomologicalComplex.mapBifunctor K L F.flip (.up ℤ)) M r)
        (p q s n t : ℤ) (hp : p + r = s) (hn : p + q = n)
        (ht : q + s = t) (hnt : n + r = t),
        (((E K L M).inv.f r) β).v p s hp ≫ bifunctorHomπ H L M s q t ht =
          (adj.adj (L.X q)).homEquiv (K.X p) (M.X t)
            ((q * s).negOnePow •
              (HomologicalComplex.ιMapBifunctor K L F.flip (.up ℤ) p q n hn ≫
                β.v n t hnt))) ∧
      (∀ E' : ∀ K L M : CochainComplex A ℤ,
          HomComplex K (bifunctorHomObj H L M) ≅
            HomComplex (HomologicalComplex.mapBifunctor K L F.flip (.up ℤ)) M,
        (∀ (K L M : CochainComplex A ℤ) (r : ℤ)
        (α : Cochain K (bifunctorHomObj H L M) r)
        (p q s n t : ℤ) (hp : p + r = s) (hn : p + q = n)
        (ht : q + s = t) (hnt : n + r = t),
        HomologicalComplex.ιMapBifunctor K L F.flip (.up ℤ) p q n hn ≫
          (((E' K L M).hom.f r) α).v n t hnt =
        (q * s).negOnePow •
          ((F.obj (L.X q)).map (α.v p s hp ≫ bifunctorHomπ H L M s q t ht) ≫
            (adj.adj (L.X q)).counit.app (M.X t))) → E' = E) ∧
      (∀ (K K' L L' M M' : CochainComplex A ℤ)
        (f : K' ⟶ K) (g : L' ⟶ L) (t : M ⟶ M') (r : ℤ)
        (α : Cochain K (bifunctorHomObj H L M) r),
        ((E K' L' M').hom.f r)
            ((Cochain.ofHom f).comp
              (α.comp (Cochain.ofHom
                (bifunctorHomMapLeft g ≫ bifunctorHomMapRight t)) (add_zero r))
              (zero_add r)) =
          ((Cochain.ofHom
            (HomologicalComplex.mapBifunctorMap f g F.flip (.up ℤ))).comp
              (((E K L M).hom.f r) α) (zero_add r)).comp
            (Cochain.ofHom t) (add_zero r)) ∧
      (∀ (K L M : CochainComplex A ℤ) (z : Cochain K (bifunctorHomObj H L M) 0),
        δ 0 1 z = 0 ↔ ∃ f : K ⟶ (bifunctorHomObj H L M), Cochain.ofHom f = z) ∧
      (∀ (K L M : CochainComplex A ℤ)
        (z : Cochain (HomologicalComplex.mapBifunctor K L F.flip (.up ℤ)) M 0),
        δ 0 1 z = 0 ↔
          ∃ f : HomologicalComplex.mapBifunctor K L F.flip (.up ℤ) ⟶ M,
            Cochain.ofHom f = z) ∧
      (∀ (K L M : CochainComplex A ℤ)
        (u v : K ⟶ bifunctorHomObj H L M)
        (h : Cochain K (bifunctorHomObj H L M) (-1)),
        (δ (-1) 0 h = Cochain.ofHom u - Cochain.ofHom v ↔
          ∀ p : ℤ, h.v p (p - 1) (sub_eq_add_neg p 1).symm ≫
              (bifunctorHomObj H L M).d (p - 1) p +
            K.d p (p + 1) ≫ h.v (p + 1) p (by omega) = u.f p - v.f p)) ∧
      (∀ (K L M : CochainComplex A ℤ)
        (u v : HomologicalComplex.mapBifunctor K L F.flip (.up ℤ) ⟶ M)
        (h : Cochain (HomologicalComplex.mapBifunctor K L F.flip (.up ℤ)) M (-1)),
        (δ (-1) 0 h = Cochain.ofHom u - Cochain.ofHom v ↔
          ∀ p : ℤ, h.v p (p - 1) (sub_eq_add_neg p 1).symm ≫ M.d (p - 1) p +
            (HomologicalComplex.mapBifunctor K L F.flip (.up ℤ)).d p (p + 1) ≫
              h.v (p + 1) p (by omega) = u.f p - v.f p)) ∧
      (∀ (K L M : CochainComplex A ℤ)
        (u v : Cochain K (bifunctorHomObj H L M) 0)
        (h : Cochain K (bifunctorHomObj H L M) (-1)),
        δ 0 1 u = 0 → δ 0 1 v = 0 → δ (-1) 0 h = u - v →
        δ (-1) 0 (((E K L M).hom.f (-1)) h) =
          ((E K L M).hom.f 0) u - ((E K L M).hom.f 0) v) ∧
      (∀ (K L M : CochainComplex A ℤ)
        (u v : Cochain (HomologicalComplex.mapBifunctor K L F.flip (.up ℤ)) M 0)
        (h : Cochain (HomologicalComplex.mapBifunctor K L F.flip (.up ℤ)) M (-1)),
        δ 0 1 u = 0 → δ 0 1 v = 0 → δ (-1) 0 h = u - v →
        δ (-1) 0 (((E K L M).inv.f (-1)) h) =
          ((E K L M).inv.f 0) u - ((E K L M).inv.f 0) v) := by
  refine ⟨fun K L M ↦ curryIso adj K L M, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro K L M r α p q s n t hp hn ht hnt
    rw [curryIso_hom_apply, curryTo_ι adj K L M r α p q s n t hp hn ht hnt]
    rfl
  · intro K L M r β p q s n t hp hn ht hnt
    rw [curryIso_inv_apply, curryFrom_π adj K L M r β p q s n t hp hn ht hnt]
    rfl
  · intro E' hE'
    funext K L M
    apply Iso.ext
    apply HomologicalComplex.hom_ext
    intro r
    apply ConcreteCategory.hom_ext
    intro α
    apply Cochain.ext
    intro n t hnt
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hn
    change p + q = n at hn
    rw [hE' K L M r α p q (p + r) n t rfl hn (by omega) hnt,
      curryIso_hom_apply, curryTo_ι adj K L M r α p q (p + r) n t rfl hn (by omega) hnt]
    rfl
  · intro K K' L L' M M' f g t r α
    simpa only [curryIso_hom_apply] using curryTo_naturality adj K K' L L' M M' f g t r α
  · intro K L M z
    exact zero_cocycle_iff _ _ z
  · intro K L M z
    exact zero_cocycle_iff _ _ z
  · intro K L M u v h
    exact homotopy_iff _ _ u v h
  · intro K L M u v h
    exact homotopy_iff _ _ u v h
  · intro K L M u v h _ _ hh
    exact preserves_homotopy (curryIso adj K L M).hom u v h hh
  · intro K L M u v h _ _ hh
    exact preserves_homotopy (curryIso adj K L M).inv u v h hh

end CochainComplex

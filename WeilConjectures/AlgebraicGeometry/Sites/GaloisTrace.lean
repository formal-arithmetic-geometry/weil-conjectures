/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.GaloisDescent

/-!
# The trace of a finite separable extension on étale sheaves over a field

Let `K` be a field, `L/K` a finite Galois extension with group `G`, `P ≤ G` a subgroup and
`K' = L^P` its fixed field, of degree `d = [G : P]` over `K`. For an abelian étale sheaf `F` on
`Spec K`, let `F_{K'}` be the pushforward along `a : Spec K' ⟶ Spec K` of the restriction of `F`
to `Spec K'`; its sections over `U` are the sections of `F` over `U ×_K Spec K'`. We construct a
trace `F_{K'} ⟶ F` whose composite with the unit `F ⟶ F_{K'}` is multiplication by `d`: a
section over `U ×_K Spec K'` is pulled back to `U ×_K Spec L` along each of the `d` embeddings
`K' ⟶ L` (up to `P`), summed, and the `G`-invariant sum descends to `U`
(`AlgebraicGeometry.Scheme.existsUnique_map_prodEtaleSpecFst_eq`).

## Main definitions

- `AlgebraicGeometry.Scheme.prodEtaleSpecSheaf`: the sheaf `F_{K'} = a_* a^* F`.
- `AlgebraicGeometry.Scheme.toProdEtaleSpecSheaf`: the unit `F ⟶ F_{K'}`.
- `AlgebraicGeometry.Scheme.galoisTrace`: the trace `F_{K'} ⟶ F`.

## Main statements

- `AlgebraicGeometry.Scheme.toProdEtaleSpecSheaf_comp_galoisTrace`: the composite
  `F ⟶ F_{K'} ⟶ F` is multiplication by `[G : P]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K]

section Sheaf

variable (A : Type u) [Field A] [Algebra K A] [Algebra.Etale K A]

/-- The sheaf `U ↦ F(U ×_K Spec A)`: the pushforward along `Spec A ⟶ Spec K` of the restriction
of `F` to `Spec A`. -/
noncomputable abbrev prodEtaleSpecSheaf
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} (etaleSpec K A).hom).obj
    ((Etale.localizationRestriction AddCommGrpCat.{u + 1} (etaleSpec K A).hom
      (etaleSpec K A).prop).obj F)

lemma prodEtaleSpecSheaf_obj_obj (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : (Spec (.of K)).Etale) :
    (prodEtaleSpecSheaf A F).obj.obj (op U) = F.obj.obj (op (prodEtaleSpec A U)) :=
  rfl

lemma prodEtaleSpecSheaf_obj_map
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    {U V : (Spec (.of K)).Etale} (f : V ⟶ U) :
    (prodEtaleSpecSheaf A F).obj.map f.op = F.obj.map (prodEtaleSpecMapLeft A f).op :=
  rfl

/-- The unit `F ⟶ F_A`, pulling sections back along `U ×_K Spec A ⟶ U`. -/
noncomputable def toProdEtaleSpecSheaf
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}) :
    F ⟶ prodEtaleSpecSheaf A F :=
  ⟨{ app U := F.obj.map (prodEtaleSpecFst A U.unop).op
     naturality U V f := by
       change F.obj.map f ≫ F.obj.map (prodEtaleSpecFst A V.unop).op =
         F.obj.map (prodEtaleSpecFst A U.unop).op ≫ F.obj.map (prodEtaleSpecMapLeft A f.unop).op
       rw [← Functor.map_comp, ← Functor.map_comp]
       congr 1
       exact Quiver.Hom.unop_inj (by exact (prodEtaleSpecMapLeft_fst (A := A) f.unop).symm) }⟩

lemma toProdEtaleSpecSheaf_app
    (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : (Spec (.of K)).Etale) :
    (toProdEtaleSpecSheaf A F).hom.app (op U) = F.obj.map (prodEtaleSpecFst A U).op :=
  rfl

end Sheaf

section Trace

variable {L : Type u} [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

omit [IsGalois K L] in
lemma algebra_etale_of_isSeparable {E : Type u} [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra.IsSeparable K E] : Algebra.Etale K E :=
  ⟨Algebra.FormallyEtale.of_isSeparable K E, Algebra.FinitePresentation.of_finiteType.mp
    inferInstance⟩

attribute [local instance] algebra_etale_of_isSeparable

variable (P : Subgroup (L ≃ₐ[K] L))
  (F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The pullback of a section over `U ×_K Spec K'` to `U ×_K Spec L` along the embedding `g ∘ ι`
of `K' = L^P` into `L`. -/
noncomputable def galoisTraceTerm (U : (Spec (.of K)).Etale) (g : L ≃ₐ[K] L) :
    F.obj.obj (op (prodEtaleSpec (IntermediateField.fixedField P) U)) →+
      F.obj.obj (op (prodEtaleSpec L U)) :=
  (F.obj.map (prodEtaleSpecMap U g.toAlgHom ≫
    prodEtaleSpecMap U (IntermediateField.fixedField P).val).op).hom

lemma galoisTraceTerm_mul (U : (Spec (.of K)).Etale) (g h : L ≃ₐ[K] L) :
    galoisTraceTerm P F U (g * h) = (F.obj.map (prodEtaleSpecMap U g.toAlgHom).op).hom.comp
      (galoisTraceTerm P F U h) := by
  have e : prodEtaleSpecMap U (g * h).toAlgHom ≫
      prodEtaleSpecMap U (IntermediateField.fixedField P).val = prodEtaleSpecMap U g.toAlgHom ≫
        prodEtaleSpecMap U h.toAlgHom ≫ prodEtaleSpecMap U (IntermediateField.fixedField P).val := by
    rw [prodEtaleSpecMap_comp, prodEtaleSpecMap_comp, prodEtaleSpecMap_comp]
    rfl
  ext x
  simp only [galoisTraceTerm, e, op_comp, Functor.map_comp]
  rfl

lemma galoisTraceTerm_mul_of_mem (U : (Spec (.of K)).Etale) (g : L ≃ₐ[K] L) {p : L ≃ₐ[K] L}
    (hp : p ∈ P) : galoisTraceTerm P F U (g * p) = galoisTraceTerm P F U g := by
  have h : p.toAlgHom.comp (IntermediateField.fixedField P).val =
      (IntermediateField.fixedField P).val := by
    ext x
    exact x.2 ⟨p, hp⟩
  ext x
  simp only [galoisTraceTerm]
  congr 3
  rw [show (g * p).toAlgHom = g.toAlgHom.comp p.toAlgHom from rfl, ← prodEtaleSpecMap_comp,
    Category.assoc, prodEtaleSpecMap_comp U _ p.toAlgHom, h]

open scoped Classical in
/-- The sum over `G/P` of the pullbacks along the embeddings `K' ⟶ L`. -/
noncomputable def galoisTraceSum (U : (Spec (.of K)).Etale) :
    F.obj.obj (op (prodEtaleSpec (IntermediateField.fixedField P) U)) →+
      F.obj.obj (op (prodEtaleSpec L U)) :=
  ∑ q : (L ≃ₐ[K] L) ⧸ P, Quotient.liftOn' q (galoisTraceTerm P F U) fun g h hgh ↦ by
    obtain ⟨p, hp, rfl⟩ : ∃ p ∈ P, h = g * p :=
      ⟨g⁻¹ * h, QuotientGroup.leftRel_apply.1 hgh, by group⟩
    exact (galoisTraceTerm_mul_of_mem P F U g hp).symm

lemma galoisTraceSum_invariant (U : (Spec (.of K)).Etale) (σ : L ≃ₐ[K] L)
    (x : F.obj.obj (op (prodEtaleSpec (IntermediateField.fixedField P) U))) :
    F.obj.map (prodEtaleSpecMap U σ.toAlgHom).op (galoisTraceSum P F U x) =
      galoisTraceSum P F U x := by
  classical
  simp only [galoisTraceSum, AddMonoidHom.finsetSum_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm σ) _ _ fun q ↦ ?_
  induction q using QuotientGroup.induction_on with
  | H g =>
    change (F.obj.map (prodEtaleSpecMap U σ.toAlgHom).op) (galoisTraceTerm P F U g x) =
      galoisTraceTerm P F U (σ * g) x
    rw [galoisTraceTerm_mul]
    rfl

variable [Normal K L]

/-- The trace on sections over `U`: the unique section whose pullback to `U ×_K Spec L` is the
`G`-invariant sum `galoisTraceSum`. -/
noncomputable def galoisTraceApp (U : (Spec (.of K)).Etale)
    (x : F.obj.obj (op (prodEtaleSpec (IntermediateField.fixedField P) U))) :
    F.obj.obj (op U) :=
  (existsUnique_map_prodEtaleSpecFst_eq F U (galoisTraceSum P F U x)
    (galoisTraceSum_invariant P F U · x)).exists.choose

lemma map_galoisTraceApp (U : (Spec (.of K)).Etale)
    (x : F.obj.obj (op (prodEtaleSpec (IntermediateField.fixedField P) U))) :
    F.obj.map (prodEtaleSpecFst L U).op (galoisTraceApp P F U x) = galoisTraceSum P F U x :=
  (existsUnique_map_prodEtaleSpecFst_eq F U (galoisTraceSum P F U x)
    (galoisTraceSum_invariant P F U · x)).exists.choose_spec

lemma eq_galoisTraceApp {U : (Spec (.of K)).Etale}
    {x : F.obj.obj (op (prodEtaleSpec (IntermediateField.fixedField P) U))} {y : F.obj.obj (op U)}
    (h : F.obj.map (prodEtaleSpecFst L U).op y = galoisTraceSum P F U x) :
    y = galoisTraceApp P F U x :=
  (existsUnique_map_prodEtaleSpecFst_eq F U (galoisTraceSum P F U x)
    (galoisTraceSum_invariant P F U · x)).unique h (map_galoisTraceApp P F U x)

/-- The trace on sections over `U`, as an additive map. -/
noncomputable def galoisTraceAddHom (U : (Spec (.of K)).Etale) :
    F.obj.obj (op (prodEtaleSpec (IntermediateField.fixedField P) U)) →+ F.obj.obj (op U) where
  toFun := galoisTraceApp P F U
  map_zero' := (eq_galoisTraceApp P F (by rw [map_zero, map_zero])).symm
  map_add' x y := (eq_galoisTraceApp P F (by
    rw [map_add, map_add, map_galoisTraceApp, map_galoisTraceApp])).symm

/-- **The trace** `F_{K'} ⟶ F` of the fixed field `K' = L^P` of a subgroup `P` of the Galois
group of a finite Galois extension `L/K`. -/
noncomputable def galoisTrace :
    prodEtaleSpecSheaf (IntermediateField.fixedField P) F ⟶ F :=
  ⟨{ app U := AddCommGrpCat.ofHom (galoisTraceAddHom P F U.unop)
     naturality U V f := by
       ext x
       change galoisTraceApp P F V.unop
         (F.obj.map (prodEtaleSpecMapLeft (IntermediateField.fixedField P) f.unop).op x) =
         F.obj.map f (galoisTraceApp P F U.unop x)
       refine (eq_galoisTraceApp P F ?_).symm
       rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
       change F.obj.map (prodEtaleSpecFst L V.unop ≫ f.unop).op _ = _
       rw [← prodEtaleSpecMapLeft_fst, op_comp, Functor.map_comp, ConcreteCategory.comp_apply,
         map_galoisTraceApp]
       simp only [galoisTraceSum, AddMonoidHom.finsetSum_apply, map_sum]
       refine Finset.sum_congr rfl fun q _ ↦ ?_
       induction q using QuotientGroup.induction_on with
       | H g =>
         change F.obj.map (prodEtaleSpecMapLeft L f.unop).op (galoisTraceTerm P F U.unop g x) =
           galoisTraceTerm P F V.unop g _
         simp only [galoisTraceTerm]
         rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
           ← Functor.map_comp, ← op_comp, ← op_comp, Category.assoc,
           prodEtaleSpecMapLeft_prodEtaleSpecMap_assoc,
           prodEtaleSpecMapLeft_prodEtaleSpecMap] }⟩

lemma galoisTrace_app (U : (Spec (.of K)).Etale) :
    (galoisTrace P F).hom.app (op U) = AddCommGrpCat.ofHom (galoisTraceAddHom P F U) :=
  rfl

/-- **Trace after unit is the degree.** The composite `F ⟶ F_{K'} ⟶ F` is multiplication by the
index `[G : P] = [K' : K]`. -/
theorem toProdEtaleSpecSheaf_comp_galoisTrace :
    toProdEtaleSpecSheaf (IntermediateField.fixedField P) F ≫ galoisTrace P F =
      P.index • 𝟙 F := by
  classical
  ext U y
  have hd : ((P.index • 𝟙 F).hom.app U) y = P.index • y := by
    have e : (P.index • 𝟙 F).hom = P.index • 𝟙 F.obj :=
      (sheafToPresheaf _ _).map_nsmul (f := 𝟙 F) (n := P.index)
    rw [e, NatTrans.app_nsmul, NatTrans.id_app]
    rfl
  change galoisTraceApp P F U.unop (F.obj.map (prodEtaleSpecFst _ U.unop).op y) = _
  rw [hd]
  refine (eq_galoisTraceApp P F ?_).symm
  have hterm (g : L ≃ₐ[K] L) : galoisTraceTerm P F U.unop g
      (F.obj.map (prodEtaleSpecFst _ U.unop).op y) = F.obj.map (prodEtaleSpecFst L U.unop).op y := by
    simp only [galoisTraceTerm]
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Category.assoc,
      prodEtaleSpecMap_fst, prodEtaleSpecMap_fst]
  simp only [galoisTraceSum, AddMonoidHom.finsetSum_apply, map_nsmul]
  symm
  calc _ = ∑ _q : (L ≃ₐ[K] L) ⧸ P, F.obj.map (prodEtaleSpecFst L U.unop).op y :=
        Finset.sum_congr rfl fun q _ ↦ by
          induction q using QuotientGroup.induction_on with | H g => exact hterm g
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

end Trace

end AlgebraicGeometry.Scheme

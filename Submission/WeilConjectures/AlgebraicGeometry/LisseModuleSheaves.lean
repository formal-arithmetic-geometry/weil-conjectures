/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Sites.Adjunction
import Submission.WeilConjectures.AlgebraicGeometry.ModuleLocalConstancyOfFiniteUnderlying
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Lisse sheaves of finite modules and module objects

Source: literature/stacks-project/etale-cohomology.tex, Lemma 0DV5, proof of (1)--(3),
with sites-modules Lemma 093S (1)
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects).

Sheaves of left `Λ`-modules on `Y_et` are `Sheaf Y.smallEtaleTopology (ModuleCat.{u+1} Λ)`
with `Λ : Type (u + 1)` (STATE: the encoding of the six-functor and constructible chapters).
`FLC(Y)` is `IsFiniteLocallyConstantSheafOfTypes` (def-weil-pbc-etale-sheaves).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Λ : Type (u + 1)} [Ring Λ]

/-- A sheaf of left `Λ`-modules on `Y_et` is *lisse* when there are an etale covering
`{U_i → Y}` and finite left `Λ`-modules `M_i` with `F|_{U_i}` isomorphic, as a sheaf of
`Λ`-modules, to the constant sheaf (the sheafified constant presheaf) of `M_i`.
Source: Stacks Project, Lemma 0DV5
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
def IsLisseModuleSheaf (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ 𝒰 : Cover.{u} etalePrecoverage Y, ∀ i : 𝒰.I₀,
    ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
      Nonempty (F.over (𝒰.etalePrecoverageToEtale i) ≅
        (constantSheaf (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
          (ModuleCat.{u + 1} Λ)).obj M)

/-- A `Λ`-module structure on a sheaf of sets `A` in the sense of commutative diagrams:
morphisms `+ : A × A → A`, `0 : * → A` from the final object, `- : A → A` and `λ · : A → A`
for every `λ ∈ Λ`, satisfying the axioms of a left `Λ`-module as equalities of morphisms
(products are those of all sheaves of sets). Source: Stacks Project, Lemma 0DV5, proof of
(2)--(3) (blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
structure ModuleObjectStruct (Λ : Type (u + 1)) [Ring Λ]
    (A : Sheaf Y.smallEtaleTopology (Type (u + 1))) where
  /-- Addition. -/
  add : A ⨯ A ⟶ A
  /-- Zero, from the final object. -/
  zero : ⊤_ (Sheaf Y.smallEtaleTopology (Type (u + 1))) ⟶ A
  /-- Negation. -/
  neg : A ⟶ A
  /-- Scalar multiplication by each element of `Λ`. -/
  smul : Λ → (A ⟶ A)
  add_assoc : prod.map add (𝟙 A) ≫ add =
    (prod.associator A A A).hom ≫ prod.map (𝟙 A) add ≫ add
  add_comm : (prod.braiding A A).hom ≫ add = add
  zero_add : prod.lift (terminal.from A ≫ zero) (𝟙 A) ≫ add = 𝟙 A
  neg_add_cancel : prod.lift neg (𝟙 A) ≫ add = terminal.from A ≫ zero
  one_smul : smul 1 = 𝟙 A
  mul_smul (r s : Λ) : smul (r * s) = smul s ≫ smul r
  smul_add (r : Λ) : add ≫ smul r = prod.map (smul r) (smul r) ≫ add
  add_smul (r s : Λ) : smul (r + s) = prod.lift (smul r) (smul s) ≫ add
  smul_zero (r : Λ) : zero ≫ smul r = zero
  zero_smul : smul 0 = terminal.from A ≫ zero

variable (Y Λ) in
/-- A `Λ`-module object of `FLC(Y)`: a finite locally constant sheaf of sets with a
`Λ`-module structure in the sense of commutative diagrams. Source: Stacks Project,
Lemma 0DV5 (blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
structure LambdaModuleObject where
  /-- The underlying sheaf of sets. -/
  sheaf : Sheaf Y.smallEtaleTopology (Type (u + 1))
  isFLC : IsFiniteLocallyConstantSheafOfTypes sheaf
  /-- The module operations. -/
  str : ModuleObjectStruct Λ sheaf

namespace LambdaModuleObject

/-- A morphism of `Λ`-module objects: a morphism of `FLC(Y)` commuting with addition, zero,
negation and every scalar multiplication. Source: Stacks Project, Lemma 0DV5
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
@[ext]
structure Hom (A B : LambdaModuleObject Y Λ) where
  /-- The underlying morphism of sheaves of sets. -/
  hom : A.sheaf ⟶ B.sheaf
  add : A.str.add ≫ hom = prod.map hom hom ≫ B.str.add
  zero : A.str.zero ≫ hom = B.str.zero
  neg : A.str.neg ≫ hom = hom ≫ B.str.neg
  smul (r : Λ) : A.str.smul r ≫ hom = hom ≫ B.str.smul r

/-- The category of `Λ`-module objects of `FLC(Y)`. Source: Stacks Project, Lemma 0DV5
(blueprint: lem-pod-lisse-module-sheaves-as-module-objects). -/
instance : Category (LambdaModuleObject Y Λ) where
  Hom := Hom
  id A := ⟨𝟙 _, by simp, by simp, by simp, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by rw [← Category.assoc, f.add, Category.assoc, g.add,
      ← Category.assoc, prod.map_map], by rw [← Category.assoc, f.zero, g.zero],
    by rw [← Category.assoc, f.neg, Category.assoc, g.neg, Category.assoc],
    fun r => by rw [← Category.assoc, f.smul, Category.assoc, g.smul, Category.assoc]⟩

end LambdaModuleObject

@[simp] private theorem sheafType_comp_apply
    {A B C : Sheaf Y.smallEtaleTopology (Type (u + 1))} (f : A ⟶ B) (g : B ⟶ C)
    (U : Y.Etaleᵒᵖ) (x : A.obj.obj U) :
    (f ≫ g).hom.app U x = g.hom.app U (f.hom.app U x) := rfl

@[simp] private theorem sheafType_id_apply
    (A : Sheaf Y.smallEtaleTopology (Type (u + 1))) (U : Y.Etaleᵒᵖ)
    (x : A.obj.obj U) : (𝟙 A : A ⟶ A).hom.app U x = x := rfl

private theorem sheafType_congr
    {A B : Sheaf Y.smallEtaleTopology (Type (u + 1))} {f g : A ⟶ B}
    (h : f = g) (U : Y.Etaleᵒᵖ) (x : A.obj.obj U) :
    f.hom.app U x = g.hom.app U x := congrArg (fun k ↦ k.hom.app U x) h

@[simp] private theorem sheafType_map_fst_apply
    {A B C D : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    (f : A ⟶ C) (g : B ⟶ D) (U : Y.Etaleᵒᵖ) (x : (A ⨯ B).obj.obj U) :
    (prod.fst : C ⨯ D ⟶ C).hom.app U ((prod.map f g).hom.app U x) =
      f.hom.app U ((prod.fst : A ⨯ B ⟶ A).hom.app U x) := by
  exact sheafType_congr (prod.map_fst f g) U x

@[simp] private theorem sheafType_map_snd_apply
    {A B C D : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    (f : A ⟶ C) (g : B ⟶ D) (U : Y.Etaleᵒᵖ) (x : (A ⨯ B).obj.obj U) :
    (prod.snd : C ⨯ D ⟶ D).hom.app U ((prod.map f g).hom.app U x) =
      g.hom.app U ((prod.snd : A ⨯ B ⟶ B).hom.app U x) := by
  exact sheafType_congr (prod.map_snd f g) U x

private instance : JointlySurjective etalePrecoverage.{u} :=
  inferInstanceAs (JointlySurjective (precoverage @Etale))

private noncomputable def moduleUnderlyingStalkIso
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
    ((pointSmallEtale s).sheafFiber (A := Type (u + 1))).obj
      ((sheafForget Y.smallEtaleTopology).obj F) ≅
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)).obj
        (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  exact ((pointSmallEtale s).sheafFiberCompIso
    (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).app F

private noncomputable def moduleConstantValueStalkIso
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (U : Y.Etale) (M : ModuleCat.{u + 1} Λ)
    (e : F.over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)).obj M)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    ((pointSmallEtale (s ≫ U.hom)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj F ≅ M := by
  let : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  let eU : (Etale.upperStar (ModuleCat.{u + 1} Λ) U.hom).obj F ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M :=
    (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} Λ) U F).symm ≪≫
      (Etale.overSheafEquiv U (ModuleCat.{u + 1} Λ)).functor.mapIso e ≪≫
      ((Etale.overEquiv U).constantSheafSheafCongrIso
        (Y.smallEtaleTopology.over U) U.left.smallEtaleTopology
        (ModuleCat.{u + 1} Λ) CategoryTheory.Over.mkIdTerminal).app M
  exact ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) U.hom s).app F).symm ≪≫
    (pointSmallEtale s).sheafFiber.mapIso eU ≪≫
      (pointSmallEtale s).sheafFiberConstantSheafIso M

private theorem finiteModuleConstantModel_over
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (U : Y.Etale)
    (hc : (F.over U).IsConstant (Y.smallEtaleTopology.over U))
    (hf : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
      Finite (((pointSmallEtale s).sheafFiber (A := Type (u + 1))).obj
        ((sheafForget Y.smallEtaleTopology).obj F))) :
    ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧
      Nonempty (F.over U ≅
        (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)).obj M) := by
  classical
  by_cases hU : IsEmpty U.left
  · let := hU
    let E := (Etale.overSheafEquiv U (ModuleCat.{u + 1} Λ)).functor
    have hF : IsZero (E.obj (F.over U)) := Etale.isZero_sheaf_of_isEmpty _
    have hM : IsZero (E.obj
        ((constantSheaf (Y.smallEtaleTopology.over U)
          (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ PUnit))) :=
      Etale.isZero_sheaf_of_isEmpty _
    exact ⟨ModuleCat.of Λ PUnit, inferInstance, ⟨E.preimageIso (hF.iso hM)⟩⟩
  · have : Nonempty U.left := not_isEmpty_iff.mp hU
    let x : U.left := Classical.choice inferInstance
    let Ω := AlgebraicClosure (U.left.residueField x)
    let s : Spec (.of Ω) ⟶ U.left :=
      Spec.map (CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)) ≫
        U.left.fromSpecResidueField x
    let := hc
    obtain ⟨M, ⟨e⟩⟩ := (F.over U).mem_essImage_of_isConstant
    have : Finite (((pointSmallEtale (s ≫ U.hom)).sheafFiber
        (A := Type (u + 1))).obj ((sheafForget Y.smallEtaleTopology).obj F)) :=
      hf Ω (s ≫ U.hom)
    let eM := moduleUnderlyingStalkIso F (s ≫ U.hom) ≪≫
      (CategoryTheory.forget (ModuleCat.{u + 1} Λ)).mapIso
        (moduleConstantValueStalkIso F U M e.symm s)
    exact ⟨M, Finite.of_equiv _ eM.toEquiv, ⟨e.symm⟩⟩

/-- Clause (1): a sheaf of left modules over a finite ring `Λ` is lisse if and only if its
underlying sheaf of sets lies in `FLC(Y)`. Source: Stacks Project, Lemma 0DV5 (1), using
Lemma 093S (1) (blueprint: lem-pod-lisse-module-sheaves-as-module-objects).

Proof: if `F` is lisse, choose an etale covering on which it is isomorphic, as a sheaf of
`Λ`-modules, to the constant sheaf of a finite left `Λ`-module `M_i`; forgetting the module
structure gives an isomorphism of sheaves of sets with the constant finite sheaf underlying
`M_i`, so the underlying sheaf lies in `FLC(Y)`. Conversely, trivialize the underlying sheaf
on an etale cover, and also the finite products that occur as sources of the operations.
Each operation sends every element of its finite constant source to a section of the finite
constant target, which after an etale refinement is a constant section; refining over the
finite source makes the operation a map of finite constant sets. As `Λ` is finite there are
finitely many operations, so one common refinement makes all of them constant. The module
axioms hold as equalities of sheaf maps, so the local constant finite set is a finite left
`Λ`-module and the local identification is an isomorphism of sheaves of `Λ`-modules. -/
theorem lisseModuleSheaf_iff_underlying_finiteLocallyConstant [Finite Λ]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsLisseModuleSheaf F ↔
      IsFiniteLocallyConstantSheafOfTypes ((sheafForget Y.smallEtaleTopology).obj F) := by
  constructor
  · rintro ⟨𝒰, h𝒰⟩
    constructor
    · refine ⟨𝒰, fun i ↦ ?_⟩
      obtain ⟨M, _, ⟨e⟩⟩ := h𝒰 i
      have : (F.over (𝒰.etalePrecoverageToEtale i)).IsConstant
          (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i)) :=
        Sheaf.isConstant_of_iso _ e
      change ((sheafCompose (Y.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))
        (CategoryTheory.forget (ModuleCat.{u + 1} Λ))).obj
        (F.over (𝒰.etalePrecoverageToEtale i))).IsConstant _
      infer_instance
    · refine ⟨fun Ω _ _ s ↦ (ConcreteCategory.isFinitelyGenerated_iff_finite _).mpr ?_⟩
      obtain ⟨i, x, hx⟩ := 𝒰.exists_eq (s default)
      have : Etale (𝒰.f i) := 𝒰.map_prop i
      obtain ⟨t, ht, -⟩ := exists_fac_of_etale_of_isSepClosed (𝒰.f i) s x hx
      obtain ⟨M, hM, ⟨e⟩⟩ := h𝒰 i
      let := hM
      let es := moduleUnderlyingStalkIso F s
      have em := moduleConstantValueStalkIso F (𝒰.etalePrecoverageToEtale i) M e t
      change ((pointSmallEtale (t ≫ 𝒰.f i)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).obj F ≅ M at em
      rw [ht] at em
      exact Finite.of_equiv M
        (es ≪≫ (CategoryTheory.forget (ModuleCat.{u + 1} Λ)).mapIso em).toEquiv.symm
  · intro hF
    let := module_localConstancy_of_finite_underlying F hF
    obtain ⟨d⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
    exact ⟨d.cover, fun i ↦ finiteModuleConstantModel_over F
      (d.cover.etalePrecoverageToEtale i) (d.isConstant i)
      (fun Ω _ _ s ↦ hF.finite_sheafFiber Ω s)⟩

private abbrev sectionFunctor (U : Y.Etaleᵒᵖ) :
    Sheaf Y.smallEtaleTopology (Type (u + 1)) ⥤ Type (u + 1) :=
  sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj U

private noncomputable def sectionPair
    (A B : Sheaf Y.smallEtaleTopology (Type (u + 1))) (U : Y.Etaleᵒᵖ)
    (x : A.obj.obj U) (y : B.obj.obj U) : (A ⨯ B).obj.obj U :=
  ((PreservesLimitPair.iso (sectionFunctor U) A B) ≪≫
    Types.binaryProductIso _ _).inv (x, y)

@[simp] private theorem sectionPair_fst
    (A B : Sheaf Y.smallEtaleTopology (Type (u + 1))) (U : Y.Etaleᵒᵖ)
    (x : A.obj.obj U) (y : B.obj.obj U) :
    (prod.fst : A ⨯ B ⟶ A).hom.app U (sectionPair A B U x y) = x := by
  have h := PreservesLimitPair.iso_inv_fst (sectionFunctor U) A B
  have h' := congrArg (fun k ↦ (Types.binaryProductIso _ _).inv ≫ k) h
  simp only [Types.binaryProductIso_inv_comp_fst] at h'
  exact congrArg (fun k ↦ k (x, y)) h'

@[simp] private theorem sectionPair_snd
    (A B : Sheaf Y.smallEtaleTopology (Type (u + 1))) (U : Y.Etaleᵒᵖ)
    (x : A.obj.obj U) (y : B.obj.obj U) :
    (prod.snd : A ⨯ B ⟶ B).hom.app U (sectionPair A B U x y) = y := by
  have h := PreservesLimitPair.iso_inv_snd (sectionFunctor U) A B
  have h' := congrArg (fun k ↦ (Types.binaryProductIso _ _).inv ≫ k) h
  simp only [Types.binaryProductIso_inv_comp_snd] at h'
  exact congrArg (fun k ↦ k (x, y)) h'

private theorem sectionPair_ext
    {A B : Sheaf Y.smallEtaleTopology (Type (u + 1))} {U : Y.Etaleᵒᵖ}
    {x y : (A ⨯ B).obj.obj U}
    (hf : (prod.fst : A ⨯ B ⟶ A).hom.app U x =
      (prod.fst : A ⨯ B ⟶ A).hom.app U y)
    (hs : (prod.snd : A ⨯ B ⟶ B).hom.app U x =
      (prod.snd : A ⨯ B ⟶ B).hom.app U y) : x = y := by
  apply ((PreservesLimitPair.iso (sectionFunctor U) A B) ≪≫
    Types.binaryProductIso _ _).toEquiv.injective
  apply Prod.ext
  · have h : ((PreservesLimitPair.iso (sectionFunctor U) A B) ≪≫
        Types.binaryProductIso _ _).hom ≫ ↾Prod.fst =
        (sectionFunctor U).map (prod.fst : A ⨯ B ⟶ A) := by
      simp only [Iso.trans_hom, Category.assoc, Types.binaryProductIso_hom_comp_fst,
        PreservesLimitPair.iso_hom]
      exact prodComparison_fst _ _ _
    exact (congrArg (fun k ↦ k x) h).trans (hf.trans (congrArg (fun k ↦ k y) h).symm)
  · have h : ((PreservesLimitPair.iso (sectionFunctor U) A B) ≪≫
        Types.binaryProductIso _ _).hom ≫ ↾Prod.snd =
        (sectionFunctor U).map (prod.snd : A ⨯ B ⟶ B) := by
      simp only [Iso.trans_hom, Category.assoc, Types.binaryProductIso_hom_comp_snd,
        PreservesLimitPair.iso_hom]
      exact prodComparison_snd _ _ _
    exact (congrArg (fun k ↦ k x) h).trans (hs.trans (congrArg (fun k ↦ k y) h).symm)

@[simp] private theorem sectionPair_map
    {A B C D : Sheaf Y.smallEtaleTopology (Type (u + 1))}
    (f : A ⟶ C) (g : B ⟶ D) (U : Y.Etaleᵒᵖ)
    (x : A.obj.obj U) (y : B.obj.obj U) :
    (prod.map f g).hom.app U (sectionPair A B U x y) =
      sectionPair C D U (f.hom.app U x) (g.hom.app U y) := by
  apply sectionPair_ext <;> simp


end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

import Sheaf.Paper.NormalCompletedIntegralModel
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.TraceFormula.SmoothGeometricallyNormal
import Mathlib.RingTheory.Flat.Basic

/-!
# Global integral lattices on smooth geometric fibres

Source: Bhatt--Scholze, Lemmas 7.4.7 and 7.4.10 and Proposition 6.8.4(1),(4);
Stacks Project, Tags 056T, 01VB and 0BQ3
(blueprint: lem-a1-smooth-lisse-integral-lattice).

The integral ring is the recorded inverse limit of finite constant coefficient sheaves.
The rational ring is its sheaf localization at the recorded uniformizer. A lattice is
an actual subobject of the restriction of the given rational sheaf. The normalization
on `1 ⊗ m` says that its rationalization isomorphism is induced by that inclusion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor
open scoped ChangeOfRings

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type v) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})

/-- Forgetting abelian groups preserves the smaller filtered colimits used on this site.
Source: the size convention in Bhatt--Scholze, Definition 6.8.3
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
instance (priority := 100000) smoothLatticeForgetAbFiltered [UnivLE.{u + 1, w}] :
    PreservesFilteredColimitsOfSize.{u + 1, u + 1} (forget AddCommGrpCat.{w}) :=
  preservesFilteredColimitsOfSize_of_univLE.{w, w, u + 1, u + 1}
    (forget AddCommGrpCat.{w})

/-- Sheafification in any universe containing the pro-etale site, by transport of
the existing Grothendieck-abelian construction on a small model.
Source: Bhatt--Scholze, Definition 6.8.3, size convention
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
instance (priority := 100000) smoothLatticeSiteAbSheafify (T : Scheme.{u})
    [Small.{w} T.ProEt] [LocallySmall.{w} T.ProEt] :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{w} :=
  letI : EssentiallySmall.{w} T.ProEt := inferInstance
  letI : HasSheafify ((equivSmallModel.{w} T.ProEt).inverse.inducedTopology
      (Scheme.ProEt.topology T)) AddCommGrpCat.{w} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  hasSheafifyEssentiallySmallSite.{u, w, u + 1, w + 1, w} _ _

/-- Sheafification on each slice in the common coefficient universe. This transports
the existing small-site construction without identifying object and arrow universes.
Source: the size convention for Bhatt--Scholze, Definition 6.8.3
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
instance (priority := 100000) smoothLatticeSliceAbSheafify (T : Scheme.{u}) (U : T.ProEt)
    [Small.{w} (Over U)] [LocallySmall.{w} (Over U)] :
    HasSheafify ((Scheme.ProEt.topology T).over U) AddCommGrpCat.{w} :=
  letI : EssentiallySmall.{w} (Over U) := inferInstance
  letI : HasSheafify
      ((equivSmallModel.{w} (Over U)).inverse.inducedTopology
        ((Scheme.ProEt.topology T).over U)) AddCommGrpCat.{w} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  hasSheafifyEssentiallySmallSite.{u, w, u + 1,
    w + 1, w} _ _

/-- Local bijectivity on the same slices supplies the ordinary module sheafification API.
Source: the size convention for Bhatt--Scholze, Definition 6.8.3
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
instance (priority := 100000) smoothLatticeSliceAbLocallyBijective
    (T : Scheme.{u}) (U : T.ProEt)
    [Small.{w} (Over U)] [LocallySmall.{w} (Over U)] :
    ((Scheme.ProEt.topology T).over U).WEqualsLocallyBijective
      AddCommGrpCat.{w} :=
  letI : EssentiallySmall.{w} (Over U) := inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Local bijectivity for the base site in the common coefficient universe.
Source: Bhatt--Scholze, Definition 6.8.3, size convention
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
instance (priority := 100000) smoothLatticeSiteAbLocallyBijective (T : Scheme.{u})
    [Small.{w} T.ProEt] [LocallySmall.{w} T.ProEt] :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{w} :=
  letI : EssentiallySmall.{w} T.ProEt := inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- The uniformizer as a global section of the completed coefficient ring, obtained
from its constant section through the canonical quotient-cone map.
Source: Bhatt--Scholze, Section 6.8
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
def smoothLatticeUniformizerSection :
    ((WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj ⋙
      forget CommRingCat).sections :=
  (Functor.sectionsFunctor T.ProEtᵒᵖ).map
    (whiskerRight
      (whiskerRight
        (toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)))))
        (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)}) ≫
        (WeilConjectures.integralConstantToCompletionOfUniverses l E T).hom)
      (forget RingCat))
    ⟨fun _ ↦ ULift.up (Padic.coefficientExtensionUniformizer l E), fun _ ↦ rfl⟩

/-- The rational coefficient sheaf `B_T[1/varpi]`, by actual sheafified localization.
Source: Bhatt--Scholze, Definition 6.8.1 and Lemma 6.8.2(2)
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
def smoothLatticeRationalRing :
    Sheaf (Scheme.ProEt.topology T) CommRingCat.{max v (u + 1)} :=
  ringedLocalizationRingOfUniverses.{max v (u + 1), u + 1, u}
    (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (smoothLatticeUniformizerSection l E T)

/-- The canonical coefficient localization map, with no choice of rational realization.
Source: Bhatt--Scholze, Lemma 6.8.2(2)
(blueprint: lem-a1-smooth-lisse-integral-lattice). -/
def smoothLatticeCoefficientMap :
    WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T ⟶
      smoothLatticeRationalRing l E T :=
  ringedLocalizationRingUnitOfUniverses.{max v (u + 1), u + 1, u}
    (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (smoothLatticeUniformizerSection l E T)

section LocalizationInjection

universe c d r

variable {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
  [HasSheafify J CommRingCat.{r}] [J.WEqualsLocallyBijective CommRingCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  (R : Sheaf J CommRingCat.{r}) (s : (R.obj ⋙ forget CommRingCat).sections)

private theorem localizationCoefficient_injective
    (hs : ∀ U, Function.Injective (fun b : R.obj.obj U ↦ (show R.obj.obj U from s.val U) * b))
    (U : Cᵒᵖ) :
    Function.Injective ((ringedLocalizationRingUnitOfUniverses R s).hom.app U).hom := by
  intro x y hxy
  let P := ringedLocalizationRingPresheafOfUniverses R s
  have hz := Presheaf.equalizerSieve_mem J (toSheafify J P)
    ((algebraMap _ (ringedSectionLocalizationCarrierOfUniverses R s U)) x)
    ((algebraMap _ (ringedSectionLocalizationCarrierOfUniverses R s U)) y) hxy
  let F := R.obj ⋙ forget CommRingCat.{r}
  have hF : Presheaf.IsSheaf J F :=
    Presheaf.isSheaf_comp_of_isSheaf J R.obj (forget CommRingCat.{r}) R.property
  have heq : Presheaf.equalizerSieve (F := F) x y ∈ J U.unop := by
    apply J.superset_covering _ hz
    intro V f hf
    change F.map f.op x = F.map f.op y
    have hinj : Function.Injective
        (algebraMap (R.obj.obj (op V))
          (ringedSectionLocalizationCarrierOfUniverses R s (op V))) := by
      apply (IsLocalization.injective_iff_isRegular
        (M := Submonoid.powers (show R.obj.obj (op V) from s.val (op V)))).mpr
      rintro ⟨a, ⟨n, rfl⟩⟩
      apply IsRegular.pow
      refine ⟨hs (op V), ?_⟩
      intro a b h
      apply hs (op V)
      exact (mul_comm _ _).trans (h.trans (mul_comm _ _))
    apply hinj
    exact (congrArg (fun k ↦ k x)
      (ringedLocalizationRing_unit_naturalityOfUniverses R s f.op)).trans
        (hf.trans (congrArg (fun k ↦ k y)
          (ringedLocalizationRing_unit_naturalityOfUniverses R s f.op)).symm)
  exact (((isSheaf_iff_isSheaf_of_type _ _).mp hF).isSeparated _ heq).ext
    (fun _ _ h ↦ h)

end LocalizationInjection

section ScalarExtensionEmbedding

universe c d r

variable {C : Type c} [Category.{d} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S)
  (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
  (L : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
  (e : SheafOfModules.changeOfRingsOfUniverses a M ≅ L)

private def latticeTensorMap :
    SheafOfModules.changeOfRingsPresheafOfUniverses a M ⟶ L.val :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 _)) e.hom

private def latticeModelEmbedding :
    M ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map a)).obj L where
  val :=
    { app U := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (a.hom.app U).hom ((latticeTensorMap a M L e).app U)
      naturality := by
        intro U V f
        ext m
        change (latticeTensorMap a M L e).app V
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] M.val.map f m) =
            L.val.map f ((latticeTensorMap a M L e).app U
              ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] m))
        have h := PresheafOfModules.naturality_apply (latticeTensorMap a M L e) f
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] m)
        change (latticeTensorMap a M L e).app V
          (SheafOfModules.changeOfRingsMapOfUniverses a M f _) = _ at h
        rw [SheafOfModules.changeOfRingsMap_tmulOfUniverses, map_one] at h
        exact h }

private theorem latticeModelEmbedding_apply (U : Cᵒᵖ) (m : M.val.obj U) :
    (latticeModelEmbedding a M L e).val.app U m =
      e.hom.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app
          (SheafOfModules.changeOfRingsPresheafOfUniverses a M)).app U
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] m)) := by
  rfl

private theorem tensorUnit_injective {A B : Type r} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) (N : Type r) [AddCommGroup N]
    [Module A N] [Module.Free A N] :
    Function.Injective (fun n : N ↦ (1 : B) ⊗ₜ[A, f] n) := by
  let : Algebra A B := f.toAlgebra
  let : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hf
  exact Module.Flat.tensorProduct_mk_injective A N B

variable [∀ U, HasWeakSheafify (J.over U) AddCommGrpCat.{r}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{r}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify J AddCommGrpCat.{r}] in
private theorem tensorUnit_injective_at_basis
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] [q.IsFiniteType]
    (i : q.I) {W : C} (t : W ⟶ q.X i)
    (ha : Function.Injective (a.hom.app (op W)).hom) :
    Function.Injective (fun m : M.val.obj (op W) ↦
      (1 : S.obj.obj (op W)) ⊗ₜ[R.obj.obj (op W), (a.hom.app (op W)).hom] m) := by
  classical
  let := SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType (p := q) i
  let : Fintype (q.generators i).I := Fintype.ofFinite _
  let ee : M.val.obj (op W) ≃ₗ[R.obj.obj (op W)]
      ((q.generators i).I → R.obj.obj (op W)) :=
    SheafOfModules.sectionsLinearEquivOfIsoFree
      (asIso (q.generators i).π).symm (op (Over.mk t))
  let : Module.Free (R.obj.obj (op W)) (M.val.obj (op W)) :=
    Module.Free.of_equiv ee.symm
  exact tensorUnit_injective _ ha _

private theorem latticeModelEmbedding_injective
    (ha : ∀ U, Function.Injective (a.hom.app U).hom) (hM : M.IsFiniteLocallyFree)
    (U : Cᵒᵖ) : Function.Injective ((latticeModelEmbedding a M L e).val.app U) := by
  classical
  obtain ⟨q, hq, hf⟩ := hM.exists_localGeneratorsData
  let := hq
  let := hf
  intro m n hmn
  have ht :
      (((PresheafOfModules.sheafificationAdjunction
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app
        (SheafOfModules.changeOfRingsPresheafOfUniverses a M)).app U)
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] m) =
      (((PresheafOfModules.sheafificationAdjunction
          (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _)).unit.app
        (SheafOfModules.changeOfRingsPresheafOfUniverses a M)).app U)
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] n) := by
    apply ((SheafOfModules.evaluation _ U).mapIso e).toLinearEquiv.injective
    exact hmn
  let N := SheafOfModules.changeOfRingsPresheafOfUniverses a M
  have hz := Presheaf.equalizerSieve_mem J (toSheafify J N.presheaf)
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] m)
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (a.hom.app U).hom] n) ht
  let F := M.val.presheaf ⋙ forget AddCommGrpCat.{r}
  have hF : Presheaf.IsSheaf J F :=
    Presheaf.isSheaf_comp_of_isSheaf J M.val.presheaf (forget AddCommGrpCat.{r})
      M.isSheaf
  have heq : Presheaf.equalizerSieve (F := F) m n ∈ J U.unop := by
    apply J.transitive hz _
    intro V f hfz
    apply J.superset_covering _ (q.coversTop V)
    rintro W g ⟨i, ⟨t⟩⟩
    change F.map (g ≫ f).op m = F.map (g ≫ f).op n
    apply tensorUnit_injective_at_basis a M q i t (ha (op W))
    have hfg := congrArg (fun x ↦ N.presheaf.map g.op x) hfz
    change N.presheaf.map g.op (N.presheaf.map f.op _) =
      N.presheaf.map g.op (N.presheaf.map f.op _) at hfg
    simp only [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp] at hfg
    change SheafOfModules.changeOfRingsMapOfUniverses a M (g ≫ f).op _ =
      SheafOfModules.changeOfRingsMapOfUniverses a M (g ≫ f).op _ at hfg
    have hm := SheafOfModules.changeOfRingsMap_tmulOfUniverses a M (g ≫ f).op
      (1 : S.obj.obj U) m
    have hn := SheafOfModules.changeOfRingsMap_tmulOfUniverses a M (g ≫ f).op
      (1 : S.obj.obj U) n
    rw [map_one] at hm hn
    exact hm.symm.trans (hfg.trans hn)
  exact (((isSheaf_iff_isSheaf_of_type _ _).mp hF).isSeparated _ heq).ext
    (fun _ _ h ↦ h)

private theorem latticeModelEmbedding_mono
    (ha : ∀ U, Function.Injective (a.hom.app U).hom) (hM : M.IsFiniteLocallyFree) :
    Mono (latticeModelEmbedding a M L e) := by
  constructor
  intro Z f g h
  apply (SheafOfModules.fullyFaithfulForget _).map_injective
  ext U z
  apply latticeModelEmbedding_injective a M L e ha hM U
  exact congrArg (fun k ↦ k.val.app U z) h

end ScalarExtensionEmbedding

section CompletedRegular

universe c d r

private theorem quotient_transition_kills_annihilator
    {A : Type u} [CommRing A] [IsDomain A] (π : A) (hπ : π ≠ 0) (n : ℕ)
    (x : A ⧸ (Ideal.span {π}) ^ (n + 2))
    (hx : Ideal.Quotient.mk _ π * x = 0) :
    Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.le_succ (n + 1)) x = 0 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, pow_succ, mul_comm (π ^ (n + 1)) π] at hx
  have ha : π ^ (n + 1) ∣ a := (mul_dvd_mul_iff_left hπ).mp hx
  change Ideal.Quotient.mk _ a = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact ha

private theorem constantSheaf_kills_annihilator
    {C : Type c} [Category.{d} C] (J : GrothendieckTopology C)
    [HasSheafify J CommRingCat.{r}] [J.WEqualsLocallyBijective CommRingCat.{r}]
    (A B : CommRingCat.{r}) (f : A ⟶ B) (p : A)
    (hf : ∀ a : A, p * a = 0 → f a = 0)
    (U : Cᵒᵖ) (x : ((constantSheaf J CommRingCat.{r}).obj A).obj.obj U)
    (hx : (show ((constantSheaf J CommRingCat.{r}).obj A).obj.obj U from
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app U p) * x = 0) :
    (((constantSheaf J CommRingCat.{r}).map f).hom.app U) x = 0 := by
  let P := (Functor.const Cᵒᵖ).obj A
  let Q := (Functor.const Cᵒᵖ).obj B
  let F := (constantSheaf J CommRingCat.{r}).obj A
  let G := (constantSheaf J CommRingCat.{r}).obj B
  let a : P ⟶ F.obj := toSheafify J P
  let b : Q ⟶ G.obj := toSheafify J Q
  let t := (constantSheaf J CommRingCat.{r}).map f
  change a.app U p * x = 0 at hx
  let GF := G.obj ⋙ forget CommRingCat.{r}
  have hGF : Presheaf.IsSheaf J GF :=
    Presheaf.isSheaf_comp_of_isSheaf J G.obj (forget CommRingCat.{r}) G.property
  have hcover : Presheaf.equalizerSieve (F := GF) (t.hom.app U x) 0 ∈ J U.unop := by
    apply J.transitive (Presheaf.imageSieve_mem J a x)
    intro V g hg
    let y : A := Presheaf.localPreimage a x g hg
    have hy : a.app (op V) y = F.obj.map g.op x :=
      Presheaf.app_localPreimage a x g hg
    have hyzero : a.app (op V) (p * y) = a.app (op V) 0 := by
      rw [map_mul, map_zero, hy]
      have hp : F.obj.map g.op (a.app U p) = a.app (op V) p :=
        (NatTrans.naturality_apply a g.op p).symm
      rw [← hp, ← map_mul, hx, map_zero]
    apply J.superset_covering _ (Presheaf.equalizerSieve_mem J a (p * y) 0 hyzero)
    intro W h hh
    have hp : p * y = 0 := hh
    have hfy : f y = 0 := hf y hp
    have htb : t.hom.app (op W) (a.app (op W) y) = b.app (op W) (f y) :=
      (congrArg (fun k ↦ k.app (op W) y)
        (toSheafify_naturality J ((Functor.const Cᵒᵖ).map f))).symm
    change G.obj.map (h ≫ g).op (t.hom.app U x) = G.obj.map (h ≫ g).op 0
    rw [map_zero, ← NatTrans.naturality_apply t.hom]
    have hyh : F.obj.map (h ≫ g).op x = a.app (op W) y := by
      rw [op_comp, F.obj.map_comp, ConcreteCategory.comp_apply, ← hy]
      exact (NatTrans.naturality_apply a h.op y).symm
    rw [hyh, htb, hfy, map_zero]
  exact (((isSheaf_iff_isSheaf_of_type _ _).mp hGF).isSeparated _ hcover).ext
    (fun _ _ h ↦ h)

private theorem smoothLatticeUniformizer_ne_zero :
    Padic.coefficientExtensionUniformizer l E ≠ 0 := by
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hm : Padic.coefficientExtensionMaximalIdeal l E ≠ ⊥ :=
    h.2.2.2.2.2.2.2.2.2.1
  have hg : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
        Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  intro he
  apply hm
  rw [← hg, he]
  simp

private theorem smoothLatticeUniformizer_regular
    (U : T.ProEtᵒᵖ) :
    Function.Injective (fun b :
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U ↦
        (show (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U
          from (smoothLatticeUniformizerSection l E T).val U) * b) := by
  let : EssentiallySmall.{max v (u + 1)} T.ProEt := essentiallySmallSelf _
  let : (Scheme.ProEt.topology T).WEqualsLocallyBijective
      CommRingCat.{max v (u + 1)} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  suffices hz : ∀ b :
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U,
      (show (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T).obj.obj U
          from (smoothLatticeUniformizerSection l E T).val U) * b = 0 → b = 0 by
    intro a b hab
    apply sub_eq_zero.mp
    apply hz
    dsimp only at hab
    rw [mul_sub, hab, sub_self]
  intro b hb
  let D := WeilConjectures.integralCoefficientSheafSystem l E T
  let ev := sheafToPresheaf (Scheme.ProEt.topology T) RingCat.{max v (u + 1)} ⋙
    (evaluation T.ProEtᵒᵖ RingCat.{max v (u + 1)}).obj U
  apply Concrete.isLimit_ext (D ⋙ ev)
    (isLimitOfPreserves ev (limit.isLimit D)) b 0
  intro j
  obtain ⟨n⟩ := j
  let πn := ((limit.π D (op n)).hom.app U).hom
  let πs := ((limit.π D (op (n + 1))).hom.app U).hom
  have hp : πs ((smoothLatticeUniformizerSection l E T).val U) =
      (toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 2)))))).app U
            (ULift.up (Ideal.Quotient.mk _ (Padic.coefficientExtensionUniformizer l E))) := by
    change (((WeilConjectures.integralConstantToCompletionOfUniverses l E T ≫
      limit.π D (op (n + 1))).hom.app U)
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of
            (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))).app U
              (ULift.up (Padic.coefficientExtensionUniformizer l E)))) = _
    rw [WeilConjectures.integralConstantToCompletionOfUniverses, limit.lift_π]
    let q : CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
        CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 2))) :=
      CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 2))).comp
          ULift.ringEquiv.toRingHom))
    have he := toSheafify_naturality (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).map q)
    exact congrArg (fun k ↦ (ConcreteCategory.hom k)
      (ULift.up (Padic.coefficientExtensionUniformizer l E)))
        (NatTrans.congr_app he U).symm
  have hz :
      ((WeilConjectures.integralCoefficientSheafTransition l E T n).hom.app U)
        (πs b) = 0 := by
    apply constantSheaf_kills_annihilator (Scheme.ProEt.topology T)
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 2))))
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
      (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Padic.coefficientExtensionTransition l E (n + 1)).comp
          ULift.ringEquiv.toRingHom)))
      (ULift.up (Ideal.Quotient.mk _ (Padic.coefficientExtensionUniformizer l E)))
    · intro a ha
      apply ULift.ext
      apply quotient_transition_kills_annihilator
        (Padic.coefficientExtensionUniformizer l E) (smoothLatticeUniformizer_ne_zero l E) n
      exact congrArg ULift.down ha
    · rw [← hp]
      exact (πs.map_mul _ _).symm.trans ((congrArg πs hb).trans πs.map_zero)
  have hw := congrArg (fun f ↦ f.hom.app U b)
    (limit.w D (homOfLE (Nat.le_succ n)).op)
  change _ = _
  change πn b = πn 0
  rw [map_zero]
  apply hw.symm.trans
  have hmap : D.map (homOfLE (Nat.le_succ n)).op =
      WeilConjectures.integralCoefficientSheafTransition l E T n := by
    simp only [D, WeilConjectures.integralCoefficientSheafSystem,
      Functor.ofOpSequence_map_homOfLE_succ]
  rw [hmap]
  exact hz

end CompletedRegular

set_option maxHeartbeats 800000 in
-- Elaborating the independent coefficient universes and localization tensor needs this budget.
/-- Every locally finite free rational sheaf on a smooth geometric fibre contains a
locally finite free integral subobject whose inclusion induces its rationalization.
The monomorphism `i` presents the submodule sheaf, and the equation on pure tensors
fixes the induced isomorphism, rather than merely giving an abstract integral model.
Source: Bhatt--Scholze, Lemmas 7.4.7, 7.4.10 and Proposition 6.8.4(1),(4), pp. 59--71
(blueprint: lem-a1-smooth-lisse-integral-lattice).

Proof following the seven DAG steps:
1. Base-change permanence gives separated finite type over K. A field is Noetherian,
so finite-type-over-Noetherian gives a Noetherian T. Smooth geometric normality
(lem-trf-smooth-geometrically-normal, Stacks 056T) gives normal local domains for
every field extension K/K0. The inverse of l in K0 stays an inverse on T.
2. The Noetherian closed-subset minimum principle and
lem-sfb-noetherian-connected-components-open give finitely many clopen connected
components. Each open component is Noetherian, separated and normal. Restriction
to its open slice preserves the constant quotient sheaves, their limit, and localization.
The empty scheme already has the zero lattice.
3. On a nonempty component choose a geometric point and apply
lem-a1-normal-proetale-monodromy. Normality makes the monodromy group profinite,
and the sheaf corresponds to a continuous finite-dimensional E-representation V.
4. By lem-pod-profinite-stable-lattice choose a stable finite free A-lattice in V.
Its quotients are continuous finite free A/varpi^n representations. Clause (1) of
cor-galois-lisse-representations, including coefficient compatibility and full
faithfulness, gives their normalized tower of finite locally constant etale sheaves.
5. By lem-per-lisse-completed-system-comparison, its pro-etale inverse limit N is
locally finite free over the completed B. The integral normalization of the
monodromy equivalence and its full faithfulness give N[1/varpi] isomorphic to L.
6. The coefficient comparison of lem-sfb-integral-lisse-reduction-equivalence
identifies B with continuous A-valued functions. These are varpi-torsion free,
pointwise, since A embeds in E. On free charts this makes N torsion free, so
N maps monomorphically into N[1/varpi]. Compose with the preceding isomorphism
and take the image in L. It is isomorphic to N and its inclusion induces exactly
the displayed rationalization, characterized by sending 1 tensor m to i(m).
7. Glue these submodules over the finite disjoint clopen components, using products
on sections and componentwise restrictions. Their local trivializations and their
inclusion-induced isomorphisms glue. Ranks may differ between components and may
be zero; on the empty scheme the empty product is the zero module sheaf. -/
theorem exists_smooth_lisse_integral_lattice
    (K₀ K : Type u) [Field K₀] [Field K] [Algebra K₀ K]
    (T₀ : Scheme.{u}) (f : T₀ ⟶ Spec (.of K₀))
    [Smooth f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (l : ℕ) [Fact l.Prime] (_hl : IsUnit (l : K₀))
    (E : Type v) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : ringedSiteModules.{max v (u + 1)}
      ((sheafCompose _ (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)})).obj
        (smoothLatticeRationalRing l E
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K)))))))
    (_hL : L.IsFiniteLocallyFree) :
    ∃ (M : ringedSiteModules.{max v (u + 1)}
        (WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E
          (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K))))))
      (i : M ⟶ (SheafOfModules.restrictScalars
        ((sheafCompose _ (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)})).map
          (smoothLatticeCoefficientMap l E
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K))))))).obj L),
      Mono i ∧ M.IsFiniteLocallyFree ∧
      ∃ e : SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, max v (u + 1), max v (u + 1)}
          (smoothLatticeCoefficientMap l E
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K))))) M ≅ L,
        ∀ (U : (Scheme.ProEt
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K)))))ᵒᵖ)
          (m : M.val.obj U),
          e.hom.val.app U
            (((PresheafOfModules.sheafificationAdjunction
                (R := (sheafCompose _
                  (forget₂ CommRingCat.{max v (u + 1)} RingCat.{max v (u + 1)})).obj
                    (smoothLatticeRationalRing l E
                      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K))))))
                (𝟙 _)).unit.app
              (SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1,
                max v (u + 1), max v (u + 1)}
                (smoothLatticeCoefficientMap l E
                  (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K))))) M)).app U
              ((1 : (smoothLatticeRationalRing l E
                  (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K))))).obj.obj U)
                ⊗ₜ[_, ((smoothLatticeCoefficientMap l E
                  (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K₀ K))))).hom.app U).hom]
                  m)) = i.val.app U m := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K₀ K))
  let T := pullback f g
  let t : T ⟶ Spec (.of K) := pullback.snd f g
  let : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  let : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace t
  let : IsNoetherian T := ⟨⟩
  let : T.IsSeparated := by
    constructor
    rw [← terminal.comp_from t]
    infer_instance
  have hn : ∀ x : T,
      IsDomain (T.presheaf.stalk x) ∧ IsIntegrallyClosed (T.presheaf.stalk x) :=
    ((smooth_geometrically_normal K₀ T₀ f).2 K).1
  have hlT : ∀ x : T, IsUnit (l : T.presheaf.stalk x) := by
    intro x
    let q : T ⟶ Spec (.of K₀) := pullback.fst f g ≫ f
    let r : CommRingCat.of K₀ ⟶ T.presheaf.stalk x :=
      (Scheme.ΓSpecIso (.of K₀)).inv ≫ q.appTop ≫ T.presheaf.germ ⊤ x trivial
    simpa only [map_natCast] using _hl.map r.hom
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_normal_completed_integral_model l E T hn hlT
    (smoothLatticeUniformizerSection l E T) (fun _ ↦ rfl) L _hL
  let a := smoothLatticeCoefficientMap l E T
  let i := latticeModelEmbedding a M L e
  have ha : ∀ U, Function.Injective (a.hom.app U).hom := by
    let : EssentiallySmall.{max v (u + 1)} T.ProEt := essentiallySmallSelf _
    let : (Scheme.ProEt.topology T).WEqualsLocallyBijective
        CommRingCat.{max v (u + 1)} :=
      GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
    exact localizationCoefficient_injective
      (C := T.ProEt) (J := Scheme.ProEt.topology T)
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
      (smoothLatticeUniformizerSection l E T) (smoothLatticeUniformizer_regular l E T)
  refine ⟨M, i, latticeModelEmbedding_mono a M L e ha hM, hM, e, ?_⟩
  intro U m
  exact (latticeModelEmbedding_apply a M L e U m).symm

end AlgebraicGeometry.ProEtale

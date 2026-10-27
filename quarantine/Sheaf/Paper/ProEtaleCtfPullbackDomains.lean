/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.Paper.SmoothPurityTowerGamma
public import Sheaf.SecSmoothPurity.FiniteGeneralRing
public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitudePresentations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.ConstructibleSheaf.Pullback
public import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.Paper.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Paper.SmoothPurityTowerGluing
import Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse
import Sheaf.Paper.ProEtaleFiniteModelLocalConstancy
import Sheaf.Paper.ProEtaleFiniteModelStalks
import Sheaf.Paper.UniformTowerTensorClosure
import Sheaf.Paper.FiniteOrientationReduction
import all Sheaf.Paper.FiniteSmoothLevelOfOrientation
import all Sheaf.Paper.PurityPullbackLevelBounds
import all Sheaf.AlgebraicGeometry.EtaleProEtaleExceptionalObjectComparison
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-! # Finite-ring and uniform-tower pullback domains

Source: blueprint, smooth-purity base-change factors, proof (2), domains of the two
adjoint transposes (blueprint: lem-sp-proetale-ctf-pullback-domains).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.CtfPullbackDomains

/-- The actual pulled-back trivializing cover on the fibre-product stratum.
Its index set and all finite module values are retained. The covering proof is
part of Mathlib's base-change construction of a zero hypercover.
Source: blueprint smooth-purity base-change factors, proof (2)
(blueprint: lem-sp-proetale-ctf-pullback-domains). -/
def pulledBackTrivializingCover {Y Y' : Scheme.{u}} (v : Y' ⟶ Y)
    (S : Stratification Y) (i : Fin S.n)
    (C : (S.domain i).Cover.{u + 1} proetalePrecoverage) :
    (pullback (S.immersion i) v).Cover.{u + 1} proetalePrecoverage :=
  C.pullback₁ (pullback.fst (S.immersion i) v)

private def constantPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] (M : ModuleCat.{u + 1} A) :
    (upperStar (ModuleCat.{u + 1} A) f).obj
        ((constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A)).obj M) ≅
      (constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} A)).obj M :=
  (Functor.isoWhiskerLeft (constantSheaf (ProEt.topology Y) (ModuleCat.{u + 1} A))
    (Functor.sheafPullbackConstruction.sheafPullbackIso (proEtaleBaseChange f)
      (ModuleCat.{u + 1} A) (ProEt.topology Y) (ProEt.topology X)).symm).app M ≪≫
    ((proEtaleBaseChange f).constantSheafsheafPullbackIso (ModuleCat.{u + 1} A)
      (ProEt.topology Y) (ProEt.topology X) (ProEt.isTerminalMkId Y)
      ((ProEt.isTerminalMkId Y).isTerminalObj (proEtaleBaseChange f) _)).app M

private theorem lisse_of_iso (X : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
    {F G : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A)} (e : F ≅ G)
    (h : IsLocallyConstantProEtaleFixedModuleSheaf X A F ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Finite (proEtaleGeometricFixedModuleStalk x A F)) :
    IsLocallyConstantProEtaleFixedModuleSheaf X A G ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Finite (proEtaleGeometricFixedModuleStalk x A G) := by
  constructor
  · obtain ⟨I, U, f, hf, hm⟩ := h.1
    refine ⟨I, U, f, hf, fun i ↦ ?_⟩
    obtain ⟨M, ⟨em⟩⟩ := hm i
    exact ⟨M, ⟨(((ProEt.topology X).overPullback _ (U i)).mapIso e).symm ≪≫ em⟩⟩
  · intro Ω _ _ x
    have := h.2 Ω x
    let es := colim.mapIso
      (Functor.isoWhiskerLeft (proEtaleGeometricNeighbourhoodForget x).op
        ((sheafToPresheaf _ _).mapIso e))
    exact Finite.of_equiv (proEtaleGeometricFixedModuleStalk x A F)
      (Equiv.ofBijective _ (ConcreteCategory.bijective_of_isIso es.hom))

private theorem lisse_pullback {X Y : Scheme.{u}} (v : X ⟶ Y)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} A))
    (hF : IsLocallyConstantProEtaleFixedModuleSheaf Y A F ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y),
        Finite (proEtaleGeometricFixedModuleStalk y A F)) :
    IsLocallyConstantProEtaleFixedModuleSheaf X A
        ((upperStar (ModuleCat.{u + 1} A) v).obj F) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X),
        Finite (proEtaleGeometricFixedModuleStalk x A
          ((upperStar (ModuleCat.{u + 1} A) v).obj F)) := by
  obtain ⟨I, W, g, hg, hm⟩ := finite_models_of_fixed_lisse Y A F hF
  have hp : ∃ (I : Type (u + 1)) (W : I → Scheme.{u}) (g : ∀ i, W i ⟶ X),
      Presieve.ofArrows W g ∈ proetalePrecoverage X ∧
        ∀ i, ∃ M : ModuleCat.{u + 1} A, Finite M ∧
          Nonempty ((upperStar (ModuleCat.{u + 1} A) (g i)).obj
              ((upperStar (ModuleCat.{u + 1} A) v).obj F) ≅
            (constantSheaf (ProEt.topology (W i)) (ModuleCat.{u + 1} A)).obj M) := by
    refine ⟨I, fun i ↦ pullback (g i) v, fun i ↦ pullback.snd (g i) v, ?_, ?_⟩
    · exact Precoverage.mem_coverings_of_isPullback g hg v _ _
        (fun i ↦ (IsPullback.of_hasPullback (g i) v).flip)
    · intro i
      obtain ⟨M, hM, ⟨e⟩⟩ := hm i
      exact ⟨M, hM, ⟨
        ((upperStarComp (ModuleCat.{u + 1} A) (pullback.snd (g i) v) v).app F).symm ≪≫
        eqToIso (congrArg (fun f ↦ (upperStar (ModuleCat.{u + 1} A) f).obj F)
          (pullback.condition (f := g i) (g := v)).symm) ≪≫
        (upperStarComp (ModuleCat.{u + 1} A) (pullback.fst (g i) v) (g i)).app F ≪≫
        (upperStar (ModuleCat.{u + 1} A) (pullback.fst (g i) v)).mapIso e ≪≫
        constantPullbackIso (pullback.fst (g i) v) A M⟩⟩
  constructor
  · obtain ⟨I, U, f, hf, hm⟩ := finiteModels_over A _ hp
    exact ⟨I, U, f, hf, fun i ↦ by
      obtain ⟨M, _, hM⟩ := hm i
      exact ⟨M, hM⟩⟩
  · intro Ω _ _ x
    exact finite_geometricStalk_of_finite_models A _ hp Ω x

/-- Every supplied finite stratification and every finite constant model pulls back
along the actual fibre-product immersion and trivializing morphism.
Source: blueprint smooth-purity base-change factors, proof (2)
(blueprint: lem-sp-proetale-ctf-pullback-domains).

Proof: use lemma-constructible-pullback-stratification, retaining empty strata.
The two composites from the fibre product to the original scheme agree. The
inverse-image composition comparison identifies the restrictions. Inverse image
commutes with constants, because both are inverse images from a point. Pullback
of a trivializing covering is a covering by stability of the pro-etale topology.
The same finite module, including its scalar action, therefore trivializes every
pulled-back cover member. This applies separately to each term and each homology
sheaf in finite_models_and_pullback. -/
theorem stratification_local_models
    (D : FiniteFieldDatum.{u})
    (Y Y' : Over (Spec (.of D.k)))
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (v : Y' ⟶ Y) (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology Y.left) (ModuleCat.{u + 1} A))
    (S : Stratification Y.left) (_hn : 0 < S.n)
    (_hS : ∀ i : Fin S.n,
      IsLocallyConstantProEtaleFixedModuleSheaf (S.domain i) A
        ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj F) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ S.domain i),
        Finite (proEtaleGeometricFixedModuleStalk y A
          ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj F))) :
    (∀ i : Fin (S.pullback v.left).n,
      IsLocallyConstantProEtaleFixedModuleSheaf ((S.pullback v.left).domain i) A
        ((upperStar (ModuleCat.{u + 1} A) ((S.pullback v.left).immersion i)).obj
          ((upperStar (ModuleCat.{u + 1} A) v.left).obj F)) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ (S.pullback v.left).domain i),
        Finite (proEtaleGeometricFixedModuleStalk y A
          ((upperStar (ModuleCat.{u + 1} A) ((S.pullback v.left).immersion i)).obj
            ((upperStar (ModuleCat.{u + 1} A) v.left).obj F)))) ∧
    ∀ (i : Fin S.n) (U : Scheme.{u}) (t : U ⟶ S.domain i) [WeaklyEtale t]
      (M : ModuleCat.{u + 1} A) [Finite M],
      Nonempty ((upperStar (ModuleCat.{u + 1} A) t).obj
        ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj F) ≅
          (constantSheaf (ProEt.topology U) (ModuleCat.{u + 1} A)).obj M) →
      Nonempty
        ((upperStar (ModuleCat.{u + 1} A)
            (pullback.snd t (pullback.fst (S.immersion i) v.left))).obj
          ((upperStar (ModuleCat.{u + 1} A) (pullback.snd (S.immersion i) v.left)).obj
            ((upperStar (ModuleCat.{u + 1} A) v.left).obj F)) ≅
          (constantSheaf
            (ProEt.topology (pullback t (pullback.fst (S.immersion i) v.left)))
            (ModuleCat.{u + 1} A)).obj M) := by
  constructor
  · intro i
    let e := (upperStarCompIso (ModuleCat.{u + 1} A)
      (pullback.condition (f := S.immersion i) (g := v.left))).app F
    exact lisse_of_iso _ A e
      (lisse_pullback (pullback.fst (S.immersion i) v.left) A _ (_hS i))
  · intro i U t _ M _ hM
    obtain ⟨eM⟩ := hM
    let e := (upperStarCompIso (ModuleCat.{u + 1} A)
      (pullback.condition (f := S.immersion i) (g := v.left))).app F
    exact ⟨(upperStar (ModuleCat.{u + 1} A)
        (pullback.snd t (pullback.fst (S.immersion i) v.left))).mapIso e.symm ≪≫
      ((upperStarComp (ModuleCat.{u + 1} A)
        (pullback.snd t (pullback.fst (S.immersion i) v.left))
        (pullback.fst (S.immersion i) v.left)).app
          ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj F)).symm ≪≫
      eqToIso (congrArg (fun f ↦ (upperStar (ModuleCat.{u + 1} A) f).obj
        ((upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj F))
          (pullback.condition (f := t)
            (g := pullback.fst (S.immersion i) v.left)).symm) ≪≫
      (upperStarComp (ModuleCat.{u + 1} A)
        (pullback.fst t (pullback.fst (S.immersion i) v.left)) t).app _ ≪≫
      (upperStar (ModuleCat.{u + 1} A)
        (pullback.fst t (pullback.fst (S.immersion i) v.left))).mapIso eM ≪≫
      constantPullbackIso
        (pullback.fst t (pullback.fst (S.immersion i) v.left)) A M⟩

/-- The finite dualizing object is the specified exceptional inverse image of the
constant coefficient object in degree zero.
Source: blueprint smooth-purity base-change factors, proof (2)
(blueprint: lem-sp-proetale-ctf-pullback-domains). -/
def finiteOmega (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :=
  (Etale.FiniteSmoothPurity.exceptional A f).obj (finiteGeneralRingUnit A Y)

/-- The actual three-factor comparison: monoidal pullback, composition around the
square, and tensoring the given isomorphism at the coefficient object.
Source: blueprint smooth-purity base-change factors, proof (2)
(blueprint: lem-sp-proetale-ctf-pullback-domains). -/
def finiteComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} (u : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (v : Y' ⟶ Y) (sq : IsPullback u f' f v)
    [HasCompactification f] [HasCompactification f']
    (K : Etale.FiniteSmoothPurity.proCategory A Y)
    (e1 : (Etale.FiniteSmoothPurity.proPullback A u).obj (finiteOmega A f) ≅
      finiteOmega A f') :
    (Etale.FiniteSmoothPurity.proPullback A u).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((Etale.FiniteSmoothPurity.proPullback A f).obj K)).obj (finiteOmega A f)) ≅
      ((derivedTensor (ModuleCat.{u + 1} A) X').obj
        ((Etale.FiniteSmoothPurity.proPullback A f').obj
          ((Etale.FiniteSmoothPurity.proPullback A v).obj K))).obj (finiteOmega A f') :=
  leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) u _ _ ≪≫
    MonoidalCategory.tensorIso
      ((leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} A) sq.toCommSq).symm.app K) e1

private theorem constructible_pullback
    (D : FiniteFieldDatum.{u}) (Y Y' : Over (Spec (.of D.k)))
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (v : Y' ⟶ Y) (A : Type (u + 1)) [CommRing A] [Finite A]
    (F : Sheaf (ProEt.topology Y.left) (ModuleCat.{u + 1} A))
    (hF : IsConstructibleProEtaleFixedModuleSheaf Y.left A F) :
    IsConstructibleProEtaleFixedModuleSheaf Y'.left A
      ((upperStar (ModuleCat.{u + 1} A) v.left).obj F) := by
  obtain ⟨S, hn, _, hS⟩ := hF
  exact ⟨S.pullback v.left, hn, (S.pullback v.left).isConstructible_stratum,
    (stratification_local_models D Y Y' v A F S hn hS).1⟩

/-- Bounded flat constructible models, their exact inverse images, and the unchanged
Tor interval, including commutation with every cohomology sheaf.
Source: blueprint smooth-purity base-change factors, proof (2)
(blueprint: lem-sp-proetale-ctf-pullback-domains).

Proof: (1) sk-lem-sf-flat-model supplies a bounded flat constructible representative.
(2) lem-pc-bounded-above-flat-kflat-site makes every supplied bounded flat model
K-flat; lem-weil-pbc-ringed-pullback-preserves-kflat preserves its flat terms and
K-flatness. Exact inverse image computes the derived inverse image termwise.
(3) Pull back each constructible stratification and its finite local module models
by lemma-constructible-pullback-stratification. Finite type over the standing field
makes the schemes Noetherian, so the preimages remain constructible.
(4) Tensoring the resulting model with any degree-zero module has zero terms,
and hence zero cohomology, outside its original interval. Exactness commutes with
kernels, images and cokernels, giving the cohomology comparison in every degree. -/
theorem finite_models_and_pullback
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, 0 < n ∧ ((ell ^ n : ℕ) : A) = 0)
    (Y Y' : Over (Spec (.of D.k)))
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (v : Y' ⟶ Y) (K : Etale.FiniteSmoothPurity.proCategory A Y.left)
    (_hK : Etale.FiniteSmoothPurity.IsCtf A Y.left K) :
    (∃ (P : CochainComplex (Sheaf (ProEt.topology Y.left) (ModuleCat.{u + 1} A)) ℤ)
        (a b : ℤ), a ≤ b ∧
      (∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i)) ∧
      (∀ i : ℤ, ObjectProperty.flat (P.X i) ∧
        IsConstructibleProEtaleFixedModuleSheaf Y.left A (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj P ≅ K)) ∧
    ∀ (P : CochainComplex (Sheaf (ProEt.topology Y.left) (ModuleCat.{u + 1} A)) ℤ)
      (a b : ℤ), a ≤ b →
      (∀ i : ℤ, (i < a ∨ b < i) → IsZero (P.X i)) →
      (∀ i : ℤ, ObjectProperty.flat (P.X i) ∧
        IsConstructibleProEtaleFixedModuleSheaf Y.left A (P.X i)) →
      Nonempty (DerivedCategory.Q.obj P ≅ K) →
      (∀ i : ℤ, ObjectProperty.flat
        (((upperStar (ModuleCat.{u + 1} A) v.left).mapHomologicalComplex (.up ℤ)).obj
          P |>.X i) ∧
        IsConstructibleProEtaleFixedModuleSheaf Y'.left A
          (((upperStar (ModuleCat.{u + 1} A) v.left).mapHomologicalComplex (.up ℤ)).obj
            P |>.X i)) ∧
      (HomologicalComplex.quasiIso
        (Sheaf (ProEt.topology Y'.left) (ModuleCat.{u + 1} A)) (.up ℤ)).kFlat
        (((upperStar (ModuleCat.{u + 1} A) v.left).mapHomologicalComplex (.up ℤ)).obj P) ∧
      Nonempty (DerivedCategory.Q.obj
        (((upperStar (ModuleCat.{u + 1} A) v.left).mapHomologicalComplex (.up ℤ)).obj P) ≅
          (Etale.FiniteSmoothPurity.proPullback A v.left).obj K) ∧
      (∀ i : ℤ, (i < a ∨ b < i) → IsZero
        ((((upperStar (ModuleCat.{u + 1} A) v.left).mapHomologicalComplex (.up ℤ)).obj P).X i)) ∧
      Etale.FiniteSmoothPurity.IsCtf A Y'.left
        ((Etale.FiniteSmoothPurity.proPullback A v.left).obj K) ∧
      HasFixedCoefficientProEtaleTorAmplitude Y'.left A
        ((Etale.FiniteSmoothPurity.proPullback A v.left).obj K) a b ∧
      ∀ i : ℤ, Nonempty
        ((DerivedCategory.homologyFunctor _ i).obj
            ((Etale.FiniteSmoothPurity.proPullback A v.left).obj K) ≅
          (upperStar (ModuleCat.{u + 1} A) v.left).obj
            ((DerivedCategory.homologyFunctor _ i).obj K)) := by
  classical
  let := isNoetherian_of_locallyOfFiniteType Y.hom
  let := isNoetherian_of_locallyOfFiniteType Y'.hom
  let : IsNoetherianRing A := isNoetherian_of_finite A A
  let C := Sheaf (ProEt.topology Y.left) (ModuleCat.{u + 1} A)
  let C' := Sheaf (ProEt.topology Y'.left) (ModuleCat.{u + 1} A)
  let V := upperStar (ModuleCat.{u + 1} A) v.left
  let L := Etale.FiniteSmoothPurity.proPullback A v.left
  have hc (i : ℤ) : (DerivedCategory.homologyFunctor C' i).obj (L.obj K) ≅
      V.obj ((DerivedCategory.homologyFunctor C i).obj K) :=
    (DerivedCategory.homologyFunctor C' i).mapIso
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v.left).app K) ≪≫
      ((V.mapDerivedCategoryHomologyFunctorIso i).app K).symm
  have hctf : Etale.FiniteSmoothPurity.IsCtf A Y'.left (L.obj K) := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (fixed_constructible_iff A Y'.left _).mpr
        (isConstructible_of_iso (hc i).symm
          ((fixed_constructible_iff A Y'.left _).mp
            (constructible_pullback D Y Y' v A _ (_hK.1 i))))
    · obtain ⟨a, z, haz, hv⟩ := _hK.2.1
      exact ⟨a, z, haz, fun i hi ↦ (V.map_isZero (hv i hi)).of_iso (hc i)⟩
    · obtain ⟨a, z, haz, ht⟩ := _hK.2.2
      exact ⟨a, z, haz, torAmplitudeIn_leftDerivedUpperStar _ v.left a z ht⟩
  constructor
  · obtain ⟨K₀, hK₀, ⟨eK⟩⟩ := Etale.FiniteSmoothPurity.intrinsicOrigin A Y.left K _hK
    obtain ⟨a, z, haz, ht⟩ := _hK.2.2
    have ht₀ : Etale.DerivedCategory.hasTorAmplitudeIn A Y.left a z K₀ :=
      Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
        ((ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a z K₀).mp
          ((_root_.DerivedCategory.torAmplitudeIn C a z).prop_of_iso eK.symm ht))
    obtain ⟨P, hP, hcon, ⟨eP⟩⟩ :=
      (Etale.hasTorAmplitudeIn_iff_exists_flatConstructibleModel A a z haz K₀ hK₀.1).mp ht₀
    let N := comparisonUpperStar (ModuleCat.{u + 1} A) Y.left
    let Q := (N.mapHomologicalComplex (.up ℤ)).obj P
    refine ⟨Q, a, z, haz, fun i hi ↦ N.map_isZero (hP.1 i hi), ?_, ?_⟩
    · intro i
      have := hcon i
      exact ⟨Functor.PreservesFlat.flat_obj (F := N) (hP.2 i),
        (fixed_constructible_iff A Y.left _).mpr (isConstructible_comparisonUpperStar_obj _)⟩
    · exact ⟨(N.mapDerivedCategoryFactors.app P).symm ≪≫
        N.mapDerivedCategory.mapIso eP.symm ≪≫ eK⟩
  · intro P a z haz hzero hflat he
    let Q := (V.mapHomologicalComplex (.up ℤ)).obj P
    have hz : ∀ i : ℤ, (i < a ∨ z < i) → IsZero (Q.X i) :=
      fun i hi ↦ V.map_isZero (hzero i hi)
    have hf : ∀ i : ℤ, ObjectProperty.flat (Q.X i) :=
      fun i ↦ Functor.PreservesFlat.flat_obj (F := V) (hflat i).1
    have : CochainComplex.IsStrictlyGE Q a := (CochainComplex.isStrictlyGE_iff Q a).mpr
      (fun i hi ↦ hz i (.inl hi))
    have : CochainComplex.IsStrictlyLE Q z := (CochainComplex.isStrictlyLE_iff Q z).mpr
      (fun i hi ↦ hz i (.inr hi))
    obtain ⟨e⟩ := he
    let eQ : DerivedCategory.Q.obj Q ≅ L.obj K :=
      (V.mapDerivedCategoryFactors.app P).symm ≪≫ V.mapDerivedCategory.mapIso e ≪≫
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v.left).app K).symm
    refine ⟨fun i ↦ ⟨hf i, constructible_pullback D Y Y' v A _ (hflat i).2⟩,
      CochainComplex.kFlat_of_bounded_of_flat Q a z hf, ⟨eQ⟩, hz, hctf, ?_, ?_⟩
    · exact ⟨haz, (_root_.DerivedCategory.torAmplitudeIn C' a z).prop_of_iso eQ
        (DerivedCategory.torAmplitudeIn_Q_obj_of_flat Q a z hf)⟩
    · exact fun i ↦ ⟨hc i⟩

private theorem finite_pullback_ctf
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hne : ell ≠ D.p)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 0 < n ∧ ((ell ^ n : ℕ) : A) = 0)
    (Y Y' : Over (Spec (.of D.k)))
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (v : Y' ⟶ Y) (K : Etale.FiniteSmoothPurity.proCategory A Y.left)
    (hK : Etale.FiniteSmoothPurity.IsCtf A Y.left K) :
    Etale.FiniteSmoothPurity.IsCtf A Y'.left
      ((Etale.FiniteSmoothPurity.proPullback A v.left).obj K) := by
  obtain ⟨hex, hpull⟩ := finite_models_and_pullback D ell hne A hA Y Y' v K hK
  obtain ⟨P, a, z, haz, hz, hflat, he⟩ := hex
  exact (hpull P a z haz hz hflat he).2.2.2.2.1

private theorem finite_smooth_tensor_ctf
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (hne : ell ≠ D.p)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, 0 < n ∧ ((ell ^ n : ℕ) : A) = 0)
    (X Y : Over (Spec (.of D.k)))
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) (d : ℕ) [IsSeparated f.left]
    [SmoothOfRelativeDimension d f.left] [HasCompactification f.left]
    (K : Etale.FiniteSmoothPurity.proCategory A Y.left)
    (hK : Etale.FiniteSmoothPurity.IsCtf A Y.left K) :
    Etale.FiniteSmoothPurity.IsCtf A X.left
      (((derivedTensor (ModuleCat.{u + 1} A) X.left).obj
        ((Etale.FiniteSmoothPurity.proPullback A f.left).obj K)).obj
          (finiteOmega A f.left)) := by
  let := isNoetherian_of_locallyOfFiniteType X.hom
  let := isNoetherian_of_locallyOfFiniteType Y.hom
  obtain ⟨n, hn, hAn⟩ := hA
  let P := finiteGeneralRingPrimeSetting D ell hne n hn
  have hY (y : Y.left) : IsUnit ((ell ^ n : ℕ) : Y.left.presheaf.stalk y) := by
    simpa only [map_natCast, P, PurityFiniteSetting.diagonalExponent,
      finiteGeneralRingPrimeSetting] using
      (P.diagonalExponent_isUnit Y.hom).map (Y.left.presheaf.germ ⊤ y trivial).hom
  have hsource := (Etale.FiniteSmoothPurity.proObjectsCtf A (ell ^ n)
    (pow_pos (Fact.out : ell.Prime).pos n) hAn f.left d hY
    (Etale.dualizingComplex (ModuleCat.{u + 1} A) f.left) (Iso.refl _) K hK).1
  have hu := isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} A) Y.left
    (Etale.ordinaryFiniteUnit A Y.left) ⟨0, inferInstance⟩
  have : IsIso (finiteGeneralRingDualizingUnitMap A f.left) := by
    unfold finiteGeneralRingDualizingUnitMap
    infer_instance
  let e : (Etale.FiniteSmoothPurity.comparison A X.left).obj
      (Etale.dualizingComplex (ModuleCat.{u + 1} A) f.left) ≅ finiteOmega A f.left :=
    asIso (finiteGeneralRingDualizingUnitMap A f.left)
  exact Etale.FiniteSmoothPurity.isCtfOfIso A X.left
    (((derivedTensor (ModuleCat.{u + 1} A) X.left).obj
      ((Etale.FiniteSmoothPurity.proPullback A f.left).obj K)).mapIso e) hsource

/-- Both finite-coefficient tensor sources lie in the full constructible finite-Tor
category, so that the specified comparison is an arrow between admissible sources
of the restricted exceptional adjunction.
Source: blueprint smooth-purity base-change factors, proof (2)
(blueprint: lem-sp-proetale-ctf-pullback-domains).

Proof: apply finite_models_and_pullback to v and f. The oriented tensor source in
det-sp-finite-general-ring is constructible finite-Tor, both for f and its smooth
base change f'. Apply finite_models_and_pullback again along u. The formula of
finiteComparison is the monoidal comparison, then the composition comparison for
fu=vf', then 1 tensor e1. Each factor is invertible. Fullness makes these the same
objects and morphisms in the restricted adjunction of def-pur-co-smoothness. -/
theorem finite_smooth_domains
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (_hA : ∃ n : ℕ, 0 < n ∧ ((ell ^ n : ℕ) : A) = 0)
    (X' X Y' Y : Over (Spec (.of D.k)))
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (_sq : IsPullback u.left f'.left f.left v.left)
    (d : ℕ) [IsSeparated f.left] [SmoothOfRelativeDimension d f.left]
    [HasCompactification f.left] [HasCompactification f'.left]
    (K : Etale.FiniteSmoothPurity.proCategory A Y.left)
    (_hK : Etale.FiniteSmoothPurity.IsCtf A Y.left K)
    (_e1 : (Etale.FiniteSmoothPurity.proPullback A u.left).obj (finiteOmega A f.left) ≅
      finiteOmega A f'.left) :
    Etale.FiniteSmoothPurity.IsCtf A X'.left
      (((derivedTensor (ModuleCat.{u + 1} A) X'.left).obj
        ((Etale.FiniteSmoothPurity.proPullback A f'.left).obj
          ((Etale.FiniteSmoothPurity.proPullback A v.left).obj K))).obj
            (finiteOmega A f'.left)) ∧
    Etale.FiniteSmoothPurity.IsCtf A X'.left
      ((Etale.FiniteSmoothPurity.proPullback A u.left).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X.left).obj
          ((Etale.FiniteSmoothPurity.proPullback A f.left).obj K)).obj
            (finiteOmega A f.left)))  := by
  let := isNoetherian_of_locallyOfFiniteType X'.hom
  have hsource := finite_smooth_tensor_ctf D ell _hne A _hA X Y f d K _hK
  have hsecond := finite_pullback_ctf D ell _hne A _hA X X' u _ hsource
  exact ⟨Etale.FiniteSmoothPurity.isCtfOfIso A X'.left
    (finiteComparison A u.left f'.left f.left v.left _sq K _e1) hsecond, hsecond⟩

section Towers
variable (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
  [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
  (b : SpTowerShriek.Base ell E) (o : SpTowerShriek.Operations ell E b)
  (q : SpTowerCalculus.Coordinates ell E b)

/-- Exact levelwise inverse image in the original strict tower coordinates.
Source: blueprint smooth-purity base-change factors, proof (2)
(blueprint: lem-sp-proetale-ctf-pullback-domains). -/
def towerPullback {X Y : Scheme.{u}} (v : X ⟶ Y) :
    spDerivedCoefficientTowers ell E Y (q.abelian Y) ⥤
      spDerivedCoefficientTowers ell E X (q.abelian X) :=
  (SpTowerCalculus.realization ell E b Y (q.abelian Y)).functor ⋙
    SpTowerShriek.pull ell E b (o.geometry v) ⋙
      (SpTowerCalculus.realization ell E b X (q.abelian X)).inverse

private theorem intrinsic_tor_iso (T : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L) (a z : ℤ)
    (h : HasProEtaleTorAmplitude T A K a z) : HasProEtaleTorAmplitude T A L a z := by
  refine ⟨h.1, ?_⟩
  rintro C P ⟨eC⟩ f hf hP M i hi
  exact h.2 C P ⟨eC ≪≫ e.symm⟩ f hf hP M i hi

private theorem intrinsic_ctf_iso (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {K L : proEtaleDerivedCategory T A} (e : K ≅ L)
    (h : spFiniteConstructibleTor T A K) : spFiniteConstructibleTor T A L := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨a, z, haz, hv⟩ := h.1
    exact ⟨a, z, haz, fun i hi ↦ (hv i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso e).symm⟩
  · intro i
    have hi := h.2.1 i
    rw [proEtaleModuleRestriction_constructible_iff] at hi ⊢
    exact isConstructible_of_iso ((proEtaleModuleRestriction T A).mapIso
      ((DerivedCategory.homologyFunctor _ i).mapIso e)) hi
  · obtain ⟨a, z, ht⟩ := h.2.2
    exact ⟨a, z, intrinsic_tor_iso T A e a z ht⟩

/-- Uniform cohomological and Tor intervals are preserved with the very same endpoints;
no normalization of the transition maps is assumed.
Source: blueprint smooth-purity base-change factors, proof (2)
(blueprint: lem-sp-proetale-ctf-pullback-domains).

Proof: pull back every term and every semilinear transition. The quotient maps commute
with the canonical constant-ring identifications, so this is exact levelwise inverse
image on the ordinary tower category (det-sp-coefficient-towers-abelian and
 def-sp-varying-ring-operations). Exact evaluation identifies its n-th level with
the finite inverse image. Apply the finite assertion to each level, retaining the
cohomological and Tor intervals. The residue index is r(n+1), since ell equals a
unit times the r-th power of the uniformizer. No reduction map must be an iso. -/
theorem tower_bounds
    (D : FiniteFieldDatum.{u}) (_hne : ell ≠ D.p)
    (Y Y' : Over (Spec (.of D.k)))
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (v : Y' ⟶ Y)
    (K : spDerivedCoefficientTowers ell E Y.left (q.abelian Y.left))
    (a b' c e : ℤ) (_hab : a ≤ b') (_hce : c ≤ e)
    (_hlevels : ∀ n : ℕ, spFiniteConstructibleTor Y.left (SpTowerShriek.R ell E n)
      ((spDerivedCoefficientEvaluation ell E Y.left (q.abelian Y.left) n).obj K))
    (_hcoh : ∀ n : ℕ, SpTowerCalculus.cohomologicalInterval ell E Y.left n
      ((spDerivedCoefficientEvaluation ell E Y.left (q.abelian Y.left) n).obj K) c e)
    (_htor : ∀ n : ℕ, HasProEtaleTorAmplitude Y.left (SpTowerShriek.R ell E n)
      ((spDerivedCoefficientEvaluation ell E Y.left (q.abelian Y.left) n).obj K) a b') :
    (∀ n : ℕ, spFiniteConstructibleTor Y'.left (SpTowerShriek.R ell E n)
      ((spDerivedCoefficientEvaluation ell E Y'.left (q.abelian Y'.left) n).obj
        ((towerPullback ell E b o q v.left).obj K))) ∧
    (∀ n : ℕ, SpTowerCalculus.cohomologicalInterval ell E Y'.left n
      ((spDerivedCoefficientEvaluation ell E Y'.left (q.abelian Y'.left) n).obj
        ((towerPullback ell E b o q v.left).obj K)) c e) ∧
    (∀ n : ℕ, HasProEtaleTorAmplitude Y'.left (SpTowerShriek.R ell E n)
      ((spDerivedCoefficientEvaluation ell E Y'.left (q.abelian Y'.left) n).obj
        ((towerPullback ell E b o q v.left).obj K)) a b') ∧
    ∀ n : ℕ, Nonempty
      ((spDerivedCoefficientEvaluation ell E Y'.left (q.abelian Y'.left) n).obj
          ((towerPullback ell E b o q v.left).obj K) ≅
        (proEtaleConstantRingDerivedPullback (SpTowerShriek.R ell E n) v.left).obj
          ((spDerivedCoefficientEvaluation ell E Y.left (q.abelian Y.left) n).obj K)) := by
  let := isNoetherian_of_locallyOfFiniteType Y.hom
  let := isNoetherian_of_locallyOfFiniteType Y'.hom
  let FY := SpTowerCalculus.realization ell E b Y.left (q.abelian Y.left)
  let FX := SpTowerCalculus.realization ell E b Y'.left (q.abelian Y'.left)
  let V := (SpTowerShriek.pull ell E b (o.geometry v.left)).obj (FY.functor.obj K)
  let en (n : ℕ) :
      (spDerivedCoefficientEvaluation ell E Y'.left (q.abelian Y'.left) n).obj
          ((towerPullback ell E b o q v.left).obj K) ≅
        (proEtaleConstantRingDerivedPullback (SpTowerShriek.R ell E n) v.left).obj
          ((spDerivedCoefficientEvaluation ell E Y.left (q.abelian Y.left) n).obj K) :=
    ((SpTowerCalculus.levelComparison ell E b q Y'.left n).app (FX.inverse.obj V)).symm ≪≫
      (SpTowerShriek.Ev ell E Y'.left n).mapIso (FX.counitIso.app V) ≪≫
      ((o.geometry v.left).pullEvaluation n).app (FY.functor.obj K) ≪≫
      (proEtaleConstantRingDerivedPullback (SpTowerShriek.R ell E n) v.left).mapIso
        ((SpTowerCalculus.levelComparison ell E b q Y.left n).app K)
  have hb (n : ℕ) := SpPurityReduction.finite_constant_pullback_bounds
    (SpTowerShriek.R ell E n) v.left _ (_hlevels n) a b' (_htor n)
  refine ⟨fun n ↦ intrinsic_ctf_iso Y'.left _ (en n).symm (hb n).1, ?_,
    fun n ↦ intrinsic_tor_iso Y'.left _ (en n).symm a b' (hb n).2,
    fun n ↦ ⟨en n⟩⟩
  intro n i hi
  let F := proEtaleConstantRingPullback (SpTowerShriek.R ell E n) v.left
  let eH := (DerivedCategory.homologyFunctor _ i).mapIso (en n) ≪≫
    ((F.mapDerivedCategoryHomologyFunctorIso i).app
      ((spDerivedCoefficientEvaluation ell E Y.left (q.abelian Y.left) n).obj K)).symm
  exact (F.map_isZero (_hcoh n i hi)).of_iso eH

private theorem tower_ctf_iso (T : Scheme.{u})
    {K L : spDerivedCoefficientTowers ell E T (q.abelian T)} (e : K ≅ L)
    (h : spConstructibleTorTowers ell E T (q.abelian T) K) :
    spConstructibleTorTowers ell E T (q.abelian T) L := by
  refine ⟨fun n ↦ intrinsic_ctf_iso T _
    ((spDerivedCoefficientEvaluation ell E T (q.abelian T) n).mapIso e) (h.1 n), ?_⟩
  obtain ⟨a, z, c, d, haz, hcd, hv⟩ := h.2
  refine ⟨a, z, c, d, haz, hcd, fun n ↦ ⟨?_, ?_⟩⟩
  · intro i hi
    exact ((hv n).1 i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
      ((spDerivedCoefficientEvaluation ell E T (q.abelian T) n).mapIso e)).symm
  · exact intrinsic_tor_iso T _
      ((spDerivedCoefficientEvaluation ell E T (q.abelian T) n).mapIso e)
      c d (hv n).2

private theorem tower_pullback_mem
    (D : FiniteFieldDatum.{u}) (hne : ell ≠ D.p)
    (Y Y' : Over (Spec (.of D.k)))
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    (v : Y' ⟶ Y) (K : spDerivedCoefficientTowers ell E Y.left (q.abelian Y.left))
    (hK : spConstructibleTorTowers ell E Y.left (q.abelian Y.left) K) :
    spConstructibleTorTowers ell E Y'.left (q.abelian Y'.left)
      ((towerPullback ell E b o q v.left).obj K) := by
  obtain ⟨c, e, a, z, hce, haz, hv⟩ := hK.2
  have h := tower_bounds ell E b o q D hne Y Y' v K a z c e haz hce hK.1
    (fun n ↦ (hv n).1) (fun n ↦ (hv n).2)
  exact ⟨h.1, c, e, a, z, hce, haz, fun n ↦ ⟨h.2.1 n, h.2.2.1 n⟩⟩

/-- Identify the actual ell-power coefficient with the uniformizer quotient of
index r(n+1), by the equality of the defining ideals, induced by the identity of O_E.
Source: blueprint smooth-purity base-change factors, ramification-index clause
(blueprint: lem-sp-proetale-ctf-pullback-domains). -/
def towerResidueTransport (T : Scheme.{u}) (n : ℕ) :
    proEtaleDerivedCategory T (SpTowerShriek.R ell E n) ⥤
      proEtaleDerivedCategory T
        (Padic.coefficientExtensionRing ell E (b.ramification * (n + 1))) :=
  SpTowerShriek.quotientTransport ell E T _ _ (b.ideals n)

/-- The actual coefficient tower in degree zero belongs to the uniform category.
Source: blueprint smooth-purity base-change factors, coefficient object B_Y
(blueprint: lem-sp-proetale-ctf-pullback-domains).

Proof: each coefficient sheaf is constant of rank one over itself, hence flat
and constructible. Its degree-zero complex has cohomological and Tor intervals
[0,0]. These intervals are independent of the level. The section-preserving
realization identifies its strict transitions with the quotient maps. -/
theorem tower_unit (T : Scheme.{u}) :
    spConstructibleTorTowers ell E T (q.abelian T)
      (SpTowerGamma.originalUnit ell E b q T) := by
  exact SpFiniteOrientation.unit_tower_mem ell E b q T

/-- Exceptional inverse image of the actual tower coefficient unit, in the
section-preserving system presentation of the ordinary tower derived category.
Source: blueprint smooth-purity base-change factors, omega_(f,B)
(blueprint: lem-sp-proetale-ctf-pullback-domains). -/
def towerOmega {X Y : Scheme.{u}}
    (G : SpTowerCalculus.C ell E b q Y ⥤ SpTowerCalculus.C ell E b q X) :
    SpTowerShriek.D ell E X :=
  (SpTowerGamma.exceptional ell E b q G).obj
    ⟨SpTowerGamma.originalUnit ell E b q Y, tower_unit ell E b q Y⟩

/-- The canonical three-factor tensor comparison is formed in the actual ordinary
system derived category before any finite evaluation. No family of level maps is
lifted to a derived tower map.
Source: blueprint smooth-purity base-change factors, proof (2)
(blueprint: lem-sp-proetale-ctf-pullback-domains). -/
def towerComparison {X' X Y' Y : Scheme.{u}}
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (sq : IsPullback u f' f v)
    (W : SpTowerShriek.D ell E X) (W' : SpTowerShriek.D ell E X')
    (K : SpTowerShriek.D ell E Y)
    (e1 : (SpTowerShriek.pull ell E b (o.geometry u)).obj W ≅ W') :
    (SpTowerShriek.pull ell E b (o.geometry u)).obj
        ((SpTowerShriek.tensor ell E b X).obj
          ((SpTowerShriek.pull ell E b (o.geometry f)).obj K, W)) ≅
      (SpTowerShriek.tensor ell E b X').obj
        ((SpTowerShriek.pull ell E b (o.geometry f')).obj
          ((SpTowerShriek.pull ell E b (o.geometry v)).obj K), W') :=
  ((o.geometry u).tensorPullback.app
    ((SpTowerShriek.pull ell E b (o.geometry f)).obj K, W)) ≪≫
    (SpTowerShriek.tensor ell E b X').mapIso
      (((SpTowerShriek.square ell E b o u f' f v sq.w).symm.app K).prod e1)

/-- Both tensor-map sources in the tower case lie in the same full uniformly bounded
constructible finite-Tor category as the restricted smooth adjunction.
Source: blueprint smooth-purity base-change factors, proof (2)
(blueprint: lem-sp-proetale-ctf-pullback-domains).

Proof: (1) Apply tower_bounds to v. No normalization is used.
(2) det-sp-tower-gamma supplies the oriented tensor source, in the ordinary
uniformly bounded constructible finite-Tor category, for f and for its smooth
base change f'. Smoothness and the same pure dimension are preserved by base
change (lem-sbc-smooth-relative-dimension-permanence).
(3) Apply tower_bounds to u and the tensor source for f. This gives the second
membership assertion. The first is the tensor-source assertion for f' and v*K.
(4) towerComparison is the actual monoidal comparison followed by the inverse
composition square comparison and 1 tensor e1. Its factors are isomorphisms in
the system derived category, hence also in the full restricted category after
transport by the section-preserving realization. The adjunction and its Hom
bijection are exactly det-sp-tower-gluing; both resulting objects are its inputs. -/
theorem tower_smooth_domains
    (D : FiniteFieldDatum.{u}) (_hne : ell ≠ D.p)
    (X' X Y' Y : Over (Spec (.of D.k)))
    [IsSeparated X'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated Y'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (u : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (v : Y' ⟶ Y)
    (_sq : IsPullback u.left f'.left f.left v.left)
    (d : ℕ) [IsSeparated f.left] [SmoothOfRelativeDimension d f.left]
    (cf : Compactification f.left) (cf' : Compactification f'.left)
    (hF : ∀ M : SpTowerCalculus.C ell E b q X.left,
      spConstructibleTorTowers ell E Y.left (q.abelian Y.left)
        ((SpTowerCalculus.F ell E b o q cf).obj M.obj))
    (hF' : ∀ M : SpTowerCalculus.C ell E b q X'.left,
      spConstructibleTorTowers ell E Y'.left (q.abelian Y'.left)
        ((SpTowerCalculus.F ell E b o q cf').obj M.obj))
    (G : SpTowerCalculus.C ell E b q Y.left ⥤ SpTowerCalculus.C ell E b q X.left)
    (G' : SpTowerCalculus.C ell E b q Y'.left ⥤ SpTowerCalculus.C ell E b q X'.left)
    (_adj : SpTowerGluing.support ell E b o q cf hF ⊣ G)
    (_adj' : SpTowerGluing.support ell E b o q cf' hF' ⊣ G')
    (K : SpTowerCalculus.C ell E b q Y.left)
    (_e1 : (SpTowerShriek.pull ell E b (o.geometry u.left)).obj
      (towerOmega ell E b q G) ≅ towerOmega ell E b q G') :
    spConstructibleTorTowers ell E X'.left (q.abelian X'.left)
      ((SpTowerCalculus.realization ell E b X'.left (q.abelian X'.left)).inverse.obj
        ((SpTowerShriek.tensor ell E b X'.left).obj
          ((SpTowerShriek.pull ell E b (o.geometry f'.left)).obj
            ((SpTowerShriek.pull ell E b (o.geometry v.left)).obj
              ((SpTowerGamma.realization ell E b q Y.left).obj K)),
            towerOmega ell E b q G'))) ∧
    spConstructibleTorTowers ell E X'.left (q.abelian X'.left)
      ((SpTowerCalculus.realization ell E b X'.left (q.abelian X'.left)).inverse.obj
        ((SpTowerShriek.pull ell E b (o.geometry u.left)).obj
          ((SpTowerShriek.tensor ell E b X.left).obj
            ((SpTowerShriek.pull ell E b (o.geometry f.left)).obj
              ((SpTowerGamma.realization ell E b q Y.left).obj K),
              towerOmega ell E b q G)))) := by
  let := isNoetherian_of_locallyOfFiniteType X.hom
  let FX := SpTowerCalculus.realization ell E b X.left (q.abelian X.left)
  let FX' := SpTowerCalculus.realization ell E b X'.left (q.abelian X'.left)
  let P := (SpTowerShriek.pull ell E b (o.geometry f.left)).obj
    ((SpTowerGamma.realization ell E b q Y.left).obj K)
  let N := G.obj ⟨SpTowerGamma.originalUnit ell E b q Y.left,
    tower_unit ell E b q Y.left⟩
  let S := (SpTowerShriek.tensor ell E b X.left).obj (P, towerOmega ell E b q G)
  have hP := tower_pullback_mem ell E b o q D _hne Y X f K.obj K.property
  have hS : spConstructibleTorTowers ell E X.left (q.abelian X.left)
      (FX.inverse.obj S) := by
    have h := UniformTowerTensorClosure.tensor_mem ell E b q X.left
      (FX.inverse.obj P) N.obj hP N.property
    exact tower_ctf_iso ell E b q X.left
      (FX.inverse.mapIso ((SpTowerShriek.tensor ell E b X.left).mapIso
        ((FX.counitIso.app P).prod (Iso.refl _)))) h
  have hsecond : spConstructibleTorTowers ell E X'.left (q.abelian X'.left)
      (FX'.inverse.obj ((SpTowerShriek.pull ell E b (o.geometry u.left)).obj S)) := by
    have h := tower_pullback_mem ell E b o q D _hne X X' u (FX.inverse.obj S) hS
    exact tower_ctf_iso ell E b q X'.left
      (FX'.inverse.mapIso ((SpTowerShriek.pull ell E b (o.geometry u.left)).mapIso
        (FX.counitIso.app S))) h
  refine ⟨?_, hsecond⟩
  exact tower_ctf_iso ell E b q X'.left
    (FX'.inverse.mapIso (towerComparison ell E b o u.left f'.left f.left v.left
      _sq (towerOmega ell E b q G) (towerOmega ell E b q G')
      ((SpTowerGamma.realization ell E b q Y.left).obj K) _e1)) hsecond

end Towers
end AlgebraicGeometry.ProEtale.CtfPullbackDomains

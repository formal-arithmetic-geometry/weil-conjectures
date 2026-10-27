/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q80
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.Paper.ScalarPerfectDualRealization
public import Sheaf.Algebra.Homology.RingedOrdinaryEvaluationLocalization
public import Sheaf.Topology.ProfiniteCondensedRing
public import Sheaf.Paper.FiniteFreeDualChainModels
import Sheaf.Paper.FiniteFreeOrdinaryChainComparison
import Sheaf.Paper.NativeOrdinaryEvaluationLocalization
import all Sheaf.Paper.ScalarPerfectFiniteFree
import Sheaf.CategoryTheory.RingedSiteFiniteRetractDualExact
import Sheaf.Algebra.Homology.IndependentBoundedExactTermHom
public import Mathlib.CategoryTheory.Sites.LocalSite

/-! # Signed finite-free dual comparison in native internal modules

Source: Stacks Project, Tags 08JH and 08JJ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
open scoped CategoryTheory.Obj
open ZeroObject
namespace AlgebraicGeometry.ProEtale.FiniteFreeDualComparison
variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
  (A : Type (u + 1)) [CommRing A]
  (α : (constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).obj
    (CommRingCat.of A) ⟶ ring Λ X)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private def scalarUnitIso :
    (SheafOfModules.scalarPerfectFunctor (Scheme.ProEt.topology X) A α).obj
      (ModuleCat.of A A) ≅
        SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring Λ X)) := by
  have := SheafOfModules.constantUnitHom_isIso (Scheme.ProEt.topology X) A
  exact (SheafOfModules.scalarPerfectExtensionFunctor (Scheme.ProEt.topology X) α).mapIso
    (asIso (SheafOfModules.constantUnitHom (Scheme.ProEt.topology X) A)) ≪≫
      SheafOfModules.scalarExtensionUnitIso.{u + 1, u, u + 1} α

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteFreeSectionIso (V : ModuleCat.{u + 1} A)
    [Module.Finite A V] [Module.Free A V] :
    ∃ n : ℕ, Nonempty (((equivalence Λ X).functor.obj
      ((realization Λ X A α).obj V)) ≅
        SheafOfModules.free (R := (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring Λ X))
          (ULift.{u + 1} (Fin n))) := by
  classical
  let b := Module.Free.chooseBasis A V
  let n := Fintype.card (Module.Free.ChooseBasisIndex A V)
  let e : V ≅ ModuleCat.of A (Fin n → A) :=
    (b.reindex (Fintype.equivFin (Module.Free.ChooseBasisIndex A V))).equivFun.toModuleIso
  let G := SheafOfModules.scalarPerfectFunctor (Scheme.ProEt.topology X) A α
  have : G.Additive := SheafOfModules.scalarPerfectFunctor_additive _ _ _
  let f : G.obj (ModuleCat.of A (Fin n → A)) ≅
      ∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring Λ X)) :=
    G.mapIso (ModuleCat.piIsoPi (fun _ : Fin n ↦ ModuleCat.of A A)).symm ≪≫
      PreservesProduct.iso G (fun _ : Fin n ↦ ModuleCat.of A A) ≪≫
        Pi.mapIso (fun _ : Fin n ↦ scalarUnitIso Λ X A α)
  let B := SheafOfModules.unit ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring Λ X))
  have : HasFiniteBiproducts (Modules Λ X) := HasFiniteBiproducts.of_hasFiniteProducts
  let g : (∏ᶜ fun _ : Fin n ↦ B) ≅
      SheafOfModules.free (R := (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring Λ X)) (ULift.{u + 1} (Fin n)) :=
    (biproduct.isoProduct _).symm ≪≫ biproduct.isoCoproduct _ ≪≫
      Sigma.reindex (Equiv.ulift.symm : Fin n ≃ ULift.{u + 1} (Fin n)) (fun _ ↦ B)
  exact ⟨n, ⟨(sectionChartIso Λ X A α).app V ≪≫ G.mapIso e ≪≫ f ≪≫ g⟩⟩

private theorem exactTermHom (V : ModuleCat.{u + 1} A)
    [Module.Finite A V] [Module.Free A V] (S : ShortComplex (Modules Λ X))
    (hS : S.ShortExact) :
    ∃ hz : SheafOfModules.homObjMap (R := ring Λ X)
        (𝟙 ((equivalence Λ X).functor.obj ((realization Λ X A α).obj V))) S.f ≫
      SheafOfModules.homObjMap (R := ring Λ X)
        (𝟙 ((equivalence Λ X).functor.obj ((realization Λ X A α).obj V))) S.g = 0,
      (ShortComplex.mk
        (SheafOfModules.homObjMap (R := ring Λ X)
          (𝟙 ((equivalence Λ X).functor.obj ((realization Λ X A α).obj V))) S.f)
        (SheafOfModules.homObjMap (R := ring Λ X)
          (𝟙 ((equivalence Λ X).functor.obj ((realization Λ X A α).obj V))) S.g)
          hz).ShortExact := by
  obtain ⟨n, ⟨e⟩⟩ := finiteFreeSectionIso Λ X A α V
  exact (SheafOfModules.ringedSite_finite_retract_dual_exact.{u + 1, u, u}
    (R := ring Λ X) n _ e.hom e.inv e.hom_inv_id).2.2.2.2.2.1 S hS

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryHom_additive (T : CochainComplex (Modules Λ X) ℤ) :
    ((homComplexFunctor (R := ring Λ X)).obj (op T)).Additive := by
  constructor
  intro F G f g
  ext n : 1
  apply homComplex_hom_ext
  intro p q hpq
  simp only [HomologicalComplex.add_f_apply, Preadditive.add_comp]
  rw [homComplexFunctor_obj_map_f_π.{u + 1, u, u + 1, u + 1} (f + g),
    homComplexFunctor_obj_map_f_π.{u + 1, u, u + 1, u + 1} f,
    homComplexFunctor_obj_map_f_π.{u + 1, u, u + 1, u + 1} g,
    HomologicalComplex.add_f_apply]
  rw [← Preadditive.comp_add]
  congr 1

private theorem section_acyclic (T : CochainComplex (Internal Λ X) ℤ) :
    T.Acyclic ↔ ((complexForward Λ X).obj T).Acyclic := by
  exact forall_congr' fun n ↦
    ((T.sc n).exact_map_iff_of_faithful (equivalence Λ X).functor).symm

private theorem reflect_cancel_iso {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) [L.IsEquivalence] {U V W : C} (f : U ⟶ V) (g : V ⟶ W)
    [IsIso f] [IsIso (L.map (f ≫ g))] : IsIso g := by
  have : IsIso (f ≫ g) := isIso_of_reflects_iso _ L
  exact IsIso.of_isIso_comp_left f g

attribute [local irreducible] evaluationTranspose sectionDerivedHomMap localizationTensorMap
  CoefficientClosedStructure.tensor CoefficientTensorModels.iso forward

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The scalar signed dual, its generator-normalized chain comparison, the finite-basis
inverse, invariance under every K-injective augmentation, and the native derived
normalization. No scalar-flatness assumption or bound on the target appears.

Source: Stacks 08JH and 08JJ; main-20261015,
det-lem-int-tensor-product.proof.md, first paragraph
(blueprint: lem-sfb-finite-free-dual-chain-comparison).

Proof, following the seven DAG steps:
1. Use internal_section_tensor_comparison and internal_section_scalar_adjunction to
identify the native scalar chart and scalar dual with the ordinary balanced scalar
extensions. These comparisons preserve actions, pure tensors, total differentials,
acyclicity and K-flatness; they introduce no tensor structure by choice.
2. Apply scalarPerfectDualRealization to finite free terms. The dual coordinates
in degree b are Hom_A(P^(-b),A), and their differential is (-1)^(b+1) times
precomposition. Scalar extension preserves finite free splittings and finite bounds,
including rank zero, without any flatness of the scalar ring map.
3. On a finite free term define evaluation by y tensor phi maps to (x maps to
phi(x)y). The inverse in any finite basis is the sum of f(e_j) tensor e_j^*.
The two dual-basis expansions prove both composites are identities. Balanced
sheafification extends these formulas uniquely; hence they are basis independent
and commute with restriction on every slice.
4. Use bounded evaluation assembly and the scalar-dual identification kappa.
Only finitely many source degrees occur even for unbounded F. The tensor
 differential gives d_F y tensor phi + (-1)^(a+b+1)y tensor (phi d_P);
the Hom differential gives d_F f - (-1)^(a+b) f d_P. Thus the comparison is a
chain map without an extra sign. Its inverse is the finite sum written below.
Naturality follows by evaluating on every pure tensor and Hom projection.
5. Bounded exact-term Hom sends every quasi-isomorphism to a quasi-isomorphism,
in particular every K-injective augmentation. Apply this to 0 → Z for acyclic Z;
the chain comparison implies Tot(Z tensor D_T) is acyclic. Reflect K-flatness
through the section equivalence. The augmentation for the coefficient unit
identifies the scalar dual with its derived internal Hom.
6. First use a flat-term K-flat resolution of F. Ordinary evaluation localization
identifies the specified formula with the closed evaluation transpose. For general
unbounded F the natural square of tensor and Hom comparisons and two-out-of-three
carry that equality back from the resolution. K-flat localization supplies the
invertible tensor comparison for the original F because D_T is K-flat.
7. The evaluation-normalized module-object/ringed-site derived comparison carries
this equality to the actual native closed adjunction, giving delta and the final
map equality. Its evaluation transpose is invertible. All constructions restrict
to the identical local formulas on every slice; neither boundedness of F nor
flatness over the constant scalar ring was used. -/
theorem finiteFreeDualChainComparison
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hfinite : ∀ i : ℤ, Module.Finite A (P.X i))
    (hfree : ∀ i : ℤ, Module.Free A (P.X i))
    (l h : ℤ) (hbounded : ∀ i : ℤ, i < l ∨ h < i → IsZero (P.X i)) :
    ∃ κ : (complexForward Λ X).obj (chart Λ X A α (scalarDual A P)) ≅
        homComplex.{u + 1, u, u + 1, u + 1} (R := ring Λ X) ((complexForward Λ X).obj (chart Λ X A
          α P))
          (ringedTensorUnitComplex.{u + 1, u, u} (Scheme.ProEt.topology X) (ring Λ X)),
    (∀ (b : ℤ) (U : X.ProEtᵒᵖ) (r r' : (ring Λ X).obj.obj U)
      (z : (scalarDual A P).X b) (x : P.X (-b)),
      ringedOrdinaryDualValue.{u + 1, u, u} (Scheme.ProEt.topology X) (ring Λ X)
        ((complexForward Λ X).obj (chart Λ X A α P)) b (-b) (neg_add_cancel b) U
        ((κ.hom.f b).val.app U (scalarSection Λ X A α _ U r z))
        (scalarSection Λ X A α _ U r' x) =
          r * r' * scalar Λ X A α U ((CategoryTheory.ScalarPerfectDual.coordinates A P b).hom
            z x)) ∧
    ∃ ε : ∀ F : CochainComplex (Internal Λ X) ℤ,
        (complexForward Λ X).obj
            (internalTotalTensor Λ X F (chart Λ X A α (scalarDual A P))) ≅
          homComplex.{u + 1, u, u + 1, u + 1} (R := ring Λ X) ((complexForward Λ X).obj (chart Λ X
            A α P))
            ((complexForward Λ X).obj F),
    (∀ F : CochainComplex (Internal Λ X) ℤ,
      ∃ aEF : (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X)).obj
          ((complexForward Λ X).obj F,
            homComplex.{u + 1, u, u + 1, u + 1} (R := ring Λ X) ((complexForward Λ X).obj (chart Λ
              X A α P))
              (ringedTensorUnitComplex.{u + 1, u, u} (Scheme.ProEt.topology X) (ring Λ X))) ⟶
            homComplex.{u + 1, u, u + 1, u + 1} (R := ring Λ X) ((complexForward Λ X).obj (chart Λ
              X A α P))
              ((complexForward Λ X).obj F),
        RingedOrdinaryEvaluationFormula.{u + 1, u, u} (Scheme.ProEt.topology X) (ring Λ X)
          ((complexForward Λ X).obj (chart Λ X A α P)) ((complexForward Λ X).obj F) aEF ∧
        (ε F).hom = (totalComparison Λ X F (chart Λ X A α (scalarDual A P))).hom ≫
          (coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X)).map
            (𝟙 ((complexForward Λ X).obj F), κ.hom) ≫ aEF) ∧
    (∀ {F G : CochainComplex (Internal Λ X) ℤ} (f : F ⟶ G),
      (complexForward Λ X).map (tensorTargetMap Λ X A α P f) ≫ (ε G).hom =
        (ε F).hom ≫ ((homComplexFunctor.{u + 1, u, u + 1, u + 1} (R := ring Λ X)).obj
          (op ((complexForward Λ X).obj (chart Λ X A α P)))).map
            ((complexForward Λ X).map f)) ∧
    (∀ (F : CochainComplex (Internal Λ X) ℤ) (n : ℤ) (U : X.ProEtᵒᵖ)
      (f : ((homComplex.{u + 1, u, u + 1, u + 1} (R := ring Λ X)
        ((complexForward Λ X).obj (chart Λ X A α P)) ((complexForward Λ X).obj F)).X n).val.obj U)
      (ι : ℤ → Type (u + 1)) [∀ b : ℤ, Fintype (ι b)]
      (e : ∀ b : ℤ, Module.Basis (ι b) A (P.X (-b))),
      ((totalComparison Λ X F (chart Λ X A α (scalarDual A P))).hom.f n).val.app U
          (((ε F).inv.f n).val.app U f) =
        ∑ b : ↥(Finset.Icc (-h) (-l)), ∑ j : ι b.val,
          coefficientTensorGenerator.{u, u + 1, u} (Scheme.ProEt.topology X) (ring Λ X)
            ((complexForward Λ X).obj F)
            ((complexForward Λ X).obj (chart Λ X A α (scalarDual A P)))
            (n - b.val) b.val n (by omega) U
            (ringedOrdinaryHomValue.{u + 1, u, u} (Scheme.ProEt.topology X) (ring Λ X)
              ((complexForward Λ X).obj (chart Λ X A α P)) ((complexForward Λ X).obj F)
              n (-b.val) (n - b.val) (by omega) U f
              (scalarSection Λ X A α _ U 1 (e b.val j)))
            (scalarSection Λ X A α _ U 1
              ((CategoryTheory.ScalarPerfectDual.coordinates A P b.val).inv
                ((e b.val).coord j)))) ∧
    (∀ Z : CochainComplex (Internal Λ X) ℤ, Z.Acyclic →
      (internalTotalTensor Λ X Z (chart Λ X A α (scalarDual A P))).Acyclic) ∧
    (∀ (F : CochainComplex (Internal Λ X) ℤ)
      (I : CochainComplex (Modules Λ X) ℤ) (η : (complexForward Λ X).obj F ⟶ I),
      QuasiIso η → I.IsKInjective →
        QuasiIso (((homComplexFunctor.{u + 1, u, u + 1, u + 1} (R := ring Λ X)).obj
          (op ((complexForward Λ X).obj (chart Λ X A α P)))).map η)) ∧
    ∃ (S : CoefficientClosedStructure (hom Λ X))
      (M : CoefficientTensorModels.{u, u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) S)
      (t : TensorComparison Λ X S M)
      (θ : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
        ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X),
      (∀ K N : DerivedCategory.{u + 1} (Internal Λ X),
        (forward Λ X).map
          ((@BraidedCategory.braiding _ _ _ (internalBraiding Λ X)
              (((CondensedRing.derivedHom Λ X).obj (op K)).obj N) K).hom ≫
            (CondensedRing.derivedTensorHomAdjunction Λ K).counit.app N) =
          (t.iso.hom.app (((CondensedRing.derivedHom Λ X).obj (op K)).obj N, K)) ≫
            S.tensor.map
              (X := ((forward Λ X).obj (((CondensedRing.derivedHom Λ X).obj (op K)).obj N),
                (forward Λ X).obj K))
              (Y := ((hom Λ X).obj (op ((forward Λ X).obj K), (forward Λ X).obj N),
                (forward Λ X).obj K))
              (θ.hom.app (op K, N), 𝟙 ((forward Λ X).obj K)) ≫
            S.evaluation ((forward Λ X).obj K) ((forward Λ X).obj N)) ∧
    ∃ δ : DerivedCategory.Q.{u + 1}.obj (chart Λ X A α (scalarDual A P)) ≅
        ((CondensedRing.derivedHom Λ X).obj
          (op (DerivedCategory.Q.{u + 1}.obj (chart Λ X A α P)))).obj
            (nativeUnit Λ X),
    ∀ F : CochainComplex (Internal Λ X) ℤ,
      IsIso (localizationTensorMap Λ X F (chart Λ X A α (scalarDual A P))) ∧
      IsIso (evaluationTranspose Λ X (DerivedCategory.Q.{u + 1}.obj (chart Λ X A α P))
        (DerivedCategory.Q.{u + 1}.obj F)) ∧
      (forward Λ X).map
          ((((CondensedRing.derivedTensor Λ X).obj (DerivedCategory.Q.{u + 1}.obj F)).map
            δ.hom) ≫
            evaluationTranspose Λ X (DerivedCategory.Q.{u + 1}.obj (chart Λ X A α P))
              (DerivedCategory.Q.{u + 1}.obj F)) ≫
          sectionDerivedHomMap Λ X θ (chart Λ X A α P) F =
        (forward Λ X).map
            (localizationTensorMap Λ X F (chart Λ X A α (scalarDual A P))) ≫
          (localizationIso Λ X).hom.app
            (internalTotalTensor Λ X F (chart Λ X A α (scalarDual A P))) ≫
          DerivedCategory.Q.{u + 1}.map (ε F).hom ≫
          ringedOrdinaryHomComparison.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X) (ring Λ X)
            ((complexForward Λ X).obj (chart Λ X A α P)) ((complexForward Λ X).obj F) := by
  classical
  obtain ⟨κ, hκ, ε, hevaluation, hnatural, hinverse⟩ :=
    finiteFreeOrdinaryChainComparison Λ X A α P hfinite hfree l h hbounded
  have hbound : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      IsZero (((complexForward Λ X).obj (chart Λ X A α P)).X n) := by
    refine ⟨l, h, fun n hn ↦ ?_⟩
    exact (equivalence Λ X).functor.map_isZero
      ((realization Λ X A α).map_isZero (hbounded n hn))
  have hexact (n : ℤ) (S : ShortComplex (Modules Λ X)) (hS : S.ShortExact) := by
    have := hfinite n
    have := hfree n
    exact exactTermHom Λ X A α (P.X n) S hS
  have hhom (F G : CochainComplex (Modules Λ X) ℤ) (f : F ⟶ G)
      (hf : QuasiIso f) : QuasiIso (((homComplexFunctor (R := ring Λ X)).obj
        (op ((complexForward Λ X).obj (chart Λ X A α P)))).map f) := by
    have := hf
    exact
      CategoryTheory.SplitPerfectHom.quasiIso_homComplex_map_of_bounded_exact_terms.{u + 1, u, u}
      (Scheme.ProEt.topology X) (ring Λ X) _ hbound hexact f
  have hkflat (Z : CochainComplex (Internal Λ X) ℤ) (hZ : Z.Acyclic) :
      (internalTotalTensor Λ X Z (chart Λ X A α (scalarDual A P))).Acyclic := by
    let H := (homComplexFunctor (R := ring Λ X)).obj
      (op ((complexForward Λ X).obj (chart Λ X A α P)))
    have : H.Additive := ordinaryHom_additive Λ X _
    let z : (0 : CochainComplex (Modules Λ X) ℤ) ⟶ (complexForward Λ X).obj Z := 0
    have hz : QuasiIso z := by
      constructor
      intro n
      exact (quasiIsoAt_iff_exactAt z n
        (HomologicalComplex.acyclic_of_isZero _ (Limits.isZero_zero _) n)).mpr
          ((section_acyclic Λ X Z).mp hZ n)
    have : QuasiIso (H.map z) := hhom _ _ z hz
    have hH : (H.obj ((complexForward Λ X).obj Z)).Acyclic := by
      intro n
      exact (exactAt_iff_of_quasiIsoAt (H.map z) n).mp
        (HomologicalComplex.acyclic_of_isZero _ (H.map_isZero (Limits.isZero_zero _)) n)
    exact (section_acyclic Λ X _).mpr (fun n ↦ (hH n).of_iso (ε Z).symm)
  refine ⟨κ, hκ, ε, hevaluation, hnatural, hinverse, hkflat, ?_, ?_⟩
  · intro F I η hη _
    exact hhom _ _ η hη
  · obtain ⟨S, M, t, θ, hcounit, _⟩ := moduleObject_ringedSite_derived_comparison Λ X
    have hlocalized :=
      nativeOrdinaryEvaluationLocalization Λ X (chart Λ X A α P)
        (chart Λ X A α (scalarDual A P)) κ ε hevaluation hnatural hkflat hhom
          S M t θ hcounit
    obtain ⟨δ, hlocal⟩ := hlocalized
    refine ⟨S, M, t, θ, hcounit, δ, ?_⟩
    intro F
    obtain ⟨hμ, heq⟩ := hlocal F
    have := hμ
    let E := (complexForward Λ X).obj (chart Λ X A α P)
    let G := (complexForward Λ X).obj F
    have hη : QuasiIso ((coefficientHomAugmentation.{u, u + 1, u}
        (Scheme.ProEt.topology X) (ring Λ X)).app G) := by
      change QuasiIso ((CochainComplex.toKInjectiveResolution.{u + 1}
        (Modules Λ X)).app G)
      exact (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1}
        (Modules Λ X) G).2
    have : QuasiIso (ringedHomAugmentationMap.{u + 1, u, u}
        (Scheme.ProEt.topology X) (ring Λ X) E G) := hhom _ _ _ hη
    have : IsIso (DerivedCategory.Q.{u + 1}.map
        (ringedHomAugmentationMap.{u + 1, u, u}
          (Scheme.ProEt.topology X) (ring Λ X) E G)) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
    have hcomparison : IsIso (ringedOrdinaryHomComparison.{u + 1, u, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) E G) := by
      unfold ringedOrdinaryHomComparison
      infer_instance
    have hright : IsIso ((forward Λ X).map
        (localizationTensorMap Λ X F (chart Λ X A α (scalarDual A P))) ≫
          (localizationIso Λ X).hom.app
            (internalTotalTensor Λ X F (chart Λ X A α (scalarDual A P))) ≫
          DerivedCategory.Q.{u + 1}.map (ε F).hom ≫
          ringedOrdinaryHomComparison.{u + 1, u, u, u + 1}
            (Scheme.ProEt.topology X) (ring Λ X) E G) := by infer_instance
    have hθ : IsIso (sectionDerivedHomMap Λ X θ (chart Λ X A α P) F) := by
      have : IsIso (((localizationIso Λ X).inv.app (chart Λ X A α P)).op,
          (localizationIso Λ X).hom.app F) :=
        (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
      unfold sectionDerivedHomMap
      infer_instance
    have hmap : IsIso ((forward Λ X).map
        ((((CondensedRing.derivedTensor Λ X).obj (DerivedCategory.Q.{u + 1}.obj F)).map
          δ.hom) ≫ evaluationTranspose Λ X
            (DerivedCategory.Q.{u + 1}.obj (chart Λ X A α P))
            (DerivedCategory.Q.{u + 1}.obj F))) :=
      IsIso.of_isIso_fac_right heq
    have : (forward Λ X).IsEquivalence := by
      unfold forward
      infer_instance
    have heval : IsIso (evaluationTranspose Λ X
        (DerivedCategory.Q.{u + 1}.obj (chart Λ X A α P))
        (DerivedCategory.Q.{u + 1}.obj F)) :=
      reflect_cancel_iso (forward Λ X)
        (((CondensedRing.derivedTensor Λ X).obj (DerivedCategory.Q.{u + 1}.obj F)).map
          δ.hom) _
    exact ⟨hμ, heval, heq⟩

end AlgebraicGeometry.ProEtale.FiniteFreeDualComparison

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.LineSubbundleProjectiveDivisorData
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleQuotientEpi
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleSymmetricAlgebraIso
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.AlgebraicGeometry.Modules.Determinant
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalGeometry
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.Modules.LocalSectionOfEpi
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientGeometry
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.SymmetricProjSectionCompatibility
import WeilConjectures.AlgebraicGeometry.Modules.PullbackSections
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleCoefficientComparison
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleBaseChangeTheta
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundlePullbackSectionNormalization
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundlePullbackUnitLaws
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The projective divisor of a line subbundle

Source: Stacks Project, Tag 0FI5, `proposition-chern-class`, line-subbundle paragraph;
Tags 01OB, 01OE and 01X0.
(blueprint: lem-pur-line-subbundle-projective-divisor-core).

Proof:
1. The degree-one symmetric generators cover every affine Proj chart. The corresponding
   sections freely generate the degree-one twist on their standard opens. Transport through
   the specified twist charts and descend along the affine base cover to prove that the
   tautological line of every realization is invertible.
2. Compare an arbitrary realization with the normalized projectivization supplied by
   `exists_completeFlagProjectivization`, using coefficient base change along the identity.
   The comparison is an isomorphism because it is a pullback of the identity. Its specified
   theta preserves the quotient. Transporting existence and uniqueness of classifying maps
   gives the normalized quotient-line universal property for the arbitrary realization.
   The adjunction units identify the two pullback-composition conventions explicitly.
3. Classify the quotient p_Q*F -> p_Q*G -> Q.L to construct i and its normalized theta.
   The tautological map phi : p_P*L -> P.L pulls back to zero because iota followed by pi
   is zero. Let z : Z -> P be its zero scheme. Pullback of the tautological epimorphism to
   Z factors through p_Z*G by right exactness, giving an epimorphic line quotient epsilon.
   Classify epsilon to obtain v : Z -> Q. Uniqueness for P gives v followed by i equal to z.
   Vanishing of phi on Q also gives a closed-subscheme lift k : Q -> Z with k followed by z
   equal to i. Pulling epsilon back along k gives the original quotient on Q: the equality
   follows after precomposing by the epimorphism p_Q*pi, using the quotient square for i.
   Uniqueness for Q gives k followed by v equal to the identity. Cancellation against the
   monomorphism z gives v followed by k equal to the identity. Thus k is an isomorphism,
   i is a closed immersion and its kernel is the zero ideal of phi, equivalently of the
   prescribed adjoint section.
4. Take adapted local frames for the short exact sequence, with the first frame vector
   spanning L. Its symmetric-algebra image is regular: a basis identifies it with a
   polynomial variable over the arbitrary base ring. Localization preserves regularity,
   so multiplication by this element defines a monomorphism from the unit to the twist.
   The specified quotient-generator equation identifies it with phi on the affine Proj
   chart, after trivializing the pulled-back line. These charts cover P, so phi is mono.
   On any common affine trivialization of its two invertible modules, injectivity forces
   the coefficient b to be a nonzerodivisor. The zero ideal there is (b), so it is invertible.
   This argument includes nonreduced base rings and empty schemes.
5. The normalized zero-locus comparison for the dual section identifies the dual section
   line with the kernel ideal, carrying its inclusion to the dual section. Dualize this
   isomorphism and use the bidual isomorphism of an invertible module to construct delta.
   Naturality of biduality and its compatibility with the specified dual-unit isomorphism
   give exactly the claimed canonical-section equality. Kernel invertibility also gives
   the effective Cartier-center assertion.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules
namespace AlgebraicGeometry
open Scheme.Modules


attribute [local irreducible] Scheme.Modules.tensorPullback
  projectiveBundleTensorPullbackIso projectiveBundlePullbackId projectiveBundlePullbackComp
  projectiveBundlePullbackCongr projectiveBundlePullbackAdjunction projectiveBundlePullbackUnitIso
  projectiveBundlePullbackSection

private theorem congr_app_refl {X Y : Scheme.{u}} (f : X ⟶ Y) (F : Y.Modules)
    (e : f = f) : (projectiveBundlePullbackCongr e).app F = Iso.refl _ := by
  simp [projectiveBundlePullbackCongr]
  rfl

private theorem realization_invertible {S : Scheme.{u}} {F : S.Modules}
    (D : ProjectiveBundleRealization S F) : D.L.IsInvertible := by
  have hlocal (U : S.affineOpens) :
      ((Scheme.Modules.pullback (D.A.data.relProjι U)).obj D.L).IsFiniteLocallyFreeOfRank 1 := by
    have hι (m : F.val.obj (op U.1)) :
        D.A.sectionEquiv U (SymmetricAlgebra.ι _ _ m) ∈ D.A.data.grading U 1 := by
      apply (D.A.sectionEquiv_grade U 1 _).mp
      rw [projectiveBundleSymmetricDegree_eq, pow_one]
      exact LinearMap.mem_range_self _ _
    let : (Proj.twist (D.A.data.grading U) 1).IsInvertible :=
      Proj.isInvertible_twist _ 1 fun x ↦ by
        obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp
          ((realization_chart_cover D.A U hι).ge (Set.mem_univ x))
        exact ⟨_, hι m, hm⟩
    let : ((Scheme.Modules.tensorPullback (D.A.data.relProjι U)).obj D.L).IsInvertible :=
      Scheme.Modules.IsInvertible.of_iso (D.twists.chart U).symm
    let : ((Scheme.Modules.pullback (D.A.data.relProjι U)).obj D.L).IsInvertible :=
      Scheme.Modules.IsInvertible.of_iso
        ((projectiveBundleTensorPullbackIso _).app D.L)
    have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
      ((Scheme.Modules.pullback (D.A.data.relProjι U)).obj D.L)
    exact (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one
      ((Scheme.Modules.pullback (D.A.data.relProjι U)).obj D.L)).mp this
  have := Scheme.Modules.isFiniteLocallyFreeOfRank_of_isOpenImmersion D.L
    D.A.data.relProjι D.A.data.iSup_opensRange_relProjι hlocal
  have := (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one D.L).mpr this
  exact Scheme.Modules.IsInvertible.of_sheafOfModules D.L

private theorem dualMap_comp {X : Scheme.{u}} {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) :
    Scheme.Modules.dualMap (f ≫ g) =
      Scheme.Modules.dualMap g ≫ Scheme.Modules.dualMap f :=
  (Scheme.Modules.dualFunctor X).map_comp g.op f.op

private theorem dualUnit_hom_app {X : Scheme.{u}} (U : X.Opens)
    (φ : Γ((𝟙_ X.Modules)ᵛ, U)) :
    ((Scheme.Modules.dualUnitIso (X := X)).hom).app U φ =
      φ.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U)) := by
  change (Scheme.Modules.dualEvaluation (𝟙_ X.Modules)).app U
    ((λ_ (𝟙_ X.Modules)ᵛ).inv.app U φ) = _
  rw [Scheme.Modules.leftUnitor_inv_app, dual_evaluation_tmul]
  rfl

set_option maxHeartbeats 600000 in
-- The unit and bidual constructions expand several sheaf restrictions in the kernel.
private theorem dualUnit_bidual {X : Scheme.{u}} :
    Scheme.Modules.dualUnitIso.inv ≫
      Scheme.Modules.dualMap ((Scheme.Modules.dualUnitIso (X := X)).hom) =
        SheafOfModules.bidual (R := X.sheaf) (𝟙_ X.Modules) := by
  apply (cancel_epi ((Scheme.Modules.dualUnitIso (X := X)).hom)).mp
  simp only [Iso.hom_inv_id_assoc]
  apply Scheme.Modules.hom_ext
  intro U
  ext φ
  refine PresheafOfModules.hom_ext (M₁ := _)
    (M₂ := PresheafOfModules.unit _) fun V ↦ ?_
  ext r
  change φ.app V (((Scheme.Modules.dualUnitIso (X := X)).hom).app V.unop.left r) =
    r.app (op (Over.mk (𝟙 V.unop.left)))
      ((𝟙_ X.Modules).presheaf.map V.unop.hom.op
        (((Scheme.Modules.dualUnitIso (X := X)).hom).app U φ))
  rw [dualUnit_hom_app, dualUnit_hom_app]
  have hφ := PresheafOfModules.app_unit_eq_smul φ V
    (r.app (op (Over.mk (𝟙 V.unop.left))) (1 : Γ(X, V.unop.left)))
  have hr := (r.app (op (Over.mk (𝟙 V.unop.left)))).hom.map_smul
    ((𝟙_ X.Modules).presheaf.map V.unop.hom.op
      (φ.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))))
    (1 : Γ(X, V.unop.left))
  let a : Γ(X, V.unop.left) := (𝟙_ X.Modules).presheaf.map V.unop.hom.op
    (φ.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U)))
  let b : Γ(X, V.unop.left) :=
    r.app (op (Over.mk (𝟙 V.unop.left))) (1 : Γ(X, V.unop.left))
  let f : Γ(X, V.unop.left) →ₗ[Γ(X, V.unop.left)] Γ(X, V.unop.left) :=
    (r.app (op (Over.mk (𝟙 V.unop.left)))).hom
  have hφ' : φ.app V b = b * a := hφ
  have hr' : f (a * 1) = a * b := hr
  exact hφ'.trans ((mul_comm b a).trans
    ((congrArg f (mul_one a)).symm.trans hr').symm)

private theorem ideal_comparison_transport {X : Scheme.{u}}
    {I J : X.IdealSheafData} (h : I = J) {M : X.Modules} (s : M ⟶ 𝟙_ X.Modules) :
    (∃ κ : M ≅ I.toModules, κ.hom ≫ I.toModulesι = s) →
      ∃ κ : M ≅ J.toModules, κ.hom ≫ J.toModulesι = s := by
  cases h
  exact id

private theorem dualMap_id {X : Scheme.{u}} (M : X.Modules) :
    Scheme.Modules.dualMap (𝟙 M) = 𝟙 Mᵛ :=
  (Scheme.Modules.dualFunctor X).map_id (op M)

private def dualIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) : Nᵛ ≅ Mᵛ where
  hom := Scheme.Modules.dualMap e.hom
  inv := Scheme.Modules.dualMap e.inv
  hom_inv_id := by rw [← dualMap_comp, e.inv_hom_id, dualMap_id]
  inv_hom_id := by rw [← dualMap_comp, e.hom_inv_id, dualMap_id]

private theorem section_divisor_comparison {X : Scheme.{u}} {M : X.Modules}
    [M.IsInvertible] (s : 𝟙_ X.Modules ⟶ M) (hs : s.zeroLocus.IsInvertible) :
    ∃ δ : s.zeroLocus.toModulesᵛ ≅ M,
      Scheme.Modules.dualUnitIso.inv ≫
        Scheme.Modules.dualMap s.zeroLocus.toModulesι ≫ δ.hom = s := by
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible M
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible Mᵛ
  let ψ := Scheme.Modules.dualMap s ≫ Scheme.Modules.dualUnitIso.hom
  have hz : ψ.zeroLocus = s.zeroLocus :=
    Scheme.Modules.Hom.zeroLocus_dualMap_comp_dualUnitIso s
  have hψ : ψ.zeroLocus.IsInvertible := hz.symm ▸ hs
  obtain ⟨κ, hκ⟩ := ideal_comparison_transport hz ψ
    (Scheme.Modules.Hom.exists_iso_toModules_zeroLocus ψ hψ)
  have := SheafOfModules.isIso_bidual (R := X.sheaf) M
  let β : M ≅ Mᵛᵛ := asIso (SheafOfModules.bidual (R := X.sheaf) M)
  let δ : s.zeroLocus.toModulesᵛ ≅ M := dualIso κ ≪≫ β.symm
  refine ⟨δ, ?_⟩
  apply (cancel_mono β.hom).mp
  change Scheme.Modules.dualUnitIso.inv ≫
    Scheme.Modules.dualMap s.zeroLocus.toModulesι ≫
    (Scheme.Modules.dualMap κ.hom ≫ β.inv) ≫ β.hom = s ≫ β.hom
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← dualMap_comp, hκ, dualMap_comp]
  have hn := Scheme.Modules.bidual_naturality s
  rw [← dualUnit_bidual] at hn
  exact hn.symm


private theorem comp_conventions {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (projectiveBundlePullbackComp f g).symm = Scheme.Modules.tensorPullbackSectionComp f g := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((projectiveBundlePullbackAdjunction (f ≫ g)).homEquiv M _).injective
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    ConcreteCategory.comp_apply]
  have ht := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.tensorPullbackSectionAdjunction (f ≫ g))
    (((Scheme.Modules.tensorPullbackSectionAdjunction g).comp
      (Scheme.Modules.tensorPullbackSectionAdjunction f)).ofNatIsoRight
        (Scheme.Modules.pushforwardComp f g)) M
  have he := congrArg (fun t ↦ t.app U m) ht
  simp only [Adjunction.ofNatIsoRight_unit, Adjunction.comp_unit_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, ConcreteCategory.comp_apply] at he
  rw [sectionAdjunction_eq, sectionAdjunction_eq, sectionAdjunction_eq] at he
  erw [ConcreteCategory.id_apply] at he
  have hp := section_comp f g (F := M) (U := U) m
  have hp' := congrArg
    (fun s ↦ ((projectiveBundlePullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U) s) hp
  have hi := congrArg (fun t ↦ t.app ((f ≫ g) ⁻¹ᵁ U)
    (projectiveBundlePullbackSection f (projectiveBundlePullbackSection g m)))
      ((projectiveBundlePullbackComp f g).hom_inv_id_app M)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
    ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at hi
  unfold projectiveBundlePullbackSection at hp' hi
  simp only [Scheme.Modules.tensorPullbackSectionComp, sectionAdjunction_eq,
    Iso.symm_hom]
  exact hp'.symm.trans (hi.trans he.symm)


private theorem comp_component_conventions {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    ((Scheme.Modules.tensorPullbackSectionComp f g).app M).inv =
      (compApp f g M).hom := by
  rw [← comp_conventions]
  rfl

private theorem congr_two {X Y : Scheme.{u}} {f₀ f₁ f₂ : X ⟶ Y}
    (h₁ : f₀ = f₁) (h₂ : f₁ = f₂) (h : f₀ = f₂) (M : Y.Modules) :
    (projectiveBundlePullbackCongr h₁).hom.app M ≫
      (projectiveBundlePullbackCongr h₂).hom.app M =
        (projectiveBundlePullbackCongr h).hom.app M := by
  subst f₁
  subst f₂
  simp [projectiveBundlePullbackCongr]

private theorem left_unit_component {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    (compApp f (𝟙 Y) M).inv ≫
      (Scheme.Modules.tensorPullback f).map ((projectiveBundlePullbackId Y).hom.app M) =
        (projectiveBundlePullbackCongr (Category.comp_id f)).hom.app M := by
  have h := congrArg (fun k ↦ k.app M) (projectiveBundlePullback_left_unitality f)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at h
  unfold projectiveBundlePullbackCongr
  rw [eqToIso.hom, eqToHom_app]
  exact (congrArg ((compApp f (𝟙 Y) M).inv ≫ ·) (Category.comp_id _)).symm.trans
    (h.trans (eqToHom_app _ _))

private theorem identity_base_quotient {S : Scheme.{u}} {F : S.Modules}
    (P D : ProjectiveBundleRealization S F)
    (j : D.A.data.relProj ⟶ P.A.data.relProj)
    (hj : j ≫ P.A.data.relProjHom = D.A.data.relProjHom ≫ 𝟙 S)
    (θ : (Scheme.Modules.tensorPullback j).obj P.L ≅ D.L)
    (hθ : projectiveBundleThetaQuotientLaw P D (𝟙 S)
      ((projectiveBundlePullbackId S).app F).symm j hj θ) :
    (Scheme.Modules.tensorPullback j).map P.quotient ≫ θ.hom =
      (compApp j P.A.data.relProjHom F).hom ≫
        (projectiveBundlePullbackCongr (hj.trans (Category.comp_id _))).hom.app F ≫
          D.quotient := by
  change (Scheme.Modules.tensorPullback j).map P.quotient ≫ θ.hom =
    (compApp j P.A.data.relProjHom F).hom ≫
      (projectiveBundlePullbackCongr hj).hom.app F ≫
      (compApp D.A.data.relProjHom (𝟙 S) F).inv ≫
      (Scheme.Modules.tensorPullback D.A.data.relProjHom).map
        ((projectiveBundlePullbackId S).hom.app F) ≫ D.quotient at hθ
  rw [reassoc_of% (left_unit_component D.A.data.relProjHom F)] at hθ
  rw [← Category.assoc ((projectiveBundlePullbackCongr hj).hom.app F),
    congr_two hj (Category.comp_id _) (hj.trans (Category.comp_id _)) F] at hθ
  exact hθ

private theorem over_square_paste {S X Y T : Scheme.{u}}
    (p : X ⟶ S) (p' : Y ⟶ S) (p'' : T ⟶ S)
    (j : Y ⟶ X) (a : T ⟶ Y) (hj : j ≫ p = p') (ha : a ≫ p' = p'')
    (hi : (a ≫ j) ≫ p = p'') (F : S.Modules) :
    (compApp a j ((Scheme.Modules.tensorPullback p).obj F)).inv ≫
      (Scheme.Modules.tensorPullback a).map
        ((compApp j p F).hom ≫ (projectiveBundlePullbackCongr hj).hom.app F) ≫
      (compApp a p' F).hom ≫ (projectiveBundlePullbackCongr ha).hom.app F =
        (compApp (a ≫ j) p F).hom ≫ (projectiveBundlePullbackCongr hi).hom.app F := by
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (comp_assoc_first_app a j p F)]
  rw [reassoc_of% (comp_congr_right_app a hj F)]
  simp only [Iso.inv_hom_id_assoc]
  rw [congr_two (congrArg (a ≫ ·) hj) ha ((congrArg (a ≫ ·) hj).trans ha) F]
  rw [congr_two (Category.assoc a j p) ((congrArg (a ≫ ·) hj).trans ha) hi F]

private def pasteIso {X Y T : Scheme.{u}} (j : Y ⟶ X) (a : T ⟶ Y)
    (L : X.Modules) (L' : Y.Modules) (M : T.Modules)
    (θj : (tensorPullback j).obj L ≅ L') (θa : (tensorPullback a).obj L' ≅ M) :
    (tensorPullback (a ≫ j)).obj L ≅ M where
  hom := (compApp a j L).inv ≫ (tensorPullback a).map θj.hom ≫ θa.hom
  inv := θa.inv ≫ (tensorPullback a).map θj.inv ≫ (compApp a j L).hom
  hom_inv_id := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, θj.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id]
  inv_hom_id := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc, θj.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id]

private theorem quotient_paste {S X Y T : Scheme.{u}}
    (p : X ⟶ S) (p' : Y ⟶ S) (p'' : T ⟶ S)
    (F : S.Modules) (L : X.Modules) (L' : Y.Modules) (M : T.Modules)
    (q : (Scheme.Modules.tensorPullback p).obj F ⟶ L)
    (q' : (Scheme.Modules.tensorPullback p').obj F ⟶ L')
    (q'' : (Scheme.Modules.tensorPullback p'').obj F ⟶ M)
    (j : Y ⟶ X) (a : T ⟶ Y) (hj : j ≫ p = p') (ha : a ≫ p' = p'')
    (hi : (a ≫ j) ≫ p = p'')
    (θj : (Scheme.Modules.tensorPullback j).obj L ≅ L')
    (θa : (Scheme.Modules.tensorPullback a).obj L' ≅ M)
    (hqj : (Scheme.Modules.tensorPullback j).map q ≫ θj.hom =
      (compApp j p F).hom ≫ (projectiveBundlePullbackCongr hj).hom.app F ≫ q')
    (hqa : (Scheme.Modules.tensorPullback a).map q' ≫ θa.hom =
      (compApp a p' F).hom ≫ (projectiveBundlePullbackCongr ha).hom.app F ≫ q'') :
    (Scheme.Modules.tensorPullback (a ≫ j)).map q ≫
      (pasteIso j a L L' M θj θa).hom =
        (compApp (a ≫ j) p F).hom ≫
          (projectiveBundlePullbackCongr hi).hom.app F ≫ q'' := by
  change (Scheme.Modules.tensorPullback (a ≫ j)).map q ≫
    (compApp a j L).inv ≫ (Scheme.Modules.tensorPullback a).map θj.hom ≫ θa.hom = _
  rw [compApp_inv_naturality_assoc a j q, ← Functor.map_comp_assoc, hqj]
  simp only [Functor.map_comp, Category.assoc]
  rw [hqa]
  have hp := over_square_paste p p' p'' j a hj ha hi F
  simp only [Functor.map_comp, Category.assoc] at hp
  rw [reassoc_of% hp]

private theorem identity_realization_comparison {S : Scheme.{u}} {F : S.Modules}
    [F.IsQuasicoherent] (P D : ProjectiveBundleRealization S F) :
    ∃ (j : D.A.data.relProj ⟶ P.A.data.relProj)
      (hj : j ≫ P.A.data.relProjHom = D.A.data.relProjHom)
      (θ : (Scheme.Modules.tensorPullback j).obj P.L ≅ D.L),
      (Scheme.Modules.tensorPullback j).map P.quotient ≫ θ.hom =
        (compApp j P.A.data.relProjHom F).hom ≫
          (projectiveBundlePullbackCongr hj).hom.app F ≫ D.quotient := by
  let e : F ≅ (Scheme.Modules.tensorPullback (𝟙 S)).obj F :=
    ((projectiveBundlePullbackId S).app F).symm
  obtain ⟨b, hb⟩ := exists_projectiveBundleCoefficientComparison (𝟙 S) e P.A D.A
  obtain ⟨θ, hθ⟩ := exists_projectiveBundleBaseChangeTheta P D (𝟙 S) e b hb
  exact ⟨b.relProjComparison, b.isPullback.w.trans (Category.comp_id _), θ,
    identity_base_quotient P D b.relProjComparison b.isPullback.w θ hθ⟩

private theorem realization_quotient_exists {S : Scheme.{u}} {F : S.Modules}
    (n : ℕ) [F.IsFiniteLocallyFreeOfRank (n + 1)]
    (P : ProjectiveBundleRealization S F)
    (T : Scheme.{u}) (p : T ⟶ S) (M : T.Modules) [M.IsInvertible]
    (q : (Scheme.Modules.tensorPullback p).obj F ⟶ M) [Epi q] :
    ∃ (i : T ⟶ P.A.data.relProj) (hi : i ≫ P.A.data.relProjHom = p)
      (θ : (Scheme.Modules.tensorPullback i).obj P.L ≅ M),
      (Scheme.Modules.tensorPullback i).map P.quotient ≫ θ.hom =
        (compApp i P.A.data.relProjHom F).hom ≫
          (projectiveBundlePullbackCongr hi).hom.app F ≫ q := by
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree F (n + 1)
  have := SheafOfModules.instIsQuasicoherentOfIsLocallyFree F
  obtain ⟨D, hD⟩ := exists_completeFlagProjectivization S n F
  obtain ⟨j, hj, θj, hqj⟩ := identity_realization_comparison P D
  obtain ⟨a, ⟨ha, θa, hθa⟩, -⟩ := hD T p M q
  have hθa' : (Scheme.Modules.tensorPullback a).map D.quotient ≫ θa.hom =
      (compApp a D.A.data.relProjHom F).hom ≫
        (projectiveBundlePullbackCongr ha).hom.app F ≫ q := by
    exact hθa.trans (congrArg
      (· ≫ (projectiveBundlePullbackCongr ha).hom.app F ≫ q)
      (comp_component_conventions a D.A.data.relProjHom F))
  have hi : (a ≫ j) ≫ P.A.data.relProjHom = p := by
    rw [Category.assoc, hj, ha]
  refine ⟨a ≫ j, hi,
    pasteIso j a P.L D.L M θj θa, ?_⟩
  exact quotient_paste P.A.data.relProjHom D.A.data.relProjHom p F P.L D.L M
    P.quotient D.quotient q j a hj ha hi θj θa hqj hθa'


private theorem identity_realization_iso_comparison {S : Scheme.{u}} {F : S.Modules}
    [F.IsQuasicoherent] (P D : ProjectiveBundleRealization S F) :
    ∃ (j : D.A.data.relProj ⟶ P.A.data.relProj)
      (hj : j ≫ P.A.data.relProjHom = D.A.data.relProjHom)
      (θ : (Scheme.Modules.tensorPullback j).obj P.L ≅ D.L),
      IsIso j ∧ (Scheme.Modules.tensorPullback j).map P.quotient ≫ θ.hom =
        (compApp j P.A.data.relProjHom F).hom ≫
          (projectiveBundlePullbackCongr hj).hom.app F ≫ D.quotient := by
  let e : F ≅ (Scheme.Modules.tensorPullback (𝟙 S)).obj F :=
    ((projectiveBundlePullbackId S).app F).symm
  obtain ⟨b, hb⟩ := exists_projectiveBundleCoefficientComparison (𝟙 S) e P.A D.A
  obtain ⟨θ, hθ⟩ := exists_projectiveBundleBaseChangeTheta P D (𝟙 S) e b hb
  exact ⟨b.relProjComparison, b.isPullback.w.trans (Category.comp_id _), θ,
    b.isPullback.isIso_fst_of_isIso,
    identity_base_quotient P D b.relProjComparison b.isPullback.w θ hθ⟩

private theorem realization_quotient_unique {S : Scheme.{u}} {F : S.Modules}
    (n : ℕ) [F.IsFiniteLocallyFreeOfRank (n + 1)]
    (P : ProjectiveBundleRealization S F)
    (T : Scheme.{u}) (p : T ⟶ S) (M : T.Modules) [M.IsInvertible]
    (q : (Scheme.Modules.tensorPullback p).obj F ⟶ M) [Epi q]
    (i₁ i₂ : T ⟶ P.A.data.relProj)
    (h₁ : i₁ ≫ P.A.data.relProjHom = p)
    (h₂ : i₂ ≫ P.A.data.relProjHom = p)
    (θ₁ : (Scheme.Modules.tensorPullback i₁).obj P.L ≅ M)
    (θ₂ : (Scheme.Modules.tensorPullback i₂).obj P.L ≅ M)
    (hq₁ : (Scheme.Modules.tensorPullback i₁).map P.quotient ≫ θ₁.hom =
      (compApp i₁ P.A.data.relProjHom F).hom ≫
        (projectiveBundlePullbackCongr h₁).hom.app F ≫ q)
    (hq₂ : (Scheme.Modules.tensorPullback i₂).map P.quotient ≫ θ₂.hom =
      (compApp i₂ P.A.data.relProjHom F).hom ≫
        (projectiveBundlePullbackCongr h₂).hom.app F ≫ q) : i₁ = i₂ := by
  have := SheafOfModules.IsFiniteLocallyFreeOfRank.isLocallyFree F (n + 1)
  have := SheafOfModules.instIsQuasicoherentOfIsLocallyFree F
  obtain ⟨D, hD⟩ := exists_completeFlagProjectivization S n F
  obtain ⟨j, hj, θj, hjiso, hqj⟩ := identity_realization_iso_comparison D P
  let := hjiso
  have classifies (i : T ⟶ P.A.data.relProj)
      (hi : i ≫ P.A.data.relProjHom = p)
      (θ : (Scheme.Modules.tensorPullback i).obj P.L ≅ M)
      (hq : (Scheme.Modules.tensorPullback i).map P.quotient ≫ θ.hom =
        (compApp i P.A.data.relProjHom F).hom ≫
          (projectiveBundlePullbackCongr hi).hom.app F ≫ q) :
      ∃ h : (i ≫ j) ≫ D.A.data.relProjHom = p,
        ∃ δ : (Scheme.Modules.tensorPullback (i ≫ j)).obj D.L ≅ M,
          (Scheme.Modules.tensorPullback (i ≫ j)).map D.quotient ≫ δ.hom =
            ((Scheme.Modules.tensorPullbackSectionComp (i ≫ j) D.A.data.relProjHom).app F).inv ≫
              (projectiveBundlePullbackCongr h).hom.app F ≫ q := by
    have h : (i ≫ j) ≫ D.A.data.relProjHom = p := by rw [Category.assoc, hj, hi]
    refine ⟨h, pasteIso j i D.L P.L M θj θ, ?_⟩
    have hp := quotient_paste D.A.data.relProjHom P.A.data.relProjHom p F D.L P.L M
      D.quotient P.quotient q j i hj hi h θj θ hqj hq
    exact hp.trans (congrArg (· ≫ (projectiveBundlePullbackCongr h).hom.app F ≫ q)
      (comp_component_conventions (i ≫ j) D.A.data.relProjHom F).symm)
  obtain ⟨a, ha, huniq⟩ := hD T p M q
  apply (cancel_mono j).mp
  exact (huniq _ (classifies i₁ h₁ θ₁ hq₁)).trans
    (huniq _ (classifies i₂ h₂ θ₂ hq₂)).symm


private theorem section_zeroLocus {S : Scheme.{u}} {L F : S.Modules} [L.IsInvertible]
    (P : ProjectiveBundleRealization S F) [P.L.IsInvertible] (ι : L ⟶ F) :
    (lineSubbundleProjectiveSection P ι).zeroLocus =
      (lineSubbundleProjectiveMap P ι).zeroLocus := by
  let : ((Scheme.Modules.tensorPullback P.A.data.relProjHom).obj L).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso
      ((projectiveBundleTensorPullbackIso P.A.data.relProjHom).app L).symm
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  let := Scheme.picardTensorDualComparison_isIso P.A.data.relProjHom L
  unfold lineSubbundleProjectiveSection
  exact Scheme.Modules.Hom.zeroLocus_adjointSection_comp_whiskerLeft _
    (asIso (Scheme.Modules.picardTensorDualComparison P.A.data.relProjHom L)).symm

private theorem zeroLocus_tensorPullback {X Y : Scheme.{u}} {M N : Y.Modules}
    [M.IsInvertible] [N.IsInvertible] (f : X ⟶ Y) (s : M ⟶ N) :
    s.zeroLocus.comap f = ((Scheme.Modules.tensorPullback f).map s).zeroLocus := by
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible M
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible N
  rw [Scheme.Modules.Hom.comap_zeroLocus]
  exact Scheme.Modules.Hom.zeroLocus_eq_of_arrowIso _ _
    (Arrow.isoMk ((projectiveBundleTensorPullbackIso f).app M).symm
      ((projectiveBundleTensorPullbackIso f).app N).symm (by
        change (projectiveBundleTensorPullbackIso f).inv.app M ≫
          (Scheme.Modules.tensorPullback f).map s =
            (Scheme.Modules.pullback f).map s ≫
              (projectiveBundleTensorPullbackIso f).inv.app N
        exact ((projectiveBundleTensorPullbackIso f).inv.naturality s).symm))

private theorem vanishes_on_zeroLocus {X : Scheme.{u}} {M N : X.Modules}
    [M.IsInvertible] [N.IsInvertible] (s : M ⟶ N) :
    (Scheme.Modules.tensorPullback s.zeroLocus.subschemeι).map s = 0 := by
  let : ((Scheme.Modules.tensorPullback s.zeroLocus.subschemeι).obj M).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso
      ((projectiveBundleTensorPullbackIso _).app M).symm
  let : ((Scheme.Modules.tensorPullback s.zeroLocus.subschemeι).obj N).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso
      ((projectiveBundleTensorPullbackIso _).app N).symm
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    ((Scheme.Modules.tensorPullback s.zeroLocus.subschemeι).obj M)
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    ((Scheme.Modules.tensorPullback s.zeroLocus.subschemeι).obj N)
  apply (Scheme.Modules.Hom.zeroLocus_eq_bot_iff _).mp
  rw [← zeroLocus_tensorPullback, Scheme.IdealSheafData.comap_subschemeι]


private theorem quotient_vanishing {S : Scheme.{u}} {L F G : S.Modules}
    (ι : L ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)
    (P : ProjectiveBundleRealization S F) (Q : ProjectiveBundleRealization S G)
    (i : Q.A.data.relProj ⟶ P.A.data.relProj)
    (hi : i ≫ P.A.data.relProjHom = Q.A.data.relProjHom)
    (θ : (Scheme.Modules.tensorPullback i).obj P.L ≅ Q.L)
    (hθ : (Scheme.Modules.tensorPullback i).map P.quotient ≫ θ.hom =
      (compApp i P.A.data.relProjHom F).hom ≫
      (projectiveBundlePullbackCongr hi).hom.app F ≫
      (Scheme.Modules.tensorPullback Q.A.data.relProjHom).map π ≫ Q.quotient) :
    (Scheme.Modules.tensorPullback i).map (lineSubbundleProjectiveMap P ι) = 0 := by
  let : (Scheme.Modules.tensorPullback Q.A.data.relProjHom).IsLeftAdjoint :=
    (projectiveBundlePullbackAdjunction Q.A.data.relProjHom).isLeftAdjoint
  apply (cancel_mono θ.hom).mp
  simp only [lineSubbundleProjectiveMap, Functor.map_comp, Category.assoc, zero_comp]
  rw [hθ, compApp_hom_naturality_assoc i P.A.data.relProjHom ι]
  erw [(projectiveBundlePullbackCongr hi).hom.naturality_assoc ι]
  rw [← Functor.map_comp_assoc, w, Functor.map_zero, zero_comp, comp_zero, comp_zero]

private theorem quotient_zeroLocus_le_ker {S : Scheme.{u}} {L F G : S.Modules}
    [L.IsInvertible] (ι : L ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)
    (P : ProjectiveBundleRealization S F) (Q : ProjectiveBundleRealization S G)
    [P.L.IsInvertible]
    (i : Q.A.data.relProj ⟶ P.A.data.relProj)
    (hi : i ≫ P.A.data.relProjHom = Q.A.data.relProjHom)
    (θ : (Scheme.Modules.tensorPullback i).obj P.L ≅ Q.L)
    (hθ : (Scheme.Modules.tensorPullback i).map P.quotient ≫ θ.hom =
      (compApp i P.A.data.relProjHom F).hom ≫
      (projectiveBundlePullbackCongr hi).hom.app F ≫
      (Scheme.Modules.tensorPullback Q.A.data.relProjHom).map π ≫ Q.quotient) :
    (lineSubbundleProjectiveSection P ι).zeroLocus ≤ i.ker := by
  let : ((Scheme.Modules.tensorPullback P.A.data.relProjHom).obj L).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso
      ((projectiveBundleTensorPullbackIso P.A.data.relProjHom).app L).symm
  let : ((Scheme.Modules.tensorPullback i).obj
      ((Scheme.Modules.tensorPullback P.A.data.relProjHom).obj L)).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso ((projectiveBundleTensorPullbackIso i).app _).symm
  let : ((Scheme.Modules.tensorPullback i).obj P.L).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso ((projectiveBundleTensorPullbackIso i).app _).symm
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    ((Scheme.Modules.tensorPullback i).obj
      ((Scheme.Modules.tensorPullback P.A.data.relProjHom).obj L))
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    ((Scheme.Modules.tensorPullback i).obj P.L)
  rw [section_zeroLocus]
  apply Scheme.IdealSheafData.le_ker_of_comap_eq_bot
  rw [zeroLocus_tensorPullback, Scheme.Modules.Hom.zeroLocus_eq_bot_iff]
  exact quotient_vanishing ι π w P Q i hi θ hθ

private theorem quotient_desc {S T : Scheme.{u}} {L F G : S.Modules}
    (ι : L ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)
    (h : (ShortComplex.mk ι π w).ShortExact) (p : T ⟶ S) (M : T.Modules)
    (q : (Scheme.Modules.tensorPullback p).obj F ⟶ M)
    (hq : (Scheme.Modules.tensorPullback p).map ι ≫ q = 0) :
    ∃ ε : (Scheme.Modules.tensorPullback p).obj G ⟶ M,
      (Scheme.Modules.tensorPullback p).map π ≫ ε = q := by
  let := h.epi_g
  let : (Scheme.Modules.tensorPullback p).IsLeftAdjoint :=
    (projectiveBundlePullbackAdjunction p).isLeftAdjoint
  let hc := CokernelCofork.mapIsColimit _ h.exact.gIsCokernel
    (Scheme.Modules.tensorPullback p)
  exact ⟨(CokernelCofork.IsColimit.desc' hc q hq).val,
    (CokernelCofork.IsColimit.desc' hc q hq).property⟩


section Regularity
universe v

private theorem zeroLocus_invertible_of_mono {X : Scheme.{u}} {M N : X.Modules}
    [SheafOfModules.IsInvertible.{u, u, u} M]
    [SheafOfModules.IsInvertible.{u, u, u} N]
    (φ : M ⟶ N) [Mono φ] : φ.zeroLocus.IsInvertible := by
  intro x
  obtain ⟨U, hxU, -, ⟨eM, hM⟩, eN, hN⟩ :=
    Scheme.Modules.exists_isFreeGenerator₂ M N (TopologicalSpace.Opens.mem_top x)
  obtain ⟨b, hb⟩ := hN.exists_smul_eq (φ.app U.1 eM)
  refine ⟨U, hxU, ?_⟩
  rw [Scheme.Modules.Hom.ideal_zeroLocus φ U hM hN hb.symm]
  apply Ideal.isRegularPrincipal_span_singleton_of_isRegular
  apply (Commute.isRegular_iff (fun a ↦ mul_comm b a)).mpr
  intro a c hac
  change b * a = b * c at hac
  apply hM.smul_left_injective
  apply Scheme.Modules.injective_app_of_mono' φ U.1
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, ← hb,
    smul_smul, smul_smul]
  rw [mul_comm a b, mul_comm c b, hac]

private theorem unitToTwist_mono {A σ : Type u} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) (hreg : IsRegular f) :
    Mono (Proj.unitToTwist hf) := by
  apply Functor.mono_of_mono_map (SheafOfModules.forget _)
  apply PresheafOfModules.mono_of_injective
  intro U s t hst
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  have he := congrArg (fun z ↦ ((z.1 x).1 :
    Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)) hst
  change (s.1 x).val * Localization.mk f 1 = (t.1 x).val * Localization.mk f 1 at he
  have hloc : IsRegular (algebraMap A
      (Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) f) :=
    isRegular_iff_mem_nonZeroDivisors.mpr
      (IsLocalization.nonZeroDivisors_le_comap
        x.1.asHomogeneousIdeal.toIdeal.primeCompl _
        (isRegular_iff_mem_nonZeroDivisors.mp hreg))
  apply hloc.right
  simpa only [Localization.mk_one_eq_algebraMap] using he

private theorem symmetric_basis_regular {R M : Type u} {I : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Module.Basis I R M) (i : I) :
    IsRegular (SymmetricAlgebra.ι R M (b i)) := by
  let e := SymmetricAlgebra.equivMvPolynomial b
  have h : IsRegular (e (SymmetricAlgebra.ι R M (b i))) := by
    rw [SymmetricAlgebra.equivMvPolynomial_ι_apply]
    exact MvPolynomial.isRegular_X
  apply (Commute.isRegular_iff (fun a ↦ mul_comm _ a)).mpr
  intro a c hac
  apply e.injective
  apply h.left
  simpa only [map_mul] using congrArg e hac

private theorem regular_pullback_free {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) (hs : IsFreeGenerator s) :
    IsFreeGenerator (projectiveBundlePullbackSection f s) := by
  let adj := projectiveBundlePullbackAdjunction f
  let e := (adj.leftAdjointUniq (pullbackPushforwardAdjunction f)).app M
  have h := (hs.pullback_unit_app f).app_hom e.symm
  have hu := adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction f) M
  have hv := congrArg (fun t ↦ t.app U s) hu
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply] at hv
  have hv' : e.hom.app _ (projectiveBundlePullbackSection f s) =
      ((pullbackPushforwardAdjunction f).unit.app M).app U s := by
    unfold projectiveBundlePullbackSection
    exact hv
  have hi : e.inv.app _ (e.hom.app _ (projectiveBundlePullbackSection f s)) =
      projectiveBundlePullbackSection f s := by
    change (e.hom.app _ ≫ e.inv.app _) _ = _
    rw [← Hom.comp_app, e.hom_inv_id, Hom.id_app]
    rfl
  exact (hi.symm.trans (congrArg (e.inv.app (f ⁻¹ᵁ U)) hv')).symm ▸ h

private theorem regular_pullback_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (φ : M ⟶ N) (U : Y.Opens) (s : Γ(M, U)) :
    ((tensorPullback f).map φ).app (f ⁻¹ᵁ U)
      (projectiveBundlePullbackSection f s) =
      projectiveBundlePullbackSection f (φ.app U s) := by
  exact section_naturality f φ s

private theorem local_line_map_regular {S : Scheme.{u}} {L F : S.Modules}
    (P : ProjectiveBundleRealization S F) (ι : L ⟶ F)
    (U : S.affineOpens) (l : Γ(L, U.1)) (hl : IsFreeGenerator l)
    (hf : P.A.sectionEquiv U (SymmetricAlgebra.ι _ _ (ι.app U.1 l)) ∈
      P.A.data.grading U 1)
    (hreg : IsRegular (P.A.sectionEquiv U (SymmetricAlgebra.ι _ _ (ι.app U.1 l)))) :
    Mono ((tensorPullback (P.A.data.relProjι U)).map (lineSubbundleProjectiveMap P ι)) := by
  let p := P.A.data.relProjHom
  let j := P.A.data.relProjι U
  let φ := lineSubbundleProjectiveMap P ι
  have htop : j ⁻¹ᵁ (p ⁻¹ᵁ U.1) = ⊤ := by
    rw [P.A.data.relProjHom_preimage U]
    exact j.preimage_opensRange
  let l' := projectiveBundlePullbackSection p l
  let l'' := projectiveBundlePullbackSection j l'
  have hl'' : IsFreeGenerator l'' :=
    regular_pullback_free j _ _ l' (regular_pullback_free p L U.1 l hl)
  have hg : (P.twists.chart U).hom.app (j ⁻¹ᵁ (p ⁻¹ᵁ U.1))
      (((tensorPullback j).map φ).app _ l'') =
        (Proj.unitToTwist hf).app (j ⁻¹ᵁ (p ⁻¹ᵁ U.1))
          (1 : Γ(Proj (P.A.data.grading U), j ⁻¹ᵁ (p ⁻¹ᵁ U.1))) := by
    rw [regular_pullback_naturality]
    have hi : φ.app (p ⁻¹ᵁ U.1) l' =
        (((projectiveBundlePullbackAdjunction p).homEquiv F P.L P.quotient).app U.1
          (ι.app U.1 l)) := by
      change P.quotient.app _ (((tensorPullback p).map ι).app _ l') = _
      rw [regular_pullback_naturality, Adjunction.homEquiv_unit]
      unfold projectiveBundlePullbackSection
      rfl
    rw [hi]
    exact P.quotient_generator U (ι.app U.1 l) hf
  have hlglobal : ∃ e : Γ((tensorPullback j).obj ((tensorPullback p).obj L), ⊤),
      IsFreeGenerator e ∧
      (P.twists.chart U).hom.app ⊤ (((tensorPullback j).map φ).app ⊤ e) =
        (Proj.unitToTwist hf).app ⊤ (1 : Γ(Proj (P.A.data.grading U), ⊤)) := by
    have he : ∃ e : Γ((tensorPullback j).obj ((tensorPullback p).obj L),
        j ⁻¹ᵁ (p ⁻¹ᵁ U.1)), IsFreeGenerator e ∧
        (P.twists.chart U).hom.app _ (((tensorPullback j).map φ).app _ e) =
          (Proj.unitToTwist hf).app _
            (1 : Γ(Proj (P.A.data.grading U), j ⁻¹ᵁ (p ⁻¹ᵁ U.1))) :=
      ⟨l'', hl'', hg⟩
    rw [htop] at he
    exact he
  obtain ⟨e, he, hge⟩ := hlglobal
  let ε := homOfGlobalSection _ e
  have : IsIso ε := isIso_homOfGlobalSection he
  have hε : ε ≫ (tensorPullback j).map φ ≫ (P.twists.chart U).hom =
      Proj.unitToTwist hf := by
    apply unit_hom_ext
    change (P.twists.chart U).hom.app ⊤
      (((tensorPullback j).map φ).app ⊤
        ((homOfGlobalSection _ e).app ⊤ (1 : Γ(Proj (P.A.data.grading U), ⊤)))) = _
    rw [homOfGlobalSection_app_one, presheaf_map_id_apply]
    exact hge
  have : Mono (Proj.unitToTwist hf) := unitToTwist_mono _ hf hreg
  have : Mono (ε ≫ (tensorPullback j).map φ ≫ (P.twists.chart U).hom) := hε.symm ▸ this
  have : Mono (ε ≫ (tensorPullback j).map φ) := mono_of_mono _ (P.twists.chart U).hom
  have : Mono (inv ε ≫ (ε ≫ (tensorPullback j).map φ)) := inferInstance
  simpa only [IsIso.inv_hom_id_assoc] using this

private theorem map_regular_from_adapted_frames
    (S : Scheme.{u}) (r : ℕ) (_hr : 2 ≤ r) (L F G : S.Modules)
    [L.IsInvertible] [F.IsFiniteLocallyFreeOfRank r]
    [G.IsFiniteLocallyFreeOfRank (r - 1)]
    (ι : L ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)
    (hexact : (ShortComplex.mk ι π w).ShortExact)
    (P : ProjectiveBundleRealization S F) :
    (lineSubbundleProjectiveSection P ι).zeroLocus.IsInvertible := by
  classical
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  have := (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one L).mp
    (inferInstance : SheafOfModules.IsInvertible.{u, u, u} L)
  let Good (U : S.affineOpens) := ∃ l : Γ(L, U.1), IsFreeGenerator l ∧
    IsRegular (P.A.sectionEquiv U (SymmetricAlgebra.ι _ _ (ι.app U.1 l)))
  have hgood (x : S) : ∃ U : S.affineOpens, x ∈ U.1 ∧ Good U := by
    obtain ⟨U, l, t, hxU, hl, ht⟩ := exists_adapted_frame (r := r - 1) hexact x
    obtain ⟨V, hVaff, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hxU
    let lV := L.presheaf.map (homOfLE hVU).op (l 0)
    have hlV : IsFreeGenerator lV := hl.isFreeGenerator.map hVU
    obtain ⟨b, hb⟩ := (IsLocalFrame.cons_of_shortExact hexact hl ht) V hVU
    have hbi : b (0 : Fin ((r - 1) + 1)) = ι.app V lV := by
      rw [hb]
      simp only [Fin.cons_zero, ← Hom.app_presheaf_map]
      rfl
    let b' : Module.Basis (Fin ((r - 1) + 1))
        (S.presheaf.obj (op V)) (F.val.obj (op V)) := b
    have hbi' : b' 0 = ι.app V lV := hbi
    have hs : IsRegular (SymmetricAlgebra.ι (S.presheaf.obj (op V))
        (F.val.obj (op V)) (ι.app V lV)) := by
      rw [← hbi']
      exact symmetric_basis_regular b' 0
    let : Algebra Γ(S, V) (P.A.data.obj ⟨V, hVaff⟩) := P.A.data.algebra ⟨V, hVaff⟩
    let e := P.A.sectionEquiv ⟨V, hVaff⟩
    have hse : IsRegular (e (SymmetricAlgebra.ι _ _ (ι.app V lV))) := by
      apply (Commute.isRegular_iff (fun a ↦ mul_comm _ a)).mpr
      intro a c hac
      apply e.symm.injective
      apply hs.left
      simpa only [map_mul, AlgEquiv.symm_apply_apply] using congrArg e.symm hac
    exact ⟨⟨V, hVaff⟩, hxV, lV, hlV, hse⟩
  let I := {U : S.affineOpens // Good U}
  let j (i : I) := P.A.data.relProjι i.1
  have hcover : ⨆ i : I, (j i).opensRange = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨U, hxU, hU⟩ := hgood (P.A.data.relProjHom x)
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨⟨U, hU⟩, ?_⟩
    rw [← P.A.data.relProjHom_preimage U]
    exact hxU
  have hmono : Mono (lineSubbundleProjectiveMap P ι) := by
    apply CategoryTheory.Preadditive.mono_of_cancel_zero
    intro M g hg
    apply zero_of_tensor_open_cover
      (fun i : I ↦ Proj (P.A.data.grading i.1)) j hcover
    intro i
    obtain ⟨l, hl, hreg⟩ := i.2
    have hι : P.A.sectionEquiv i.1 (SymmetricAlgebra.ι _ _ (ι.app i.1.1 l)) ∈
        P.A.data.grading i.1 1 := by
      apply (P.A.sectionEquiv_grade i.1 1 _).mp
      rw [projectiveBundleSymmetricDegree_eq, pow_one]
      exact LinearMap.mem_range_self _ _
    have := local_line_map_regular P ι i.1 l hl hι hreg
    let : (tensorPullback (j i)).IsLeftAdjoint :=
      (projectiveBundlePullbackAdjunction (j i)).isLeftAdjoint
    apply (cancel_mono ((tensorPullback (j i)).map (lineSubbundleProjectiveMap P ι))).mp
    rw [← Functor.map_comp, hg, Functor.map_zero, zero_comp]
  have := realization_invertible P
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible P.L
  have : ((tensorPullback P.A.data.relProjHom).obj L).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso
      ((projectiveBundleTensorPullbackIso P.A.data.relProjHom).app L).symm
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    ((tensorPullback P.A.data.relProjHom).obj L)
  rw [section_zeroLocus P ι]
  exact zeroLocus_invertible_of_mono (lineSubbundleProjectiveMap P ι)


end Regularity

private def overComp {S X Y : Scheme.{u}} (j : Y ⟶ X) (p : X ⟶ S)
    {p' : Y ⟶ S} (h : j ≫ p = p') (F : S.Modules) :
    (tensorPullback j).obj ((tensorPullback p).obj F) ≅ (tensorPullback p').obj F where
  hom := (compApp j p F).hom ≫ (projectiveBundlePullbackCongr h).hom.app F
  inv := (projectiveBundlePullbackCongr h).inv.app F ≫ (compApp j p F).inv
  hom_inv_id := by
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id]
  inv_hom_id := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id_app]

private theorem overComp_naturality {S X Y : Scheme.{u}} (j : Y ⟶ X) (p : X ⟶ S)
    {p' : Y ⟶ S} (h : j ≫ p = p') {F G : S.Modules} (φ : F ⟶ G) :
    (tensorPullback j).map ((tensorPullback p).map φ) ≫ (overComp j p h G).hom =
      (overComp j p h F).hom ≫ (tensorPullback p').map φ := by
  simp only [overComp, Category.assoc]
  rw [compApp_hom_naturality_assoc]
  rw [← (projectiveBundlePullbackCongr h).hom.naturality φ]

private theorem overComp_paste {S X Y T : Scheme.{u}}
    (p : X ⟶ S) (p' : Y ⟶ S) (p'' : T ⟶ S)
    (j : Y ⟶ X) (a : T ⟶ Y) (hj : j ≫ p = p') (ha : a ≫ p' = p'')
    (hi : (a ≫ j) ≫ p = p'') (F : S.Modules) :
    (compApp a j ((tensorPullback p).obj F)).inv ≫
      (tensorPullback a).map (overComp j p hj F).hom ≫
      (overComp a p' ha F).hom = (overComp (a ≫ j) p hi F).hom :=
  by
    simpa only [overComp, Iso.trans_hom, Iso.app_hom, Category.assoc] using
      over_square_paste p p' p'' j a hj ha hi F

private theorem quotient_over_paste {S X Y T : Scheme.{u}}
    (p : X ⟶ S) (p' : Y ⟶ S) (p'' : T ⟶ S)
    (F : S.Modules) (L : X.Modules) (L' : Y.Modules) (M : T.Modules)
    (q : (Scheme.Modules.tensorPullback p).obj F ⟶ L)
    (q' : (Scheme.Modules.tensorPullback p').obj F ⟶ L')
    (q'' : (Scheme.Modules.tensorPullback p'').obj F ⟶ M)
    (j : Y ⟶ X) (a : T ⟶ Y) (hj : j ≫ p = p') (ha : a ≫ p' = p'')
    (hi : (a ≫ j) ≫ p = p'')
    (θj : (Scheme.Modules.tensorPullback j).obj L ≅ L')
    (θa : (Scheme.Modules.tensorPullback a).obj L' ≅ M)
    (hqj : (Scheme.Modules.tensorPullback j).map q ≫ θj.hom =
      (overComp j p hj F).hom ≫ q')
    (hqa : (Scheme.Modules.tensorPullback a).map q' ≫ θa.hom =
      (overComp a p' ha F).hom ≫ q'') :
    (Scheme.Modules.tensorPullback (a ≫ j)).map q ≫
      (pasteIso j a L L' M θj θa).hom =
        (overComp (a ≫ j) p hi F).hom ≫ q'' := by
  simp only [overComp, pasteIso, Category.assoc] at hqj hqa ⊢
  exact quotient_paste p p' p'' F L L' M q q' q'' j a hj ha hi θj θa hqj hqa

private theorem realization_quotient_unique_over {S : Scheme.{u}} {F : S.Modules}
    (n : ℕ) [F.IsFiniteLocallyFreeOfRank (n + 1)]
    (P : ProjectiveBundleRealization S F)
    (T : Scheme.{u}) (p : T ⟶ S) (M : T.Modules) [M.IsInvertible]
    (q : (Scheme.Modules.tensorPullback p).obj F ⟶ M) [Epi q]
    (i₁ i₂ : T ⟶ P.A.data.relProj)
    (h₁ : i₁ ≫ P.A.data.relProjHom = p)
    (h₂ : i₂ ≫ P.A.data.relProjHom = p)
    (θ₁ : (Scheme.Modules.tensorPullback i₁).obj P.L ≅ M)
    (θ₂ : (Scheme.Modules.tensorPullback i₂).obj P.L ≅ M)
    (hq₁ : (Scheme.Modules.tensorPullback i₁).map P.quotient ≫ θ₁.hom =
      (overComp i₁ P.A.data.relProjHom h₁ F).hom ≫ q)
    (hq₂ : (Scheme.Modules.tensorPullback i₂).map P.quotient ≫ θ₂.hom =
      (overComp i₂ P.A.data.relProjHom h₂ F).hom ≫ q) : i₁ = i₂ := by
  simp only [overComp, Category.assoc] at hq₁ hq₂
  exact realization_quotient_unique n P T p M q i₁ i₂ h₁ h₂ θ₁ θ₂ hq₁ hq₂

private theorem quotient_precompose_square {S X Y : Scheme.{u}}
    (p : X ⟶ S) (p' : Y ⟶ S) {F G : S.Modules} (π : F ⟶ G)
    {M : X.Modules} {N : Y.Modules}
    (q : (tensorPullback p).obj G ⟶ M) (q' : (tensorPullback p').obj G ⟶ N)
    (j : Y ⟶ X) (hj : j ≫ p = p') (θ : (tensorPullback j).obj M ≅ N)
    (hq : (tensorPullback j).map q ≫ θ.hom = (overComp j p hj G).hom ≫ q') :
    (tensorPullback j).map ((tensorPullback p).map π ≫ q) ≫ θ.hom =
      (overComp j p hj F).hom ≫ (tensorPullback p').map π ≫ q' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [hq, ← Category.assoc _ _ q', overComp_naturality]
  simp only [Category.assoc]

private theorem quotient_cancel_precompose {S X Y : Scheme.{u}}
    (p : X ⟶ S) (p' : Y ⟶ S) {F G : S.Modules} (π : F ⟶ G) [Epi π]
    {M : X.Modules} {N : Y.Modules}
    (q : (tensorPullback p).obj G ⟶ M) (q' : (tensorPullback p').obj G ⟶ N)
    (j : Y ⟶ X) (hj : j ≫ p = p') (θ : (tensorPullback j).obj M ≅ N)
    (hq : (tensorPullback j).map ((tensorPullback p).map π ≫ q) ≫ θ.hom =
      (overComp j p hj F).hom ≫ (tensorPullback p').map π ≫ q') :
    (tensorPullback j).map q ≫ θ.hom = (overComp j p hj G).hom ≫ q' := by
  let : (tensorPullback p).IsLeftAdjoint :=
    (projectiveBundlePullbackAdjunction p).isLeftAdjoint
  let : (tensorPullback j).IsLeftAdjoint :=
    (projectiveBundlePullbackAdjunction j).isLeftAdjoint
  apply (cancel_epi ((tensorPullback j).map ((tensorPullback p).map π))).mp
  rw [← Category.assoc _ _ q', overComp_naturality]
  exact (by simpa only [Functor.map_comp, Category.assoc] using hq)

private theorem overComp_transport {S X Y : Scheme.{u}} (p : X ⟶ S)
    {j j' : Y ⟶ X} (h : j = j') {p' : Y ⟶ S}
    (hj : j ≫ p = p') (hj' : j' ≫ p = p') (F : S.Modules) :
    (projectiveBundlePullbackCongr h).hom.app ((tensorPullback p).obj F) ≫
      (overComp j' p hj' F).hom = (overComp j p hj F).hom := by
  subst j'
  simp only [← Iso.app_hom, congr_app_refl, Iso.refl_hom, Category.id_comp]

private def reindexIso {X Y : Scheme.{u}} {j j' : Y ⟶ X} (h : j = j')
    (L : X.Modules) (M : Y.Modules) (θ : (tensorPullback j').obj L ≅ M) :
    (tensorPullback j).obj L ≅ M where
  hom := (projectiveBundlePullbackCongr h).hom.app L ≫ θ.hom
  inv := θ.inv ≫ (projectiveBundlePullbackCongr h).inv.app L
  hom_inv_id := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_app]
  inv_hom_id := by
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id]

private theorem quotient_square_reindex {S X Y : Scheme.{u}}
    (p : X ⟶ S) (p' : Y ⟶ S) (F : S.Modules) (L : X.Modules) (M : Y.Modules)
    (q : (tensorPullback p).obj F ⟶ L) (q' : (tensorPullback p').obj F ⟶ M)
    {j j' : Y ⟶ X} (h : j = j') (hj : j ≫ p = p') (hj' : j' ≫ p = p')
    (θ : (tensorPullback j').obj L ≅ M)
    (hq : (tensorPullback j').map q ≫ θ.hom = (overComp j' p hj' F).hom ≫ q') :
    (tensorPullback j).map q ≫
      (reindexIso h L M θ).hom =
        (overComp j p hj F).hom ≫ q' := by
  simp only [reindexIso]
  rw [← Category.assoc, (projectiveBundlePullbackCongr h).hom.naturality q,
    Category.assoc, hq, ← Category.assoc, overComp_transport]

private theorem identity_quotient_square {S X : Scheme.{u}} (p : X ⟶ S)
    (F : S.Modules) (L : X.Modules) (q : (tensorPullback p).obj F ⟶ L) :
    (tensorPullback (𝟙 X)).map q ≫ ((projectiveBundlePullbackId X).app L).hom =
      (overComp (𝟙 X) p (Category.id_comp p) F).hom ≫ q := by
  simp only [Iso.app_hom]
  rw [(projectiveBundlePullbackId X).hom.naturality q]
  apply congrArg (· ≫ q)
  apply (cancel_epi (compApp (𝟙 X) p F).inv).mp
  simp only [overComp, Iso.inv_hom_id_assoc]
  have hu := congrArg (fun t ↦ t.app F) (projectiveBundlePullback_right_unitality p)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app] at hu
  change (compApp (𝟙 X) p F).inv ≫
      (projectiveBundlePullbackId X).hom.app ((tensorPullback p).obj F) =
        (projectiveBundlePullbackCongr (Category.id_comp p)).hom.app F
  unfold projectiveBundlePullbackCongr
  rw [eqToIso.hom]
  exact (congrArg ((compApp (𝟙 X) p F).inv ≫ ·)
    (Category.comp_id ((projectiveBundlePullbackId X).hom.app
      ((tensorPullback p).obj F)))).symm.trans hu


private def expandIso {X Y T : Scheme.{u}} (j : Y ⟶ X) (a : T ⟶ Y)
    (L : X.Modules) (M : T.Modules) (θ : (tensorPullback (a ≫ j)).obj L ≅ M) :
    (tensorPullback a).obj ((tensorPullback j).obj L) ≅ M where
  hom := (compApp a j L).hom ≫ θ.hom
  inv := θ.inv ≫ (compApp a j L).inv
  hom_inv_id := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id]
  inv_hom_id := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

private theorem quotient_pullback_square {S X Y T : Scheme.{u}}
    (p : X ⟶ S) (p' : Y ⟶ S) (p'' : T ⟶ S)
    (F : S.Modules) (L : X.Modules) (M : T.Modules)
    (q : (tensorPullback p).obj F ⟶ L)
    (q'' : (tensorPullback p'').obj F ⟶ M)
    (j : Y ⟶ X) (a : T ⟶ Y) (hj : j ≫ p = p') (ha : a ≫ p' = p'')
    (hi : (a ≫ j) ≫ p = p'')
    (θ : (tensorPullback (a ≫ j)).obj L ≅ M)
    (hq : (tensorPullback (a ≫ j)).map q ≫ θ.hom =
      (overComp (a ≫ j) p hi F).hom ≫ q'') :
    (tensorPullback a).map ((overComp j p hj F).inv ≫ (tensorPullback j).map q) ≫
      (expandIso j a L M θ).hom =
        (overComp a p' ha F).hom ≫ q'' := by
  simp only [Functor.map_comp, expandIso, Category.assoc]
  rw [compApp_hom_naturality_assoc, hq]
  rw [← overComp_paste p p' p'' j a hj ha hi F]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem closed_kernel_of_factorizations {X Y Z : Scheme.{u}}
    (z : Z ⟶ X) [IsClosedImmersion z] (i : Y ⟶ X)
    (k : Y ⟶ Z) (v : Z ⟶ Y) (hk : k ≫ z = i) (hvi : v ≫ i = z)
    (hkv : k ≫ v = 𝟙 Y) : IsClosedImmersion i ∧ i.ker = z.ker := by
  have hvk : v ≫ k = 𝟙 Z := by
    apply (cancel_mono z).mp
    rw [Category.assoc, hk, hvi, Category.id_comp]
  let e : Y ≅ Z := ⟨k, v, hkv, hvk⟩
  have : IsIso k := e.isIso_hom
  have hclosed : IsClosedImmersion i := by
    rw [← hk]
    infer_instance
  refine ⟨hclosed, ?_⟩
  rw [← hk, Scheme.Hom.ker_comp_of_isIso]

private def QuotientUniversal {S X : Scheme.{u}} (p : X ⟶ S)
    (F : S.Modules) (L : X.Modules) (q : (tensorPullback p).obj F ⟶ L) : Prop :=
  ∀ (T : Scheme.{u}) (p' : T ⟶ S) (M : T.Modules) [M.IsInvertible]
    (q' : (tensorPullback p').obj F ⟶ M) [Epi q'],
    ∃! j : T ⟶ X, ∃ hj : j ≫ p = p', ∃ θ : (tensorPullback j).obj L ≅ M,
      (tensorPullback j).map q ≫ θ.hom = (overComp j p hj F).hom ≫ q'

private theorem realization_quotient_universal {S : Scheme.{u}} {F : S.Modules}
    (n : ℕ) [F.IsFiniteLocallyFreeOfRank (n + 1)]
    (P : ProjectiveBundleRealization S F) :
    QuotientUniversal P.A.data.relProjHom F P.L P.quotient := by
  intro T p M _ q _
  obtain ⟨i, hi, θ, hθ⟩ := realization_quotient_exists n P T p M q
  have hθ' : (tensorPullback i).map P.quotient ≫ θ.hom =
      (overComp i P.A.data.relProjHom hi F).hom ≫ q := by
    simpa only [overComp, Category.assoc] using hθ
  refine ⟨i, ⟨hi, θ, hθ'⟩, ?_⟩
  rintro j ⟨hj, δ, hδ⟩
  exact realization_quotient_unique_over n P T p M q j i hj hi δ θ hδ hθ'

-- The categorical argument uses schemes as parameters rather than unfolding their presentations.
private theorem closed_kernel_of_universal_quotients
    {S X Y Z : Scheme.{u}} (L F G : S.Modules)
    (ι : L ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)
    (hexact : (ShortComplex.mk ι π w).ShortExact)
    (p : X ⟶ S) (pQ : Y ⟶ S) (PL : X.Modules) (QL : Y.Modules)
    [PL.IsInvertible] [QL.IsInvertible]
    (qP : (tensorPullback p).obj F ⟶ PL) [Epi qP]
    (qQ : (tensorPullback pQ).obj G ⟶ QL) [Epi qQ]
    (hP : QuotientUniversal p F PL qP) (hQ : QuotientUniversal pQ G QL qQ)
    (z : Z ⟶ X) [IsClosedImmersion z]
    (hzφ : (tensorPullback z).map ((tensorPullback p).map ι ≫ qP) = 0)
    (i : Y ⟶ X) (hi : i ≫ p = pQ) (θi : (tensorPullback i).obj PL ≅ QL)
    (hθi : (tensorPullback i).map qP ≫ θi.hom =
      (overComp i p hi F).hom ≫ (tensorPullback pQ).map π ≫ qQ)
    (hbound : z.ker ≤ i.ker) : IsClosedImmersion i ∧ i.ker = z.ker := by
  have := hexact.epi_g
  let pZ := z ≫ p
  let M := (tensorPullback z).obj PL
  let qZ : (tensorPullback pZ).obj F ⟶ M :=
    (overComp z p rfl F).inv ≫ (tensorPullback z).map qP
  let qQF := (tensorPullback pQ).map π ≫ qQ
  let : (tensorPullback z).IsLeftAdjoint :=
    (projectiveBundlePullbackAdjunction z).isLeftAdjoint
  have : M.IsInvertible := Scheme.Modules.IsInvertible.of_iso
    ((projectiveBundleTensorPullbackIso z).app PL).symm
  have : Epi qZ := inferInstance
  have hqZ : (tensorPullback pZ).map ι ≫ qZ = 0 := by
    have hn := overComp_naturality z p rfl ι
    have he := congrArg (fun t ↦ (overComp z p rfl L).inv ≫ t ≫
      (overComp z p rfl F).inv) hn
    simp only [Category.assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id, Category.comp_id] at he
    change (tensorPullback pZ).map ι ≫ (overComp z p rfl F).inv ≫
      (tensorPullback z).map qP = 0
    rw [← Category.assoc, ← he, Category.assoc, ← Functor.map_comp,
      hzφ, comp_zero]
  obtain ⟨ε, hε⟩ := quotient_desc ι π w hexact pZ M qZ hqZ
  have : Epi ((tensorPullback pZ).map π ≫ ε) := hε.symm ▸ (inferInstance : Epi qZ)
  have : Epi ε := epi_of_epi ((tensorPullback pZ).map π) ε
  obtain ⟨v, ⟨hv, θv, hθv'⟩, -⟩ := hQ Z pZ M ε
  have hvF := quotient_precompose_square pQ pZ π qQ ε v hv θv hθv'
  rw [hε] at hvF
  have hviOver : (v ≫ i) ≫ p = pZ := by rw [Category.assoc, hi, hv]
  let θvi : (tensorPullback (v ≫ i)).obj PL ≅ M :=
    pasteIso i v PL QL M θi θv
  have hθvi : (tensorPullback (v ≫ i)).map qP ≫ θvi.hom =
      (overComp (v ≫ i) p hviOver F).hom ≫ qZ :=
    quotient_over_paste p pQ pZ F PL QL M qP qQF qZ i v hi hv hviOver
      θi θv hθi hvF
  have hzsquare : (tensorPullback z).map qP ≫ (Iso.refl M).hom =
      (overComp z p rfl F).hom ≫ qZ := by
    simpa only [Iso.refl_hom, qZ, Iso.hom_inv_id_assoc] using
      Category.comp_id ((tensorPullback z).map qP)
  obtain ⟨a, -, ha⟩ := hP Z pZ M qZ
  have hvi : v ≫ i = z :=
    (ha _ ⟨hviOver, θvi, hθvi⟩).trans (ha _ ⟨rfl, Iso.refl M, hzsquare⟩).symm
  let k : Y ⟶ Z :=
    IsClosedImmersion.lift z i hbound
  have hk : k ≫ z = i := IsClosedImmersion.lift_fac z i _
  have hkp : k ≫ pZ = pQ := by
    change k ≫ (z ≫ p) = pQ
    rw [← Category.assoc, hk, hi]
  have hkzOver : (k ≫ z) ≫ p = pQ := by rw [hk, hi]
  let θk : (tensorPullback k).obj M ≅ QL :=
    expandIso z k PL QL (reindexIso hk PL QL θi)
  have hθkz := quotient_square_reindex p pQ F PL QL qP qQF
    hk hkzOver hi θi hθi
  have hθk : (tensorPullback k).map qZ ≫ θk.hom =
      (overComp k pZ hkp F).hom ≫ qQF :=
    quotient_pullback_square p pZ pQ F PL QL qP qQF z k rfl hkp
      hkzOver (reindexIso hk PL QL θi) hθkz
  have hkvOver : (k ≫ v) ≫ pQ = pQ := by rw [Category.assoc, hv, hkp]
  let θkv : (tensorPullback (k ≫ v)).obj QL ≅ QL :=
    pasteIso v k QL M QL θv θk
  have hθkvF : (tensorPullback (k ≫ v)).map qQF ≫ θkv.hom =
      (overComp (k ≫ v) pQ hkvOver F).hom ≫ qQF :=
    quotient_over_paste pQ pZ pQ F QL M QL qQF qZ qQF v k hv hkp hkvOver
      θv θk hvF hθk
  have hθkvG := quotient_cancel_precompose pQ pQ π qQ qQ
    (k ≫ v) hkvOver θkv hθkvF
  obtain ⟨b, -, hb⟩ := hQ Y pQ QL qQ
  have hkv : k ≫ v = 𝟙 Y :=
    (hb _ ⟨hkvOver, θkv, hθkvG⟩).trans
      (hb _ ⟨Category.id_comp pQ, (projectiveBundlePullbackId _).app QL,
        identity_quotient_square pQ G QL qQ⟩).symm
  exact closed_kernel_of_factorizations z i k v hk hvi hkv

private theorem closed_kernel_from_quotient
    (S : Scheme.{u}) (r : ℕ) (hr : 2 ≤ r) (L F G : S.Modules)
    [L.IsInvertible] [F.IsFiniteLocallyFreeOfRank r]
    [G.IsFiniteLocallyFreeOfRank (r - 1)]
    (ι : L ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)
    (hexact : (ShortComplex.mk ι π w).ShortExact)
    (P : ProjectiveBundleRealization S F) (Q : ProjectiveBundleRealization S G)
    (i : Q.A.data.relProj ⟶ P.A.data.relProj)
    (hi : i ≫ P.A.data.relProjHom = Q.A.data.relProjHom)
    (θi : (tensorPullback i).obj P.L ≅ Q.L)
    (hθi : (tensorPullback i).map P.quotient ≫ θi.hom =
      (overComp i P.A.data.relProjHom hi F).hom ≫
        (tensorPullback Q.A.data.relProjHom).map π ≫ Q.quotient) :
    IsClosedImmersion i ∧ i.ker = (lineSubbundleProjectiveSection P ι).zeroLocus := by
  have := realization_invertible P
  have := realization_invertible Q
  have := projectiveBundleQuotient_epi P
  have := projectiveBundleQuotient_epi Q
  have : ((tensorPullback P.A.data.relProjHom).obj L).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso
      ((projectiveBundleTensorPullbackIso P.A.data.relProjHom).app L).symm
  let φ := lineSubbundleProjectiveMap P ι
  let z := φ.zeroLocus.subschemeι
  have hzφ : (tensorPullback z).map φ = 0 := vanishes_on_zeroLocus φ
  have hbound : z.ker ≤ i.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, ← section_zeroLocus P ι]
    apply quotient_zeroLocus_le_ker ι π w P Q i hi θi
    simpa only [overComp, Category.assoc] using hθi
  have hrF : (r - 1) + 1 = r := by omega
  have hrG : (r - 2) + 1 = r - 1 := by omega
  let : F.IsFiniteLocallyFreeOfRank ((r - 1) + 1) := by
    simpa only [hrF] using (inferInstance : F.IsFiniteLocallyFreeOfRank r)
  let : G.IsFiniteLocallyFreeOfRank ((r - 2) + 1) := by
    simpa only [hrG] using (inferInstance : G.IsFiniteLocallyFreeOfRank (r - 1))
  obtain ⟨hc, hk⟩ := closed_kernel_of_universal_quotients L F G ι π w hexact
    P.A.data.relProjHom Q.A.data.relProjHom P.L Q.L P.quotient Q.quotient
    (realization_quotient_universal (r - 1) P)
    (realization_quotient_universal (r - 2) Q) z hzφ i hi θi hθi hbound
  refine ⟨hc, hk.trans ?_⟩
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact (section_zeroLocus P ι).symm


/-- Steps 1-5 of the line-subbundle divisor theorem: the quotient projective bundle is the
regular zero divisor of the tautological section, with the normalized divisor-line comparison.
Source: Stacks Project, Tag 0FI5, `proposition-chern-class`, line-subbundle paragraph;
Tags 01OB and 01X0. The proof in words is in the module docstring.
(blueprint: lem-pur-line-subbundle-projective-divisor-core). -/
theorem lineSubbundle_projective_divisor_core
    (S : Scheme.{u}) (r : ℕ) (hr : 2 ≤ r)
    (L F G : S.Modules) [L.IsInvertible]
    [F.IsFiniteLocallyFreeOfRank r] [G.IsFiniteLocallyFreeOfRank (r - 1)]
    (ι : L ⟶ F) (π : F ⟶ G) (w : ι ≫ π = 0)
    (hexact : (ShortComplex.mk ι π w).ShortExact)
    (P : ProjectiveBundleRealization S F) (Q : ProjectiveBundleRealization S G) :
    P.L.IsInvertible ∧ Q.L.IsInvertible ∧
    ∃ (i : Q.A.data.relProj ⟶ P.A.data.relProj)
      (hi : i ≫ P.A.data.relProjHom = Q.A.data.relProjHom)
      (θ : (Scheme.Modules.tensorPullback i).obj P.L ≅ Q.L),
      IsClosedImmersion i ∧
      (Scheme.Modules.tensorPullback i).map P.quotient ≫ θ.hom =
        ((projectiveBundlePullbackComp i P.A.data.relProjHom).app F).hom ≫
          (projectiveBundlePullbackCongr hi).hom.app F ≫
          (Scheme.Modules.tensorPullback Q.A.data.relProjHom).map π ≫ Q.quotient ∧
      i.ker = (lineSubbundleProjectiveSection P ι).zeroLocus ∧
      (lineSubbundleProjectiveSection P ι).zeroLocus.IsInvertible ∧
      IsEffectiveCartierCenter i ∧
      (∃ δ : i.ker.toModulesᵛ ≅
          P.L ⊗ (Scheme.Modules.tensorPullback P.A.data.relProjHom).obj Lᵛ,
        Scheme.Modules.dualUnitIso.inv ≫ Scheme.Modules.dualMap i.ker.toModulesι ≫ δ.hom =
          lineSubbundleProjectiveSection P ι) := by
  have hP := realization_invertible P
  have hQ := realization_invertible Q
  have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  have := hexact.epi_g
  have := projectiveBundleQuotient_epi Q
  let : (Scheme.Modules.tensorPullback Q.A.data.relProjHom).IsLeftAdjoint :=
    (projectiveBundlePullbackAdjunction Q.A.data.relProjHom).isLeftAdjoint
  have hr' : r - 1 + 1 = r := by omega
  let : F.IsFiniteLocallyFreeOfRank (r - 1 + 1) := by
    simpa only [hr'] using (inferInstance : F.IsFiniteLocallyFreeOfRank r)
  obtain ⟨i, hi, θ, hθ⟩ := realization_quotient_exists (r - 1) P
    Q.A.data.relProj Q.A.data.relProjHom Q.L
    ((Scheme.Modules.tensorPullback Q.A.data.relProjHom).map π ≫ Q.quotient)
  have hθ' : (Scheme.Modules.tensorPullback i).map P.quotient ≫ θ.hom =
      ((projectiveBundlePullbackComp i P.A.data.relProjHom).app F).hom ≫
        (projectiveBundlePullbackCongr hi).hom.app F ≫
        (Scheme.Modules.tensorPullback Q.A.data.relProjHom).map π ≫ Q.quotient := by
    simpa only [compApp, Category.assoc] using hθ
  obtain ⟨hc, hk⟩ := closed_kernel_from_quotient
    S r hr L F G ι π w hexact P Q i hi θ (by
      simpa only [overComp, Iso.trans_hom, Iso.app_hom, Category.assoc] using hθ)
  have hs := map_regular_from_adapted_frames S r hr L F G ι π w hexact P
  have : IsClosedImmersion i := hc
  refine ⟨hP, hQ, i, hi, θ, hc, hθ', hk, hs, ?_, ?_⟩
  · apply isEffectiveCartierCenter_iff_isInvertible_ker.mpr
    rwa [hk]
  · have : ((Scheme.Modules.tensorPullback P.A.data.relProjHom).obj Lᵛ).IsInvertible :=
      Scheme.Modules.IsInvertible.of_iso
        ((projectiveBundleTensorPullbackIso P.A.data.relProjHom).app Lᵛ).symm
    rw [hk]
    exact section_divisor_comparison (lineSubbundleProjectiveSection P ι) hs

end AlgebraicGeometry

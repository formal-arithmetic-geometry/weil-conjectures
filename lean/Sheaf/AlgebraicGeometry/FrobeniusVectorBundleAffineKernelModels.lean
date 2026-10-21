/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V8
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.AlgebraicGeometry.FrobeniusPolynomialSolutions
import Sheaf.AlgebraicGeometry.FrobeniusVectorBundleLocalCoordinates
import Mathlib.CategoryTheory.Sites.Subcanonical
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Local Frobenius equations on finite locally free modules -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

open Modules
attribute [local instance 3000] CategoryStruct.toQuiver
attribute [local instance 2000]
 instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj

private theorem kernelLift {X : Scheme.{u}}
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (D : G ⟶ G)
    (V : X.Etale) (x : G.obj.obj (op V)) (hx : D.hom.app (op V) x = 0) :
    ∃ t : (kernel D).obj.obj (op V), (kernel.ι D).hom.app (op V) t = x := by
  let Ev := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj (op V)
  let e := PreservesKernel.iso Ev D ≪≫ AddCommGrpCat.kernelIsoKer (Ev.map D)
  refine ⟨e.inv ⟨x, hx⟩, ?_⟩
  change (e.inv ≫ Ev.map (kernel.ι D)) ⟨x, hx⟩ = x
  rw [Iso.trans_inv, Category.assoc, PreservesKernel.iso_inv_ι,
    AddCommGrpCat.kernelIsoKer_inv_comp_ι]
  rfl

private theorem kernelCoordinatesRepresentable
    (X : Scheme.{u}) [IsAffine X] (p : ℕ) [Fact p.Prime]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (F : G ⟶ G)
    (n : ℕ) (c : Fin n → Fin n → Γ(X, ⊤))
    (e : ∀ V : X.Etale, G.obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)))
    (hp : (p : Γ(X, ⊤)) = 0)
    (hnat : ∀ (V W : X.Etale) (g : W ⟶ V) (s : G.obj.obj (op V)),
      ∀ i, e W (G.obj.map g.op s) i = g.left.appTop (e V s i))
    (heq : ∀ (V : X.Etale) (s : G.obj.obj (op V)),
      ∀ i, e V (F.hom.app (op V) s) i =
        ∑ j, (@id Γ(V.left, ⊤) (V.hom.appTop (c i j))) * (e V s j) ^ p) :
    ∃ (P : Scheme.{u}) (π : P ⟶ X), IsAffine P ∧ ∃ _ : Etale π,
      Nonempty ((sheafCompose X.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj (kernel (F - 𝟙 _)) ≅
          X.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk π)) := by
  classical
  let D := F - 𝟙 G
  obtain ⟨P, π, y, hP, hπ, -, hy, huni⟩ :=
    frobenius_polynomial_solution_cover X p hp n c 0
  have : Etale π := hπ
  let VP : X.Etale := Etale.mk π
  let t := (e VP).symm y
  have ht : D.hom.app (op VP) t = 0 := by
    apply (e VP).injective
    ext i
    change e VP (F.hom.app (op VP) t - t) i = e VP 0 i
    rw [map_sub, Pi.sub_apply, heq, AddEquiv.apply_symm_apply, map_zero, Pi.zero_apply]
    convert (by simpa only [Pi.zero_apply, map_zero] using hy i) using 1 <;> rfl
  obtain ⟨tK, htK⟩ := kernelLift D VP t ht
  let H := (sheafCompose X.smallEtaleTopology
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj (kernel D)
  let α : X.smallEtaleTopology.uliftYoneda.{u + 1}.obj VP ⟶ H :=
    (GrothendieckTopology.uliftYonedaEquiv (J := X.smallEtaleTopology)).symm tK
  have hα (V : X.Etale) (g : V ⟶ VP) :
      e V ((kernel.ι D).hom.app (op V) (α.hom.app (op V) (ULift.up g))) =
        fun i ↦ g.left.appTop (y i) := by
    change e V ((kernel.ι D).hom.app (op V) ((kernel D).obj.map g.op tK)) = _
    have hn := ConcreteCategory.congr_hom ((kernel.ι D).hom.naturality g.op) tK
    simp only [ConcreteCategory.comp_apply] at hn
    rw [hn, htK]
    ext i
    rw [hnat]
    simp only [t, AddEquiv.apply_symm_apply]
  have hbij (V : X.Etale) : Function.Bijective (α.hom.app (op V)) := by
    constructor
    · rintro ⟨g⟩ ⟨h⟩ hgh
      apply ULift.ext
      apply MorphismProperty.Over.Hom.ext
      have hg : ∀ i, g.left.appTop (y i) = h.left.appTop (y i) := by
        have hh := congrArg (fun z ↦ e V ((kernel.ι D).hom.app (op V) z)) hgh
        rw [hα, hα] at hh
        exact congrFun hh
      have hhsol : ∀ i, ∑ j, (@id Γ(V.left, ⊤) (V.hom.appTop (c i j))) *
          (h.left.appTop (y j)) ^ p - h.left.appTop (y i) =
            V.hom.appTop ((0 : Fin n → Γ(X, ⊤)) i) := by
        intro i
        have hh := congrArg h.left.appTop (hy i)
        have hw : h.left ≫ π = V.hom := h.w
        have hcoeff (a : Γ(X, ⊤)) : h.left.appTop (π.appTop a) = V.hom.appTop a := by
          convert (ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop hw) a)
            using 1 <;> rfl
        simpa only [map_sub, map_sum, map_mul, map_pow, hcoeff, id_eq] using hh
      obtain ⟨z, hz, hzuniq⟩ := huni V.left V.hom (fun i ↦ h.left.appTop (y i)) hhsol
      exact (hzuniq g.left ⟨g.w, hg⟩).trans (hzuniq h.left ⟨h.w, fun _ ↦ rfl⟩).symm
    · intro s
      let z := (kernel.ι D).hom.app (op V) s
      have hz : D.hom.app (op V) z = 0 := by
        have hc := congrArg (fun k ↦ k.hom.app (op V) s) (kernel.condition D)
        exact hc
      have hsol : ∀ i, ∑ j, (@id Γ(V.left, ⊤) (V.hom.appTop (c i j))) * (e V z j) ^ p - e V z i =
          V.hom.appTop ((0 : Fin n → Γ(X, ⊤)) i) := by
        intro i
        have h := congrArg (fun s ↦ e V s i) hz
        change e V (F.hom.app (op V) z - z) i = e V 0 i at h
        simpa only [map_sub, Pi.sub_apply, heq, map_zero, Pi.zero_apply] using h
      obtain ⟨g, hg, -⟩ := huni V.left V.hom (e V z) hsol
      let k : V ⟶ VP := MorphismProperty.Over.homMk g hg.1 trivial
      refine ⟨ULift.up k, ?_⟩
      have hmono : Function.Injective ((kernel.ι D).hom.app (op V)) := by
        let Ev := sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
          (CategoryTheory.evaluation _ _).obj (op V)
        exact (AddCommGrpCat.mono_iff_injective (Ev.map (kernel.ι D))).mp inferInstance
      apply hmono
      apply (e V).injective
      rw [hα]
      exact funext hg.2
  have : ∀ V, IsIso (α.hom.app V) := fun V ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr (hbij V.unop)
  have : IsIso α.hom := NatIso.isIso_of_isIso_app _
  have : IsIso ((sheafToPresheaf X.smallEtaleTopology (Type (u + 1))).map α) := by
    change IsIso α.hom
    infer_instance
  have : IsIso α := isIso_of_reflects_iso α (sheafToPresheaf _ _)
  exact ⟨P, π, hP, hπ, ⟨(asIso α).symm⟩⟩

-- Keep the kernel/restriction transport behind an irreducible comparison. Its data
-- is the canonical limit comparison, rather than an unfolded sheaf-limit construction.
@[irreducible] private noncomputable def localizedKernelIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [Mono f]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (F : G ⟶ G) :
    (Etale.upperStar AddCommGrpCat.{u + 1} f).obj (kernel (F - 𝟙 G)) ≅
      kernel ((Etale.localizationRestriction AddCommGrpCat.{u + 1} f inferInstance).map F -
        𝟙 ((Etale.localizationRestriction AddCommGrpCat.{u + 1} f inferInstance).obj G)) := by
  let L := Etale.localizationRestriction AddCommGrpCat.{u + 1} f inferInstance
  have : PreservesFiniteLimits L := by
    dsimp only [L, Etale.localizationRestriction]
    exact Functor.preservesFiniteLimits_sheafPushforwardContinuous _ _ _ _
  have hD : L.map (F - 𝟙 G) = L.map F - 𝟙 (L.obj G) := by
    ext V s
    rfl
  exact (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f
    inferInstance).app (kernel (F - 𝟙 G)) ≪≫
      PreservesKernel.iso L (F - 𝟙 G) ≪≫ kernelIsoOfEq hD

private theorem affineKernelModelsOfCoordinates
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [CompactSpace S]
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) (F : G ⟶ G)
    (hcoords :
    ∀ (U : S.Etale) (x : U.left),
      ∃ (A : U.left.Opens) (_ : IsAffineOpen A), x ∈ A ∧
      ∃ (n : ℕ) (c : Fin n → Fin n → Γ(A.toScheme, ⊤)),
      let L := Etale.localizationRestriction (U := S) AddCommGrpCat.{u + 1}
        (A.ι ≫ U.hom) inferInstance
      ∃ e : ∀ V : A.toScheme.Etale,
          (L.obj G).obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤)),
        (p : Γ(A.toScheme, ⊤)) = 0 ∧
        (∀ (V W : A.toScheme.Etale) (g : W ⟶ V) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e W ((L.obj G).obj.map g.op s) i = g.left.appTop (e V s i)) ∧
        (∀ (V : A.toScheme.Etale) (s : (L.obj G).obj.obj (op V)),
          ∀ i, e V ((L.map F).hom.app (op V) s) i =
            ∑ j, (@id Γ(V.left, ⊤) (V.hom.appTop (c i j))) * (e V s j) ^ p)) :
    ∃ (n : ℕ) (W : Fin n → S.Opens),
      (∀ a, IsAffineOpen (W a)) ∧
      (⋃ a : Fin n, (W a : Set S)) = Set.univ ∧
      ∀ a, ∃ (P : Scheme.{u}) (π : P ⟶ (W a).toScheme),
        IsAffine P ∧ ∃ _ : Etale π, Nonempty
          ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
            ((Etale.upperStar AddCommGrpCat.{u + 1} (W a).ι).obj
              (kernel (F - 𝟙 _))) ≅
                ((W a).toScheme.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Etale.mk π)) := by
  classical
  have hlocal (x : S) : ∃ W : S.Opens, IsAffineOpen W ∧ x ∈ W ∧
      ∃ (P : Scheme.{u}) (π : P ⟶ W.toScheme), IsAffine P ∧ ∃ _ : Etale π,
        Nonempty ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} W.ι).obj (kernel (F - 𝟙 _))) ≅
            W.toScheme.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk π)) := by
    have hc0 := hcoords (Etale.mk (𝟙 S)) x
    obtain ⟨W, hW, hxW, n, c, e, hp, hnat, heq⟩ := hc0
    change S.Opens at W
    have : IsAffine W.toScheme := hW
    let L := Etale.localizationRestriction AddCommGrpCat.{u + 1} W.ι inferInstance
    change (∀ V : W.toScheme.Etale,
      (L.obj G).obj.obj (op V) ≃+ (Fin n → Γ(V.left, ⊤))) at e
    change (∀ (V W' : W.toScheme.Etale) (g : W' ⟶ V)
      (s : (L.obj G).obj.obj (op V)) (i : Fin n),
      e W' ((L.obj G).obj.map g.op s) i = g.left.appTop (e V s i)) at hnat
    change (∀ (V : W.toScheme.Etale) (s : (L.obj G).obj.obj (op V)) (i : Fin n),
      e V ((L.map F).hom.app (op V) s) i =
        ∑ j, (@id Γ(V.left, ⊤) (V.hom.appTop (c i j))) * (e V s j) ^ p) at heq
    obtain ⟨P, π, hP, hπ, ⟨eP⟩⟩ :=
      kernelCoordinatesRepresentable W.toScheme p (L.obj G) (L.map F) n c e hp hnat heq
    let eK := localizedKernelIso W.ι G F
    exact ⟨W, hW, hxW, P, π, hP, hπ,
      ⟨(sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).mapIso eK ≪≫ eP⟩⟩
  choose W hW hxW P π hP hπ e using hlocal
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (W x : Set S))
    (fun x ↦ (W x).isOpen) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxW x⟩)
  let f : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  refine ⟨Fintype.card t, fun a ↦ W (f a).1, fun a ↦ hW _, ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨f.symm ⟨a, ha⟩, by simpa [f] using hxa⟩
  · intro a
    exact ⟨P (f a).1, π (f a).1, hP _, hπ _, e _⟩

/-- On finitely many affine charts, the fixed-point sheaf is represented by an affine
étale scheme. The ranks on different charts need not agree.

Source: Stacks Project, More on Étale Cohomology, Tag 0GKU,
label lemma-frobenius-linear-on-vb, first and constructibility paragraphs.
(blueprint: lem-weil-pbc-frobenius-vector-bundle-affine-kernel-models)

Proof: Local freeness and the affine-open basis give affine trivializing opens; compactness
extracts a finite subcover, indexed by Fin n. On a chart Spec A of rank r, write the images
of the basis sections as the columns of c. Semilinearity and naturality say that fixed
sections on an étale T over this chart are the coordinate tuples satisfying
x_i - sum_j c_ij x_j^p = 0 in Γ(T,O_T). Let P be the spectrum of the polynomial ring over A
modulo these relations. Its Jacobian is the identity, so P is étale over the chart.
Both schemes are affine. The universal property of the quotient ring and the Spec/global
sections adjunction identify morphisms T to P over the chart with precisely those tuples.
This identification is natural in T and is additive on its fixed-section side. Limits of
abelian sheaves are computed sectionwise, so this identifies the underlying set sheaf of
the categorical kernel. The étale inverse-image/restriction comparison identifies its
restriction with the displayed upperStar. Lift morphisms and coordinate tuples into the
same universe with ULift. For the empty scheme choose n=0; for rank zero the quotient is A
and P is the chart itself, representing the one-element underlying zero group. -/
theorem frobenius_vectorBundle_affine_kernel_models
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u})
    [S.Over (Spec (.of (ULift.{u} (ZMod p))))] [CompactSpace S] [IsLocallyNoetherian S]
    (E : S.Modules) [E.IsFiniteLocallyFree]
    (F : (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E) ⟶
      (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf E))
    (hF : ∀ (U : S.Etaleᵒᵖ) (a : ULift.{u + 1} Γ(U.unop.left, ⊤))
        (e : ULift.{u + 1} Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)),
      F.hom.app U (ULift.up (a.down • e.down)) =
        ULift.up (a.down ^ p • (@id Γ((Modules.tensorPullback U.unop.hom).obj E, ⊤)
          (F.hom.app U e).down))) :
    ∃ (n : ℕ) (W : Fin n → S.Opens),
      (∀ a, IsAffineOpen (W a)) ∧
      (⋃ a : Fin n, (W a : Set S)) = Set.univ ∧
      ∀ a, ∃ (P : Scheme.{u}) (π : P ⟶ (W a).toScheme),
        IsAffine P ∧ ∃ _ : Etale π, Nonempty
          ((sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
            ((Etale.upperStar AddCommGrpCat.{u + 1} (W a).ι).obj
              (kernel (F - 𝟙 _))) ≅
                ((W a).toScheme.smallEtaleTopology.uliftYoneda.{u + 1}).obj (Etale.mk π)) := by
  exact affineKernelModelsOfCoordinates p S _ F
    (frobenius_vectorBundle_local_coordinates p S E F hF)

end AlgebraicGeometry.Scheme

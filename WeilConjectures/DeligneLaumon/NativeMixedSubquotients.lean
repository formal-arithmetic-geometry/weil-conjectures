/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
import all WeilConjectures.DeligneLaumon.NativeMixedExtensions
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.WeilObject.Sheaf.StalkFiniteFree
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective

/-! # Constructible subquotients of native mixed Weil modules

Source: latest blueprint, lem-zl-composition-weight-bound.proof.md, paragraph 2
(blueprint: lem-zl-native-mixed-subquotients).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.DeligneLaumon
open NativeCondensedModule

private theorem lfp_comap_iso {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsLocallyFinitelyPresented S M) :
    IsLocallyFinitelyPresented R ((Mod.comap φ).obj M) := by
  obtain ⟨U, hU⟩ := h
  refine ⟨U, fun i ↦ ?_⟩
  let F := upperStar Ab.{u + 1} (U.f i)
  exact ((hU i).comap (F.map φ)).of_iso ((F.mapModComapIso φ).app M).symm

private theorem lfp_transport {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (e : M ≅ N) (h : IsLocallyFinitelyPresented R M) :
    IsLocallyFinitelyPresented R N := by
  obtain ⟨U, hU⟩ := h
  exact ⟨U, fun i ↦ (hU i).of_iso
    (((upperStar Ab.{u + 1} (U.f i)).mapMod R).mapIso e)⟩

private theorem constant_constructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    IsConstructibleModuleObject (condensedRingObj Λ X) M := by
  classical
  rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩] at hM
  obtain ⟨S, hS⟩ := hM
  refine ⟨S, fun a ↦ ?_⟩
  exact lfp_transport (CondensedRing.comapUpperStarObjIso Λ (S.immersion a) M)
    (lfp_comap_iso (condensedPullbackHom Λ (S.immersion a))
      ((hS a).isLocallyFinitelyPresented _))

set_option maxHeartbeats 2000000 in
-- The internal-module presentation and finite-biproduct comparison are large.
private theorem finiteDimensional_fibre (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (M : Modules l X)
    (hM : IsConstantModelConstructible (Profinite.padicAlgClRingObj l) X M)
    (z : Spec (.of D.k) ⟶ X) :
    FiniteDimensional (ULift.{u + 1} (PadicAlgCl l)) (fibre l D M z) := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let S := pointSections l D.k
  have : S.Additive := by dsimp [S, pointSections]; infer_instance
  have : PreservesFiniteBiproducts S := by dsimp [S, pointSections]; infer_instance
  obtain ⟨n, m, f, ⟨e⟩⟩ :=
    CondensedRing.isFinitelyPresented_upperStar_of_isConstructibleModuleObject
      (Profinite.padicAlgClRingObj l) (Field.toIsField D.k) IsField.isSepClosed_toField
      (constant_constructible (Profinite.padicAlgClRingObj l) M hM) z
  obtain ⟨r, ⟨er⟩⟩ := Limits.exists_iso_biproduct_cokernel
    (CondensedRing.isIso_of_ne_zero_end_tensorUnit l (Field.toIsField D.k)
      IsField.isSepClosed_toField) (Iso.refl _) (Iso.refl _) f
  let es := S.mapIso (e ≪≫ er) ≪≫ S.mapBiproduct _ ≪≫
    biproduct.mapIso (fun _ : Fin r ↦ (pointSectionsUnitIso l D.k).symm) ≪≫
    ModuleCat.biproductIsoPi _
  exact Module.Finite.equiv es.toLinearEquiv.symm

private theorem eigenvalue_surjective
    {K M N : Type*} [Field K] [AddCommGroup M] [AddCommGroup N]
    [Module K M] [Module K N] [FiniteDimensional K M]
    (A : Module.End K M) (B : Module.End K N) (g : M →ₗ[K] N)
    (hg : ∀ v, g (A v) = B (g v)) (hs : Function.Surjective g)
    {α : K} (hα : B.HasEigenvalue α) : A.HasEigenvalue α := by
  by_contra hA
  obtain ⟨y, hy⟩ := hα.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at hy
  let T := A - α • LinearMap.id
  have ht : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro v hv
    by_contra h0
    apply hA
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := v)
    rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
    exact ⟨sub_eq_zero.mp hv, h0⟩
  have hgt (v : M) : g (T v) = B (g v) - α • g v := by simp [T, hg]
  have hm : ∀ v ∈ LinearMap.ker g, T v ∈ LinearMap.ker g := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hgt, hv, map_zero, smul_zero, sub_zero]
  have ht' : Function.Injective (T.restrict hm) :=
    fun a b h ↦ Subtype.ext (ht (congrArg Subtype.val h))
  have hs' := LinearMap.injective_iff_surjective.mp ht'
  obtain ⟨x, rfl⟩ := hs y
  have hx : T x ∈ LinearMap.ker g := by
    rw [LinearMap.mem_ker, hgt, hy.1, sub_self]
  obtain ⟨z, hz⟩ := hs' ⟨T x, hx⟩
  have hzx : (z : M) = x := ht (congrArg Subtype.val hz)
  apply hy.2
  rw [← hzx]
  exact z.2

private theorem operator_eigenvalue_of_epi (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) {T : Scheme.{u}} (a : T ⟶ T) (M N : Modules l T)
    (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj M ≅ M)
    (η : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).obj N ≅ N)
    (f : M ⟶ N) [Epi f]
    (hf : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a).map f ≫ η.hom =
      θ.hom ≫ f) (z : Spec (.of D.k) ⟶ T) (n : ℕ)
    (h : z ≫ localPositivePower a n =
      localPositivePower (frobeniusPointIso D).hom n ≫ z)
    [FiniteDimensional (ULift.{u + 1} (PadicAlgCl l)) (fibre l D M z)]
    (α : ULift.{u + 1} (PadicAlgCl l))
    (hα : Module.End.HasEigenvalue (operator l D a N η z n h).hom α) :
    Module.End.HasEigenvalue (operator l D a M θ z n h).hom α := by
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have : Projective (𝟙_ (Modules l (Spec (.of D.k)))) :=
    projective_regular_of_isSepClosed
      (condensedRingObj (Profinite.padicAlgClRingObj l) (Spec (.of D.k)))
  have : (preadditiveCoyonedaObj (𝟙_ (Modules l (Spec (.of D.k))))).PreservesEpimorphisms :=
    (Projective.projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj _).mp
      inferInstance
  have : (ModuleCat.restrictScalars (pointScalarsOp l D.k)).PreservesEpimorphisms :=
    ⟨fun f hf ↦ by
      apply (ModuleCat.epi_iff_surjective _).mpr
      exact (ModuleCat.epi_iff_surjective f).mp hf⟩
  have : (pointSections l D.k).PreservesEpimorphisms := by
    unfold pointSections
    infer_instance
  let t := (pointSections l D.k).map
    ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).map f)
  have : Epi t := Functor.map_epi _ _
  have ht : Function.Surjective t.hom := (ModuleCat.epi_iff_surjective t).mp inferInstance
  have : FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
      ((pointSections l D.k).obj
        ((CondensedRing.upperStar (Profinite.padicAlgClRingObj l) z).obj M)) :=
    inferInstanceAs (FiniteDimensional _ (fibre l D M z))
  apply eigenvalue_surjective _ _ t.hom ?_ ht hα
  intro v
  exact congrArg (fun k ↦ k.hom v)
    (NativeLocal.operator_naturality l D a M N θ η f hf z n h)

private theorem native_map_epi
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {F G : NativeL2.WeilModule D l X₀} (f : F ⟶ G) [Epi f] : Epi f.hom.f :=
  (CategoryTheory.Endofunctor.IsoAlgebra.forget _).map_epi f

private theorem pure_of_epi
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    {F G : NativeL2.WeilModule D l X₀} (f : F ⟶ G) [Epi f]
    (hF : IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left F.carrier)
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    (hp : NativeL2.Pure D l X₀ F iota w) :
    NativeL2.Pure D l X₀ G iota w := by
  have : LocallyOfFiniteType (D.geometricFiber X₀).hom := by
    exact inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom _))
  have : QuasiCompact (D.geometricFiber X₀).hom := by
    exact inferInstanceAs (QuasiCompact (pullback.snd X₀.hom _))
  have : CompactSpace (D.geometricFiber X₀).left :=
    QuasiCompact.compactSpace_of_compactSpace (D.geometricFiber X₀).hom
  have : IsLocallyNoetherian (D.geometricFiber X₀).left :=
    LocallyOfFiniteType.isLocallyNoetherian (D.geometricFiber X₀).hom
  have : IsNoetherian (D.geometricFiber X₀).left := ⟨⟩
  intro x i hi α hα
  rw [NativeLocal.closedOperator_eq] at hα
  apply hp x i hi α
  rw [NativeLocal.closedOperator_eq]
  have : Epi f.hom.f := native_map_epi D l X₀ f
  have : FiniteDimensional (ULift.{u + 1} (PadicAlgCl l))
      (fibre l D F.carrier (localClosedPoint D X₀ x i hi)) :=
    finiteDimensional_fibre l D F.carrier hF _
  exact operator_eigenvalue_of_epi l D (D.geometricFrobenius X₀).hom
    F.carrier G.carrier F.str G.str f.hom.f f.hom.h _ _ _ α hα

private theorem constructible_filtration
    {C : Type*} [Category* C] [Abelian C] (P Q : ObjectProperty C)
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions]
    {M : C} (h : (P ⊓ Q).filtrationClosure M) : P M := by
  induction h with
  | of_isZero hz => exact P.prop_of_isZero hz
  | of_mono i h hi ih =>
    exact P.prop_X₂_of_shortExact
      (show (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact from
        ⟨ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)⟩) ih hi.1

private theorem filtration_subobject
    {C : Type*} [Category* C] [Abelian C] (P Q : ObjectProperty C)
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [Q.IsClosedUnderIsomorphisms]
    (hsub : ∀ {A B : C} (f : A ⟶ B) [Mono f], P A → P B → Q B → Q A)
    {G Y : C} (m : G ⟶ Y) [Mono m] (hG : P G)
    (hY : (P ⊓ Q).filtrationClosure Y) : (P ⊓ Q).filtrationClosure G := by
  induction hY generalizing G with
  | of_isZero hz => exact .of_isZero (hz.of_mono m)
  | @of_mono X Y i _ hX hi ih =>
    let g := m ≫ cokernel.π i
    have hex : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).Exact :=
      ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel i)
    let t := hex.lift (kernel.ι g ≫ m) (by simp [g])
    have ht : t ≫ i = kernel.ι g ≫ m := hex.lift_f _ _
    have : Mono t := mono_of_mono_fac ht
    have hk : P (kernel g) := P.prop_kernel g hG hi.1
    have hco : P (cokernel (kernel.ι g)) := P.prop_cokernel _ hk hG
    have him : P (Abelian.image g) := P.prop_of_iso (Abelian.coimageIsoImage g) hco
    exact .of_mono (kernel.ι g) (ih t hk)
      ((P ⊓ Q).prop_of_iso (Abelian.coimageIsoImage g).symm
        ⟨him, hsub (Abelian.image.ι g) him hi.1 hi.2⟩)

private theorem filtration_quotient
    {C : Type*} [Category* C] [Abelian C] (P Q : ObjectProperty C)
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [Q.IsClosedUnderIsomorphisms]
    (hquot : ∀ {A B : C} (f : A ⟶ B) [Epi f], P A → P B → Q A → Q B)
    {X H : C} (p : X ⟶ H) [Epi p] (hH : P H)
    (hX : (P ⊓ Q).filtrationClosure X) : (P ⊓ Q).filtrationClosure H := by
  induction hX generalizing H with
  | of_isZero hz => exact .of_isZero (hz.of_epi p)
  | @of_mono X₀ X i _ hX₀ hi ih =>
    let f := i ≫ p
    have hf : i ≫ p ≫ cokernel.π f = 0 := by
      rw [← Category.assoc]
      exact cokernel.condition f
    have : Epi (cokernel.desc i (p ≫ cokernel.π f) hf) :=
      epi_of_epi_fac (cokernel.π_desc i (p ≫ cokernel.π f) hf)
    have h₀ : P X₀ := constructible_filtration P Q hX₀
    have hk : P (kernel f) := P.prop_kernel f h₀ hH
    have hco : P (cokernel (kernel.ι f)) := P.prop_cokernel _ hk h₀
    have him : P (Abelian.image f) := P.prop_of_iso (Abelian.coimageIsoImage f) hco
    have hcf : P (cokernel f) := P.prop_cokernel f h₀ hH
    exact .of_mono (Abelian.image.ι f) (ih (Abelian.factorThruImage f) him)
      ((P ⊓ Q).prop_of_iso
        (ObjectProperty.cokernelKernelιIsoOfEpi (cokernel.π f)).symm
        ⟨hcf, hquot (cokernel.desc i (p ≫ cokernel.π f) hf) hi.1 hcf hi.2⟩)

/-- Constructible Weil subobjects and quotients preserve a native mixed upper bound.
Source: latest blueprint, lem-zl-composition-weight-bound.proof.md, paragraph 2,
and lem-a1-mixed-direct-summand.proof.md, Subsheaves and Quotients
(blueprint: lem-zl-native-mixed-subquotients).

Proof: the local Frobenius is natural in an equivariant sheaf morphism. On a
geometric fibre monomorphisms remain injective, so nonzero eigenvectors stay
nonzero. Epimorphisms give surjections: the coefficient unit at a separably
closed point is projective. A constructible fibre is finite-dimensional,
as a cokernel of a map of finite free modules over a field. An eigenvalue
of a quotient is an eigenvalue of the original operator: if A-alpha is
injective it is invertible, including on the invariant kernel of the
quotient map, so the quotient operator cannot have a nonzero alpha-eigenvector.
Intersect a mixed filtration with a subobject; its graded quotients embed
in the original pure quotients. For a quotient take images of the original
filtration; its graded quotients are quotients of the pure quotients.
Kernel and cokernel closure of the constructible heart keeps every term
constructible. The same assigned weights and upper bound therefore work.
Zero-length filtrations and zero graded quotients cause no exception. -/
theorem nativeMixedSubquotients
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (iota : PadicAlgCl l →+* ℂ) (w : ℝ) :
    ∀ (F G : NativeL2.WeilModule D l X₀),
      IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber X₀).left G.carrier →
      NativeL2.Mixed D l X₀ F iota w →
      (∀ (f : G ⟶ F) [Mono f], NativeL2.Mixed D l X₀ G iota w) ∧
      (∀ (f : F ⟶ G) [Epi f], NativeL2.Mixed D l X₀ G iota w) := by
  let P : ObjectProperty (NativeL2.WeilModule D l X₀) := fun M ↦
    IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
      (D.geometricFiber X₀).left M.carrier
  let Q : ObjectProperty (NativeL2.WeilModule D l X₀) := fun M ↦
    ∃ v : ℝ, v ≤ w ∧ NativeL2.Pure D l X₀ M iota v
  obtain ⟨hz, hi, hk, hc, he⟩ := native_constructible_closure D l X₀
  have : P.ContainsZero := hz
  have : P.IsClosedUnderIsomorphisms := hi
  have : P.IsClosedUnderKernels := hk
  have : P.IsClosedUnderCokernels := hc
  have : P.IsClosedUnderExtensions := he
  have : Q.IsClosedUnderIsomorphisms := ⟨by
    intro M N e h
    obtain ⟨v, hv, hp⟩ := h
    exact ⟨v, hv, NativeLocal.pure_of_mono D l X₀ e.inv iota v hp⟩⟩
  have hm (M : NativeL2.WeilModule D l X₀) :
      (P ⊓ Q).filtrationClosure M ↔ NativeL2.Mixed D l X₀ M iota w :=
    filtration_with_constructible P Q M
  intro F G hG hF
  constructor
  · intro f _
    apply (hm G).mp
    exact filtration_subobject P Q
      (fun f _ _ _ h ↦ by
        obtain ⟨v, hv, hp⟩ := h
        exact ⟨v, hv, NativeLocal.pure_of_mono D l X₀ f iota v hp⟩)
      f hG ((hm F).mpr hF)
  · intro f _
    apply (hm G).mp
    exact filtration_quotient P Q
      (fun f _ hA _ h ↦ by
        obtain ⟨v, hv, hp⟩ := h
        exact ⟨v, hv, pure_of_epi D l X₀ f hA iota v hp⟩)
      f hG ((hm F).mpr hF)

end WeilConjectures.DeligneLaumon

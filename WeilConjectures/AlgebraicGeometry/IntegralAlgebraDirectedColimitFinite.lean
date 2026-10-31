/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore
import WeilConjectures.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraAffine
import WeilConjectures.AlgebraicGeometry.KernelIdealDirectedPairs
import WeilConjectures.AlgebraicGeometry.FiniteQuotientEventualFiniteness
import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import WeilConjectures.AlgebraicGeometry.AlgebraDirectedColimitFiniteType
import WeilConjectures.AlgebraicGeometry.ModuleDirectedColimitFinitePresentation
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraColimit
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraKernelImageIdeal
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections
import WeilConjectures.RingTheory.SymmetricAlgebraFinitePresentation
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # Integral quasi-coherent algebras as directed colimits

Source: Stacks Project, Properties, Lemma 28.23.13, Tag 0817
(blueprint: lem-weil-pbc-integral-algebra-directed-colimit-finite).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

private theorem subalgebra_finite_iff_finiteType
    {X : Scheme.{v}} (A : QuasiCoherentAlgebra X) (hA : A.obj.IsIntegral)
    (B : Subobject A.obj) :
    (B : X.CommAlgebraSheaf).IsFinite ↔
      ∀ U : X.Opens, IsAffineOpen U →
        ((B : X.CommAlgebraSheaf).hom.hom.app (Opposite.op U)).hom.FiniteType := by
  constructor
  · intro h U hU
    exact (h U hU).to_finiteType
  · intro h U hU
    apply RingHom.IsIntegral.to_finite _ (h U hU)
    have : Mono B.arrow.right := Under.mono_right_of_mono B.arrow
    have : Mono B.arrow.right.hom :=
      (sheafToPresheaf _ CommRingCat).map_mono B.arrow.right
    have : Mono (B.arrow.right.hom.app (Opposite.op U)) := inferInstance
    apply RingHom.IsIntegral.tower_bot
      ((B : X.CommAlgebraSheaf).hom.hom.app (Opposite.op U)).hom
      (B.arrow.right.hom.app (Opposite.op U)).hom
      (CategoryTheory.ConcreteCategory.injective_of_mono_of_preservesPullback
        (B.arrow.right.hom.app (Opposite.op U)))
    have hw := congrArg (fun f ↦ f.hom.app (Opposite.op U)) (Under.w B.arrow)
    change ((B : X.CommAlgebraSheaf).hom.hom.app (Opposite.op U) ≫
      B.arrow.right.hom.app (Opposite.op U)) = A.obj.hom.hom.app (Opposite.op U) at hw
    simpa only [← CommRingCat.hom_comp, hw] using hA U hU

private abbrev moduleFunctor (X : Scheme.{v}) := commAlgebraSheafModuleFunctor X.sheaf

private def symLift {X : Scheme.{v}} (M : X.Modules) (B : X.CommAlgebraSheaf)
    (f : M ⟶ B.toModule) : SymmetricAlgebraSheaf.algebra M ⟶ B :=
  (exists_quasiCoherentSymmetricAlgebra_core X M B f).choose

private theorem symLift_spec {X : Scheme.{v}} (M : X.Modules) (B : X.CommAlgebraSheaf)
    (f : M ⟶ B.toModule) :
    SymmetricAlgebraSheaf.inclusion M ≫ (moduleFunctor X).map (symLift M B f) = f := by
  ext U x
  exact (exists_quasiCoherentSymmetricAlgebra_core X M B f).choose_spec.1 U x

private theorem sym_ext {X : Scheme.{v}} (M : X.Modules) (B : X.CommAlgebraSheaf)
    (f g : SymmetricAlgebraSheaf.algebra M ⟶ B)
    (h : SymmetricAlgebraSheaf.inclusion M ≫ (moduleFunctor X).map f =
      SymmetricAlgebraSheaf.inclusion M ≫ (moduleFunctor X).map g) : f = g := by
  let l := SymmetricAlgebraSheaf.inclusion M ≫ (moduleFunctor X).map g
  have hf : ∀ (U : X.Opens) (x : M.val.obj (op U)),
      f.right.hom.app (op U) ((SymmetricAlgebraSheaf.inclusion M).val.app (op U) x) =
        l.val.app (op U) x := by
    intro U x
    exact congrArg (fun t ↦ t.val.app (op U) x) h
  have hg : ∀ (U : X.Opens) (x : M.val.obj (op U)),
      g.right.hom.app (op U) ((SymmetricAlgebraSheaf.inclusion M).val.app (op U) x) =
        l.val.app (op U) x := fun _ _ ↦ rfl
  exact ((exists_quasiCoherentSymmetricAlgebra_core X M B l).unique hf hg)

private def symDiagram {X : Scheme.{v}} {I : Type v} [Preorder I]
    (F : I ⥤ X.Modules) : I ⥤ X.CommAlgebraSheaf where
  obj i := SymmetricAlgebraSheaf.algebra (F.obj i)
  map {i j} f := symLift (F.obj i) _ (F.map f ≫ SymmetricAlgebraSheaf.inclusion (F.obj j))
  map_id i := by
    apply sym_ext
    rw [symLift_spec, F.map_id, Category.id_comp, (moduleFunctor X).map_id]
    exact (Category.comp_id _).symm
  map_comp {i j k} f g := by
    apply sym_ext
    rw [symLift_spec, (moduleFunctor X).map_comp, ← Category.assoc,
      symLift_spec, Category.assoc, symLift_spec, F.map_comp, Category.assoc]

private def symCocone {X : Scheme.{v}} {I : Type v} [Preorder I]
    (F : I ⥤ X.Modules) (A : X.CommAlgebraSheaf)
    (φ : F ⟶ (Functor.const I).obj A.toModule) : Cocone (symDiagram F) where
  pt := A
  ι :=
    { app i := symLift (F.obj i) A (φ.app i)
      naturality {i j} f := by
        change (symDiagram F).map f ≫ symLift (F.obj j) A (φ.app j) =
          symLift (F.obj i) A (φ.app i) ≫ 𝟙 A
        rw [Category.comp_id]
        change symLift (F.obj i) _
          (F.map f ≫ SymmetricAlgebraSheaf.inclusion (F.obj j)) ≫ _ = _
        apply sym_ext
        rw [(moduleFunctor X).map_comp, ← Category.assoc, symLift_spec, Category.assoc,
          symLift_spec, symLift_spec]
        exact φ.naturality f }

private theorem quotient_affine {X : Scheme.{v}}
    (S : X.CommAlgebraSheaf) (hS : S.toModule.IsQuasicoherent)
    (E : X.Modules) (hE : E.IsQuasicoherent) (e : E ⟶ S.toModule)
    (Q : X.CommAlgebraSheaf) (q : S ⟶ Q)
    (hq : ∀ (U : X.Opens) (x : E.val.obj (op U)),
      q.right.hom.app (op U) (e.app U x) = 0)
    (hup : ∀ (C : X.CommAlgebraSheaf) (χ : S ⟶ C),
      (∀ (U : X.Opens) (x : E.val.obj (op U)),
        χ.right.hom.app (op U) (e.app U x) = 0) →
      ∃! d : Q ⟶ C, q ≫ d = χ) :
    ∀ (U : X.Opens), IsAffineOpen U →
      Function.Surjective (q.right.hom.app (op U)) ∧
      RingHom.ker (q.right.hom.app (op U)).hom =
        Ideal.span (Set.range (e.app U) : Set (S.right.obj.obj (op U))) := by
  obtain ⟨J, j, L, _, _, hcontain, _, hL, _, Q', q', P, p, a, hp, hqeq, _, _, hq', hup'⟩ :=
    Scheme.CommAlgebraSheaf.generated_ideal_quotient_quasiCoherent S hS E hE e
  have hkill : ∀ (U : X.Opens) (x : E.val.obj (op U)),
      q'.right.hom.app (op U) (e.app U x) = 0 := by
    intro U x
    have hx : (p.app (op U)).hom (e.app U x) = 0 := by
      apply (show e.app U x ∈ RingHom.ker (p.app (op U)).hom from ?_)
      rw [(hp U).2]
      exact hcontain U ⟨x, rfl⟩
    rw [hqeq]
    change (a.hom.hom.app (op U))
      (((sheafificationAdjunction (Opens.grothendieckTopology X) CommRingCat).unit.app P).app
        (op U) (p.app (op U) (e.app U x))) = 0
    rw [hx, map_zero, map_zero]
  obtain ⟨f, hf, _⟩ := hup Q' q' hkill
  obtain ⟨g, hg, _⟩ := hup' Q q hq
  have hfg : f ≫ g = 𝟙 Q := by
    apply (hup Q q hq).unique
    · rw [← Category.assoc, hf, hg]
    · exact Category.comp_id q
  have hgf : g ≫ f = 𝟙 Q' := by
    apply (hup' Q' q' hkill).unique
    · rw [← Category.assoc, hg, hf]
    · exact Category.comp_id q'
  let iso : Q' ≅ Q := ⟨g, f, hgf, hfg⟩
  intro U hU
  have hgU : Function.Bijective (g.right.hom.app (op U)) :=
    ConcreteCategory.bijective_of_isIso
      (((evaluation X.Opensᵒᵖ CommRingCat).obj (op U)).mapIso
        ((sheafToPresheaf _ CommRingCat).mapIso ((Under.forget X.sheaf).mapIso iso))).hom
  constructor
  · intro x
    obtain ⟨y, rfl⟩ := hgU.2 x
    obtain ⟨z, hz⟩ := (hq' U hU).1 y
    refine ⟨z, ?_⟩
    have hh := congrArg (fun t ↦ t.right.hom.app (op U) z) hg
    exact hh.symm.trans (congrArg (g.right.hom.app (op U)) hz)
  · rw [← hL U hU, ← (hq' U hU).2]
    ext x
    change q.right.hom.app (op U) x = 0 ↔ q'.right.hom.app (op U) x = 0
    have hh := congrArg (fun t ↦ t.right.hom.app (op U) x) hg
    change g.right.hom.app (op U) (q'.right.hom.app (op U) x) =
      q.right.hom.app (op U) x at hh
    exact ⟨fun hx ↦ hgU.1 (hh.trans hx |>.trans (map_zero _).symm),
      fun hx ↦ hh.symm.trans (by rw [hx, map_zero])⟩

private theorem sym_fp {X : Scheme.{v}} (M : X.Modules)
    [M.IsFinitePresentation] : (SymmetricAlgebraSheaf.algebra M).IsFinitePresentation := by
  have hM := (Scheme.Modules.quasicoherent_finite_type_affine.{v, v} X).1 M inferInstance
  let : M.IsQuasicoherent := hM
  intro U hU
  have : Module.FinitePresentation Γ(X, U) Γ(M, U) :=
    ((Scheme.Modules.quasicoherent_finite_type_affine.{v, v} X).2 M hM).2.2 inferInstance U hU
  have hfp := (SymmetricAlgebra.generators_and_finitePresentation Γ(X, U) Γ(M, U)).2
    inferInstance
  have : Algebra.FinitePresentation Γ(X, U) (SymmetricAlgebraSheaf.sections M (op U)) :=
    hfp.1
  have hf : (algebraMap Γ(X, U) (SymmetricAlgebraSheaf.sections M (op U))).FinitePresentation :=
    (RingHom.finitePresentation_algebraMap).mpr inferInstance
  have hb := (quasiCoherentSymmetricAlgebra_affine_comparison X M).2 ⟨U, hU⟩
  have hcomp := hf.comp_surjective hb.2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hb.1]
    exact Submodule.fg_bot)
  exact hcomp

private theorem span_range_fg {R S M : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module.Finite R M]
    (f : M →ₗ[R] S) : (Ideal.span (Set.range f)).FG := by
  exact (Submodule.fg_range f).span

private theorem quotient_fp {X : Scheme.{v}}
    (S : X.CommAlgebraSheaf) (hSfp : S.IsFinitePresentation)
    (E : X.Modules) [E.IsFinitePresentation] (e : E ⟶ S.toModule)
    (Q : X.CommAlgebraSheaf) (q : S ⟶ Q)
    (hq : ∀ (U : X.Opens), IsAffineOpen U →
      Function.Surjective (q.right.hom.app (op U)) ∧
      RingHom.ker (q.right.hom.app (op U)).hom =
        Ideal.span (Set.range (e.app U) : Set (S.right.obj.obj (op U)))) :
    Q.IsFinitePresentation := by
  have hE := (Scheme.Modules.quasicoherent_finite_type_affine.{v, v} X).1 E inferInstance
  intro U hU
  have : Module.FinitePresentation Γ(X, U) Γ(E, U) :=
    ((Scheme.Modules.quasicoherent_finite_type_affine.{v, v} X).2 E hE).2.2 inferInstance U hU
  let : Algebra Γ(X, U) (S.right.obj.obj (op U)) :=
    (S.hom.hom.app (op U)).hom.toAlgebra
  have hfg : (RingHom.ker (q.right.hom.app (op U)).hom).FG := by
    rw [(hq U hU).2]
    let f : Γ(E, U) →ₗ[Γ(X, U)] S.right.obj.obj (op U) :=
      { toFun := e.app U
        map_add' := map_add _
        map_smul' := fun r x ↦ (e.val.app (op U)).hom.map_smul r x }
    exact span_range_fg f
  have hcomp := (hSfp U hU).comp_surjective (hq U hU).1 hfg
  have hw := congrArg (fun f ↦ f.hom.app (op U)) (Under.w q)
  change S.hom.hom.app (op U) ≫ q.right.hom.app (op U) = Q.hom.hom.app (op U) at hw
  simpa only [← CommRingCat.hom_comp, hw] using hcomp

private theorem kernel_quotient_finite {X : Scheme.{v}}
    (A S : X.CommAlgebraSheaf) (hA : A.IsIntegral)
    (hS : ∀ U : X.Opens, IsAffineOpen U → (S.hom.hom.app (op U)).hom.FiniteType)
    (ψ : S ⟶ A) :
    ∀ U : X.Opens, IsAffineOpen U →
      ((Ideal.Quotient.mk (RingHom.ker (ψ.right.hom.app (op U)).hom)).comp
        (S.hom.hom.app (op U)).hom).Finite := by
  intro U hU
  let f := (S.hom.hom.app (op U)).hom
  let g := (ψ.right.hom.app (op U)).hom
  have hg : (RingHom.kerLift g).comp ((Ideal.Quotient.mk (RingHom.ker g)).comp f) =
      (A.hom.hom.app (op U)).hom := by
    ext r
    exact congrArg (fun t ↦ t.hom.app (op U) r) (Under.w ψ)
  have hint : ((Ideal.Quotient.mk (RingHom.ker g)).comp f).IsIntegral :=
    RingHom.IsIntegral.tower_bot _ _ (RingHom.kerLift_injective g) (hg ▸ hA U hU)
  exact hint.to_finite ((hS U hU).comp_surjective Ideal.Quotient.mk_surjective)

set_option linter.unusedVariables false in
/-- An integral quasi-coherent algebra on a qcqs scheme is the directed colimit of
all its finite quasi-coherent subalgebras, and a directed colimit of finite,
finitely presented quasi-coherent algebras. Cocones are colimits in all algebra
sheaves, and their legs are the stated maps to the given algebra.
Source: Stacks Project, Properties, Tag 0817
(blueprint: lem-weil-pbc-integral-algebra-directed-colimit-finite).

Proof:
1. Integrality descends along each subalgebra inclusion. The ring theorem
   `RingHom.IsIntegral.to_finite` identifies finite type and finite subalgebras.
   Transport the finite-type subalgebra colimit along this order isomorphism.
2. Approximate the underlying module by finitely presented modules F_i. Their constructed
   symmetric algebras S_i form a diagram by the symmetric-algebra universal property,
   with compatible maps to A. Each S_i is finitely presented on affine opens.
3. Approximate each kernel J_i by finitely presented modules E_ik. Apply the directed-pairs
   theorem to obtain the quotient diagram Q_ik = S_i/(E_ik). Compare its quotient universal
   property with the generated-ideal quotient theorem to identify its affine sections.
   These quotients are finitely presented because their kernels are generated by the
   images of finitely generated section modules.
4. The map from the quasi-coherent algebra colimit of Q to A is bijective on affine
   sections. Surjectivity follows by lifting a section through some F_i. For injectivity,
   lift a representative to S_i; its vanishing in A puts it in J_i. Lift that kernel
   section through some E_ik and pass to a common later quotient, where it vanishes.
   The affine basis criterion gives the colimit isomorphism.
5. The quotient S_i/J_i is integral as it embeds in A, and finite type, hence finite.
   Apply eventual finiteness to obtain row bounds k₀(i). The pairs beyond these bounds
   form a cofinal directed subtype. Restrict the colimit to this subtype, whose terms
   are finite and finitely presented.
-/
theorem integral_algebra_directed_colimit_finite
    (X : Scheme.{v}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : QuasiCoherentAlgebra X) (hA : A.obj.IsIntegral) :
    (Nonempty A.FiniteSubalgebras ∧
      IsDirected A.FiniteSubalgebras (· ≤ ·) ∧
      ∃ (c : Cocone A.finiteSubalgebraDiagram) (e : c.pt ≅ A.obj),
        (∀ B : A.FiniteSubalgebras, c.ι.app B ≫ e.hom = B.val.arrow) ∧
        Nonempty (IsColimit c)) ∧
    (∃ (I : Type v) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ QuasiCoherentAlgebra X)
      (c : Cocone (F ⋙ (X.IsQuasiCoherentAlgebra).ι)) (e : c.pt ≅ A.obj),
      (∀ i : I, (F.obj i).obj.IsFinite ∧ (F.obj i).obj.IsFinitePresentation) ∧
      Nonempty (IsColimit c)) := by
  classical
  let e : A.FiniteSubalgebras ≃o A.obj.finiteTypeQuasiCoherentSubalgebras :=
    { toFun B := ⟨B.val, B.property.1,
        (subalgebra_finite_iff_finiteType A hA B.val).mp B.property.2⟩
      invFun B := ⟨B.val, B.property.1,
        (subalgebra_finite_iff_finiteType A hA B.val).mpr B.property.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_rel_iff' := Iff.rfl }
  constructor
  · obtain ⟨⟨hn, hd⟩, ⟨c, heq, ⟨hc⟩, hlegs⟩, _⟩ :=
      Scheme.CommAlgebraSheaf.directed_colimit_finiteType X A.obj A.property
    refine ⟨⟨e.symm hn.some⟩, ⟨fun i j ↦ ?_⟩,
      c.whisker e.equivalence.functor, eqToIso heq, ?_,
      ⟨hc.whiskerEquivalence e.equivalence⟩⟩
    · obtain ⟨k, hi, hj⟩ := hd (e i) (e j)
      exact ⟨e.symm k, e.symm.monotone hi, e.symm.monotone hj⟩
    · intro B
      exact hlegs (e B)
  · let : A.obj.toModule.IsQuasicoherent := A.property
    obtain ⟨I, hI, hne, hdir, F, hF, φ, ⟨hcF⟩⟩ :=
      Scheme.Modules.exists_directedColimit_finitePresentation X A.obj.toModule
    let : Preorder I := hI
    let : Nonempty I := hne
    let : IsDirected I (· ≤ ·) := hdir
    let (i : I) : (F.obj i).IsFinitePresentation := hF i
    let (i : I) : (F.obj i).IsQuasicoherent :=
      (Scheme.Modules.quasicoherent_finite_type_affine.{v, v} X).1 (F.obj i) (hF i)
    let S := symDiagram F
    let ψ := symCocone F A.obj φ
    have hS (i : I) : (S.obj i).toModule.IsQuasicoherent :=
      (quasiCoherentSymmetricAlgebra_affine_comparison X (F.obj i)).1
    have hSfp (i : I) : (S.obj i).IsFinitePresentation := sym_fp (F.obj i)
    have hSft (i : I) (U : X.Opens) (hU : IsAffineOpen U) :
        ((S.obj i).hom.hom.app (op U)).hom.FiniteType :=
      RingHom.FiniteType.of_finitePresentation (hSfp i U hU)
    have hkern (i : I) :=
      (Scheme.CommAlgebraSheaf.kernel_image_quasiCoherent (S.obj i) A.obj
        (hS i) A.property (ψ.ι.app i)).1
    choose J j hJ hji using hkern
    let (i : I) : (J i).IsQuasicoherent := hJ i
    have happrox (i : I) :=
      Scheme.Modules.exists_directedColimit_finitePresentation X (J i)
    choose K hK hnK hdK E hE ε hcE using happrox
    let (i : I) : Preorder (K i) := hK i
    let (i : I) : Nonempty (K i) := hnK i
    let (i : I) : IsDirected (K i) (· ≤ ·) := hdK i
    let (i : I) (k : K i) : ((E i).obj k).IsFinitePresentation := hE i k
    have hEqc (i : I) (k : K i) : ((E i).obj k).IsQuasicoherent :=
      (Scheme.Modules.quasicoherent_finite_type_affine.{v, v} X).1 _ (hE i k)
    let cE (i : I) : Cocone (E i) := Cocone.mk (J i) (ε i)
    let L (i : I) (U : X.Opens) := RingHom.ker ((ψ.ι.app i).right.hom.app (op U)).hom
    have hσ (i i' : I) (h : i ≤ i') (U : X.Opens) (s : (S.obj i).right.obj.obj (op U))
        (hs : s ∈ L i U) : (S.map (homOfLE h)).right.hom.app (op U) s ∈ L i' U := by
      change (ψ.ι.app i').right.hom.app (op U)
        ((S.map (homOfLE h)).right.hom.app (op U) s) = 0
      have hw := congrArg (fun f ↦ f.right.hom.app (op U) s) (ψ.w (homOfLE h))
      exact hw.trans hs
    obtain ⟨M, m, H, hm, hcontain, hmin, pairOrder, horder, hnon, hpairdir,
      hproj, hinc, hlift, Q, q, hQ, hqker, hup, hqnat⟩ :=
      Scheme.CommAlgebraSheaf.kernelIdeal_directed_pairs X I S hS K E cE
        (fun i ↦ (hcE i).some) j L hji hJ hσ
    let : Preorder (Σ i, K i) := pairOrder
    let : Nonempty (Σ i, K i) := hnon
    let : IsDirected (Σ i, K i) (· ≤ ·) := hpairdir
    have hkill (p : Σ i, K i) (U : X.Opens) (s : ((E p.1).obj p.2).val.obj (op U)) :
        (ψ.ι.app p.1).right.hom.app (op U)
          (((cE p.1).ι.app p.2 ≫ j p.1).app U s) = 0 := by
      change ((cE p.1).ι.app p.2 ≫ j p.1).app U s ∈ L p.1 U
      change ((cE p.1).ι.app p.2 ≫ j p.1).app U s ∈
        (RingHom.ker ((ψ.ι.app p.1).right.hom.app (op U)).hom :
          Set ((S.obj p.1).right.obj.obj (op U)))
      rw [← (hji p.1 U).2]
      exact ⟨(cE p.1).ι.app p.2 |>.app U s, rfl⟩
    have hχ (p : Σ i, K i) := hup p A.obj (ψ.ι.app p.1) (hkill p)
    choose χ hχfac hχuniq using hχ
    have hqkill (p : Σ i, K i) (U : X.Opens)
        (s : ((E p.1).obj p.2).val.obj (op U)) :
        (q p).right.hom.app (op U) (((cE p.1).ι.app p.2 ≫ j p.1).app U s) = 0 := by
      change ((cE p.1).ι.app p.2 ≫ j p.1).app U s ∈
        RingHom.ker ((q p).right.hom.app (op U)).hom
      rw [hqker]
      exact hcontain p U ⟨s, rfl⟩
    have hqa (p : Σ i, K i) := quotient_affine (S.obj p.1) (hS p.1)
      ((E p.1).obj p.2) (hEqc p.1 p.2) ((cE p.1).ι.app p.2 ≫ j p.1)
      (Q.obj p) (q p) (hqkill p) (hup p)
    have hQfp (p : Σ i, K i) : (Q.obj p).IsFinitePresentation :=
      quotient_fp (S.obj p.1) (hSfp p.1) ((E p.1).obj p.2)
        ((cE p.1).ι.app p.2 ≫ j p.1) (Q.obj p) (q p) (hqa p)
    have hχnat (p r : Σ i, K i) (f : p ⟶ r) : Q.map f ≫ χ r = χ p := by
      apply (hup p A.obj (ψ.ι.app p.1) (hkill p)).unique
      · rw [← Category.assoc, hqnat p r f (hproj f.le), Category.assoc, hχfac, ψ.w]
      · exact hχfac p
    let cQ : Cocone Q := ⟨A.obj, ⟨χ, fun {_ _} f ↦ by
      simpa using hχnat _ _ f⟩⟩
    have hQfinite (i : I) : ∃ k₀ : K i, ∀ k : K i, k₀ ≤ k → (Q.obj ⟨i, k⟩).IsFinite := by
      obtain ⟨k₀, hk₀⟩ := Scheme.CommAlgebraSheaf.finite_quotient_eventually_finite
        X (S.obj i) (hS i) (hSft i) (K i) (E i) (cE i) (hcE i).some (hEqc i)
        (hJ i) (j i) (L i) (hji i) (kernel_quotient_finite A.obj (S.obj i) hA (hSft i)
          (ψ.ι.app i))
      refine ⟨k₀, fun k hk U hU ↦ ?_⟩
      let g := ((q ⟨i, k⟩).right.hom.app (op U)).hom
      have hker := (hqa ⟨i, k⟩ U hU).2
      have hf := hk₀ k hk U hU
      rw [← hker] at hf
      let e := RingHom.quotientKerEquivOfSurjective (f := g) (hqa ⟨i, k⟩ U hU).1
      have he : e.toRingHom.comp ((Ideal.Quotient.mk (RingHom.ker g)).comp
          ((S.obj i).hom.hom.app (op U)).hom) = ((Q.obj ⟨i, k⟩).hom.hom.app (op U)).hom := by
        ext r
        exact congrArg (fun t ↦ t.hom.app (op U) r) (Under.w (q ⟨i, k⟩))
      rw [← he]
      exact (RingHom.Finite.of_surjective e.toRingHom e.surjective).comp hf
    obtain ⟨c, ⟨hc⟩, _, _, hca, _⟩ := Scheme.quasiCoherentAlgebra_colimit X
      (Σ i, K i) Q hQ
    let κ : c.pt ⟶ A.obj := hc.desc cQ
    have hκ (p : Σ i, K i) : c.ι.app p ≫ κ = χ p := hc.fac cQ p
    have hκbij (U : X.Opens) (hU : IsAffineOpen U) :
        Function.Bijective (κ.right.hom.app (op U)) := by
      let ev := Under.forget X.sheaf ⋙ sheafToPresheaf
        (Opens.grothendieckTopology X) CommRingCat ⋙
          (evaluation X.Opensᵒᵖ CommRingCat).obj (op U)
      have hcev : IsColimit (ev.mapCocone c) := (hca U hU).some
      have hrep := (Scheme.Modules.quasiCoherentModuleColimitAffineSections X I F
        (Cocone.mk A.obj.toModule φ) hcF (fun _ ↦ inferInstance)).2 U hU |>.1
      constructor
      · apply (injective_iff_map_eq_zero (κ.right.hom.app (op U)).hom).mpr
        intro z hz
        obtain ⟨p, x, hx⟩ := Concrete.isColimit_exists_rep (Q ⋙ ev) hcev z
        obtain ⟨t, ht⟩ := (hqa p U hU).1 x
        have hχx : (χ p).right.hom.app (op U) x = 0 := by
          have hh := congrArg (fun f ↦ f.right.hom.app (op U) x) (hκ p)
          change κ.right.hom.app (op U) ((c.ι.app p).right.hom.app (op U) x) =
            (χ p).right.hom.app (op U) x at hh
          change (c.ι.app p).right.hom.app (op U) x = z at hx
          exact hh.symm.trans (by rw [hx]; exact hz)
        have htker : t ∈ L p.1 U := by
          have hh := congrArg (fun f ↦ f.right.hom.app (op U) t) (hχfac p)
          change (ψ.ι.app p.1).right.hom.app (op U) t = 0
          change (χ p).right.hom.app (op U) ((q p).right.hom.app (op U) t) =
            (ψ.ι.app p.1).right.hom.app (op U) t at hh
          exact hh.symm.trans (by rw [ht]; exact hχx)
        have htrange : t ∈ Set.range ((j p.1).app U) := by
          rw [(hji p.1 U).2]
          exact htker
        obtain ⟨y, hy⟩ := htrange
        obtain ⟨k, u, hu⟩ :=
          (Scheme.Modules.quasiCoherentModuleColimitAffineSections X (K p.1) (E p.1)
            (cE p.1) (hcE p.1).some (hEqc p.1)).2 U hU |>.1 y
        obtain ⟨l, hpl, hkl⟩ := exists_ge_ge p.2 k
        let r : Σ i, K i := ⟨p.1, l⟩
        let f : p ⟶ r := homOfLE (hinc p.1 p.2 l hpl)
        have htu : ((cE p.1).ι.app l ≫ j p.1).app U
            (((E p.1).map (homOfLE hkl)).app U u) = t := by
          have hh := congrArg (fun f ↦ f.val.app (op U) u) ((cE p.1).w (homOfLE hkl))
          change ((j p.1).app U)
            (((cE p.1).ι.app l).app U (((E p.1).map (homOfLE hkl)).app U u)) = t
          change ((cE p.1).ι.app l).app U
            (((E p.1).map (homOfLE hkl)).app U u) =
              ((cE p.1).ι.app k).app U u at hh
          exact (congrArg ((j p.1).app U) hh).trans
            ((congrArg ((j p.1).app U) hu).trans hy)
        have hzero : (q r).right.hom.app (op U) t = 0 := by
          rw [← htu]
          exact hqkill r U _
        have hxf : (Q.map f).right.hom.app (op U) x = 0 := by
          have hh := congrArg (fun f ↦ f.right.hom.app (op U) t)
            (hqnat p r f (le_refl p.1))
          have hid : S.map (homOfLE (le_refl p.1)) = 𝟙 (S.obj p.1) :=
            (congrArg S.map (Subsingleton.elim _ _)).trans (S.map_id p.1)
          rw [hid, Category.id_comp] at hh
          change (Q.map f).right.hom.app (op U)
            ((q p).right.hom.app (op U) t) =
              (q r).right.hom.app (op U) t at hh
          rw [ht, hzero] at hh
          exact hh
        have hw := congrArg (fun f ↦ f.right.hom.app (op U) x) (c.w f)
        change (c.ι.app r).right.hom.app (op U) ((Q.map f).right.hom.app (op U) x) =
          (c.ι.app p).right.hom.app (op U) x at hw
        rw [hxf, map_zero] at hw
        exact hx ▸ hw.symm
      · intro a
        obtain ⟨i, x, hx⟩ := hrep a
        let p : Σ i, K i := ⟨i, Classical.choice (hnK i)⟩
        let t := (SymmetricAlgebraSheaf.inclusion (F.obj i)).val.app (op U) x
        refine ⟨(c.ι.app p).right.hom.app (op U) ((q p).right.hom.app (op U) t), ?_⟩
        have hh := congrArg (fun f ↦ f.right.hom.app (op U)
          ((q p).right.hom.app (op U) t)) (hκ p)
        have hh' := congrArg (fun f ↦ f.right.hom.app (op U) t) (hχfac p)
        exact hh.trans (hh'.trans
          (((exists_quasiCoherentSymmetricAlgebra_core X (F.obj i) A.obj (φ.app i)).choose_spec.1
            U x).trans hx))
    have hisoRight : IsIso κ.right :=
      TopCat.Sheaf.isIso_iff_isIso_basis
        (B := fun U : X.affineOpens ↦ U.1)
        (by simpa only [Subtype.range_coe] using X.isBasis_affineOpens)
        (fun U ↦ (ConcreteCategory.isIso_iff_bijective _).mpr (hκbij U.1 U.2))
    have : IsIso ((Under.forget X.sheaf).map κ) := hisoRight
    have : IsIso κ := isIso_of_reflects_iso κ (Under.forget X.sheaf)
    have hcQ : IsColimit cQ := hc.ofPointIso
    choose k₀ hk₀ using hQfinite
    let T := {p : Σ i, K i // k₀ p.1 ≤ p.2}
    have hupper (p : Σ i, K i) : ∃ r : T, p ≤ r.val := by
      obtain ⟨l, hp, hk⟩ := exists_ge_ge p.2 (k₀ p.1)
      exact ⟨⟨⟨p.1, l⟩, hk⟩, hinc p.1 p.2 l hp⟩
    let : Nonempty T := ⟨(hupper (Classical.choice hnon)).choose⟩
    let : IsDirected T (· ≤ ·) := ⟨fun p r ↦ by
      obtain ⟨s, hps, hrs⟩ := exists_ge_ge p.val r.val
      obtain ⟨t, hst⟩ := hupper s
      exact ⟨t, hps.trans hst, hrs.trans hst⟩⟩
    let inc : T ⥤ (Σ i, K i) :=
      (show Monotone (fun p : T ↦ p.val) from fun _ _ h ↦ h).functor
    have : inc.Final := Functor.final_of_exists_of_isFiltered inc
      (fun p ↦ by obtain ⟨r, hpr⟩ := hupper p; exact ⟨r, ⟨homOfLE hpr⟩⟩)
      (fun {_ _} f g ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
    let D : T ⥤ QuasiCoherentAlgebra X :=
      (X.IsQuasiCoherentAlgebra).lift (inc ⋙ Q) (fun p ↦ hQ p.val)
    refine ⟨T, inferInstance, inferInstance, inferInstance, D,
      cQ.whisker inc, Iso.refl _, ?_,
      ⟨(Functor.Final.isColimitWhiskerEquiv inc cQ).symm hcQ⟩⟩
    intro p
    exact ⟨hk₀ p.val.1 p.val.2 p.property, hQfp p.val⟩

end AlgebraicGeometry

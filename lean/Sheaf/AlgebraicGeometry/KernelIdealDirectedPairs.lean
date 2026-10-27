/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q142
-/
module

public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraKernelImageIdeal
import Sheaf.AlgebraicGeometry.FinitePresentationHomDirectedColimit

/-! # Directed pairs of generated kernel ideals

Source: Stacks Project, Properties, Tags 0817 and 05JS, the lifting square and the
ideal-containment relation on pairs (blueprint: lem-weil-pbc-kernel-ideal-directed-pairs).

Ideal subsheaves use module inclusions with ideal-valued section ranges, as in the
kernel-image-ideal dependency. Generated ideals are specified by their minimality;
quotients by their kernel and universal property. The pair type is the small dependent
sum of the row index types. The order is characterized, rather than chosen arbitrarily.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.CommAlgebraSheaf

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleMap {X : Scheme.{u}} {B A : X.CommAlgebraSheaf}
    (f : B ⟶ A) :
    (show X.Modules from B.toModule) ⟶ (show X.Modules from A.toModule) where
  val := {
    app := fun U ↦ ModuleCat.ofHom (X := B.toModule.val.obj U) (Y := A.toModule.val.obj U) {
      toFun := f.right.hom.app U
      map_add' := map_add _
      map_smul' := fun r b ↦ by
        change f.right.hom.app U (B.hom.hom.app U r * (show B.right.obj.obj U from b)) =
          A.hom.hom.app U r * f.right.hom.app U (show B.right.obj.obj U from b)
        rw [map_mul]
        congr 1
        exact congrArg (fun g : X.sheaf ⟶ A.right ↦ (g.hom.app U).hom r) f.w }
    naturality := fun {U V} g ↦ by
      ext s
      exact ConcreteCategory.congr_hom (f.right.hom.naturality g) s }

set_option backward.isDefEq.respectTransparency false in
private theorem mono_of_sections {X : Scheme.{u}} {M N : X.Modules}
    (n : M ⟶ N) (hn : ∀ U, Function.Injective (n.app U)) : Mono n := by
  constructor
  intro Z f g h
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  apply hn U
  exact congrArg (fun a ↦ a.app U s) h

set_option backward.isDefEq.respectTransparency false in
private theorem kernel_sections {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) :
    Set.range ((kernel.ι f).app U) = {s | f.app U s = 0} := by
  let G := Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)
  have key : ((PreservesKernel.iso G f ≪≫ ModuleCat.kernelIsoKer (G.map f)).inv ≫
      G.map (kernel.ι f)) = ModuleCat.ofHom (LinearMap.ker (G.map f).hom).subtype := by
    simp [ModuleCat.kernelIsoKer_inv_kernel_ι]
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact congrArg (fun a ↦ a.app U t) (kernel.condition f)
  · intro hs
    refine ⟨(PreservesKernel.iso G f ≪≫ ModuleCat.kernelIsoKer (G.map f)).inv
      ⟨s, hs⟩, ?_⟩
    exact ConcreteCategory.congr_hom key ⟨s, hs⟩

set_option backward.isDefEq.respectTransparency false in
private theorem kernel_injective {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) : Function.Injective ((kernel.ι f).app U) := by
  let G := Scheme.Modules.toPresheafOfModules X ⋙
    PresheafOfModules.evaluation X.ringCatSheaf.obj (op U)
  exact (ModuleCat.mono_iff_injective (G.map (kernel.ι f))).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem range_iff_cokernel {X : Scheme.{u}} {M N : X.Modules}
    (n : M ⟶ N) (hn : ∀ U, Function.Injective (n.app U))
    (U : X.Opens) (s : N.val.obj (op U)) :
    s ∈ Set.range (n.app U) ↔ (cokernel.π n).app U s = 0 := by
  have : Mono n := mono_of_sections n hn
  constructor
  · rintro ⟨t, rfl⟩
    exact congrArg (fun a ↦ a.app U t) (cokernel.condition n)
  · intro hs
    obtain ⟨t, ht⟩ := (Set.ext_iff.mp
      (kernel_sections (cokernel.π n) U) s).mpr hs
    refine ⟨(inv (Abelian.factorThruImage n)).app U t, ?_⟩
    change (inv (Abelian.factorThruImage n) ≫ n).app U t = s
    have heq : inv (Abelian.factorThruImage n) ≫ n = Abelian.image.ι n := by
      calc
        _ = inv (Abelian.factorThruImage n) ≫
            (Abelian.factorThruImage n ≫ Abelian.image.ι n) := by
          rw [Abelian.image.fac]
        _ = _ := by simp
    rw [heq]
    exact ht

set_option backward.isDefEq.respectTransparency false in
private theorem zero_of_affine {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (hf : ∀ U : X.affineOpens, ∀ s, f.app U.1 s = 0) : f = 0 := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  change f.app W s = 0
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩
    (fun i : {V : X.affineOpens // V.1 ≤ W} ↦ i.1.1) W
    (fun i ↦ homOfLE i.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
    exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  · intro i
    change N.val.map _ (f.val.app _ s) = N.val.map _ 0
    rw [← PresheafOfModules.naturality_apply, map_zero]
    exact hf i.1 _

set_option backward.isDefEq.respectTransparency false in
private theorem factor_of_ranges {X : Scheme.{u}} {M N P : X.Modules}
    (f : M ⟶ P) (n : N ⟶ P) (hn : ∀ U, Function.Injective (n.app U))
    (h : ∀ U, Set.range (f.app U) ⊆ Set.range (n.app U)) :
    ∃ g : M ⟶ N, g ≫ n = f := by
  have : Mono n := mono_of_sections n hn
  have hz : f ≫ cokernel.π n = 0 := by
    apply Scheme.Modules.hom_ext
    intro U
    ext s
    exact (range_iff_cokernel n hn U _).mp (h U ⟨s, rfl⟩)
  exact ⟨Abelian.monoLift n f hz, Abelian.monoLift_comp n f hz⟩

set_option backward.isDefEq.respectTransparency false in
private theorem quotient_kernel {X : Scheme.{u}} {B Q : X.CommAlgebraSheaf}
    {M : X.Modules} (m : M ⟶ B.toModule)
    (L : ∀ U : X.Opens, Ideal (B.right.obj.obj (op U)))
    (hm : ∀ U, Function.Injective (m.app U) ∧
      Set.range (m.app U) = (L U : Set (B.right.obj.obj (op U))))
    (q : B ⟶ Q)
    (hq : ∀ U, IsAffineOpen U → RingHom.ker (q.right.hom.app (op U)).hom = L U) :
    ∀ U, RingHom.ker (q.right.hom.app (op U)).hom = L U := by
  let f := moduleMap q
  have hmf : m ≫ f = 0 := by
    apply zero_of_affine
    intro U s
    change q.right.hom.app (op U.1) (m.app U.1 s) = 0
    apply RingHom.mem_ker.mp
    rw [hq U.1 U.2]
    change m.app U.1 s ∈ (L U.1 : Set (B.right.obj.obj (op U.1)))
    rw [← (hm U.1).2]
    exact ⟨s, rfl⟩
  have hkm : kernel.ι f ≫ cokernel.π m = 0 := by
    apply zero_of_affine
    intro U s
    apply (range_iff_cokernel m (fun U ↦ (hm U).1) U.1 _).mp
    rw [(hm U.1).2, ← hq U.1 U.2]
    change f.app U.1 ((kernel.ι f).app U.1 s) = 0
    exact congrArg (fun a ↦ a.app U.1 s) (kernel.condition f)
  intro U
  ext s
  constructor
  · intro hs
    change f.app U s = 0 at hs
    obtain ⟨t, ht⟩ := (Set.ext_iff.mp (kernel_sections f U) s).mpr hs
    change s ∈ (L U : Set _)
    rw [← (hm U).2]
    apply (range_iff_cokernel m (fun U ↦ (hm U).1) U s).mpr
    rw [← ht]
    exact congrArg (fun a ↦ a.app U t) hkm
  · intro hs
    have hs' : s ∈ Set.range (m.app U) := by rwa [(hm U).2]
    obtain ⟨t, rfl⟩ := hs'
    exact congrArg (fun a ↦ a.app U t) hmf

-- Some original hypotheses and proof-irrelevant order witnesses are intentionally unused.
set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedVariables false in
/-- Generated kernel ideals give a nonempty directed preorder of pairs and a compatible
quotient algebra diagram. Source: Stacks, Properties, Tags 0817(2) and 05JS
(blueprint: lem-weil-pbc-kernel-ideal-directed-pairs).

Proof:
1. The finite-presentation modules are quasi-coherent by Mathlib's instance. Apply (b) of
   lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal to their composites into S_i.
   This gives the generated ideal subsheaves, their minimality, and the quasi-coherent
   quotient algebras with their quotient universal properties.
2. For i ≤ j and k in K_i, compose E_ik → J_i with the induced map J_i → J_j.
   The colimit factorization in lem-weil-pbc-finite-presentation-hom-directed-colimit
   gives E_ik → E_jl for some l. The inverse image of the ideal generated by E_jl
   contains E_ik, hence its generated ideal. This gives extension to row j.
3. Identity and composition of S give reflexivity and transitivity of the specified
   relation. Projection is monotone. Cocone compatibility and minimality give row
   monotonicity. The dependent sum is small and nonempty. Move two pairs to a common
   upper row using step 2, then use directedness within that row for an upper bound.
4. For comparable pairs, the later quotient map kills the earlier generated ideal.
   The quotient universal property of
   lem-weil-pbc-quasi-coherent-algebra-kernel-image-ideal gives its unique factorization.
   Uniqueness proves the identity and composition laws, giving the quotient functor
   and the required commuting squares. Its objects are quasi-coherent by step 1. -/
theorem kernelIdeal_directed_pairs
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (S : I ⥤ X.CommAlgebraSheaf) (hS : ∀ i : I, (S.obj i).toModule.IsQuasicoherent)
    (K : I → Type u) [∀ i : I, Preorder (K i)] [∀ i : I, Nonempty (K i)]
    [∀ i : I, IsDirected (K i) (· ≤ ·)]
    (E : ∀ i : I, K i ⥤ X.Modules)
    [∀ (i : I) (k : K i), SheafOfModules.IsFinitePresentation.{u}
      (R := X.ringCatSheaf) ((E i).obj k)]
    (c : ∀ i : I, Cocone (E i)) (hc : ∀ i : I, IsColimit (c i))
    (j : ∀ i : I, (c i).pt ⟶ (S.obj i).toModule)
    (J : ∀ (i : I) (U : X.Opens), Ideal ((S.obj i).right.obj.obj (op U)))
    (hJ : ∀ (i : I) (U : X.Opens), Function.Injective ((j i).app U) ∧
      Set.range ((j i).app U) = (J i U : Set ((S.obj i).right.obj.obj (op U))))
    (hJqc : ∀ i : I, (c i).pt.IsQuasicoherent)
    (hσ : ∀ (i i' : I) (h : i ≤ i') (U : X.Opens)
      (s : (S.obj i).right.obj.obj (op U)), s ∈ J i U →
      (S.map (homOfLE h)).right.hom.app (op U) s ∈ J i' U) :
    ∃ (M : (Σ i : I, K i) → X.Modules)
      (m : ∀ p : Σ i : I, K i, M p ⟶ (S.obj p.1).toModule)
      (L : ∀ (p : Σ i : I, K i) (U : X.Opens),
        Ideal ((S.obj p.1).right.obj.obj (op U))),
      (∀ (p : Σ i : I, K i) (U : X.Opens), Function.Injective ((m p).app U) ∧
        Set.range ((m p).app U) = (L p U : Set ((S.obj p.1).right.obj.obj (op U)))) ∧
      (∀ (p : Σ i : I, K i) (U : X.Opens),
        Set.range ((((c p.1).ι.app p.2) ≫ j p.1).app U) ⊆
          (L p U : Set ((S.obj p.1).right.obj.obj (op U)))) ∧
      (∀ (p : Σ i : I, K i) (N : X.Modules) (n : N ⟶ (S.obj p.1).toModule)
        (H : ∀ U : X.Opens, Ideal ((S.obj p.1).right.obj.obj (op U))),
        (∀ U : X.Opens, Function.Injective (n.app U) ∧
          Set.range (n.app U) = (H U : Set ((S.obj p.1).right.obj.obj (op U)))) →
        (∀ U : X.Opens, Set.range ((((c p.1).ι.app p.2) ≫ j p.1).app U) ⊆
          (H U : Set ((S.obj p.1).right.obj.obj (op U)))) →
        ∀ U : X.Opens, L p U ≤ H U) ∧
      ∃ pairOrder : Preorder (Σ i : I, K i),
        (∀ p r : Σ i : I, K i, p ≤ r ↔ ∃ h : p.1 ≤ r.1,
          ∀ (U : X.Opens) (s : (S.obj p.1).right.obj.obj (op U)), s ∈ L p U →
            (S.map (homOfLE h)).right.hom.app (op U) s ∈ L r U) ∧
        Nonempty (Σ i : I, K i) ∧ IsDirected (Σ i : I, K i) (· ≤ ·) ∧
        Monotone (fun p : Σ i : I, K i ↦ p.1) ∧
        (∀ (i : I) (k l : K i), k ≤ l →
          (⟨i, k⟩ : Σ i : I, K i) ≤ ⟨i, l⟩) ∧
        (∀ (i i' : I) (h : i ≤ i') (k : K i),
          ∃ l : K i', (⟨i, k⟩ : Σ i : I, K i) ≤ ⟨i', l⟩) ∧
        ∃ (Q : (Σ i : I, K i) ⥤ X.CommAlgebraSheaf)
          (q : ∀ p : Σ i : I, K i, S.obj p.1 ⟶ Q.obj p),
          (∀ p : Σ i : I, K i, (Q.obj p).toModule.IsQuasicoherent) ∧
          (∀ (p : Σ i : I, K i) (U : X.Opens),
            RingHom.ker ((q p).right.hom.app (op U)).hom = L p U) ∧
          (∀ (p : Σ i : I, K i) (C : X.CommAlgebraSheaf) (χ : S.obj p.1 ⟶ C),
            (∀ (U : X.Opens) (s : ((E p.1).obj p.2).val.obj (op U)),
              χ.right.hom.app (op U) ((((c p.1).ι.app p.2) ≫ j p.1).app U s) = 0) →
            ∃! χbar : Q.obj p ⟶ C, q p ≫ χbar = χ) ∧
          (∀ (p r : Σ i : I, K i) (f : p ⟶ r) (h : p.1 ≤ r.1),
            q p ≫ Q.map f = S.map (homOfLE h) ≫ q r) := by
  classical
  have hgen (p : Σ i : I, K i) := generated_ideal_quotient_quasiCoherent
    (S.obj p.1) (hS p.1) ((E p.1).obj p.2)
    inferInstance
    ((c p.1).ι.app p.2 ≫ j p.1)
  choose M m L hM hm hcontain hmin haff htensor hquot using hgen
  choose Q q P t a ht hq hQ hlocal hqaff hUP using hquot
  have hker (p : Σ i : I, K i) := quotient_kernel (m p) (L p) (hm p) (q p)
    (fun U hU ↦ (hqaff p U hU).2)
  have kill (p : Σ i : I, K i) (C : X.CommAlgebraSheaf) (χ : S.obj p.1 ⟶ C)
      (hχ : ∀ U s, χ.right.hom.app (op U)
        ((((c p.1).ι.app p.2) ≫ j p.1).app U s) = 0) :
      ∀ U s, s ∈ L p U → χ.right.hom.app (op U) s = 0 := by
    let f := moduleMap χ
    have hr (U : X.Opens) : Set.range ((kernel.ι f).app U) =
        (RingHom.ker (χ.right.hom.app (op U)).hom :
          Set ((S.obj p.1).right.obj.obj (op U))) := kernel_sections f U
    exact fun U s hs ↦ hmin p (kernel f) (kernel.ι f)
      (fun U ↦ RingHom.ker (χ.right.hom.app (op U)).hom)
      (fun U ↦ ⟨kernel_injective f U, hr U⟩)
      (fun U s hs ↦ by obtain ⟨v, rfl⟩ := hs; exact hχ U v) U hs
  have transfer (p r : Σ i : I, K i) (h : p.1 ≤ r.1)
      (he : ∀ U s, (S.map (homOfLE h)).right.hom.app (op U)
        ((((c p.1).ι.app p.2) ≫ j p.1).app U s) ∈ L r U) :
      ∀ U s, s ∈ L p U →
        (S.map (homOfLE h)).right.hom.app (op U) s ∈ L r U := by
    intro U s hs
    rw [← hker r U]
    exact kill p (Q r) (S.map (homOfLE h) ≫ q r)
      (fun V v ↦ by
        change (q r).right.hom.app (op V)
          ((S.map (homOfLE h)).right.hom.app (op V)
            ((((c p.1).ι.app p.2) ≫ j p.1).app V v)) = 0
        apply RingHom.mem_ker.mp
        rw [hker r V]
        exact he V v) U s hs
  have row (i : I) (k l : K i) (h : k ≤ l) :
      ∀ U s, s ∈ L ⟨i, k⟩ U → s ∈ L ⟨i, l⟩ U := by
    apply hmin ⟨i, k⟩ (M ⟨i, l⟩) (m ⟨i, l⟩) (L ⟨i, l⟩) (hm ⟨i, l⟩)
    intro U s hs
    obtain ⟨v, rfl⟩ := hs
    have he : (E i).map (homOfLE h) ≫ (c i).ι.app l ≫ j i =
        (c i).ι.app k ≫ j i := by rw [← Category.assoc, (c i).w]
    rw [← he]
    exact hcontain ⟨i, l⟩ U ⟨((E i).map (homOfLE h)).app U v, rfl⟩
  have extension (i i' : I) (h : i ≤ i') (k : K i) :
      ∃ l : K i', ∀ U s, s ∈ L ⟨i, k⟩ U →
        (S.map (homOfLE h)).right.hom.app (op U) s ∈ L ⟨i', l⟩ U := by
    obtain ⟨b, hb⟩ := factor_of_ranges (j i ≫ moduleMap (S.map (homOfLE h))) (j i')
      (fun U ↦ (hJ i' U).1) (fun U s hs ↦ by
        obtain ⟨v, rfl⟩ := hs
        rw [(hJ i' U).2]
        exact hσ i i' h U _ ((Set.ext_iff.mp (hJ i U).2 _).mp ⟨v, rfl⟩))
    obtain ⟨l, g, hg⟩ := (Scheme.Modules.hom_directedColimit_of_isFinitePresentation
      X (K i') (E i') (c i') (hc i') ((E i).obj k)).1 ((c i).ι.app k ≫ b)
    refine ⟨l, transfer ⟨i, k⟩ ⟨i', l⟩ h ?_⟩
    intro U s
    have he : (c i).ι.app k ≫ j i ≫ moduleMap (S.map (homOfLE h)) =
        g ≫ (c i').ι.app l ≫ j i' := by
      rw [← hb, ← Category.assoc, ← Category.assoc, ← hg]
    have hv := congrArg (fun a ↦ a.app U s) he
    change (S.map (homOfLE h)).right.hom.app (op U)
      ((((c i).ι.app k) ≫ j i).app U s) ∈ L ⟨i', l⟩ U
    change (S.map (homOfLE h)).right.hom.app (op U)
      ((((c i).ι.app k) ≫ j i).app U s) =
        ((((c i').ι.app l) ≫ j i').app U (g.app U s)) at hv
    exact hv.symm ▸ hcontain ⟨i', l⟩ U ⟨g.app U s, rfl⟩
  let R (p r : Σ i : I, K i) : Prop := ∃ h : p.1 ≤ r.1,
    ∀ U s, s ∈ L p U → (S.map (homOfLE h)).right.hom.app (op U) s ∈ L r U
  have hrefl (p : Σ i : I, K i) : R p p := by
    refine ⟨le_refl _, ?_⟩
    intro U s hs
    change (S.map (𝟙 p.1)).right.hom.app (op U) s ∈ L p U
    rw [S.map_id]
    change s ∈ L p U
    exact hs
  have htrans {p r v : Σ i : I, K i} (hpr : R p r) (hrv : R r v) : R p v := by
    obtain ⟨h, hh⟩ := hpr
    obtain ⟨g, hg⟩ := hrv
    refine ⟨h.trans g, ?_⟩
    intro U s hs
    have he : S.map (homOfLE (h.trans g)) =
        S.map (homOfLE h) ≫ S.map (homOfLE g) := by
      rw [← S.map_comp]
      rfl
    rw [he]
    exact hg U _ (hh U s hs)
  let pairOrder : Preorder (Σ i : I, K i) := {
    le := R
    le_refl := hrefl
    le_trans := fun _ _ _ ↦ htrans }
  have hrow (i : I) (k l : K i) (h : k ≤ l) :
      (⟨i, k⟩ : Σ i : I, K i) ≤ ⟨i, l⟩ := by
    refine ⟨le_refl i, ?_⟩
    intro U s hs
    change (S.map (𝟙 i)).right.hom.app (op U) s ∈ L ⟨i, l⟩ U
    rw [S.map_id]
    change s ∈ L ⟨i, l⟩ U
    exact row i k l h U s hs
  have hext (i i' : I) (h : i ≤ i') (k : K i) :
      ∃ l : K i', (⟨i, k⟩ : Σ i : I, K i) ≤ ⟨i', l⟩ := by
    obtain ⟨l, hl⟩ := extension i i' h k
    exact ⟨l, h, hl⟩
  have hdir : IsDirected (Σ i : I, K i) (· ≤ ·) := by
    constructor
    intro p r
    obtain ⟨i, hp, hr⟩ := exists_ge_ge p.1 r.1
    obtain ⟨k, hk⟩ := hext p.1 i hp p.2
    obtain ⟨l, hl⟩ := hext r.1 i hr r.2
    obtain ⟨v, hkv, hlv⟩ := exists_ge_ge k l
    exact ⟨⟨i, v⟩, hk.trans (hrow i k v hkv), hl.trans (hrow i l v hlv)⟩
  have hkill (p r : Σ i : I, K i) (h : p ≤ r) :
      ∀ U s, (S.map (homOfLE h.choose) ≫ q r).right.hom.app (op U)
        ((((c p.1).ι.app p.2) ≫ j p.1).app U s) = 0 := by
    intro U s
    change (q r).right.hom.app (op U)
      ((S.map (homOfLE h.choose)).right.hom.app (op U)
        ((((c p.1).ι.app p.2) ≫ j p.1).app U s)) = 0
    apply RingHom.mem_ker.mp
    rw [hker r U]
    exact h.choose_spec U _ (hcontain p U ⟨s, rfl⟩)
  have hfactor (p r : Σ i : I, K i) (h : p ≤ r) :=
    hUP p (Q r) (S.map (homOfLE h.choose) ≫ q r) (hkill p r h)
  choose α hα huniq using hfactor
  have cancel (p : Σ i : I, K i) (C : X.CommAlgebraSheaf)
      (f g : Q p ⟶ C) (h : q p ≫ f = q p ≫ g) : f = g := by
    have hz : ∀ U s, (q p ≫ g).right.hom.app (op U)
        ((((c p.1).ι.app p.2) ≫ j p.1).app U s) = 0 := by
      intro U s
      change g.right.hom.app (op U) ((q p).right.hom.app (op U)
        ((((c p.1).ι.app p.2) ≫ j p.1).app U s)) = 0
      have hk : (q p).right.hom.app (op U)
          ((((c p.1).ι.app p.2) ≫ j p.1).app U s) = 0 := by
        apply RingHom.mem_ker.mp
        rw [hker p U]
        exact hcontain p U ⟨s, rfl⟩
      rw [hk, map_zero]
    obtain ⟨v, hv, hu⟩ := hUP p C (q p ≫ g) hz
    exact (hu f h).trans (hu g rfl).symm
  let QF : (Σ i : I, K i) ⥤ X.CommAlgebraSheaf := {
    obj := Q
    map := fun {p r} f ↦ α p r (leOfHom f)
    map_id := fun p ↦ by
      apply cancel p (Q p)
      rw [hα]
      simp
    map_comp := fun {p r v} f g ↦ by
      apply cancel p (Q v)
      rw [hα, ← Category.assoc, hα, Category.assoc, hα]
      rw [← Category.assoc, ← S.map_comp]
      rfl }
  refine ⟨M, m, L, hm, hcontain, hmin, pairOrder, (fun _ _ ↦ Iff.rfl),
    ⟨⟨Classical.arbitrary I, Classical.arbitrary _⟩⟩, hdir, (fun _ _ h ↦ h.choose),
    hrow, hext, QF, q, hQ, hker, hUP, ?_⟩
  intro p r f h
  exact hα p r (leOfHom f)

end AlgebraicGeometry.Scheme.CommAlgebraSheaf

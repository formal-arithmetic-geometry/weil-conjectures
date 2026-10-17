/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.ZetaSeries
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import Sheaf.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # A sheaf supported in low dimension is a filtered union

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-sc-support-dimension-union`.
(blueprint: lem-sc-support-dimension-union)

The index category is the full poset of closed subsets of dimension at most `a`.
The parameters `D`, `c`, `hz`, and `hk` specify the support kernels by their universal
properties, including their inclusions into `N`. Naturality and monicity then force
exactly the canonical transition maps. No choice of a kernel model is imposed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry


-- Restrict strict chains to their largest member to control dimensions of finite unions.
open TopologicalSpace Topology Set Order Opposite in
private def irredRestrict {X : Type*} [TopologicalSpace X] (s : Set X)
    (t : IrreducibleCloseds X) (ht : (t : Set X) ⊆ s) : IrreducibleCloseds s where
  carrier := Subtype.val ⁻¹' (t : Set X)
  isClosed' := t.isClosed.preimage continuous_subtype_val
  isIrreducible' := by
    let f : ↥(t : Set X) → ↥s := fun x ↦ ⟨x.1, ht x.2⟩
    have hf : Continuous f := continuous_subtype_val.subtype_mk _
    have : IrreducibleSpace ↥(t : Set X) := isIrreducible_iff_irreducibleSpace.mp t.isIrreducible
    have hirr := IrreducibleSpace.isIrreducible_univ ↥(t : Set X)
    convert hirr.image f hf.continuousOn using 1
    ext x
    simp only [mem_image, mem_univ, true_and, mem_preimage]
    constructor
    · intro hx; exact ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩
    · rintro ⟨y, rfl⟩; exact y.2

open TopologicalSpace Topology Set Order Opposite in
private theorem irredRestrict_strictMono {X : Type*} [TopologicalSpace X] (s : Set X) :
    StrictMono (fun t : {t : IrreducibleCloseds X // (t : Set X) ⊆ s} ↦
      irredRestrict s t.1 t.2) := by
  intro a b hab
  refine lt_iff_le_not_ge.mpr ⟨?_, ?_⟩
  · intro x hx; exact hab.le hx
  · intro hba
    apply hab.not_ge
    intro x hx
    exact hba (show (⟨x, b.2 hx⟩ : s) ∈ irredRestrict s b.1 b.2 from hx)

open TopologicalSpace Topology Set Order Opposite in
private theorem dimension_le_of_irred {X : Type*} [TopologicalSpace X]
    {n : WithBot ℕ∞} (h : ∀ t : IrreducibleCloseds X, topologicalKrullDim (t : Set X) ≤ n) :
    topologicalKrullDim X ≤ n := by
  unfold topologicalKrullDim Order.krullDim
  apply iSup_le
  intro p
  let q : LTSeries {t : IrreducibleCloseds X // (t : Set X) ⊆ (p.last : Set X)} :=
    LTSeries.mk p.length (fun i ↦ ⟨p i, p.monotone (Fin.le_last i)⟩)
      (fun i j hij ↦ p.strictMono hij)
  have hh := (q.map _ (irredRestrict_strictMono (p.last : Set X))).length_le_krullDim
  exact hh.trans (h p.last)

open TopologicalSpace Topology Set Order Opposite in
private theorem dimension_union_le {X : Type*} [TopologicalSpace X]
    (s t : Set X) (hs : IsClosed s) (ht : IsClosed t) (n : WithBot ℕ∞)
    (hds : topologicalKrullDim s ≤ n) (hdt : topologicalKrullDim t ≤ n) :
    topologicalKrullDim (s ∪ t : Set X) ≤ n := by
  apply dimension_le_of_irred
  intro C
  have hi := C.isIrreducible.image Subtype.val continuous_subtype_val.continuousOn
  have hc : (Subtype.val '' (C : Set (s ∪ t : Set X))) ⊆ s ∪ t := by
    rintro _ ⟨x, hx, rfl⟩; exact x.2
  rcases isPreirreducible_iff_isClosed_union_isClosed.mp hi.2 s t hs ht hc with h | h
  · let f : ↥(C : Set (s ∪ t : Set X)) → ↥s := fun x ↦ ⟨x.1.1, h ⟨x.1, x.2, rfl⟩⟩
    have hf : IsEmbedding f := by
      exact IsEmbedding.of_comp (f := f) (g := (Subtype.val : ↥s → X))
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
        continuous_subtype_val (by
          change IsEmbedding (Subtype.val ∘ Subtype.val :
            ↥(C : Set ↥(s ∪ t)) → X)
          exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    exact hf.isInducing.topologicalKrullDim_le.trans hds
  · let f : ↥(C : Set (s ∪ t : Set X)) → ↥t := fun x ↦ ⟨x.1.1, h ⟨x.1, x.2, rfl⟩⟩
    have hf : IsEmbedding f := by
      exact IsEmbedding.of_comp (f := f) (g := (Subtype.val : ↥t → X))
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
        continuous_subtype_val (by
          change IsEmbedding (Subtype.val ∘ Subtype.val :
            ↥(C : Set ↥(s ∪ t)) → X)
          exact IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal)
    exact hf.isInducing.topologicalKrullDim_le.trans hdt

open TopologicalSpace Topology Set Order Opposite in
private theorem dimension_empty_le {X : Type*} [TopologicalSpace X] (a : ℕ) :
    topologicalKrullDim ↥(∅ : Set X) ≤ (a : WithBot ℕ∞) := by
  exact (topologicalKrullDim_zero_of_discreteTopology _).trans (by exact_mod_cast Nat.zero_le a)

open TopologicalSpace Topology Set Order Opposite in
private theorem dimension_finset_sup_le {X : Type*} [TopologicalSpace X] (a : ℕ)
    {ι : Type*} (s : Finset ι) (C : ι → Closeds X)
    (h : ∀ i ∈ s, topologicalKrullDim ↥(C i : Set X) ≤ (a : WithBot ℕ∞)) :
    topologicalKrullDim ↥((s.sup C : Closeds X) : Set X) ≤ (a : WithBot ℕ∞) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, Closeds.coe_bot]
    exact dimension_empty_le a
  | @insert i s hi ih =>
    rw [Finset.sup_insert, Closeds.coe_sup]
    exact dimension_union_le _ _ (C i).isClosed (s.sup C).isClosed _
      (h i (by simp)) (ih (fun j hj ↦ h j (by simp [hj])))

-- Bound the image of a closed support by the closures of finitely many image generic points.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open TopologicalSpace Topology Set Order Opposite in
private theorem closed_support_image_bound
    {K : Type u} [Field K] {B : Scheme.{u}}
    (p : B ⟶ Spec (.of K)) [LocallyOfFiniteType p] [QuasiCompact p]
    (V : B.Etale) [NoetherianSpace V.left] (S : Closeds V.left) (a : ℕ)
    (htr : ∀ v ∈ (S : Set V.left),
      @Algebra.trdeg K _ _ _ ((p.residueFieldAlgebraMap (V.hom v)).toAlgebra) ≤
        (a : Cardinal.{u})) :
    ∃ Z : Closeds B, topologicalKrullDim ↥(Z : Set B) ≤ (a : WithBot ℕ∞) ∧
      V.hom '' (S : Set V.left) ⊆ (Z : Set B) := by
  classical
  let : B.Over (Spec (.of K)) := ⟨p⟩
  have : LocallyOfFiniteType (B ↘ Spec (.of K)) := by
    change LocallyOfFiniteType p
    infer_instance
  have : QuasiCompact (B ↘ Spec (.of K)) := by
    change QuasiCompact p
    infer_instance
  obtain ⟨T, hT, hST⟩ := NoetherianSpace.exists_finset_irreducible S
  let η (i : T) := (hT i).genericPoint
  let C (i : T) : Closeds B := ⟨closure ({V.hom (η i)} : Set B), isClosed_closure⟩
  have hη (i : T) : IsGenericPoint (η i) (i.val : Set V.left) :=
    (hT i).isGenericPoint_genericPoint i.val.isClosed
  have hiS (i : T) : (i.val : Set V.left) ⊆ S := by
    rw [hST]
    exact Finset.le_sup (f := id) i.property
  have hC (i : T) : topologicalKrullDim ↥(C i : Set B) ≤ (a : WithBot ℕ∞) := by
    obtain ⟨d, hd, hdeg⟩ := topologicalKrullDim_closed_irreducible_eq_trdeg (K := K)
      (C i : Set B) (C i).isClosed isIrreducible_singleton.closure
      (V.hom (η i)) (subset_closure (by simp)) rfl
    have hdi := htr (η i) (hiS i (hη i).mem)
    rw [hdeg] at hdi
    have hdia : d ≤ a := by exact_mod_cast hdi
    rw [hd]
    exact_mod_cast hdia
  refine ⟨Finset.univ.sup C, dimension_finset_sup_le a _ C (fun i _ ↦ hC i), ?_⟩
  have hsZ : S ≤ (Finset.univ.sup C).preimage V.hom.continuous := by
    rw [hST]
    apply Finset.sup_le
    intro i hi v hvi
    have hviC : V.hom v ∈ (C ⟨i, hi⟩ : Set B) := by
      have hcl := (hη ⟨i, hi⟩).image V.hom.continuous
      change V.hom v ∈ closure ({V.hom (η ⟨i, hi⟩)} : Set B)
      rw [hcl.def]
      exact subset_closure (Set.mem_image_of_mem _ hvi)
    exact (show C ⟨i, hi⟩ ≤ Finset.univ.sup C from
      Finset.le_sup (Finset.mem_univ (⟨i, hi⟩ : T))) hviC
  rintro _ ⟨v, hv, rfl⟩
  exact hsZ hv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open TopologicalSpace Topology Set Order Opposite in
private theorem section_zero_off_bounded
    {K : Type u} [Field K] {B : Scheme.{u}}
    (p : B ⟶ Spec (.of K)) [LocallyOfFiniteType p] [QuasiCompact p]
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (a : ℕ)
    (hvanish : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ B),
      (a : Cardinal.{u}) <
          @Algebra.trdeg K _ _ _ ((p.residueFieldAlgebraMap (s default)).toAlgebra) →
        IsZero (((Scheme.pointSmallEtale s).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj N))
    (V : B.Etale) [IsAffine V.left] (t : N.obj.obj (Opposite.op V)) :
    ∃ Z : Closeds B, topologicalKrullDim ↥(Z : Set B) ≤ (a : WithBot ℕ∞) ∧
      ∀ (V' : B.Etale) (h : V' ⟶ V),
        Set.range (h.left ≫ V.hom) ⊆ (Z : Set B)ᶜ → N.obj.map h.op t = 0 := by
  classical
  obtain ⟨W, i, hi, hzero, hgerm⟩ := Scheme.etale_section_zero_open B N V t
  have : IsOpenImmersion i.left := hi
  let S : Closeds V.left :=
    ⟨(Set.range i.left)ᶜ, i.left.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  have : IsLocallyNoetherian V.left :=
    LocallyOfFiniteType.isLocallyNoetherian (V.hom ≫ p)
  have : IsNoetherian V.left := ⟨⟩
  obtain ⟨Z, hZ, himage⟩ := closed_support_image_bound p V S a (by
    intro v hv
    by_contra h
    have hd : (a : Cardinal.{u}) <
        @Algebra.trdeg K _ _ _ ((p.residueFieldAlgebraMap (V.hom v)).toAlgebra) :=
      lt_of_not_ge h
    let Ω := AlgebraicClosure (V.left.residueField v)
    let s : Spec (.of Ω) ⟶ B := V.left.algClosurePoint v ≫ V.hom
    have hvbase : (V.left.algClosurePoint v) default = v := by
      exact Scheme.algClosurePoint_base V.left v default
    have hsbase : s default = V.hom v := by
      change V.hom ((V.left.algClosurePoint v) default) = V.hom v
      rw [hvbase]
    have hz := hvanish Ω s (by rw [hsbase]; exact hd)
    have : Subsingleton (((Scheme.pointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj N) := AddCommGrpCat.subsingleton_of_isZero hz
    have : Subsingleton (((Scheme.pointSmallEtale s).presheafFiber
        (A := AddCommGrpCat.{u + 1})).obj N.obj) := by
      change Subsingleton (((Scheme.pointSmallEtale s).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj N)
      infer_instance
    have htg : (Scheme.pointSmallEtale s).toPresheafFiber V
        (Over.homMk (V.left.algClosurePoint v)) N.obj t = 0 := Subsingleton.elim _ _
    obtain ⟨y, hy⟩ := (hgerm Ω (V.left.algClosurePoint v)).mp htg
    apply hv
    refine ⟨y default, ?_⟩
    have hb := congrArg (fun f : Spec (.of Ω) ⟶ V.left ↦ f default) hy
    change i.left (y default) = (V.left.algClosurePoint v) default at hb
    exact hb.trans hvbase)
  refine ⟨Z, hZ, fun V' h hsub ↦ (hzero V' h).mpr ?_⟩
  rintro _ ⟨x, rfl⟩
  by_contra hx
  exact (hsub ⟨x, rfl⟩) (himage ⟨h.left x, hx, rfl⟩)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open TopologicalSpace Topology Set Order Opposite in
private theorem unit_section_zero_of_restriction
    {B : Scheme.{u}} (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : B.Opens) (V : B.Etale) (t : N.obj.obj (op V))
    (hzero : ∀ (W : B.Etale) (h : W ⟶ V),
      Set.range (h.left ≫ V.hom) ⊆ (U : Set B) → N.obj.map h.op t = 0) :
    (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app N).hom.app
      (op V)) t = 0 := by
  let adj := MorphismProperty.Over.mapPullbackAdj @Etale ⊤ U.ι
    (inferInstance : Etale U.ι) _root_.trivial
  let F := MorphismProperty.Over.map ⊤ (inferInstance : Etale U.ι)
  let G := MorphismProperty.Over.pullback @Etale ⊤ U.ι
  let ε : F.obj (G.obj V) ⟶ V := adj.counit.app V
  have hε : Set.range (ε.left ≫ V.hom) ⊆ (U : Set B) := by
    have hw : ε.left ≫ V.hom = (G.obj V).hom ≫ U.ι := ε.w
    rw [hw]
    rintro _ ⟨x, rfl⟩
    exact ((G.obj V).hom x).property
  have ht := hzero (F.obj (G.obj V)) ε hε
  let e := Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.ι
    (inferInstance : Etale U.ι)
  let q := (Etale.lowerStar AddCommGrpCat.{u + 1} U.ι).map (e.hom.app N)
  have : IsIso q := inferInstance
  have : Mono (q.hom.app (op V)) := inferInstance
  apply (AddCommGrpCat.mono_iff_injective (q.hom.app (op V))).mp inferInstance
  rw [map_zero]
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι)
    (Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι
      (inferInstance : Etale U.ι)) N
  have hu' := congrArg (fun f ↦ f.hom.app (op V) t) hu
  change (q.hom.app (op V))
    ((((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app N).hom.app
      (op V)) t) = _ at hu'
  rw [hu']
  exact ht

open TopologicalSpace Topology Set Order Opposite in
private theorem kernel_section_lift
    {B : Scheme.{u}} {P N Q : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (f : P ⟶ N) (g : N ⟶ Q) (w : f ≫ g = 0)
    (hk : IsLimit (KernelFork.ofι f w)) (V : B.Etale) (s : N.obj.obj (op V))
    (hs : g.hom.app (op V) s = 0) :
    ∃ t : P.obj.obj (op V), f.hom.app (op V) t = s := by
  let E := sheafToPresheaf B.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (evaluation _ _).obj (op V)
  let S := ShortComplex.mk f g w
  have : Mono f := mono_of_isLimit_fork hk
  have he := (S.exact_of_f_is_kernel hk).map_of_mono_of_preservesKernel E
    inferInstance inferInstance
  exact (ShortComplex.ab_exact_iff _).mp he s hs

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open TopologicalSpace Topology Set Order Opposite in
private theorem exists_affine_germ {B : Scheme.{u}} {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ B)
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (x : ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj N) :
    ∃ (V : B.Etale) (_ : IsAffine V.left)
      (v : (Scheme.pointSmallEtale s).fiber.obj V) (t : N.obj.obj (op V)),
      (Scheme.pointSmallEtale s).toPresheafFiber V v N.obj t = x := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1} (forget AddCommGrpCat.{u + 1})
  let Φ := Scheme.pointSmallEtale s
  obtain ⟨V, v, t, ht⟩ := Φ.toPresheafFiber_jointly_surjective (P := N.obj) x
  obtain ⟨W, ⟨f⟩⟩ := Scheme.AffinePointedEtaleNeighborhood.exists_hom s ⟨V, v⟩
  refine ⟨W.obj.1, inferInstance, W.obj.2, N.obj.map f.val.op t, ?_⟩
  have hw := Φ.toPresheafFiber_w f.val W.obj.2 N.obj
  have hf : Φ.fiber.map f.val W.obj.2 = v := f.property
  have hwt := congrArg (fun k ↦ k t) hw
  simp only [ConcreteCategory.comp_apply, hf] at hwt
  exact hwt.trans ht

-- AB5 gives monicity; stalk lifts and faithfulness give epimorphicity by cancellation.
set_option backward.isDefEq.respectTransparency false in
open TopologicalSpace Topology Set Order Opposite in
private theorem colimit_iso_of_stalk_lifts {B : Scheme.{u}} {I : Type u}
    [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (c : D ⟶ (Functor.const I).obj N)
    (hc : ∀ i, Mono (c.app i))
    (hlift : ∀ (b : B)
      (x : (((Scheme.pointSmallEtale (B.algClosurePoint b)).sheafFiber
        (A := AddCommGrpCat.{u + 1})).obj N)),
      ∃ (i : I) (y : (((Scheme.pointSmallEtale (B.algClosurePoint b)).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj
        (D.obj i))),
        (Scheme.pointSmallEtale (B.algClosurePoint b)).sheafFiber.map (c.app i) y = x) :
    IsIso ((colimit.isColimit D).desc (Cocone.mk N c)) := by
  have : HasColimitsOfSize.{u + 1, u + 1}
      (Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.hasColimits _
  have : AB5OfSize.{u, u} (Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} _
  have (i : I) : Mono (c.app i) := hc i
  have : IsConnected I := IsFiltered.isConnected I
  have : Mono c := NatTrans.mono_of_mono_app c
  let t := (colimit.isColimit D).desc (Cocone.mk N c)
  have : Mono t := colim.map_mono' c (colimit.isColimit D)
    (isColimitConstCocone I N) t (fun i ↦ by simp [t])
  have : Epi t := by
    refine ⟨fun {G} g h hgh ↦ ?_⟩
    have he (i : I) : c.app i ≫ g = c.app i ≫ h := by
      simpa [t] using colimit.ι D i ≫= hgh
    refine Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint fun b ↦ ?_
    apply ConcreteCategory.ext
    apply DFunLike.ext
    intro x
    obtain ⟨i, y, rfl⟩ := hlift b x
    have hh := congr((Scheme.pointSmallEtale (B.algClosurePoint b)).sheafFiber.map $(he i) y)
    simp only [Functor.map_comp, ConcreteCategory.comp_apply] at hh
    convert! hh using 1
  exact isIso_of_mono_of_epi t

/--
Let `B` be finite type over a field `K`, and let `N` be a torsion étale sheaf whose
geometric stalks vanish above transcendence degree `a`.  For a filtered diagram of
the kernels of restriction away from closed subsets of dimension at most `a`, the
canonical map from its colimit to `N` is an isomorphism.

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/lem-sc-support-dimension-union.md`;
Stacks Project, Étale Cohomology, Tags 04FR, 03PT, and 03PU.

Proof:
1. The empty closed subset has dimension bottom. Finite unions preserve the dimension
   bound: an irreducible closed subset of a union lies in one member. Thus the index
   poset is small, nonempty and directed (`def-kun-topological-krull-dimension`,
   `def-weil-irreducible-components`).
2. On an open immersion, inverse image is restriction, by its adjunction to direct
   image. Its unit on sections is restriction to the open complement. Its kernel
   therefore consists of sections zero there. Inclusion of closed subsets gives
   inclusions of these kernels (`def-weil-pbc-direct-image`,
   `def-weil-pbc-inverse-image`, `def-weil-pbc-etale-site`).
3. Represent a geometric germ on a pointed affine étale neighbourhood. Restrict it
   over an affine chart of `B`. The resulting map of affine schemes is quasi-compact,
   so its source is finite type over `K` (`lemma-weil-pbc-affine-neighbourhood-cofinal`,
   `def-weil-finite-type-morphism`, `lem-kun-etale-lfp`).
4. The section has a largest zero open (`lem-sc-etale-section-zero-open`). Its closed
   complement `S` has finitely many irreducible components, since the neighbourhood
   is Noetherian (`lem-weil-pbc-finite-type-over-noetherian`,
   `lem-sc-noetherian-closed-subset-finite-components`). Each component has a generic
   point by `lem-weil-pbc-scheme-sober`; the empty case has no components.
5. Each image generic point has nonzero geometric germ, so its residue field has
   transcendence degree at most `a`. Its closure has dimension at most `a` by
   `lem-sc-closed-irreducible-dimension-trdeg`. Continuity places the image of the
   corresponding component in that closure. The finite union `Z` of these closures
   has dimension at most `a` and contains the image of `S`.
6. The section is zero over the complement of `Z`, by
   `lem-sc-etale-section-zero-open`, so belongs to the support kernel at `Z`.
   Hence the kernel stalks exhaust every geometric stalk of `N`.
7. Stalks preserve these colimits (`lem-kun-stalks-commute-colimits`) and kernel
   inclusions (`prop-weil-pbc-geometric-stalks-exact`). The resulting stalk map is
   injective because each stage embeds, and surjective by step 6. Apply
   `lemma-weil-pbc-geometric-stalk-conservative`. Torsion remains a hypothesis
   although this argument does not use it.

(blueprint: lem-sc-support-dimension-union)
-/
theorem support_dimension_union
    {K : Type u} [Field K] {B : Scheme.{u}}
    (p : B ⟶ Spec (.of K)) [LocallyOfFiniteType p] [QuasiCompact p]
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ℕ) (hN : CategoryTheory.Sheaf.IsTorsion N)
    (hvanish : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ B),
      (a : Cardinal.{u}) <
          @Algebra.trdeg K _ _ _ ((p.residueFieldAlgebraMap (s default)).toAlgebra) →
        IsZero (((Scheme.pointSmallEtale s).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj N))
    (D : {Z : TopologicalSpace.Closeds B //
      topologicalKrullDim ↥(Z : Set B) ≤ (a : WithBot ℕ∞)} ⥤
        Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (c : D ⟶ (Functor.const _).obj N)
    (hz : ∀ Z, c.app Z ≫
      (Etale.upperStarLowerStarAdjunction (AddCommGrpCat.{u + 1})
        (Scheme.Opens.ι ⟨(Z.val : Set B)ᶜ, Z.val.isClosed.isOpen_compl⟩)).unit.app N = 0)
    (hk : ∀ Z, IsLimit (KernelFork.ofι (c.app Z) (hz Z))) :
    IsIso ((colimit.isColimit D).desc (Cocone.mk N c)) := by
  classical
  have _ := hN
  -- The DAG records the shorter implementation of steps 3 and 7 of the original sketch.
  let I := {Z : TopologicalSpace.Closeds B //
    topologicalKrullDim ↥(Z : Set B) ≤ (a : WithBot ℕ∞)}
  have : Nonempty I := ⟨⟨⊥, by
    simpa only [TopologicalSpace.Closeds.coe_bot] using dimension_empty_le (X := B) a⟩⟩
  have : IsDirectedOrder I := ⟨fun Z Z' ↦ by
    refine ⟨⟨Z.val ⊔ Z'.val, ?_⟩,
      (show Z.val ≤ Z.val ⊔ Z'.val from le_sup_left),
      (show Z'.val ≤ Z.val ⊔ Z'.val from le_sup_right)⟩
    rw [TopologicalSpace.Closeds.coe_sup]
    exact dimension_union_le _ _ Z.val.isClosed Z'.val.isClosed _ Z.property Z'.property⟩
  have : IsFiltered I := inferInstance
  refine colimit_iso_of_stalk_lifts D N c (fun Z ↦ mono_of_isLimit_fork (hk Z)) ?_
  intro b x
  let Φ := Scheme.pointSmallEtale (B.algClosurePoint b)
  obtain ⟨V, hV, v, t, ht⟩ := exists_affine_germ (B.algClosurePoint b) N x
  have : IsAffine V.left := hV
  obtain ⟨Z, hZ, hsection⟩ := section_zero_off_bounded p N a hvanish V t
  let i : I := ⟨Z, hZ⟩
  have hu :
      (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (Scheme.Opens.ι ⟨(Z : Set B)ᶜ, Z.isClosed.isOpen_compl⟩)).unit.app N).hom.app
        (Opposite.op V)) t = 0 :=
    unit_section_zero_of_restriction N _ V t hsection
  obtain ⟨t', ht'⟩ := kernel_section_lift (c.app i) _ (hz i) (hk i) V t hu
  refine ⟨i, Φ.toPresheafFiber V v (D.obj i).obj t', ?_⟩
  have hn := Φ.toPresheafFiber_naturality (c.app i).hom V v
  have hnt := congrArg (fun f ↦ f t') hn
  simp only [ConcreteCategory.comp_apply, ht'] at hnt
  convert! hnt.trans ht using 1

end AlgebraicGeometry

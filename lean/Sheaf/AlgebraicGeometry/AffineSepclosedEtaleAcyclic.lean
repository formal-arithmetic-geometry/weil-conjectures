/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Sheaf.AlgebraicGeometry.ZeroDimensionalSpectrumProfinite
import WeilConjectures.RingTheory.StrictlyHenselianOfDimensionZero
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore

/-!
# Étale acyclicity of affine schemes with closed separably closed points

Source: Stacks Project, Étale Cohomology, Tag 09AY, `lemma-affine-only-closed-points`
(blueprint: lem-cbc-affine-sepclosed-etale-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private noncomputable def etaleOpenInclusion (X : Scheme.{u}) : X.Opens ⥤ X.Etale :=
  MorphismProperty.Comma.lift X.restrictFunctor
    (fun U ↦ (inferInstance : AlgebraicGeometry.Etale U.ι))
    (fun _ ↦ trivial) (fun _ ↦ trivial)

private theorem etaleOpenInclusion_continuous (X : Scheme.{u}) :
    (etaleOpenInclusion X).IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology := by
  obtain ⟨i, hi, -, -, -, hcont, -⟩ := zariski_to_etale_core X
  let := hcont
  let e : etaleOpenInclusion X ≅ i :=
    ((Functor.whiskeringRight X.Opens X.Etale (Over X)).obj
      (Scheme.Etale.forget X)).preimageIso (eqToIso hi.symm)
  exact Functor.isContinuous_of_iso e.symm _ _

open CategoryTheory.Limits Opposite TopologicalSpace in
/-- Local lifts glue after a finite disjoint clopen refinement; empty overlaps have
a unique section. This is the exactness argument underlying Stacks Tag 0A3F. -/
private theorem surjective_top_of_profinite_local_lifts
    (X : TopCat.{u}) [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}}
    (φ : F ⟶ G)
    (hφ : ∀ (s : G.obj.obj (op ⊤)) (x : X),
      ∃ (U : TopologicalSpace.Opens X), x ∈ U ∧ ∃ t : F.obj.obj (op U),
        φ.hom.app (op U) t = G.obj.map (homOfLE le_top).op s) :
    Function.Surjective (φ.hom.app (op ⊤)) := by
  classical
  intro s
  choose U hxU t ht using hφ s
  have hcover : IsOpenCover U := .of_sets (fun x ↦ (U x).isOpen)
    (Set.eq_univ_iff_forall.mpr (fun x ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩))
  obtain ⟨n, W, hW, hcov, hdisj⟩ := hcover.exists_finite_nonempty_disjoint_clopen_cover
  choose r hr using fun j ↦ (hW j).2
  let V : Fin n → TopologicalSpace.Opens X := fun j ↦ (W j).toOpens
  let a : ∀ j, F.obj.obj (op (V j)) :=
    fun j ↦ F.obj.map (homOfLE (hr j)).op (t (r j))
  have hV : (⊤ : TopologicalSpace.Opens X) ≤ iSup V := by
    intro x _
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hj⟩
  have hc : TopCat.Presheaf.IsCompatible F.obj V a := by
    intro j k
    by_cases hjk : j = k
    · subst k
      congr 1
    · have he : V j ⊓ V k = ⊥ := by
        apply SetLike.coe_injective
        exact Set.disjoint_iff_inter_eq_empty.mp ((Clopens.coe_disjoint).mpr (hdisj hjk))
      let : Subsingleton (F.obj.obj (op (V j ⊓ V k))) :=
        AddCommGrpCat.subsingleton_of_isZero (TopCat.Sheaf.isTerminalOfEqEmpty F he).isZero
      exact Subsingleton.elim _ _
  obtain ⟨b, hb, -⟩ := TopCat.Sheaf.existsUnique_gluing' F V ⊤ (fun _ ↦ homOfLE le_top) hV a hc
  refine ⟨b, TopCat.Sheaf.eq_of_locally_eq' G V ⊤ (fun _ ↦ homOfLE le_top) hV _ _ ?_⟩
  intro j
  have hn := ConcreteCategory.congr_hom (φ.hom.naturality
    (homOfLE (show V j ≤ ⊤ from le_top)).op) b
  simp only [ConcreteCategory.comp_apply] at hn
  rw [← hn, hb]
  have htj := congrArg (G.obj.map (homOfLE (show V j ≤ U (r j) from hr j)).op)
    (ht (r j))
  change φ.hom.app (op (V j)) (F.obj.map (homOfLE (hr j)).op (t (r j))) = _
  rw [← ConcreteCategory.comp_apply, φ.hom.naturality]
  simp only [← ConcreteCategory.comp_apply, ← G.obj.map_comp] at htj
  exact htj

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits Opposite TopologicalSpace in
/-- Spread a section over a stalk to an open neighborhood using finite presentation.
This is the strict-local neighborhood argument used in Stacks Tag 09AY. -/
private theorem exists_section_near_of_strictlyHenselian
    {X Y : Scheme.{u}} [IsAffine X] (f : Y ⟶ X) [AlgebraicGeometry.Etale f]
    (y : Y) (hx : IsStrictlyHenselianLocalRing (X.presheaf.stalk (f y))) :
    ∃ (U : X.Opens), f y ∈ U ∧ ∃ s : U.toScheme ⟶ Y, s ≫ f = U.ι := by
  classical
  let x := f y
  let : IsStrictlyHenselianLocalRing (X.presheaf.stalk x) := hx
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : Y.Opens) from trivial)
  let g := hV.fromSpec ≫ f
  let y' := hV.primeIdealOf ⟨y, hyV⟩
  have hy' : g y' = x := by
    simp only [g, Scheme.Hom.comp_apply, y', hV.fromSpec_primeIdealOf]
    rfl
  obtain ⟨z, hz₁, hz₂⟩ := Pullback.exists_preimage_pullback
    (f := g) (g := X.fromSpecStalk x) y'
    (IsLocalRing.closedPoint (X.presheaf.stalk x))
    (hy'.trans (X.fromSpecStalk_closedPoint (x := x)).symm)
  obtain ⟨σ, hσ⟩ := exists_section_of_etale_of_isStrictlyHenselianLocalRing
    (R := ↑(X.presheaf.stalk x)) (pullback.snd g (X.fromSpecStalk x)) z hz₂
  let a := σ ≫ pullback.fst g (X.fromSpecStalk x)
  have ha : a ≫ g = X.fromSpecStalk x := by
    change (σ ≫ pullback.fst g (X.fromSpecStalk x)) ≫ g = _
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  let α : Γ(X, ⊤) ⟶ Γ(Y, V) := Spec.preimage (g ≫ X.isoSpec.hom)
  let ψ : Γ(Y, V) ⟶ X.presheaf.stalk x := Spec.preimage a
  have hα : Spec.map α = g ≫ X.isoSpec.hom := Spec.map_preimage _
  have hψ : Spec.map ψ = a := Spec.map_preimage _
  have hαfp : α.hom.FinitePresentation := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp
    rw [hα]
    infer_instance
  have hαψ : α ≫ ψ = X.presheaf.germ ⊤ x trivial := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ, hα, ← Category.assoc, ha]
    exact X.fromSpecStalk_toSpecΓ x
  let D := (OpenNhds.inclusion (X := X.toLocallyRingedSpace.toTopCat) x).op ⋙ X.presheaf
  let β : (Functor.const _).obj Γ(X, ⊤) ⟶ D :=
    { app := fun U ↦ X.presheaf.map (homOfLE (show U.unop.1 ≤ ⊤ from le_top)).op
      naturality := by
        intro U W h
        change X.presheaf.map (homOfLE le_top).op =
          X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map _
        rw [← X.presheaf.map_comp]
        rfl }
  obtain ⟨U, ψ', hψ'α, -⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
      Γ(X, ⊤) D β α (colimit.cocone D) (colimit.isColimit D) hαfp ψ
      (fun U ↦ hαψ.trans (X.presheaf.germ_res _ x U.unop.2).symm)
  refine ⟨U.unop.1, U.unop.2,
    Scheme.Opens.toSpecΓ (X := X) U.unop.1 ≫ Spec.map ψ' ≫ hV.fromSpec, ?_⟩
  apply (cancel_mono X.isoSpec.hom).mp
  change Scheme.Opens.toSpecΓ (X := X) U.unop.1 ≫
    (Spec.map ψ' ≫ (g ≫ X.isoSpec.hom)) = _
  rw [← hα, ← Spec.map_comp, hψ'α]
  exact Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top U.unop.1

set_option backward.isDefEq.respectTransparency false in
open CategoryTheory.Limits Opposite TopologicalSpace in
/-- Étale local surjectivity becomes Zariski local surjectivity when all stalks
are strictly henselian. -/
private theorem etale_epi_local_lifts
    (X : Scheme.{u}) [IsAffine X]
    (hX : ∀ x : X, IsStrictlyHenselianLocalRing (X.presheaf.stalk x))
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : F ⟶ G) [Epi φ]
    (s : G.obj.obj (op ((etaleOpenInclusion X).obj ⊤))) (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧
      ∃ t : F.obj.obj (op ((etaleOpenInclusion X).obj U)),
        φ.hom.app (op ((etaleOpenInclusion X).obj U)) t =
          G.obj.map ((etaleOpenInclusion X).map (homOfLE le_top)).op s := by
  classical
  let i := etaleOpenInclusion X
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1} φ).2 inferInstance
  obtain ⟨C, hC, p, hle⟩ := (mem_smallGrothendieckTopology _ _).1
    (Presheaf.imageSieve_mem X.smallEtaleTopology φ.hom s)
  obtain ⟨j, y, hy⟩ := C.exists_eq (show (i.obj ⊤).left from ⟨x, trivial⟩)
  have ha : Presheaf.imageSieve φ.hom s ((C.f j).asOverProp X) :=
    hle _ _ (Presieve.ofArrows.mk j)
  obtain ⟨b, hb⟩ := ha
  have hax : (C.X j ↘ X) y = x := by
    have hw : C.f j ≫ (⊤ : X.Opens).ι = (C.X j ↘ X) := comp_over (C.f j) X
    rw [← hw, Scheme.Hom.comp_apply, hy]
    rfl
  have : AlgebraicGeometry.Etale (C.X j ↘ X) := p j
  obtain ⟨U, hxU, σ, hσ⟩ := exists_section_near_of_strictlyHenselian
    (C.X j ↘ X) y (hX _)
  have hxU' : x ∈ U := hax ▸ hxU
  let l : i.obj U ⟶ (C.X j).asOverProp _ (p j) :=
    MorphismProperty.Over.homMk σ hσ trivial
  refine ⟨U, hxU', F.obj.map l.op b, ?_⟩
  have hn := ConcreteCategory.congr_hom (φ.hom.naturality l.op) b
  simp only [ConcreteCategory.comp_apply] at hn
  rw [hn, hb, ← ConcreteCategory.comp_apply, ← G.obj.map_comp, ← op_comp]
  suffices hh : l ≫ (C.f j).asOverProp X =
      i.map (homOfLE (show U ≤ ⊤ from le_top)) by rw [hh]
  apply (Scheme.Etale.forget X).map_injective
  apply Over.OverMorphism.ext
  apply (cancel_mono (⊤ : X.Opens).ι).mp
  change σ ≫ (C.f j ≫ (⊤ : X.Opens).ι) = X.homOfLE (show U ≤ ⊤ from le_top) ≫ (⊤ : X.Opens).ι
  have hw : C.f j ≫ (⊤ : X.Opens).ι = (C.X j ↘ X) := comp_over (C.f j) X
  rw [hw, hσ, Scheme.homOfLE_ι]

/-- An affine scheme whose points are closed and whose residue fields are separably
closed has zero higher étale cohomology for every abelian sheaf.
Source: Stacks Project, Étale Cohomology, Tag 09AY
(blueprint: lem-cbc-affine-sepclosed-etale-acyclic).

Proof:
1. Closed singletons imply that every prime of Γ(T, ⊤) is maximal. The spectrum
   is therefore profinite. Mathlib's stalk-dimension/coheight formula shows that
   every stalk has dimension zero. Its separably closed residue field then makes
   it strictly henselian, by lem-weil-pbc-dimension-zero-local-strictly-henselian.
2. An étale neighborhood has a section over the strict local stalk. Choose an
   affine neighborhood upstairs. Finite presentation spreads the resulting ring
   map to an open neighborhood downstairs; the compatibility with the structure
   map is preserved by the finite-presentation factorization theorem.
3. An epimorphism of étale abelian sheaves is locally surjective. Step 2 turns
   each étale local lift of a section into a Zariski local lift. Restriction to
   opens is a sheaf by lem-weil-pbc-zariski-etale-core. Refine the open cover by
   finitely many disjoint clopens and glue the lifts, whose overlaps are empty.
   Thus evaluation at the terminal étale object preserves epimorphisms.
4. The constant-sheaf/evaluation adjunction sends the projective group ULift ℤ
   to a projective constant sheaf. The definition of Sheaf.H as Ext out of this
   constant sheaf and positive-degree Ext vanishing for a projective first
   argument give the conclusion. No cohomology comparison theorem is needed. -/
theorem subsingleton_H_of_affine_closed_isSepClosed
    (T : Scheme.{u}) [IsAffine T]
    (hclosed : ∀ t : T, IsClosed ({t} : Set T))
    (hsep : ∀ t : T, IsSepClosed (T.residueField t))
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (i : ℕ) (hi : 0 < i) : Subsingleton (Sheaf.H F i) :=
    open CategoryTheory.Limits Opposite TopologicalSpace in by
  classical
  let e := T.isoSpec.hom.homeomorph
  have hmax : ∀ p : Ideal Γ(T, ⊤), p.IsPrime → p.IsMaximal := by
    intro p hp
    let x : PrimeSpectrum Γ(T, ⊤) := ⟨p, hp⟩
    apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp
    simpa only [Set.image_singleton, e.apply_symm_apply] using
      e.isClosedMap _ (hclosed (e.symm x))
  obtain ⟨hcomp, hhaus, hdisc⟩ := Spec.profinite_of_isMaximal Γ(T, ⊤) hmax
  let := hcomp
  let := hhaus
  let := hdisc
  let : CompactSpace T.toTopCat := e.symm.compactSpace
  let : T2Space T.toTopCat := e.symm.t2Space
  let : TotallyDisconnectedSpace T.toTopCat := e.symm.totallyDisconnectedSpace
  let : T1Space T := ⟨hclosed⟩
  have hstrict : ∀ t : T, IsStrictlyHenselianLocalRing (T.presheaf.stalk t) := by
    intro t
    let : IsSepClosed (IsLocalRing.ResidueField (T.presheaf.stalk t)) := hsep t
    apply (isStrictlyHenselianLocalRing_of_ringKrullDim_eq_zero.{u, u}
      (T.presheaf.stalk t) ?_).1
    let : PartialOrder T := specializationOrder T
    have ht : IsMax t := by
      intro y hty
      change y ⤳ t at hty
      change t ⤳ y
      exact specializes_of_eq hty.eq.symm
    rw [ringKrullDim_stalk_eq_coheight, Order.IsMax.coheight_eq_zero ht]
    rfl
  let j := etaleOpenInclusion T
  let : j.IsContinuous (Opens.grothendieckTopology T.carrier) T.smallEtaleTopology :=
    etaleOpenInclusion_continuous T
  let ε := j.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology T.carrier) T.smallEtaleTopology
  have hpres : ((sheafSections T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (j.obj ⊤))).PreservesEpimorphisms := by
    constructor
    intro A B φ hφ
    apply (AddCommGrpCat.epi_iff_surjective _).2
    exact surjective_top_of_profinite_local_lifts.{u} T.toTopCat (ε.map φ)
      (etale_epi_local_lifts T hstrict φ)
  let ej : j.obj ⊤ ≅ Scheme.Etale.mk (𝟙 T) :=
    MorphismProperty.Over.isoMk T.topIso (by
      change (⊤ : T.Opens).ι ≫ 𝟙 T = (⊤ : T.Opens).ι
      exact Category.comp_id _)
  let hj : IsTerminal (j.obj ⊤) :=
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T).ofIso ej.symm
  let : Projective ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift ℤ))) :=
    @Adjunction.map_projective _ _ _ _ _ _ (constantSheafAdj _ _ hj)
      hpres _ AddCommGrpCat.projective_of_uliftInt
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  exact Abelian.Ext.subsingleton_of_projective _ _ _

end AlgebraicGeometry.Scheme

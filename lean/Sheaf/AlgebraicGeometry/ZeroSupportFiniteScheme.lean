/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.SchemeTheoreticSupport
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.FiniteOverField
import WeilConjectures.AlgebraicGeometry.Cohomology.Clopen
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.Algebra.Homology.ModuleStalkFunctor

/-! # Finite scheme supporting a coherent module

Source: Stacks Project, Varieties, Tag 0AYT, proof of parts (3)--(5), and Tag 06LH
(blueprint: lem-pc-zero-support-finite-scheme).

Cohomology is computed in modules over the structure sheaf. The comparison is expressed
in modules over the global functions on `X`, restricting scalars along `i.appTop` on the
finite scheme. Thus it retains the scalar action, including the induced `k`-action.
-/

@[expose] public section

universe v

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

namespace AlgebraicGeometry

/-- On a finite discrete scheme, trivialize the invertible module on each singleton
open and assemble the tensor isomorphisms using the disjoint-cover biproduct maps.
This also covers the empty scheme. Source: Stacks, Varieties, Tag 0AYT, last paragraph
of the proof. -/
private theorem tensor_iso_of_discrete {X : Scheme.{v}} [Finite X] [DiscreteTopology X]
    (G L : X.Modules) [L.IsInvertible] : Nonempty (G ⊗ₘ L ≅ G) := by
  classical
  let _ := Fintype.ofFinite X
  let e := Fintype.equivFin X
  let U (i : Fin (Fintype.card X)) : X.Opens := ⟨{e.symm i}, isOpen_discrete _⟩
  have hU : _root_.Pairwise (Function.onFun Disjoint U) := by
    intro i j hij
    change Disjoint (U i) (U j)
    rw [← TopologicalSpace.Opens.coe_disjoint]
    exact Set.disjoint_singleton.mpr (e.symm.injective.ne hij)
  have hcover : ⨆ i, U i = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨e x, by simp [U]⟩
  have : HasFiniteBiproducts X.Modules := Abelian.hasFiniteBiproducts
  let localIso (i : Fin (Fintype.card X)) :
      (restrictFunctor (U i).ι).obj (G ⊗ₘ L) ≅ (restrictFunctor (U i).ι).obj G := by
    have : Subsingleton (U i) := ⟨fun a b ↦ Subtype.ext (a.2.trans b.2.symm)⟩
    let t := (IsInvertible.nonempty_iso_unit
      (⟨e.symm i, rfl⟩ : U i) ((Scheme.Modules.pullback (U i).ι).obj L)).some
    let s := (nonempty_pullback_tensorObj_iso (U i).ι G L).some
    exact (restrictFunctorIsoPullback (U i).ι).app _ ≪≫ s ≪≫
      (Iso.refl _ ⊗ᵢ t) ≪≫ ρ_ _ ≪≫ ((restrictFunctorIsoPullback (U i).ι).app G).symm
  let a : G ⊗ₘ L ≅ ⨁ fun i ↦
      (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj (G ⊗ₘ L) :=
    @asIso _ _ _ _ (biproduct.lift fun i ↦
      (restrictAdjunction (U i).ι).unit.app (G ⊗ₘ L))
      (isIso_biproduct_lift_restrictAdjunction_unit U hU hcover (G ⊗ₘ L))
  let b : G ≅ ⨁ fun i ↦ (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj G :=
    @asIso _ _ _ _ (biproduct.lift fun i ↦ (restrictAdjunction (U i).ι).unit.app G)
      (isIso_biproduct_lift_restrictAdjunction_unit U hU hcover G)
  exact ⟨a ≪≫ biproduct.mapIso (fun i ↦ (pushforward (U i).ι).mapIso (localIso i)) ≪≫ b.symm⟩

/-- For an affine source and affine morphism, compare degree-zero global sections with
restriction of scalars. In positive degrees both sides vanish by affine cohomology and
its pushforward comparison, transported to module-derived sections. Source: Stacks,
Varieties, Tag 0AYT, proof of (3), and Cohomology of Schemes, Tags 01XC and 089W. -/
private theorem affine_support_cohomology {k : Type v} [Field k]
    {Z X : Scheme.{v}} [Z.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (i : Z ⟶ X) [i.IsOver (Spec (.of k))] [IsAffineHom i] [IsAffine Z]
    (M : Z.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Nonempty ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
        ((pushforward i).obj M) ≅
      (ModuleCat.restrictScalars i.appTop.hom).obj
        ((RingedSpace.moduleCohomology Z.toRingedSpace q).obj M)) := by
  let : EnoughInjectives (SheafOfModules (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : EnoughInjectives (SheafOfModules (moduleRings Z.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives Z.toRingedSpace).2
  let : PreservesFiniteLimits (RingedSpace.globalSectionsFunctor X.toRingedSpace) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (Opposite.op ⊤)))
  let : PreservesFiniteLimits (RingedSpace.globalSectionsFunctor Z.toRingedSpace) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings Z.toRingedSpace) (Opposite.op ⊤)))
  cases q with
  | zero =>
    let a := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedZeroIsoSelf
    let b := (RingedSpace.globalSectionsFunctor Z.toRingedSpace).rightDerivedZeroIsoSelf
    exact ⟨a.app _ ≪≫ (ModuleCat.restrictScalars i.appTop.hom).mapIso (b.app M).symm⟩
  | succ q =>
    have : Subsingleton (M.H (q + 1)) := subsingleton_H_succ_of_isAffine M q
    obtain ⟨c⟩ := nonempty_cohomologyFunctor_iso_pushforward_of_isAffineHom k i (q + 1)
    let ec : M.H (q + 1) ≃ₗ[k] ((pushforward i).obj M).H (q + 1) :=
      (c.app ⟨M, inferInstance⟩).toLinearEquiv
    have : Subsingleton (((pushforward i).obj M).H (q + 1)) :=
      ec.symm.injective.subsingleton
    obtain ⟨a, _⟩ := exists_moduleCohomology_source_comparison X (q + 1)
    have : Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace (q + 1)).obj
        ((pushforward i).obj M)) := (a _).injective.subsingleton
    obtain ⟨b, _⟩ := exists_moduleCohomology_source_comparison Z (q + 1)
    have hz : Subsingleton ((RingedSpace.moduleCohomology Z.toRingedSpace (q + 1)).obj M) :=
      (b M).injective.subsingleton
    have : Subsingleton ((ModuleCat.restrictScalars i.appTop.hom).obj
        ((RingedSpace.moduleCohomology Z.toRingedSpace (q + 1)).obj M)) := hz
    exact ⟨(ModuleCat.isZero_of_subsingleton _).isoZero ≪≫
      (ModuleCat.isZero_of_subsingleton _).isoZero.symm⟩

/-- A coherent module with zero-dimensional support is supported on a finite affine scheme.
Source: Stacks Project, Varieties, Tag 0AYT, proof of parts (3)--(5)
(blueprint: lem-pc-zero-support-finite-scheme).

Proof:
1. Finite type over the field makes `X` locally Noetherian, so coherence implies
   quasi-coherence and finite type. The annihilator ideal from
   `lem-weil-pbc-scheme-theoretic-support` defines a closed subscheme with image the support.
2. A closed embedding identifies its dimension with the dimension of its image. Apply
   `lem-pc-zero-dimensional-closed-subscheme-finite` and use its affine presentation
   `Spec A`, with `A` the actual ring of global sections and its induced `k`-algebra.
3. The ideal annihilates `F`. The unit isomorphism of
   `lem-weil-pbc-closed-immersion-pushforward-annihilated` identifies `F` with the
   pushforward of its tensor pullback `G`, which is coherent on the Noetherian source.
4. Compare tensor pullback with ordinary pullback by uniqueness of left adjoints and
   apply the invertible projection formula. The finite source is discrete; on its
   singleton open cover the pulled-back line bundle is trivial. The disjoint-cover
   biproduct isomorphisms assemble `G` tensor the line bundle into an isomorphism with
   `G`. Pushforward therefore identifies `F` tensor `N` with `F`. Transport finite local
   generators, quasi-coherence, and stalks along this isomorphism.
5. For degree zero use the left-exact derived-sections isomorphisms and the equality
   of pushforward global sections with restricted source global sections. In positive
   degrees, affine vanishing and the affine-pushforward cohomology isomorphism show
   both sides vanish. The natural source comparison transfers this to module-valued
   cohomology, so the unique isomorphism between zero modules respects all scalars.
   Apply this comparison to `G` and to its tensor with the pulled-back line bundle.
   The empty support is included throughout; its ring of global sections is the zero ring.
-/
theorem coherent_zero_support_finite_scheme {k : Type v} [Field k]
    (X : Scheme.{v}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (hS : topologicalKrullDim {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ≤ 0)
    (N : X.Modules) [N.IsInvertible] :
    ∃ (A : Type v) (_ : CommRing A) (_ : Algebra k A) (_ : FiniteDimensional k A)
      (i : Spec (CommRingCat.of A) ⟶ X) (_ : IsClosedImmersion i)
      (G : (Spec (CommRingCat.of A)).Modules),
      i ≫ (X ↘ Spec (.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k A)) ∧
      Set.range i.base = {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
      RingedSpace.IsCoherent (Spec (CommRingCat.of A)).toRingedSpace G ∧
      Nonempty (F ≅ (Scheme.Modules.pushforward i).obj G) ∧
      Nonempty (Scheme.Modules.tensorObj F N ≅ (Scheme.Modules.pushforward i).obj
        (Scheme.Modules.tensorObj G ((Scheme.Modules.tensorPullback i).obj N))) ∧
      RingedSpace.IsCoherent X.toRingedSpace (Scheme.Modules.tensorObj F N) ∧
      {x : X | ¬ Subsingleton ((Scheme.Modules.tensorObj F N).presheaf.stalk x)} =
        {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
      (∀ q : ℕ, Nonempty ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F ≅
        (ModuleCat.restrictScalars i.appTop.hom).obj
          ((RingedSpace.moduleCohomology (Spec (CommRingCat.of A)).toRingedSpace q).obj G))) ∧
      (∀ q : ℕ, Nonempty
        ((RingedSpace.moduleCohomology X.toRingedSpace q).obj (Scheme.Modules.tensorObj F N) ≅
          (ModuleCat.restrictScalars i.appTop.hom).obj
            ((RingedSpace.moduleCohomology (Spec (CommRingCat.of A)).toRingedSpace q).obj
              (Scheme.Modules.tensorObj G ((Scheme.Modules.tensorPullback i).obj N))))) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  obtain ⟨hq, ht⟩ := (isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  let := hq
  let := ht
  obtain ⟨I, _, _, hIker, _, _, hrange, hkill, _⟩ := Scheme.schemeTheoreticSupport X F
  let j := I.subschemeι
  have hdim : topologicalKrullDim I.subscheme ≤ 0 := by
    rw [j.isClosedEmbedding.isEmbedding.topologicalKrullDim_eq_range]
    exact hrange ▸ hS
  obtain ⟨_, haff, hfd⟩ :=
    closed_subscheme_finite_of_topologicalKrullDim_le_zero (X ↘ Spec (.of k)) j hdim
  let := haff
  let A := Γ(I.subscheme, ⊤)
  let := (j ≫ (X ↘ Spec (.of k))).ΓAlgebra
  let : FiniteDimensional k A := hfd
  let i : Spec (.of A) ⟶ X := I.subscheme.isoSpec.inv ≫ j
  have : IsClosedImmersion i := inferInstance
  have hi_over : i ≫ (X ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    change I.subscheme.isoSpec.inv ≫ (j ≫ (X ↘ Spec (.of k))) = _
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have hi_range : Set.range i.base = {x : X | ¬ Subsingleton (F.presheaf.stalk x)} := by
    rw [← hrange]
    change Set.range (j.base ∘ I.subscheme.isoSpec.inv.base) = _
    rw [Set.range_comp]
    have hs : Function.Surjective I.subscheme.isoSpec.inv :=
      I.subscheme.isoSpec.inv.homeomorph.surjective
    rw [hs.range_eq, Set.image_univ]
  have hi_kill (V : X.Opens) (a : Γ(X, V)) (ha : a ∈ i.ker.idealOfOpens V)
      (s : Γ(F, V)) : a • s = 0 := by
    dsimp only [i] at ha
    rw [Scheme.Hom.ker_comp_of_isIso] at ha
    change a ∈ I.subschemeι.ker.idealOfOpens V at ha
    rw [hIker] at ha
    exact hkill V ⟨a, ha⟩ s
  obtain ⟨hqG, hunit, htG⟩ := (closedImmersion_pushforward_annihilated i).2 F hi_kill
  let G := (tensorPullback i).obj F
  have : IsLocallyNoetherian (Spec (.of A)) := LocallyOfFiniteType.isLocallyNoetherian i
  have hG : RingedSpace.IsCoherent (Spec (.of A)).toRingedSpace G :=
    (isCoherent_iff_isQuasicoherent_and_isFiniteType _ G).mpr ⟨hqG, htG ht⟩
  let adj := Classical.choose (exists_tensorPullbackAdjunction i)
  let := hunit
  let e : F ≅ (pushforward i).obj G := asIso (adj.unit.app F)
  refine ⟨A, inferInstance, inferInstance, inferInstance, i, inferInstance, G,
    hi_over, hi_range, hG, ⟨e⟩, ?_⟩
  let c : tensorPullback i ≅ Scheme.Modules.pullback i :=
    adj.leftAdjointUniq (pullbackPushforwardAdjunction i)
  let L := (tensorPullback i).obj N
  have : L.IsInvertible := IsInvertible.of_iso (c.app N).symm
  obtain ⟨p⟩ := nonempty_pushforward_tensorObj_pullback_iso i G N
  let t : F ⊗ₘ N ≅ (pushforward i).obj (G ⊗ₘ L) :=
    (e ⊗ᵢ Iso.refl N) ≪≫ p.symm ≪≫
      (pushforward i).mapIso (Iso.refl G ⊗ᵢ (c.app N).symm)
  let f := Spec.map (CommRingCat.ofHom (algebraMap k A))
  have : IsFinite f := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  obtain ⟨hfin, hdisc⟩ := finite_and_discreteTopology_of_isFinite f
  let := hfin
  let := hdisc
  obtain ⟨d⟩ := tensor_iso_of_discrete G L
  let et : F ⊗ₘ N ≅ F := t ≪≫ (pushforward i).mapIso d ≪≫ e.symm
  have hFt : RingedSpace.IsCoherent X.toRingedSpace (F ⊗ₘ N) := by
    apply (isCoherent_iff_isQuasicoherent_and_isFiniteType X _).mpr
    exact ⟨(SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso et.symm hq,
      by
        obtain ⟨g, hg⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
        refine { exists_localGeneratorsData := ⟨g.ofIso et.symm, ?_⟩ }
        constructor
        intro a
        have := hg.isFiniteType a
        exact inferInstanceAs ((g.generators a).ofEpi _).IsFiniteType⟩
  have hsupp : {x : X | ¬ Subsingleton ((F ⊗ₘ N).presheaf.stalk x)} =
      {x : X | ¬ Subsingleton (F.presheaf.stalk x)} := by
    ext x
    let a := (RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapIso et
    exact not_congr a.toLinearEquiv.toEquiv.subsingleton_congr
  refine ⟨⟨t⟩, hFt, hsupp, ?_, ?_⟩
  · let : (Spec (.of A)).Over (Spec (.of k)) := ⟨i ≫ (X ↘ Spec (.of k))⟩
    have : i.IsOver (Spec (.of k)) := ⟨rfl⟩
    let := hqG
    intro q
    obtain ⟨a⟩ := affine_support_cohomology (k := k) i G q
    exact ⟨(RingedSpace.moduleCohomology X.toRingedSpace q).mapIso e ≪≫ a⟩
  · let : (Spec (.of A)).Over (Spec (.of k)) := ⟨i ≫ (X ↘ Spec (.of k))⟩
    have : i.IsOver (Spec (.of k)) := ⟨rfl⟩
    have : (G ⊗ₘ L).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Spec (.of A)).ringCatSheaf).prop_of_iso d.symm hqG
    intro q
    obtain ⟨a⟩ := affine_support_cohomology (k := k) i (G ⊗ₘ L) q
    exact ⟨(RingedSpace.moduleCohomology X.toRingedSpace q).mapIso t ≪≫ a⟩

end AlgebraicGeometry

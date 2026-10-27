/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q139
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.FiniteTypeSheafFinitePresentationSupport
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback

/-!
# An affine supporting model preserving local fibre-support dimension

Source: Stacks Project, More on Flatness, Tag 057S, lemma-elementary-devissage,
affine reduction and general case using Tag 057Q, lemma-sheaf-lives-on-subscheme
(blueprint: lem-trf-affine-fibre-support-model).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

private theorem localDim_openEmbedding {A B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] {g : A → B}
    (hg : Topology.IsOpenEmbedding g) (a : A) :
    topologicalKrullDimAt a = topologicalKrullDimAt (g a) := by
  apply le_antisymm
  · refine le_iInf₂ fun U ha ↦ ?_
    let V : TopologicalSpace.Opens A := ⟨g ⁻¹' U, U.isOpen.preimage hg.continuous⟩
    refine (iInf₂_le V ha).trans ?_
    exact (hg.toIsInducing.restrictPreimage (U : Set B)).topologicalKrullDim_le
  · refine le_iInf₂ fun U ha ↦ ?_
    let V : TopologicalSpace.Opens B := ⟨g '' U, hg.isOpenMap _ U.isOpen⟩
    let k : U → B := fun p ↦ g p.1
    have hk : Topology.IsEmbedding k := hg.isEmbedding.comp Topology.IsEmbedding.subtypeVal
    have hr : Set.range k = (V : Set B) := by
      ext y
      simp [k, V, Set.mem_image]
    refine (iInf₂_le V ⟨a, ha, rfl⟩).trans_eq ?_
    rw [hk.topologicalKrullDim_eq_range, hr]
    rfl

private theorem support_embedding_dimension {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {i : A → B} {j : C → A} (hi : Topology.IsOpenEmbedding i)
    (hj : Topology.IsEmbedding j) (T : Set A) (S : Set B)
    (hjT : Set.range j = T) (hiT : i '' T = S ∩ Set.range i) (z : C) :
    ∃ hz : i (j z) ∈ S,
      topologicalKrullDimAt z = topologicalKrullDimAt (⟨i (j z), hz⟩ : S) := by
  have hS (w : C) : i (j w) ∈ S := by
    have : i (j w) ∈ i '' T := ⟨j w, hjT ▸ Set.mem_range_self w, rfl⟩
    rw [hiT] at this
    exact this.1
  let k : C → S := fun w ↦ ⟨i (j w), hS w⟩
  have hk : Topology.IsEmbedding k := (hi.isEmbedding.comp hj).codRestrict S hS
  have hr : Set.range k = Subtype.val ⁻¹' Set.range i := by
    ext b
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨j w, rfl⟩
    · intro hb
      have : (b : B) ∈ i '' T := hiT ▸ ⟨b.2, hb⟩
      obtain ⟨a, ha, hab⟩ := this
      obtain ⟨w, rfl⟩ := hjT.symm ▸ ha
      exact ⟨w, Subtype.ext hab⟩
  have hko : Topology.IsOpenEmbedding k :=
    ⟨hk, hr ▸ hi.isOpen_range.preimage continuous_subtype_val⟩
  exact ⟨hS z, localDim_openEmbedding hko z⟩

private theorem exists_open_fiber_map
    {U V X S : Scheme.{u}} (p : U ⟶ V) (f : X ⟶ S)
    (u : U ⟶ X) (v : V ⟶ S) [IsOpenImmersion u] [IsOpenImmersion v]
    (h : u ≫ f = p ≫ v) (sV : V) (s : S) (hv : v sV = s) :
    ∃ us : p.fiber sV ⟶ f.fiber s,
      us ≫ f.fiberι s = p.fiberι sV ≫ u ∧
      us ≫ f.fiberToSpecResidueField s = p.fiberToSpecResidueField sV ≫
        Spec.map ((S.residueFieldCongr hv).inv ≫ v.residueFieldMap sV) ∧
      IsOpenImmersion us := by
  let k := Spec.map ((S.residueFieldCongr hv).inv ≫ v.residueFieldMap sV)
  have hk : k ≫ S.fromSpecResidueField s = V.fromSpecResidueField sV ≫ v := by
    simp only [k, Spec.map_comp, Category.assoc]
    rw [Scheme.residueFieldCongr_inv, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  let us : p.fiber sV ⟶ f.fiber s :=
    Limits.pullback.map p (V.fromSpecResidueField sV) f (S.fromSpecResidueField s)
      u k v h.symm hk.symm
  have hfst : us ≫ f.fiberι s = p.fiberι sV ≫ u := by
    simp [us, Scheme.Hom.fiberι]
  have hsnd : us ≫ f.fiberToSpecResidueField s = p.fiberToSpecResidueField sV ≫ k := by
    simp [us, Scheme.Hom.fiberToSpecResidueField]
  have hb : IsPullback k (V.fromSpecResidueField sV) (S.fromSpecResidueField s) v :=
    IsPullback.of_horiz_isIso_mono ⟨hk⟩
  have hout := (IsPullback.of_hasPullback p (V.fromSpecResidueField sV)).flip.paste_horiz hb
  have htotal : IsPullback (p.fiberToSpecResidueField sV ≫ k)
      (p.fiberι sV) (S.fromSpecResidueField s) (u ≫ f) := by
    simpa only [Scheme.Hom.fiber, Scheme.Hom.fiberι,
      Scheme.Hom.fiberToSpecResidueField, h] using hout
  have hpb : IsPullback us (p.fiberι sV) (f.fiberι s) u := by
    apply IsPullback.of_right (h₁₂ := f.fiberToSpecResidueField s) ?_ hfst
      (IsPullback.of_hasPullback f (S.fromSpecResidueField s)).flip
    rw [hsnd]
    exact htotal
  exact ⟨us, hfst, hsnd, MorphismProperty.of_isPullback hpb.flip inferInstance⟩

/-- Affine open neighbourhoods admit a finitely presented closed supporting model
with exactly the original fibre support and its local dimension at the chosen point.
Here `sV` is the point of `V` corresponding to `f x`. The two projection equations
for each of `us` and `js` characterize the canonical fibre maps uniquely by the
pullback universal property. In particular these are the maps induced by `u` and `j`,
including the canonical residue-field identification along `v`. The closed immersion
`js`, together with its range equality, gives the homeomorphism onto the support.
The last support equality is written in `X_s` using the open embedding `us`.

Source: Stacks Project, More on Flatness, Tag 057S, lemma-elementary-devissage,
affine reduction and general case using Tag 057Q, lemma-sheaf-lives-on-subscheme
(blueprint: lem-trf-affine-fibre-support-model).

Proof:
1. Choose affine V about s and affine U about x inside its inverse image, using
   lem-weil-pbc-affine-opens-basis. The pointwise finite-type criterion
   lem-weil-pbc-lft-pointwise-criterion gives local finite type of p : U → V;
   lem-weil-pbc-morphism-affine-schemes-affine and affine-morphism permanence
   give quasi-compactness, hence finite type.
2. Pull back F to U and to the original fibre. Finite type and quasi-coherence
   follow from lem-weil-pbc-module-pullback-finite-type and
   lem-weil-pbc-module-pullback-quasi-coherent.
3. By lem-weil-pbc-residue-field-point-naturality the residue-field map of v
   is an isomorphism and its canonical point maps commute. The fibre-product
   universal property constructs us with the displayed projections. By
   lem-weil-pbc-open-immersion-base-change it is an open immersion. Pullback
   composition and equality of restriction stalks identify the local support
   with the intersection of the original support and its open image.
4. Apply lem-trf-finite-type-sheaf-fp-support to p and u*F. It gives j and H
   with the pushforward isomorphism and the required fibre-support image.
   The affine quotient description of def-weil-closed-immersion makes Z affine.
   Images of the finitely many algebra generators show j ≫ p is locally of
   finite type; the affine-morphism results from step 1 make it quasi-compact.
5. Construct js by the fibre-product universal property. It is a closed immersion
   by lem-weil-pbc-closed-immersion-base-change, hence a homeomorphism onto its
   range, the support from step 4. Choose z over x. The dimension equality follows
   from this homeomorphism and lem-weil-pbc-dimension-at-point-open-subspace
   applied to the open support intersection from step 3, using def-kun-dimension.
6. Finally lem-weil-pbc-open-immersion-etale makes u and v etale, and
   lem-weil-pbc-residue-field-point-naturality gives residue-field isomorphisms
   at every point of their sources. -/
theorem exists_affine_fibre_support_model
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (hF : F.IsQuasiCoherentFiniteType) (x : X)
    (hx : ¬ Subsingleton (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk
      (f.asFiber x))) :
    ∃ (U V : Scheme.{u}) (u : U ⟶ X) (v : V ⟶ S) (p : U ⟶ V),
      IsAffine U ∧ IsAffine V ∧ IsOpenImmersion u ∧ IsOpenImmersion v ∧
      LocallyOfFiniteType p ∧ QuasiCompact p ∧ u ≫ f = p ≫ v ∧
      ∃ (sV : V) (hv : v sV = f x) (Z : Scheme.{u}) (j : Z ⟶ U),
        IsAffine Z ∧ IsClosedImmersion j ∧ LocallyOfFinitePresentation j ∧
        QuasiCompact j ∧ QuasiSeparated j ∧
        LocallyOfFiniteType (j ≫ p) ∧ QuasiCompact (j ≫ p) ∧
        ∃ (H : Z.Modules) (z : (j ≫ p).fiber sV)
          (us : p.fiber sV ⟶ f.fiber (f x))
          (js : (j ≫ p).fiber sV ⟶ p.fiber sV),
          H.IsQuasiCoherentFiniteType ∧
          Nonempty ((pushforward j).obj H ≅ (tensorPullback u).obj F) ∧
          u (j ((j ≫ p).fiberι sV z)) = x ∧
          us ≫ f.fiberι (f x) = p.fiberι sV ≫ u ∧
          us ≫ f.fiberToSpecResidueField (f x) =
            p.fiberToSpecResidueField sV ≫
              Spec.map ((S.residueFieldCongr hv).inv ≫ v.residueFieldMap sV) ∧
          js ≫ p.fiberι sV = (j ≫ p).fiberι sV ≫ j ∧
          js ≫ p.fiberToSpecResidueField sV = (j ≫ p).fiberToSpecResidueField sV ∧
          IsOpenImmersion us ∧ IsClosedImmersion js ∧
          Set.range js.base =
            {y : p.fiber sV |
              ¬ Subsingleton
                (((tensorPullback (p.fiberι sV)).obj
                  ((tensorPullback u).obj F)).presheaf.stalk y)} ∧
          us.base '' {y : p.fiber sV |
              ¬ Subsingleton
                (((tensorPullback (p.fiberι sV)).obj
                  ((tensorPullback u).obj F)).presheaf.stalk y)} =
            {y : f.fiber (f x) |
              ¬ Subsingleton (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk y)} ∩
              Set.range us.base ∧
          topologicalKrullDimAt z =
            topologicalKrullDimAt
              (⟨f.asFiber x, hx⟩ :
                {y : f.fiber (f x) |
                  ¬ Subsingleton
                    (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk y)}) ∧
          Etale u ∧ Etale v ∧
          (∀ y : U, IsIso (u.residueFieldMap y)) ∧
          (∀ t : V, IsIso (v.residueFieldMap t)) := by
  classical
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV (f ⁻¹ᵁ V).isOpen
  let U : X.Opens := U
  let V : S.Opens := V
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let p := f.resLE V U hUV
  let a : U.toScheme := ⟨x, hxU⟩
  have hax : U.ι a = x := rfl
  let sV : V.toScheme := p a
  have hcomm : U.ι ≫ f = p ≫ V.ι := (Scheme.Hom.resLE_comp_ι ..).symm
  have hv : V.ι sV = f x := by
    exact congrArg (fun q : U.toScheme ⟶ S ↦ q a) hcomm.symm
  have : F.IsQuasicoherent := hF.1
  have : F.IsFiniteType := hF.2
  let FU := (tensorPullback U.ι).obj F
  have : FU.IsFiniteType := (tensorPullback_isFiniteType _ _ U.ι F).1
  have : FU.IsQuasicoherent := inferInstance
  obtain ⟨Z, j, hj, hjfp, hjqc, hjqs, H, hHft, hHqc, e, hrange⟩ :=
    exists_finitePresentation_closedImmersion_fiber_support p FU a
  have := hj
  have := hjfp
  have := hjqc
  have := hjqs
  have : IsAffine Z := isAffine_of_isAffineHom j
  let js : (j ≫ p).fiber sV ⟶ p.fiber sV :=
    Limits.pullback.map (j ≫ p) (V.toScheme.fromSpecResidueField sV)
      p (V.toScheme.fromSpecResidueField sV) j (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hjs : IsClosedImmersion js :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) hj inferInstance rfl (by simp)
  have hjsfst : js ≫ p.fiberι sV = (j ≫ p).fiberι sV ≫ j := by
    simp [js, Scheme.Hom.fiberι]
  have hjssnd : js ≫ p.fiberToSpecResidueField sV =
      (j ≫ p).fiberToSpecResidueField sV := by
    simp [js, Scheme.Hom.fiberToSpecResidueField]
  change Set.range js.base = {y : p.fiber sV |
    ¬ Subsingleton (((tensorPullback (p.fiberι sV)).obj FU).presheaf.stalk y)} at hrange
  obtain ⟨us, husfst, hussnd, hus⟩ :=
    exists_open_fiber_map p f U.ι V.ι hcomm sV (f x) hv
  have := hus
  have hsupU := (finiteType_module_support_pullback FU).2.2 _ (p.fiberι sV) |>.2
  have hsupUX := (finiteType_module_support_pullback F).2.2 _ U.ι |>.2
  have hsupX := (finiteType_module_support_pullback F).2.2 _ (f.fiberι (f x)) |>.2
  have hsupp : us.base '' {y : p.fiber sV |
        ¬ Subsingleton (((tensorPullback (p.fiberι sV)).obj FU).presheaf.stalk y)} =
      {y : f.fiber (f x) |
        ¬ Subsingleton (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk y)} ∩
        Set.range us.base := by
    rw [hsupU, hsupUX, hsupX]
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, Set.mem_range_self w⟩
      have hp := congrArg (fun q : p.fiber sV ⟶ X ↦ q w) husfst
      change ¬ Subsingleton (F.presheaf.stalk (U.ι (p.fiberι sV w))) at hw
      change ¬ Subsingleton (F.presheaf.stalk (f.fiberι (f x) (us w)))
      simp only [Scheme.Hom.comp_apply] at hp
      rw [hp]
      exact hw
    · rintro ⟨hy, w, rfl⟩
      refine ⟨w, ?_, rfl⟩
      have hp := congrArg (fun q : p.fiber sV ⟶ X ↦ q w) husfst
      change ¬ Subsingleton (F.presheaf.stalk (f.fiberι (f x) (us w))) at hy
      change ¬ Subsingleton (F.presheaf.stalk (U.ι (p.fiberι sV w)))
      simp only [Scheme.Hom.comp_apply] at hp
      rw [← hp]
      exact hy
  have ha : p.asFiber a ∈ Set.range js.base := by
    rw [hrange, hsupU, hsupUX]
    have hx' : ¬ Subsingleton (F.presheaf.stalk x) := by
      have hxmem : f.asFiber x ∈ {y : f.fiber (f x) |
          ¬ Subsingleton (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk y)} := hx
      rw [hsupX] at hxmem
      simpa using hxmem
    change ¬ Subsingleton (F.presheaf.stalk (U.ι (p.fiberι sV (p.asFiber a))))
    simpa only [sV, Scheme.Hom.fiberι_asFiber, hax] using hx'
  obtain ⟨z, hz⟩ := ha
  have hzx : U.ι (j ((j ≫ p).fiberι sV z)) = x := by
    have hp := congrArg (fun q : (j ≫ p).fiber sV ⟶ U.toScheme ↦ q z) hjsfst
    have : j ((j ≫ p).fiberι sV z) = a := by
      simpa only [Scheme.Hom.comp_apply, hz, sV, Scheme.Hom.fiberι_asFiber] using hp.symm
    exact congrArg U.ι this
  have huspoint : us (js z) = f.asFiber x := by
    apply (f.fiberι (f x)).isEmbedding.injective
    have hp := congrArg (fun q : p.fiber sV ⟶ X ↦ q (js z)) husfst
    simpa only [Scheme.Hom.comp_apply, hz, sV, Scheme.Hom.fiberι_asFiber, hax] using hp
  obtain ⟨hmem, hdim⟩ := support_embedding_dimension us.isOpenEmbedding
    (show Topology.IsEmbedding js.base from hjs.isClosedEmbedding.isEmbedding)
    _ _ hrange hsupp z
  have hdim' : topologicalKrullDimAt z = topologicalKrullDimAt
      (⟨f.asFiber x, hx⟩ : {y : f.fiber (f x) |
        ¬ Subsingleton (((tensorPullback (f.fiberι (f x))).obj F).presheaf.stalk y)}) := by
    simpa only [huspoint] using hdim
  exact ⟨U.toScheme, V.toScheme, U.ι, V.ι, p, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hcomm, sV, hv, Z, j,
    inferInstance, hj, hjfp, hjqc, hjqs, inferInstance, inferInstance,
    H, z, us, js, ⟨hHqc, hHft⟩, e, hzx, husfst, hussnd, hjsfst, hjssnd,
    hus, hjs, hrange, hsupp, hdim', inferInstance, inferInstance,
    fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

end AlgebraicGeometry.Scheme.Modules

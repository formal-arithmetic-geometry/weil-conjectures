/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import Sheaf.FieldTheory.FiniteFamilyCommonExtension
import Sheaf.AlgebraicGeometry.GeometricallyReducedDominantDescent
import WeilConjectures.FieldTheory.MakeSeparable
import WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra

/-!
# Geometric reducedness after a finite purely inseparable extension

Source: Stacks Project, Varieties, Tag 04KT, lemma-finite-extension-geometrically-reduced
(blueprint: lem-pur-finite-inseparable-geometric-reduction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open scoped TensorProduct
open TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
private theorem residueField_fg_of_locallyOfFiniteType
    (k : Type u) [Field k] (Z : Scheme.{u}) (f : Z ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : Z)
    [Algebra k (Z.residueField x)]
    (h : algebraMap k (Z.residueField x) =
      (StructureSheaf.toStalk k (f x) ≫ f.stalkMap x ≫ Z.residue x).hom) :
    (⊤ : IntermediateField k (Z.residueField x)).FG := by
  apply IntermediateField.fg_top_iff.mpr
  rw [← RingHom.essFiniteType_algebraMap, h]
  have h₁ : (StructureSheaf.toStalk k (f x)).hom.EssFiniteType := by
    let : Algebra k ((Spec (.of k)).presheaf.stalk (f x)) :=
      (StructureSheaf.toStalk k (f x)).hom.toAlgebra
    change (algebraMap k ((Spec (.of k)).presheaf.stalk (f x))).EssFiniteType
    rw [RingHom.essFiniteType_algebraMap]
    have : IsLocalization.AtPrime ((Spec (.of k)).presheaf.stalk (f x)) (f x).asIdeal :=
      StructureSheaf.IsLocalization.to_stalk k (f x)
    exact Algebra.EssFiniteType.of_isLocalization _ (f x).asIdeal.primeCompl
  exact h₁.comp ((LocallyOfFiniteType.stalkMap f x).comp
    (RingHom.FiniteType.of_surjective _ (Z.residue_surjective x)).essFiniteType)

private theorem fromSpecResidueField_comp_eq
    (k : Type u) [Field k] (Z : Scheme.{u}) (f : Z ⟶ Spec (.of k)) (x : Z)
    [Algebra k (Z.residueField x)]
    (h : algebraMap k (Z.residueField x) =
      (StructureSheaf.toStalk k (f x) ≫ f.stalkMap x ≫ Z.residue x).hom) :
    Z.fromSpecResidueField x ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k (Z.residueField x))) := by
  dsimp only [Scheme.fromSpecResidueField]
  rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
    Spec.fromSpecStalk_eq', ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext h.symm

private theorem geometricallyReduced_spec_of_separable_fg
    (k F : Type u) [Field k] [Field F] [Algebra k F]
    (hfg : (⊤ : IntermediateField k F).FG) (hsep : Algebra.IsSeparableExtension k F) :
    GeometricallyReduced (Spec.map (CommRingCat.ofHom (algebraMap k F))) := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro L _ _
  have : _root_.IsReduced ((⊤ : IntermediateField k F) ⊗[k] L) :=
    Algebra.isReduced_tensorProduct_of_isSeparablyGenerated k _ L (hsep ⊤ hfg)
  have : _root_.IsReduced (F ⊗[k] L) := by
    exact isReduced_of_injective
      (Algebra.TensorProduct.congr
        (IntermediateField.topEquiv.symm : F ≃ₐ[k] (⊤ : IntermediateField k F))
        (AlgEquiv.refl (R := k) (A₁ := L)))
      (AlgEquiv.injective _)
  exact isReduced_of_isOpenImmersion (pullbackSpecIso k F L).hom

private theorem geometricallyReduced_sigmaDesc
    (k : Type u) [Field k] (I : Type u) [Finite I]
    (X : I → Scheme.{u}) (p : ∀ i, X i ⟶ Spec (.of k))
    (hp : ∀ i, GeometricallyReduced (p i)) :
    GeometricallyReduced (Sigma.desc p) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro K _ y
  have H := IsUniversalColimit.isPullback_of_isColimit_left
    (X := X) (FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct _))
    p (Sigma.desc p) y _ _ (fun _ ↦ .of_hasPullback _ _) (coproductIsCoproduct _)
  have : IsReduced (pullback y (Sigma.desc p)) := by
    apply +allowSynthFailures @isReduced_of_isOpenImmersion (f := H.isoPullback.inv)
    apply +allowSynthFailures @IsReduced.of_openCover (𝒰 := sigmaOpenCover _)
    exact fun i ↦ (hp i).geometrically_isReduced _ _ _ (.flip (.of_hasPullback _ _))
  exact isReduced_of_isOpenImmersion (pullbackSymmetry _ _).hom

/-- A locally finite type scheme with finitely many irreducible components acquires a
geometrically reduced reduction after a finite purely inseparable extension of its base field.
Source: Stacks Project, Varieties, Tag 04KT, lemma-finite-extension-geometrically-reduced
(blueprint: lem-pur-finite-inseparable-geometric-reduction).

Proof:
1. Take the residue fields K_i at the finitely many generic points of Z. The stalk maps
   of a locally finite type morphism are essentially of finite type, as are localization
   and residue quotient maps, so each K_i is finitely generated over k.
2. Embed all K_i into one finitely generated extension E/k using
   lem-pur-finite-family-common-extension. Apply lem-weil-pbc-make-separable to E/k,
   obtaining a finite purely inseparable l/k and a finite extension F/E, with compatible
   embeddings into F and F/l separable. Then F/l is finitely generated. The tensor-reduced
   criterion lem-weil-pbc-separably-generated-tensor-reduced makes Spec F geometrically
   reduced over l.
3. Put Y = (Z_l)_red. The maps Spec F to Z through the generic residue fields lift to Z_l
   by the pullback property and factor through Y because Spec F is reduced. The projection
   Y to Z is a homeomorphism: reduction and purely inseparable base change both are.
4. Let W be the finite coproduct of these copies of Spec F. Its map g to Y has dense range,
   because its image contains the point over every generic point of Z. W has finitely many
   points, so g is quasi-compact. Since Y is reduced, g is schematically dominant.
5. W is geometrically reduced over l, as follows by base-changing its finite open coproduct
   cover. After any field extension of l, g remains schematically dominant by flat base
   change. Thus reducedness descends from the base change of W to that of Y, using injective
   maps on sections. This proves geometric reducedness of Y. The empty scheme is included:
   the generic-point family and the coproduct are empty, and the common field can be k. -/
theorem exists_finite_purelyInseparable_geometricallyReduced_reduction
    (k : Type u) [Field k] (Z : Scheme.{u}) (f : Z ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] [Finite (irreducibleComponents Z)] :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'),
      Module.Finite k k' ∧ IsPurelyInseparable k k' ∧
        GeometricallyReduced
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).nilradical.subschemeι ≫
            pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) := by
  classical
  let I := irreducibleComponents Z
  let : Fintype I := Fintype.ofFinite I
  let n := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let ξ (i : Fin n) : Z := (e.symm i).property.1.genericPoint
  let K (i : Fin n) : Type u := Z.residueField (ξ i)
  let aK : ∀ i, Algebra k (K i) := fun i ↦
    (StructureSheaf.toStalk k (f (ξ i)) ≫ f.stalkMap (ξ i) ≫ Z.residue (ξ i)).hom.toAlgebra
  let : ∀ i, Algebra k (K i) := aK
  have hK (i : Fin n) : (⊤ : IntermediateField k (K i)).FG :=
    residueField_fg_of_locallyOfFiniteType k Z f (ξ i) rfl
  obtain ⟨E, hE, aE, hfg, ⟨emb⟩⟩ := Algebra.exists_fg_common_field k n K hK
  let := hE
  let := aE
  obtain ⟨l, F, hl, hF, akl, akF, alF, aEF, htl, htE,
      hfin, hpure, hfinF, hpureF, hsep⟩ :=
    Algebra.exists_finite_purelyInseparable_separable_extension k E hfg
  let := hl
  let := hF
  let := akl
  let := akF
  let := alF
  let := aEF
  have := htl
  have := htE
  have : IsPurelyInseparable k l := hpure
  have : Module.Finite E F := hfinF
  have : Algebra.EssFiniteType k E := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType k F := Algebra.EssFiniteType.comp k E F
  have : Algebra.EssFiniteType l F := Algebra.EssFiniteType.of_comp k l F
  have hfgF : (⊤ : IntermediateField l F).FG :=
    IntermediateField.fg_top_iff.mpr inferInstance
  let b := Spec.map (CommRingCat.ofHom (algebraMap k l))
  let pF := Spec.map (CommRingCat.ofHom (algebraMap l F))
  let j (i : Fin n) : Spec (.of F) ⟶ Z :=
    Spec.map (CommRingCat.ofHom
      ((algebraMap E F).comp (emb i).toRingHom)) ≫ Z.fromSpecResidueField (ξ i)
  have hjpoint (i : Fin n) (x : Spec (.of F)) : j i x = ξ i := by
    exact Z.fromSpecResidueField_apply (ξ i)
      ((Spec.map (CommRingCat.ofHom ((algebraMap E F).comp (emb i).toRingHom))) x)
  have hjbase (i : Fin n) : j i ≫ f = pF ≫ b := by
    dsimp only [j, pF, b]
    rw [Category.assoc, fromSpecResidueField_comp_eq k Z f (ξ i) rfl,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    change algebraMap E F (emb i (algebraMap k (K i) x)) =
      algebraMap l F (algebraMap k l x)
    rw [(emb i).commutes, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  let P := pullback f b
  let Y := P.nilradical.subscheme
  let a : Y ⟶ P := P.nilradical.subschemeι
  let p : Y ⟶ Spec (.of l) := a ≫ pullback.snd f b
  let q : Y ⟶ Z := a ≫ pullback.fst f b
  let h (i : Fin n) : Spec (.of F) ⟶ P := pullback.lift (j i) pF (hjbase i)
  let gᵢ (i : Fin n) : Spec (.of F) ⟶ Y := (h i).liftNilradical
  have hgq (i : Fin n) : gᵢ i ≫ q = j i := by
    simp [gᵢ, q, a, h]
  have hgp (i : Fin n) : gᵢ i ≫ p = pF := by
    simp [gᵢ, p, a, h]
  have hY : IsReduced Y := inferInstance
  have ha : IsHomeomorph a := by
    have hs :=
      (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism P).2.2.1
    exact isHomeomorph_iff_isEmbedding_surjective.mpr ⟨a.isEmbedding, hs.surj⟩
  have hq : IsHomeomorph q := by
    exact (isHomeomorph_pullback_fst_of_isPurelyInseparable k l f).comp ha
  let W := ∐ fun _ : I ↦ Spec (.of F)
  let g : W ⟶ Y := Sigma.desc (fun i : I ↦ gᵢ (e i))
  have : Finite W :=
    (sigmaMk (fun _ : I ↦ Spec (.of F))).finite_iff.mp inferInstance
  have : QuasiCompact g := ⟨fun _ _ _ ↦ (Set.toFinite _).isCompact⟩
  have : IsDominant g := by
    rw [isDominant_iff, denseRange_iff_closure_range, Set.eq_univ_iff_forall]
    intro y
    let C : I := ⟨irreducibleComponent (q y), irreducibleComponent_mem_irreducibleComponents _⟩
    let i : Fin n := e C
    let z : W := Sigma.ι (fun _ : I ↦ Spec (.of F)) C (IsLocalRing.closedPoint F)
    have hξ : ξ i ⤳ q y := by
      simpa [ξ, i, C] using
        (IsIrreducible.isGenericPoint_genericPoint
          (isIrreducible_irreducibleComponent (x := q y))
          isClosed_irreducibleComponent).specializes mem_irreducibleComponent
    have hz : g z ⤳ y := by
      apply hq.isInducing.specializes_iff.mp
      have heq : q (g z) = ξ i := by
        change (Sigma.ι (fun _ : I ↦ Spec (.of F)) C ≫ g ≫ q)
          (IsLocalRing.closedPoint F) = ξ i
        rw [Sigma.ι_desc_assoc, hgq]
        exact hjpoint (e C) (IsLocalRing.closedPoint F)
      rw [heq]
      exact hξ
    exact hz.mem_closed isClosed_closure (subset_closure ⟨z, rfl⟩)
  have : IsSchemeTheoreticallyDominant g := .of_isDominant g
  refine ⟨l, hl, akl, hfin, hpure, ?_⟩
  change GeometricallyReduced p
  apply geometricallyReduced_of_schemeTheoreticallyDominant g p
  have heq : g ≫ p = Sigma.desc (fun _ : I ↦ pF) := by
    apply Sigma.hom_ext
    intro i
    simpa [g] using hgp (e i)
  rw [heq]
  exact geometricallyReduced_sigmaDesc l I (fun _ ↦ Spec (.of F))
    (fun _ ↦ pF) (fun _ ↦ geometricallyReduced_spec_of_separable_fg l F hfgF hsep)

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Topology.KrullDimension
import WeilConjectures.RingTheory.DimensionAtPointComponents

/-! # Affine fibre charts and dimension at their marked points

Source: Stacks Project, Schemes, Tags 01JQ, 01JR and 01J9; Algebra, Tags 05G3 and
00OT; Topology, Tag 0055 (blueprint: lem-trf-affine-fibre-point-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace AlgebraicGeometry

private theorem localDim_homeomorph_le {Y Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] (i : Y ≃ₜ Z) (y : Y) :
    topologicalKrullDimAt y ≤ topologicalKrullDimAt (i y) := by
  refine le_iInf₂ fun O hy ↦ ?_
  let V : TopologicalSpace.Opens Y := ⟨i ⁻¹' O, O.isOpen.preimage i.continuous⟩
  let iV : V ≃ₜ O := i.subtype (fun _ ↦ Iff.rfl)
  exact (iInf₂_le V hy).trans_eq
    (IsHomeomorph.topologicalKrullDim_eq iV iV.isHomeomorph)

private theorem localDim_openImmersion {Y Z : Scheme.{u}} (j : Y ⟶ Z)
    [IsOpenImmersion j] (y : Y) : topologicalKrullDimAt y = topologicalKrullDimAt (j y) := by
  let i := j.isOpenEmbedding.toHomeomorph
  have he : topologicalKrullDimAt y = topologicalKrullDimAt (i y) :=
    le_antisymm (localDim_homeomorph_le i y)
      (by simpa using localDim_homeomorph_le i.symm (i y))
  exact he.trans (j.isOpenEmbedding.isOpen_range.topologicalKrullDimAt_eq ⟨y, rfl⟩)

private theorem residue_chart (S : Scheme.{u}) (R : Type u) [CommRing R]
    (iV : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion iV]
    (s : S) (p : PrimeSpectrum R) (hs : iV p = s) :
    ∃ e : S.residueField s ≅ CommRingCat.of p.asIdeal.ResidueField,
      e.hom = (S.residueFieldCongr hs).inv ≫ iV.residueFieldMap p ≫
        (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).hom ∧
      Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField)) ≫ iV =
        Spec.map e.hom ≫ S.fromSpecResidueField s := by
  subst s
  let e := asIso (iV.residueFieldMap p) ≪≫ Scheme.Spec.residueFieldIso (.of R) p
  refine ⟨e, by simp [e], ?_⟩
  simp only [e, Iso.trans_hom, asIso_hom, Spec.map_comp, Category.assoc]
  rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
  simp only [Category.assoc, ← Spec.map_comp_assoc, Iso.inv_hom_id, Category.comp_id]

/-- An affine chart of a scheme fibre, its evaluation prime, and its point dimension.
The open immersions `iW` and `iV` specify the affine neighbourhoods, and `hφ` specifies
that their coordinate ring map is the given algebra map. The two projection identities
characterize the canonical chart morphism `j`; the pure-tensor formula characterizes
its evaluation map `ψ`. The final clause spells out the induced quotient presentation,
including the images of the variables.

Source: Stacks Project, Schemes, 01JQ, 01JR, 01J9 and 01K1; Algebra, 05G3 and 00OT;
Topology, 0055 (blueprint: lem-trf-affine-fibre-point-dimension).

Proof:
1. By lem-weil-pbc-spec-residue-field-identification and
   lem-weil-pbc-residue-field-point-naturality, identify the affine residue field
   with that of the marked base point, compatibly with the canonical point maps.
   This yields `e`; the induced prime residue-field map is an `R`-algebra map.
2. Apply lem-weil-pbc-open-fibre-product to the two affine neighbourhoods and the
   residue-field spectrum. By lem-weil-pbc-fibre-product-affine-spectra the source is
   the spectrum of the tensor algebra, with the residue field already first.
   Pullback symmetry puts the scheme factors in the order defining the fibre.
   The projections are the spectra of the two tensor inclusions, giving `j` and its range.
3. The same tensor universal property constructs evaluation `ψ` with the stated formula.
   Its kernel is prime because the target is a field, and its contraction is `q`, since
   evaluation on `1 ⊗ a` is the canonical map to the residue field of `q`.
4. The contraction calculation and the first projection identity show that `j Q`
   lies above `x`. The fibre homeomorphism in def-pc-scheme-fibre makes the fibre
   projection injective, giving `j Q = f.asFiber x`.
5. Apply lem-weil-pbc-presentation-base-change to any finite presentation. Its
   quotient isomorphism, transported along the relation-kernel equality, has the
   displayed variable images. Finite type is preserved by this tensor base change.
6. The open immersion is a homeomorphism onto its range. By
   lem-weil-pbc-homeomorphism-krull-dimension and the neighbourhood definition
   def-kun-topological-dimension-at-point it preserves point dimension. Apply
   lem-weil-pbc-dimension-at-point-open-subspace to compare with the entire fibre.
7. Finally lem-weil-pbc-dimension-at-point-components applied to this finite type
   algebra over a field gives a finite nonnegative integer dimension. The marked
   prime ensures the chart and all relevant neighbourhoods are nonempty. -/
theorem affine_fibre_point_dimension
    (X S : Scheme.{u}) (f : X ⟶ S) (x : X)
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A]
    (iW : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion iW]
    (iV : Spec (CommRingCat.of R) ⟶ S) [IsOpenImmersion iV]
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ iV = iW ≫ f)
    (q : PrimeSpectrum A) (p : PrimeSpectrum R)
    (hx : iW q = x) (hs : iV p = f x)
    (hp : p.asIdeal = q.asIdeal.comap (algebraMap R A)) :
    ∃ (e : S.residueField (f x) ≅ CommRingCat.of p.asIdeal.ResidueField)
      (ψ : p.asIdeal.Fiber A →+* q.asIdeal.ResidueField)
      (Q : PrimeSpectrum (p.asIdeal.Fiber A))
      (j : Spec (CommRingCat.of (p.asIdeal.Fiber A)) ⟶ f.fiber (f x)),
      e.hom = (S.residueFieldCongr hs).inv ≫ iV.residueFieldMap p ≫
        (Scheme.Spec.residueFieldIso (CommRingCat.of R) p).hom ∧
      (∀ (l : p.asIdeal.ResidueField) (a : A),
        ψ (l ⊗ₜ[R] a) =
          Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R A) hp l *
            algebraMap A q.asIdeal.ResidueField a) ∧
      Q.asIdeal = RingHom.ker ψ ∧
      Q.asIdeal.comap
        (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.Fiber A).toRingHom =
          q.asIdeal ∧
      IsOpenImmersion j ∧
      j ≫ f.fiberι (f x) =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.Fiber A).toRingHom) ≫
            iW ∧
      j ≫ f.fiberToSpecResidueField (f x) =
        Spec.map (e.hom ≫ CommRingCat.ofHom
          (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber A))) ∧
      Set.range j = (f.fiberι (f x)) ⁻¹' Set.range iW ∧
      j Q = f.asFiber x ∧
      RingHom.FiniteType (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber A)) ∧
      topologicalKrullDimAt Q = topologicalKrullDimAt (f.asFiber x) ∧
      (∃ d : ℕ, topologicalKrullDimAt Q = (d : WithBot ℕ∞)) ∧
      (∀ (n m : ℕ) (P : Algebra.Presentation R A (Fin n) (Fin m)),
        ∃ E : (MvPolynomial (Fin n) p.asIdeal.ResidueField ⧸
            Ideal.span (Set.range (fun b : Fin m =>
              MvPolynomial.map (algebraMap R p.asIdeal.ResidueField) (P.relation b))))
            ≃ₐ[p.asIdeal.ResidueField] p.asIdeal.Fiber A,
          ∀ a : Fin n, E (Ideal.Quotient.mk _ (MvPolynomial.X a)) =
            1 ⊗ₜ[R] P.val a) := by
  classical
  obtain ⟨e, he, hbase⟩ := residue_chart S R iV (f x) p hs
  let u : p.asIdeal.ResidueField →ₐ[R] q.asIdeal.ResidueField :=
    { __ := Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R A) hp
      commutes' r :=
        (Ideal.ResidueField.map_algebraMap p.asIdeal q.asIdeal (algebraMap R A) hp r).trans
          (IsScalarTower.algebraMap_apply R A q.asIdeal.ResidueField r).symm }
  let v : A →ₐ[R] q.asIdeal.ResidueField := IsScalarTower.toAlgHom R A _
  let ψ := (Algebra.TensorProduct.productMap u v).toRingHom
  have hψ (l : p.asIdeal.ResidueField) (a : A) :
      ψ (l ⊗ₜ[R] a) =
        Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap R A) hp l *
          algebraMap A q.asIdeal.ResidueField a := rfl
  let Q : PrimeSpectrum (p.asIdeal.Fiber A) := ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩
  have : Q.asIdeal.IsPrime := Q.isPrime
  have hQ : Q.asIdeal.comap
      (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.Fiber A).toRingHom =
        q.asIdeal := by
    ext a
    change ψ (1 ⊗ₜ[R] a) = 0 ↔ a ∈ q.asIdeal
    rw [hψ, map_one, one_mul, Ideal.algebraMap_residueField_eq_zero]
  let a := Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))
  let b := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let g := S.fromSpecResidueField (f x)
  let c := Spec.map e.hom
  let t := pullback.map a b g f c iW iV hbase hφ
  let j : Spec (CommRingCat.of (p.asIdeal.Fiber A)) ⟶ f.fiber (f x) :=
    (pullbackSpecIso R p.asIdeal.ResidueField A).inv ≫ t ≫
      (pullbackSymmetry g f).hom
  have hj : IsOpenImmersion j := by dsimp [j, t, c]; infer_instance
  have hjX : j ≫ f.fiberι (f x) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.Fiber A).toRingHom) ≫
          iW := by
    simp [j, t, a, b, g, Scheme.Hom.fiberι]
  have hjk : j ≫ f.fiberToSpecResidueField (f x) =
      Spec.map (e.hom ≫ CommRingCat.ofHom
        (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber A))) := by
    simp [j, t, a, b, g, Scheme.Hom.fiberToSpecResidueField, Spec.map_comp, c,
      Algebra.TensorProduct.algebraMap_def]
  have hjrange : Set.range j = (f.fiberι (f x)) ⁻¹' Set.range iW := by
    have ht : Set.range t = pullback.snd g f ⁻¹' Set.range iW := by
      rw [show Set.range t = pullback.fst g f ⁻¹' Set.range c ∩
        pullback.snd g f ⁻¹' Set.range iW from
          Scheme.Pullback.range_map a b g f c iW iV hbase hφ]
      rw [c.surjective.range_eq, Set.preimage_univ, Set.univ_inter]
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      change f.fiberι (f x) (j w) ∈ Set.range iW
      rw [← Scheme.Hom.comp_apply, hjX, Scheme.Hom.comp_apply]
      exact Set.mem_range_self _
    · intro hz
      have hz' : (pullbackSymmetry g f).inv z ∈ Set.range t := by
        rw [ht]
        change pullback.snd g f ((pullbackSymmetry g f).inv z) ∈ Set.range iW
        rw [← Scheme.Hom.comp_apply, pullbackSymmetry_inv_comp_snd]
        exact hz
      obtain ⟨w, hw⟩ := hz'
      refine ⟨(pullbackSpecIso R p.asIdeal.ResidueField A).hom w, ?_⟩
      change (pullbackSymmetry g f).hom
        (t ((pullbackSpecIso R p.asIdeal.ResidueField A).inv
          ((pullbackSpecIso R p.asIdeal.ResidueField A).hom w))) = z
      have hi : (pullbackSpecIso R p.asIdeal.ResidueField A).inv
          ((pullbackSpecIso R p.asIdeal.ResidueField A).hom w) = w := by
        simp only [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
        rfl
      simp only [hi, hw, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
  have hjQ : j Q = f.asFiber x := by
    apply (f.fiberι (f x)).isEmbedding.injective
    rw [Scheme.Hom.fiberι_asFiber, ← Scheme.Hom.comp_apply, hjX,
      Scheme.Hom.comp_apply]
    have hpoint : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] p.asIdeal.Fiber A).toRingHom) Q =
        q := PrimeSpectrum.ext hQ
    rw [hpoint, hx]
  have hft : Algebra.FiniteType p.asIdeal.ResidueField (p.asIdeal.Fiber A) := inferInstance
  obtain ⟨qs, hqs, hne, d, hd, hrest⟩ :=
    dimension_at_point_components (k := p.asIdeal.ResidueField) Q.asIdeal
  refine ⟨e, ψ, Q, j, he, hψ, rfl, hQ, hj, hjX, hjk, hjrange, hjQ,
    RingHom.finiteType_algebraMap.mpr hft, ?_, ⟨d, hd⟩, ?_⟩
  · exact (localDim_openImmersion j Q).trans (congrArg topologicalKrullDimAt hjQ)
  · intro n m P
    let P' := P.baseChange p.asIdeal.ResidueField
    have hker : Ideal.span (Set.range (fun b : Fin m ↦
        MvPolynomial.map (algebraMap R p.asIdeal.ResidueField) (P.relation b))) =
        P'.ker := P'.span_range_relation_eq_ker
    refine ⟨(Ideal.quotientEquivAlgOfEq _ hker).trans
      (P'.quotientEquiv.restrictScalars p.asIdeal.ResidueField), ?_⟩
    intro a
    simp [P', Algebra.Presentation.quotientEquiv_mk,
      Algebra.Generators.algebraMap_apply]
    rfl

end AlgebraicGeometry

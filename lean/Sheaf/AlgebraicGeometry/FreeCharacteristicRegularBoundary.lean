/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.NormalCrossingsDivisor
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.AlgebraicGeometry.LogRegularSharpLocalAlgebra
import Sheaf.AlgebraicGeometry.FreeCharacteristicBoundaryChart
import Sheaf.RingTheory.MonoidalLocalRegularityCriterion
import WeilConjectures.RingTheory.StrictHenselizationRegular
import Sheaf.AlgebraicGeometry.EtaleReducedCartierDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Free characteristic monoids and the regular normal crossings boundary

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose VI, 1.4 and 1.7,
printed pp. 69--70; Expose VIII, 3.4.4 and 4.1.1, printed pp. 110 and 117
(blueprint: lem-trf-free-characteristic-regular-boundary).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.FineSaturatedLogScheme

private theorem regular_iff_free_at
    (X : FineSaturatedLogScheme.{u}) (hlog : X.IsLogRegular)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme) :
    IsRegularLocalRing
        (X.scheme.presheaf.stalk (Scheme.SpecToEquivOfField Ω X.scheme t).1) ↔
      ∃ r : ℕ, Nonempty
        (X.logStructure.characteristic t ≃* Multiplicative (Fin r → ℕ)) := by
  classical
  let R := X.scheme.presheaf.stalk (Scheme.SpecToEquivOfField Ω X.scheme t).1
  let A := Scheme.strictHenselizationRing t
  let P := Additive (X.logStructure.characteristic t)
  have : IsLocallyNoetherian X.scheme := X.locallyNoetherian
  obtain ⟨hfs, hsharp, K, hK, hres, hsep, hRK, htower, hRA, hlocal, hnoeth,
    hstrict, a, I, r, ha, hcontract, hI, hr, hrank, hquot, hdim⟩ :=
    logRegular_sharp_local_algebra X hlog t
  have h := RingTheory.monoidal_local_regularity_criterion A P hfs hsharp a ha
    hcontract I hI r hr hdim
  let S := {p : P | AddIrreducible p}
  let : Fintype S := h.1.fintype
  let n := Fintype.card S
  let e : Fin n ≃ S := (Fintype.equivFin S).symm
  let p : Fin n → P := fun i ↦ (e i).val
  have hp : Function.Injective p := Subtype.val_injective.comp e.injective
  have hprange : Set.range p = {q : P | AddIrreducible q} := by
    ext q
    constructor
    · rintro ⟨i, rfl⟩
      exact (e i).property
    · intro hq
      obtain ⟨i, hi⟩ := e.surjective ⟨q, hq⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hc := h.2.2.2.1 n p hp hprange
  have hcrit : IsRegularLocalRing A ↔ Nonempty (P ≃+ (Fin r → ℕ)) :=
    hc.2.1.trans hc.2.2
  have hreg := Algebra.isRegularLocalRing_iff_strictHenselization R K A hstrict
  constructor
  · intro hR
    obtain ⟨E⟩ := hcrit.mp (hreg.mp hR)
    exact ⟨r, ⟨E.toMultiplicativeRight⟩⟩
  · rintro ⟨s, ⟨E⟩⟩
    apply hreg.mpr
    apply hcrit.mpr
    rw [hrank s ⟨E.toAdditiveLeft⟩]
    exact ⟨E.toAdditiveLeft⟩

private theorem reduced_ideal_comap
    (X : Scheme.{u}) [IsLocallyNoetherian X] (Z : TopologicalSpace.Closeds X)
    (W : Scheme.{u}) (v : W ⟶ X) [Etale v] :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap v =
      Scheme.IdealSheafData.vanishingIdeal (Z.preimage v.continuous) := by
  obtain ⟨e, he⟩ := (etale_reduced_cartier_descent.{u, u} X Z).1 W v
  change (CategoryTheory.Limits.pullback.fst v
    (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι).ker = _
  rw [← he, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/-- For a locally Noetherian log regular fs log scheme, regularity of an ordinary local
ring is equivalent to freeness of the characteristic at any geometric point above it.
If this holds everywhere, the scheme is regular and the reduced complement of its open
 dense triviality locus is an effective Cartier normal crossings divisor.
Source: ILO VI 1.4, 1.7; VIII 3.4.4, 4.1.1
(blueprint: lem-trf-free-characteristic-regular-boundary).

Proof:
1. At a geometric point put A equal to the strict local ring and P equal to its sharp
   characteristic. The sharp-chart lemma (lem-trf-log-regular-sharp-chart) identifies the
   nonunit ideal I with the chart images of P minus zero. A is Noetherian by
   lem-sc-strict-henselization-noetherian. Log regularity says A/I is regular and
   dim A = dim(A/I) + rank(P.gp).
2. A deletion-minimal finite generating set of P consists exactly of its indecomposable
   nonzero elements. Cancellation and sharpness prove this; saturation and sharpness show
   that P.gp is torsion free.
3. Monoidal ideal contraction (lem-trf-log-regular-monoidal-ideal-contraction) makes the
   chart images of these generators irredundant. Nakayama
   (lem-weil-pbc-nakayama-local-generators) then makes their classes a residue-field basis
   of I/mI.
4. If A is regular, the regular quotient kernel is generated by an initial parameter
   segment (lem-weil-pbc-regular-local-quotient-kernel-parameters). The quotient dimension
   formula (lem-weil-pbc-regular-local-generators-regular-sequence) and the log dimension
   formula show that this segment and the minimal monoid generating set have size rank P.
   The resulting surjection Z^r to P.gp has zero kernel after rationalization and hence
   zero kernel integrally. Thus P is N^r, also when r = 0.
5. Conversely, a free sharp chart gives r generators of I. Lift parameters of A/I; together
   they generate m_A with length dim A. The dimension bound
   (lem-weil-pbc-noetherian-local-dimension-le-generators) proves regularity and makes this
   list a regular system of parameters (def-weil-pbc-regular-system-of-parameters).
6. Strict-henselization invariance (lem-sc-strict-henselization-regular) gives the claimed
   equivalence for ordinary local rings. Everywhere regular local rings and local
   Noetherianity give IsRegularScheme (def-weil-regular-scheme).
7. Under everywhere freeness choose sharp N^r charts. Their triviality loci are the basic
   opens of the products of the chart coordinates. At any point the nonunit coordinates
   are precisely the remaining free generators. Strict local comparison
   (lem-sc-strict-henselization-comparison) transfers log regularity to the etale charts.
8. Cotangent base change (lem-sc-strict-henselization-cotangent-dimension) descends the
   independence of the nonunit chart coordinates to the ordinary local ring. Extend their
   classes to a cotangent basis and use Nakayama and the dimension bound to obtain an
   ordinary regular system of parameters containing them.
9. Each such parameter is prime because its quotient is regular local, hence a domain
   (lem-weil-pbc-regular-local-generators-regular-sequence and lem-sc-regular-local-domain).
   Distinct parameters do not divide one another. Their product generates the intersection
   of their prime ideals, which is radical, and is a non-zero-divisor. Unit chart factors
   do not alter the ideal. The empty product is 1.
10. The reduced chart divisors have support the complement of the triviality locus. Etale
    maps are open (lem-weil-pbc-flat-lfp-open), so this locus is open. Reduced-Cartier
    descent (lem-trf-etale-reduced-cartier-descent) and uniqueness of the reduced induced
    structure (lem-weil-pbc-reduced-induced-closed-subscheme) identify the descended ideal
    with the vanishing ideal of the complement. The parameter equations give precisely
    def-trf-normal-crossings-divisor, without a global labelling of branches.
11. If a nonempty open were contained in the boundary, shrink to a nonempty affine with
    Cartier equation g. In a regular local domain g remains nonzero. Contracting the zero
    prime produces an affine point outside V(g), a contradiction. Thus the triviality
    locus is dense. The empty scheme and empty boundary require no exception. -/
theorem free_characteristic_regular_boundary
    (X : FineSaturatedLogScheme.{u}) (hlog : X.IsLogRegular) :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme),
      IsRegularLocalRing
          (X.scheme.presheaf.stalk (Scheme.SpecToEquivOfField Ω X.scheme t).1) ↔
        ∃ r : ℕ, Nonempty
          (X.logStructure.characteristic t ≃* Multiplicative (Fin r → ℕ))) ∧
    ((∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ X.scheme),
      ∃ r : ℕ, Nonempty
        (X.logStructure.characteristic t ≃* Multiplicative (Fin r → ℕ))) →
      IsRegularScheme X.scheme ∧
        ∃ U : X.scheme.Opens,
          (U : Set X.scheme) = X.logStructure.trivialityLocus ∧
          Dense (U : Set X.scheme) ∧
          (Scheme.IdealSheafData.vanishingIdeal
            ⟨(U : Set X.scheme)ᶜ, U.isOpen.isClosed_compl⟩).IsNormalCrossingsDivisor) := by
  classical
  have : IsLocallyNoetherian X.scheme := X.locallyNoetherian
  refine ⟨fun Ω _ _ t ↦ regular_iff_free_at X hlog t, ?_⟩
  intro hfree
  have hpoint (x : X.scheme) :
      ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
        (t : Spec (.of Ω) ⟶ X.scheme),
        (Scheme.SpecToEquivOfField Ω X.scheme t).1 = x := by
    let Ω := AlgebraicClosure (X.scheme.residueField x)
    let t := (Scheme.SpecToEquivOfField Ω X.scheme).symm
      ⟨x, CommRingCat.ofHom (algebraMap (X.scheme.residueField x) Ω)⟩
    exact ⟨Ω, inferInstance, inferInstance, t,
      congrArg Sigma.fst ((Scheme.SpecToEquivOfField Ω X.scheme).apply_symm_apply _)⟩
  have hregular : IsRegularScheme X.scheme := by
    refine ⟨X.locallyNoetherian, ⟨fun x ↦ ?_⟩⟩
    obtain ⟨Ω, hΩ, hclosed, t, ht⟩ := hpoint x
    rw [← ht]
    exact (regular_iff_free_at X hlog t).mpr (hfree Ω t)
  have hchart (x : X.scheme) :
      ∃ (W : X.scheme.Etale) (w : W.left), W.hom w = x ∧
        ∃ V : W.left.Opens,
          (V : Set W.left) = W.hom ⁻¹' X.logStructure.trivialityLocus ∧
          Dense (V : Set W.left) ∧
          (Scheme.IdealSheafData.vanishingIdeal
            ⟨(V : Set W.left)ᶜ, V.isOpen.isClosed_compl⟩).IsNormalCrossingsDivisor := by
    obtain ⟨Ω, hΩ, hclosed, t, ht⟩ := hpoint x
    simpa only [ht] using exists_free_characteristic_boundary_chart X hlog t (hfree Ω t)
  choose W w hw V hV hdense hnc using hchart
  have hopen : IsOpen X.logStructure.trivialityLocus := by
    have heq : X.logStructure.trivialityLocus =
        ⋃ x : X.scheme, (W x).hom '' (V x : Set (W x).left) := by
      ext y
      constructor
      · intro hy
        apply Set.mem_iUnion.mpr
        refine ⟨y, w y, ?_, hw y⟩
        rw [hV y]
        change (W y).hom (w y) ∈ X.logStructure.trivialityLocus
        rwa [hw y]
      · intro hy
        obtain ⟨x, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
        rw [hV x] at hz
        exact hz
    rw [heq]
    exact isOpen_iUnion fun x ↦ (W x).hom.isOpenMap _ (V x).isOpen
  let U : X.scheme.Opens := ⟨X.logStructure.trivialityLocus, hopen⟩
  have hUdense : Dense (U : Set X.scheme) := by
    apply dense_iff_inter_open.mpr
    intro O hO hne
    obtain ⟨x, hx⟩ := hne
    have hpre : IsOpen ((W x).hom ⁻¹' O) := (W x).hom.continuous.isOpen_preimage O hO
    have hwO : w x ∈ (W x).hom ⁻¹' O := by
      change (W x).hom (w x) ∈ O
      rwa [hw x]
    obtain ⟨z, hzO, hzV⟩ :=
      (hdense x).inter_open_nonempty _ hpre ⟨w x, hwO⟩
    refine ⟨(W x).hom z, hzO, ?_⟩
    rw [hV x] at hzV
    exact hzV
  let Z : TopologicalSpace.Closeds X.scheme :=
    ⟨(U : Set X.scheme)ᶜ, U.isOpen.isClosed_compl⟩
  have hZ (x : X.scheme) :
      Z.preimage (W x).hom.continuous =
        ⟨(V x : Set (W x).left)ᶜ, (V x).isOpen.isClosed_compl⟩ := by
    apply TopologicalSpace.Closeds.ext
    change (W x).hom ⁻¹' X.logStructure.trivialityLocusᶜ =
      (V x : Set (W x).left)ᶜ
    rw [Set.preimage_compl, ← hV x]
  have hcover : (⋃ x : X.scheme,
      Set.range (fun z : (W x).left ↦ (W x).hom z)) = (Set.univ : Set X.scheme) := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, w x, hw x⟩
  have hinvert : (Scheme.IdealSheafData.vanishingIdeal Z).IsInvertible := by
    apply ((etale_reduced_cartier_descent X.scheme Z).2
      (fun x ↦ (W x).left) (fun x ↦ (W x).hom) hcover).mpr
    intro x
    rw [hZ x]
    exact (hnc x).1
  refine ⟨hregular, U, rfl, hUdense, hinvert, ?_⟩
  intro x
  have hlocal : ((Scheme.IdealSheafData.vanishingIdeal Z).comap
      (W x).hom).IsNormalCrossingsDivisor := by
    rw [reduced_ideal_comap X.scheme Z (W x).left (W x).hom, hZ x]
    exact hnc x
  obtain ⟨T, e, he, z, hz, B, hzB, hR, t, s, ht, hs, hideal⟩ := hlocal.2 (w x)
  have : Etale e := he
  refine ⟨T, e ≫ (W x).hom, inferInstance, z, ?_, B, hzB, hR, t, s, ht, hs, ?_⟩
  · change (W x).hom (e z) = x
    rw [hz, hw x]
  · simpa only [Scheme.IdealSheafData.comap_comp] using hideal

end AlgebraicGeometry.FineSaturatedLogScheme

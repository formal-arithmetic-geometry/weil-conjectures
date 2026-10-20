/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.AlgebraicGeometry.BertiniUniversalFamily
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.Topology.KrullDimension
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Sheaf.FieldTheory.BertiniFieldExtension
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.AlgebraicGeometry.BertiniIndependentFunctions
import Sheaf.AlgebraicGeometry.BertiniIncidenceAdaptedChart
import Sheaf.AlgebraicGeometry.BertiniPolynomialResidueArrow

/-!
# Affine presentation of the universal Bertini incidence family

Source: Stacks Project, More on Morphisms, Tag 0G4F, middle and final proof paragraphs.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry


private theorem dominant_bertiniEliminatedProjection
    (k : Type u) [Field k] (A : CommRingCat.{u})
    [Algebra k A] [Algebra.FiniteType k A] [IsDomain A]
    (n : ℕ) (hn : 2 ≤ n) (g : Fin n → A)
    (hdim : ∃ W : Set (PrimeSpectrum.zeroLocus
        ({g ⟨0, Nat.zero_lt_of_lt hn⟩, g ⟨1, hn⟩} : Set A)),
      W ∈ irreducibleComponents (PrimeSpectrum.zeroLocus
        ({g ⟨0, Nat.zero_lt_of_lt hn⟩, g ⟨1, hn⟩} : Set A)) ∧
      topologicalKrullDim W + 2 = ringKrullDim A) :
    IsDominant (bertiniEliminatedProjection k A n g) := by
  classical
  obtain ⟨c, hc⟩ := Algebra.bertini_independent_functions k A n hn g hdim
  let P := MvPolynomial (Fin n) (FractionRing A)
  let Ω := FractionRing P
  let f : Fin n ⊕ Fin 2 → Ω := fun j ↦
    algebraMap P Ω (match j with
      | Sum.inl i => MvPolynomial.X i
      | Sum.inr i => Fin.cases
          (∑ i : Fin n, MvPolynomial.C (algebraMap A (FractionRing A) (g i)) *
            MvPolynomial.X i)
          (fun _ ↦ MvPolynomial.C (∑ i : Fin n,
            algebraMap k (FractionRing A) (c i) * algebraMap A (FractionRing A) (g i))) i)
  have hf : AlgebraicIndependent k f := hc
  let τ : MvPolynomial (Fin (n + 1)) k →ₐ[k] MvPolynomial (Fin n ⊕ Fin 2) k :=
    MvPolynomial.aeval (Fin.cases (motive := fun _ ↦ MvPolynomial (Fin n ⊕ Fin 2) k)
      (-MvPolynomial.X (Sum.inr (0 : Fin 2))) (fun i ↦ MvPolynomial.X (Sum.inl i)))
  let σ : MvPolynomial (Fin n ⊕ Fin 2) k →ₐ[k] MvPolynomial (Fin (n + 1)) k :=
    MvPolynomial.aeval (Sum.elim (fun i ↦ MvPolynomial.X i.succ)
      (Fin.cases (-MvPolynomial.X (0 : Fin (n + 1))) (fun _ ↦ 0)))
  have hστ : σ.comp τ = AlgHom.id k (MvPolynomial (Fin (n + 1)) k) := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [σ, τ]
  have hτ : Function.Injective τ := by
    intro p q hpq
    have h := congrArg σ hpq
    simpa only [← AlgHom.comp_apply, hστ, AlgHom.id_apply] using h
  let φ : MvPolynomial (Fin (n + 1)) k →+* MvPolynomial (Fin n) A :=
    MvPolynomial.eval₂Hom
      ((MvPolynomial.C : A →+* MvPolynomial (Fin n) A).comp (algebraMap k A))
      (Fin.cases (motive := fun _ ↦ MvPolynomial (Fin n) A)
        (-∑ i : Fin n, MvPolynomial.C (g i) * MvPolynomial.X i) MvPolynomial.X)
  let ι : MvPolynomial (Fin n) A →+* Ω :=
    (algebraMap P Ω).comp (MvPolynomial.map (algebraMap A (FractionRing A)))
  have hmap : ι.comp φ = (MvPolynomial.aeval f).toRingHom.comp τ.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      suffices h : algebraMap P Ω
          (MvPolynomial.C (algebraMap A (FractionRing A) (algebraMap k A a))) =
          algebraMap k Ω a by
        simpa [ι, φ, τ, P, Ω] using h
      change algebraMap P Ω (algebraMap (FractionRing A) P
        (algebraMap A (FractionRing A) (algebraMap k A a))) = algebraMap k Ω a
      simp only [← IsScalarTower.algebraMap_apply]
    · intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [ι, φ, τ, f, P, Ω]
      · simp [ι, φ, τ, f, P, Ω]
  have hφ : Function.Injective φ := by
    intro p q hpq
    apply hτ
    apply hf
    change ((MvPolynomial.aeval f).toRingHom.comp τ.toRingHom) p =
      ((MvPolynomial.aeval f).toRingHom.comp τ.toRingHom) q
    rw [← hmap]
    exact congrArg ι hpq
  refine ⟨?_⟩
  change DenseRange (PrimeSpectrum.comap φ)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical φ).mpr
  rw [(RingHom.injective_iff_ker_eq_bot φ).mp hφ]
  exact bot_le

private theorem residueFieldMap_bijective_of_surjectiveOnStalks
    {X Z : Scheme.{u}} (j : X ⟶ Z) [SurjectiveOnStalks j] (x : X) :
    Function.Bijective (j.residueFieldMap x) := by
  refine ⟨(j.residueFieldMap x).hom.injective, ?_⟩
  intro b
  obtain ⟨a, rfl⟩ := X.residue_surjective x b
  obtain ⟨c, rfl⟩ := j.stalkMap_surjective x a
  exact ⟨Z.residue (j x) c, rfl⟩

private theorem residueArrow_open_iso
    {X H S T : Scheme.{u}} (j : X ⟶ H) [SurjectiveOnStalks j]
    (q : H ⟶ S) (c : S ≅ T) (x : X) :
    Nonempty (Arrow.mk (Spec.map (q.residueFieldMap (j x))) ≅
      Arrow.mk (Spec.map ((j ≫ q ≫ c.hom).residueFieldMap x))) := by
  have : IsIso (j.residueFieldMap x) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (residueFieldMap_bijective_of_surjectiveOnStalks j x)
  have : IsIso (c.hom.residueFieldMap (q (j x))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (residueFieldMap_bijective_of_surjectiveOnStalks c.hom (q (j x)))
  refine ⟨Arrow.isoMk (asIso (Spec.map (j.residueFieldMap x))).symm
    (asIso (Spec.map (c.hom.residueFieldMap (q (j x))))) ?_⟩
  simp

/-- Affine function-field presentation of the universal Bertini incidence scheme.
This supplies the local codimension-two intersection and the arrow isomorphism obtained
by eliminating the first incidence variable. It makes no geometric-irreducibility claim
about the incidence function field.

Source: Stacks Project, More on Morphisms, Tag 0G4F, the reduction, incidence-irreducibility,
and function-field identification in its proof. (blueprint: lem-zl-bertini-generic-fibre-chart).

Proof: Reduce Y; its nilradical is nilpotent by Noetherianity, and reduction after any field
base change leaves section zero-scheme supports and residue fields unchanged.
The three supplied vectors are independent by evaluation at the generic point of W and
the principal ideal height bound.
Extend them to a basis. On each nonempty trivializing affine Spec B the first section is
nonzero and the base-locus condition gives height at least two for the coefficient ideal.
Use exists_bertiniAffineIncidenceChart to identify the incidence chart and its parameter
map with the polynomial quotient. Apply irreducibleSpace_bertiniAffineIncidence using the
coefficient height bound. The zero-parameter section supplies a point over every point of
the base. Thus the
incidence charts over intersecting base opens intersect, and their union is irreducible.
Choose an affine Spec A in the complement of the first zero locus meeting W. Trivialize by
the first section and let g be the other section ratios. Its first two functions vanish on a
component of dimension
dim A minus two by the finite-type domain chain-length formula. The generic-residue-field
criterion applied to Y gives geometric irreducibility of Frac A over k. The independent
functions lemma implies independence of the variables and sum g_i x_i, hence dominance of
the incidence projection. The proved incidence elimination theorem solves for the first
variable, identifying the generic residue field of H with Frac(Frac(A)[x_2,...,x_r]).
The parameter residue field maps isomorphically onto
k(x_2,...,x_r,sum g_i x_i); the minus sign is absorbed by a coordinate automorphism.
These identifications yield the asserted arrow isomorphism. The original basis is related
to the adapted basis by an invertible linear coordinate change, and the ULift indexing by
a variable-renaming isomorphism; transport the presentation through both. -/
theorem exists_bertiniIncidenceChart
    (k : Type u) [Field k] (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [GeometricallyIrreducible (Y ↘ Spec (.of k))]
    (L : Y.Modules) [L.IsInvertible]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    letI : Module k Γ(L, ⊤) :=
      Module.compHom Γ(L, ⊤) (Scheme.globalSectionsRingHom k (X := Y))
    ∀ ψ : V →ₗ[k] Γ(L, ⊤),
      (∃ (v₁ v₂ v₃ : V) (W : TopologicalSpace.IrreducibleCloseds Y),
        Maximal (fun Z : TopologicalSpace.IrreducibleCloseds Y ↦
          (Z : Set Y) ⊆ (Scheme.Modules.homOfGlobalSection L (ψ v₂)).zeroLocus.support ∩
            (Scheme.Modules.homOfGlobalSection L (ψ v₃)).zeroLocus.support) W ∧
        ¬ (W : Set Y) ⊆ (Scheme.Modules.homOfGlobalSection L (ψ v₁)).zeroLocus.support ∧
        Order.coheight W = 2) →
      (∀ B : TopologicalSpace.IrreducibleCloseds Y,
        Maximal (fun Z : TopologicalSpace.IrreducibleCloseds Y ↦
          (Z : Set Y) ⊆ ⋂ w : V,
            ((Scheme.Modules.homOfGlobalSection L (ψ w)).zeroLocus.support : Set Y)) B →
        2 ≤ Order.coheight B) →
      ∀ (r : ℕ) (b : Module.Basis (Fin r) k V),
        let H := (bertiniUniversalIdeal (Y ↘ Spec (.of k)) L
          (fun i : ULift.{u} (Fin r) ↦ ψ (b i.down))).subscheme
        let q := bertiniUniversalProjection (Y ↘ Spec (.of k)) L
          (fun i : ULift.{u} (Fin r) ↦ ψ (b i.down))
        ∃ (A : CommRingCat.{u}) (a : Algebra k A),
          letI := a
          ∃ (hft : Algebra.FiniteType k A) (hdom : IsDomain A),
            letI := hft
            letI := hdom
            ∃ (n : ℕ) (hn : 2 ≤ n) (g : Fin n → A),
              (∃ W : Set (PrimeSpectrum.zeroLocus
                  ({g ⟨0, Nat.zero_lt_of_lt hn⟩, g ⟨1, hn⟩} : Set A)),
                W ∈ irreducibleComponents (PrimeSpectrum.zeroLocus
                  ({g ⟨0, Nat.zero_lt_of_lt hn⟩, g ⟨1, hn⟩} : Set A)) ∧
                topologicalKrullDim W + 2 = ringKrullDim A) ∧
              GeometricallyIrreducible
                (Spec.map (CommRingCat.ofHom (algebraMap k (FractionRing A)))) ∧
              ∃ hI : IrreducibleSpace H,
                letI := hI
                IsDominant q ∧ Nonempty (Arrow.mk
                  (Spec.map (q.residueFieldMap (genericPoint H))) ≅
                  Arrow.mk (Spec.map (CommRingCat.ofHom
                    (algebraMap
                      (FieldTheory.bertiniBaseField k (FractionRing A) n
                        (fun i ↦ algebraMap A (FractionRing A) (g i)))
                      (FieldTheory.bertiniOmega (FractionRing A) n))))) := by
  classical
  intro ψ hcomp hbase r b
  obtain ⟨A, a, hft, hdom, n, hn, g, hdim, hgeom, j, c, hjD, hjS, hj⟩ :=
    exists_bertiniIncidenceAdaptedChart k Y L V ψ hcomp hbase r b
  let := a
  let := hft
  let := hdom
  let := hjD
  let := hjS
  let H := (bertiniUniversalIdeal (Y ↘ Spec (.of k)) L
    (fun i : ULift.{u} (Fin r) ↦ ψ (b i.down))).subscheme
  let q := bertiniUniversalProjection (Y ↘ Spec (.of k)) L
    (fun i : ULift.{u} (Fin r) ↦ ψ (b i.down))
  have hI : IrreducibleSpace H := by
    apply (irreducibleSpace_def H).mpr
    change IsIrreducible (Set.univ : Set H)
    have hi := (IrreducibleSpace.isIrreducible_univ
      (Spec (.of (MvPolynomial (Fin n) A)))).image j j.continuous.continuousOn
    have hc := hi.closure
    simpa only [Set.image_univ, j.denseRange.closure_range] using hc
  let := hI
  have hpD := dominant_bertiniEliminatedProjection k A n hn g hdim
  obtain ⟨e⟩ := bertiniPolynomialResidueArrow k A n g hpD
  have hD : IsDominant (j ≫ q ≫ c.hom) := hj.symm ▸ hpD
  let := hD
  have hDq : IsDominant q := by
    have : IsDominant (q ≫ c.hom) := IsDominant.of_comp j (q ≫ c.hom)
    have : IsDominant ((q ≫ c.hom) ≫ c.inv) := inferInstance
    simpa using this
  let x := genericPoint (Spec (.of (MvPolynomial (Fin n) A)))
  have hx : j x = genericPoint H := by
    apply IsGenericPoint.eq _ (genericPoint_spec H)
    have hd : closure (j '' (Set.univ : Set (Spec (.of (MvPolynomial (Fin n) A))))) =
        Set.univ := by
      rw [Set.image_univ]
      exact j.denseRange.closure_range
    exact hd ▸ (genericPoint_spec _).image j.continuous
  obtain ⟨e₀⟩ := residueArrow_open_iso j q c x
  rw [hx] at e₀
  have he : Nonempty (Arrow.mk (Spec.map (q.residueFieldMap (genericPoint H))) ≅
      Arrow.mk (Spec.map (CommRingCat.ofHom (algebraMap
        (FieldTheory.bertiniBaseField k (FractionRing A) n
          (fun i ↦ algebraMap A (FractionRing A) (g i)))
        (FieldTheory.bertiniOmega (FractionRing A) n))))) := by
    rw [hj] at e₀
    exact ⟨e₀ ≪≫ e⟩
  exact ⟨A, a, hft, hdom, n, hn, g, hdim, hgeom, hI, hDq, he⟩

end AlgebraicGeometry

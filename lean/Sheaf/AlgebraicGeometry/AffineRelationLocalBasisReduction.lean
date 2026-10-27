/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.AlgebraicGeometry.GroupoidScheme
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.LinearAlgebra.FreeModule.Basic
import WeilConjectures.RingTheory.FlatLocalExtensionGivenResidueField
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Basic
import Sheaf.AlgebraicGeometry.AffineGroupoidIntegralInvariants
import Sheaf.AlgebraicGeometry.AffineGroupoidOrbitFibres
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Sheaf.AlgebraicGeometry.AffineGroupoidInvariantRankStrata
import WeilConjectures.AlgebraicGeometry.Modules.FinitePushforward
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Sheaf.RingTheory.SemilocalSubmoduleBasis
import Sheaf.AlgebraicGeometry.AffineGroupoidBasisDescent

/-! # Local basis reduction for an affine finite locally free groupoid

Source: Stacks Project, Groupoids, Tag 03BM, fourth and final proof paragraphs;
Tags 03BI, 03BK and 03C8; Algebra, Tags 03C1 and 03C3
(blueprint: lem-a1-affine-relation-local-basis-reduction).

## Main definitions

- `affineGroupoidInvariantTensorComparison`: the canonical invariant tensor comparison.
- `IsAffineGroupoidLocalBasisData`: the explicit clauses of the local conclusion.

## Main statements

- `affineGroupoid_local_basis_reduction`: existence of local extensions and the
  conclusions for every such extension.

All tensor products and invariant rings are Mathlib's.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The canonical comparison from the tensor square over the invariant subring.
Its value on a pure tensor is `s♯(a) * t♯(b)`.
Source: Stacks Project, Tag 03BM, first proof paragraph
(blueprint: lem-a1-affine-relation-local-basis-reduction). -/
noncomputable def affineGroupoidInvariantTensorComparison {A B : CommRingCat.{u}}
    (s t : Spec B ⟶ Spec A) :
    (A ⊗[(Spec.preimage s).hom.eqLocus (Spec.preimage t).hom] A) →+* B :=
  let C := (Spec.preimage s).hom.eqLocus (Spec.preimage t).hom
  letI : Algebra C B := ((Spec.preimage s).hom.comp C.subtype).toAlgebra
  let σ : A →ₐ[C] B :=
    { (Spec.preimage s).hom with commutes' := fun _ ↦ rfl }
  let τ : A →ₐ[C] B :=
    { (Spec.preimage t).hom with commutes' := fun a ↦ a.property.symm }
  (Algebra.TensorProduct.productMap σ τ).toRingHom

/-- The full local conclusion, using `E = A ⊗[C] D` and `F = B ⊗[C] D`.
The algebra structures are the canonical ones, with `D` acting on the right factors.
The pure-tensor identities uniquely specify both induced coordinate maps. The final
comparison isomorphism makes the arrow scheme the kernel pair, so its groupoid
operations are uniquely determined and hence are the induced operations.
The unique-expansion clause is precisely the `E`-basis of `F` via the source map.
Source: Stacks Project, Tags 03BM (final paragraph), 03BI, 03BK and 03C8
(blueprint: lem-a1-affine-relation-local-basis-reduction). -/
noncomputable def IsAffineGroupoidLocalBasisData {A B : CommRingCat.{u}}
    (s t : Spec B ⟶ Spec A)
    (p : PrimeSpectrum ((Spec.preimage s).hom.eqLocus (Spec.preimage t).hom))
    (D : Type v) [CommRing D] [IsLocalRing D]
    (f : Localization.AtPrime p.asIdeal →+* D) : Prop :=
  let C := (Spec.preimage s).hom.eqLocus (Spec.preimage t).hom
  letI : Algebra C B := ((Spec.preimage s).hom.comp C.subtype).toAlgebra
  letI : Algebra C D := (f.comp (algebraMap C (Localization.AtPrime p.asIdeal))).toAlgebra
  let E := A ⊗[C] D
  let F := B ⊗[C] D
  letI : Algebra D E := Algebra.TensorProduct.rightAlgebra
  letI : Algebra D F := Algebra.TensorProduct.rightAlgebra
  ∃ σD τD : E →ₐ[D] F,
    (∀ (a : A) (d : D), σD (a ⊗ₜ d) = (Spec.preimage s).hom a ⊗ₜ d) ∧
    (∀ (a : A) (d : D), τD (a ⊗ₜ d) = (Spec.preimage t).hom a ⊗ₜ d) ∧
    Function.Injective (algebraMap D E) ∧
    (∀ x : E, σD x = τD x ↔ ∃ d : D, algebraMap D E d = x) ∧
    Finite (MaximalSpectrum E) ∧
    Ideal.map (algebraMap D E) (IsLocalRing.maximalIdeal D) ≤ Ideal.jacobson (⊥ : Ideal E) ∧
    (∀ x y : MaximalSpectrum E, ∃ z : PrimeSpectrum F,
      PrimeSpectrum.comap σD.toRingHom z = x.toPrimeSpectrum ∧
      PrimeSpectrum.comap τD.toRingHom z = y.toPrimeSpectrum) ∧
    ∃ (eD : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of F))
      (iD : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of F))
      (cD : pullback (Spec.map (CommRingCat.ofHom σD.toRingHom))
        (Spec.map (CommRingCat.ofHom τD.toRingHom)) ⟶ Spec (CommRingCat.of F)),
      IsGroupoidScheme (Spec.map (CommRingCat.ofHom σD.toRingHom))
        (Spec.map (CommRingCat.ofHom τD.toRingHom)) eD iD cD ∧
      (Spec.map (CommRingCat.ofHom σD.toRingHom)).IsFiniteLocallyFree ∧
      (Spec.map (CommRingCat.ofHom τD.toRingHom)).IsFiniteLocallyFree ∧
      ∃ (r : ℕ) (x : Fin r → E), 1 ≤ r ∧
        (Spec.map (CommRingCat.ofHom σD.toRingHom)).IsFiniteLocallyFreeOfDegree r ∧
        (∀ b : F, ∃! a : Fin r → E, b = ∑ j : Fin r, σD (a j) * τD (x j)) ∧
        (∃ b : Module.Basis (Fin r) D E, ∀ j : Fin r, b j = x j) ∧
        Module.Finite D E ∧ Module.Free D E ∧
        ∃ φD : (E ⊗[D] E) ≃+* F,
          ∀ a b : E, φD (a ⊗ₜ b) = σD a * τD b

/-- Flat local extensions with infinite residue field exist at every prime of the
invariant ring. Every such extension is faithfully flat and satisfies the full local
semilocality, orbit, constant-degree, basis and comparison-isomorphism conclusions.
Source: Stacks Project, Tag 03BM, fourth and final proof paragraphs; Tags 03BI,
03BK and 03C8; Algebra, Tags 03C1 and 03C3
(blueprint: lem-a1-affine-relation-local-basis-reduction).

Proof (the eight steps of the DAG node):
1. For each p apply lem-weil-pbc-flat-local-extension-given-residue-field to C_p
   and the infinite extension κ(p)(T). Every flat local choice is faithfully flat by
   lem-weil-pbc-flat-local-hom-faithfully-flat.
2. Use lem-weil-pbc-flat-over-localization and lem-weil-pbc-flat-tensor-exact on
   0 → C → A → B, whose last arrow is σ - τ. Tensoring identifies D injectively
   with the equalizer of the induced maps, so E is nonzero.
3. The node lem-a1-affine-groupoid-basechange-polynomial-norm gives the induced
   groupoid and finite locally free projections. Apply
   lem-a1-affine-groupoid-integral-invariants and lem-a1-affine-groupoid-orbit-fibres
   to get integrality over D, surjectivity on spectra and single-orbit fibres.
4. By lem-weil-pbc-integral-maximal-contracts-maximal and
   lem-weil-pbc-integral-prime-over-maximal-maximal, the maximal ideals of E lie
   exactly above m_D and contain m_D E. Fix one maximal point. All other maximal
   points are targets of its finite source fibre, by
   lem-weil-pbc-finite-closed-map-finite-fibres. Thus E is semilocal.
5. Apply lem-a1-affine-groupoid-invariant-rank-strata. The single orbit of maximal
   points lies in one positive rank stratum r. Every prime lies in a maximal ideal;
   the clopen stratum contains its generalizations. Thus the degree is r everywhere.
6. Apply lem-pc-finite-flat-pushforward-locally-free and
   lem-pc-finite-flat-affine-sections-projective to the source projection and its
   structure sheaf. Then lem-weil-pbc-finite-projective-standard-free-cover gives
   a finite principal free cover, with rank r by the fibre-dimension calculation.
7. By lem-weil-pbc-tensor-right-exact the comparison remains surjective over D.
   Reassociate (A ⊗[C] A) ⊗[C] D with E ⊗[D] E by
   (a ⊗ b) ⊗ d ↦ (a ⊗ d) ⊗ (b ⊗ 1), with inverse multiplying the two D factors.
   Hence τD(E), a D-submodule, generates F over E via σD.
8. Apply lem-a1-semilocal-submodule-basis using the infinite residue field, the
   Jacobson containment, constant positive rank and generation. Lift its basis
   through τD to x_j. The node lem-a1-affine-groupoid-basis-descent proves that
   these x_j form a D-basis of E and that the canonical comparison is an isomorphism. -/
theorem affineGroupoid_local_basis_reduction (A B : CommRingCat.{u}) [Nontrivial A]
    (s t : Spec B ⟶ Spec A) (e : Spec A ⟶ Spec B) (i : Spec B ⟶ Spec B)
    (c : pullback s t ⟶ Spec B) (_hG : IsGroupoidScheme s t e i c)
    [s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree]
    (_hφ : Function.Surjective (affineGroupoidInvariantTensorComparison s t)) :
    ∀ p : PrimeSpectrum ((Spec.preimage s).hom.eqLocus (Spec.preimage t).hom),
      (∃ (D : Type u) (_ : CommRing D) (_ : IsLocalRing D)
        (f : Localization.AtPrime p.asIdeal →+* D),
        IsLocalHom f ∧ f.Flat ∧ Infinite (IsLocalRing.ResidueField D)) ∧
      (∀ (D : Type v) [CommRing D] [IsLocalRing D]
        (f : Localization.AtPrime p.asIdeal →+* D),
        IsLocalHom f → f.Flat → Infinite (IsLocalRing.ResidueField D) →
          f.FaithfullyFlat ∧ IsAffineGroupoidLocalBasisData s t p D f) := by
  sorry

end AlgebraicGeometry

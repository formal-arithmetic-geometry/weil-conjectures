/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Topology.ExtremallyDisconnected
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Finite algebras over extremally disconnected affine schemes -/

@[expose] public section

universe u

open scoped TensorProduct
open CategoryTheory Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme.Pullback

/-- The residue-field calculation used in the pointwise pullback step below. An algebraic
extension of a separably closed field is purely inseparable; its tensor-product spectrum
is therefore homeomorphic to the spectrum of the other field. -/
private theorem subsingleton_primeSpectrum_tensor_of_isSepClosed
    (k K L : Type u) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [IsSepClosed k] [Algebra.IsAlgebraic k K] :
    Subsingleton (PrimeSpectrum (K ⊗[k] L)) := by
  have : IsPurelyInseparable k K := inferInstance
  have h := PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
    (K := k) (R := k) (S := L) K
  let e := Algebra.TensorProduct.lid k L
  have he := PrimeSpectrum.isHomeomorph_comap_of_bijective e.toRingEquiv.bijective
  have : Subsingleton (PrimeSpectrum (k ⊗[k] L)) :=
    he.bijective.surjective.subsingleton
  exact h.bijective.injective.subsingleton

/-- A compatible pair of scheme points has at most one lift when the indicated residue
extension is integral over a separably closed field. -/
private theorem tripletTensor_subsingleton {X Y Z : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    (t : Scheme.Pullback.Triplet f g)
    (hsep : IsSepClosed (Z.residueField t.s))
    (halg : ((Z.residueFieldCongr t.hx).inv ≫ f.residueFieldMap t.x).hom.IsIntegral) :
    Subsingleton (Spec t.tensor) := by
  let A := Z.residueField t.s
  let B := X.residueField t.x
  let C := Y.residueField t.y
  let φ := (Z.residueFieldCongr t.hx).inv ≫ f.residueFieldMap t.x
  let ψ := (Z.residueFieldCongr t.hy).inv ≫ g.residueFieldMap t.y
  let : Algebra A B := φ.hom.toAlgebra
  let : Algebra A C := ψ.hom.toAlgebra
  have : IsSepClosed A := hsep
  have : Algebra.IsIntegral A B := algebraMap_isIntegral_iff.mp halg
  have : Algebra.IsAlgebraic A B := Algebra.isAlgebraic_iff_isIntegral.mpr inferInstance
  let e : t.tensor ≅ CommRingCat.of (B ⊗[A] C) :=
    IsColimit.coconePointUniqueUpToIso (IsPushout.of_hasPushout φ ψ).isColimit
      (CommRingCat.pushoutCoconeIsColimit A B C)
  have : Subsingleton (PrimeSpectrum (B ⊗[A] C)) :=
    subsingleton_primeSpectrum_tensor_of_isSepClosed A B C
  have he := PrimeSpectrum.isHomeomorph_comap_of_bijective
    e.commRingCatIsoToRingEquiv.bijective
  exact he.bijective.surjective.subsingleton

private theorem pullbackPoint_ext {X Y Z : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    (hsep : ∀ z : Z, IsSepClosed (Z.residueField z))
    (halg : ∀ t : Triplet f g,
      ((Z.residueFieldCongr t.hx).inv ≫ f.residueFieldMap t.x).hom.IsIntegral)
    (a b : ↑(Limits.pullback f g)) (ha : pullback.fst f g a = pullback.fst f g b)
    (hb : pullback.snd f g a = pullback.snd f g b) : a = b := by
  apply carrierEquiv.injective
  apply carrierEquiv_eq_iff.mpr
  have heq : (carrierEquiv a).1 = (carrierEquiv b).1 := Triplet.ext ha hb
  refine ⟨heq, ?_⟩
  have : Subsingleton (Spec (carrierEquiv b).1.tensor) :=
    tripletTensor_subsingleton _ (hsep _) (halg _)
  exact Subsingleton.elim _ _

/-- A finite finitely presented algebra over a ring with Hausdorff extremally disconnected
spectrum and separably closed residue fields has extremally disconnected spectrum.
Source: Stacks Project, Lemma 61.11.5 (Tag 0985), finite case
(blueprint: lem-ce-finite-algebra-extremally-disconnected).

Proof: Put X = Spec R and Y = Spec S. Apply the finite affine section-cover construction
of Tag 03HW. It gives a surjective finite locally free X' → X and a closed embedding
j : Y' → W, where Y' = Y ×_X X', W → X' is finite locally free, and W is covered by
finitely many closed sections. Since X is Hausdorff its primes are all maximal. Every
prime of X' or W is also maximal by integrality. These affine spaces, and Y', are therefore
compact Hausdorff and zero-dimensional.
The embedding j is finitely presented: its composite to X is finitely presented and W
is of finite type over X. Chevalley makes its image constructible, hence clopen in W.
The incidence locus of a section with Y' is therefore clopen in X'. Equalizer loci of two
sections are also clopen: they are base changes of the finitely presented closed diagonal
of W → X', and their images are constructible by Chevalley. Partition X' into the finitely
many Boolean atoms of the incidence and equality loci. On each atom retain one
representative of each section class lying in Y'. They are disjoint and cover Y' there.
Projectivity of the compact Hausdorff extremally disconnected X gives a continuous section
σ of X' → X. Pull the finite clopen partition back along σ. Each resulting piece C of X
is extremally disconnected. If x' = σ(x) and y lies above x, the points of Y' above
(y,x') are the primes of κ(y) ⊗[κ(x)] κ(x'). Both residue extensions are finite and the
base field κ(x) is separably closed. Hence κ(y)/κ(x) is purely inseparable. The private
lemma `subsingleton_primeSpectrum_tensor_of_isSepClosed` proves that this tensor spectrum
has at most one point, by Mathlib
`PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable`; nontriviality
gives a point, so it has exactly one point. The private helpers `tripletTensor_subsingleton`
and `pullbackPoint_ext` implement this uniqueness for actual scheme pullback points using
`Scheme.Pullback.carrierEquiv`. The chosen sections restricted along σ define a continuous
bijection from finitely many copies of C onto the inverse image of C in Y. Compactness and
Hausdorffness make it a homeomorphism. Finally Y is a finite disjoint union of these spaces,
so is extremally disconnected. Empty spectra and empty atoms require no chosen points.
Non-flatness and nilpotents cause no exception: finite presentation, not reducedness, is
what makes the incidence and equality loci clopen. -/
theorem extremallyDisconnected_spectrum_of_finite_finitePresentation
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Algebra.FinitePresentation R S]
    [T2Space (PrimeSpectrum R)] [ExtremallyDisconnected (PrimeSpectrum R)]
    (hsep : ∀ p : PrimeSpectrum R, IsSepClosed p.asIdeal.ResidueField) :
    ExtremallyDisconnected (PrimeSpectrum S) := by sorry

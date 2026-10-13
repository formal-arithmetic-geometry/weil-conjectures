/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.PseudoCoherentComplex
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Semicontinuity.Basic
import Sheaf.AlgebraicGeometry.FiniteFreeComplexHomologyUpperSemicontinuous
import Sheaf.AlgebraicGeometry.PseudoCoherentFiberFiniteFreeModel
import Sheaf.AlgebraicGeometry.DerivedFiberCohomologyBaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Jump loci of pseudo-coherent complexes

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.31.1, Tag 0BDI
(blueprint: lem-sc-perfect-jump-loci).
-/

@[expose] public section

universe uX wX

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Fibre cohomology dimensions of a pseudo-coherent complex commute with arbitrary
base change, are upper semicontinuous, and have locally constructible level sets.
Source: Stacks Project, Tag 0BDI (blueprint: lem-sc-perfect-jump-loci).

Proof:
1. Locally on an affine neighbourhood represent `E` by a bounded-above finite-free
   complex using def-pur-pseudo-coherent-complex. Its stupid truncation in degrees
   at least `i-1` is bounded finite free and preserves degree-`i` fibre cohomology.
   Termwise tensor computes the derived fibres by lem-pc-flat-complex-derived-pullback.
2. Apply lem-sc-finite-free-complex-homology-upper-semicontinuous on each neighbourhood;
   upper semicontinuity is local and hence holds on `X`.
3. Pull the same model back along `g`. At `y`, it is the scalar extension from
   `κ(g y)` to `κ(y)` of the original fibre. Field extensions are flat and preserve
   cohomology dimensions, giving the base-change formula. On each affine neighbourhood
   the strict sublevel sets are quasi-compact opens by the finite-free homology lemma.
   Such opens are retrocompact (Tag 054D), and each level set is the difference of
   two such opens, hence constructible (Tag 005G). This proves local constructibility.
-/
theorem pseudoCoherent_jump_loci (X : Scheme.{uX})
    [HasDerivedCategory.{wX} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{wX} (SheafOfModules.{uX} ((moduleRings X.toRingedSpace).over U))]
    [∀ x : X, HasDerivedCategory.{wX} (SheafOfModules.{uX}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : IsPseudoCoherent X E) (i : ℤ) :
    (∀ (Y : Scheme.{uX})
      [HasDerivedCategory.{wX} (SheafOfModules.{uX} (moduleRings Y.toRingedSpace))]
      [∀ y : Y, HasDerivedCategory.{wX} (SheafOfModules.{uX}
        (moduleRings (Spec (Y.residueField y)).toRingedSpace))]
      (g : Y ⟶ X) (y : Y),
        derivedFiberBetti Y ((derivedPullback g).obj E) i y = derivedFiberBetti X E i (g y)) ∧
      UpperSemicontinuous (derivedFiberBetti X E i) ∧
      ∀ r : ℕ, Topology.IsLocallyConstructible {x : X | derivedFiberBetti X E i x = r} := by
  have hlocal (x : X) : ∃ U : X.Opens, x ∈ U ∧
      (∀ r : ℕ, IsOpen {z : U | derivedFiberBetti X E i z < r}) ∧
      ∀ r : ℕ, Topology.IsConstructible {z : U | derivedFiberBetti X E i z = r} := by
    obtain ⟨U, hx, A, hA, e, K, hbounded, hfree, hmodel⟩ :=
      exists_pseudoCoherent_fiber_finiteFree_model X E hE i x
    obtain ⟨β, hβ, hupper, _, hcompact⟩ :=
      ModuleCat.finiteFreeComplex_homology_upperSemicontinuous A K hbounded hfree i
    have heq (z : U) : derivedFiberBetti X E i z = β (e z) :=
      (hmodel z).trans (hβ (e z)).symm
    refine ⟨U, hx, ?_, ?_⟩
    · intro r
      convert! (hupper.isOpen_preimage r).preimage e.continuous using 1
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iio, heq]
    · intro r
      have hlevel : Topology.IsConstructible {p : PrimeSpectrum A | β p = r} := by
        have hset : {p : PrimeSpectrum A | β p = r} =
            {p : PrimeSpectrum A | (β p : ℤ) < (r : ℤ) + 1} \
              {p : PrimeSpectrum A | (β p : ℤ) < (r : ℤ)} := by
          ext p
          simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
          omega
        rw [hset]
        exact ((hcompact ((r : ℤ) + 1)).2.isConstructible
          (hcompact ((r : ℤ) + 1)).1).sdiff
            ((hcompact r).2.isConstructible (hcompact r).1)
      convert! hlevel.preimage_of_isOpenEmbedding e.isOpenEmbedding using 1
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, heq]
  refine ⟨?_, ?_, ?_⟩
  · intro Y _ _ g y
    obtain ⟨e⟩ := derivedFiberCohomology_baseChange_iso X Y E g i y
    let := (g.residueFieldMap y).hom.toAlgebra
    exact e.toLinearEquiv.finrank_eq.trans Module.finrank_baseChange
  · rw [upperSemicontinuous_iff_isOpen_preimage]
    intro r
    rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨U, hxU, hopen, _⟩ := hlocal x
    refine ⟨Subtype.val '' {z : U | derivedFiberBetti X E i z < r}, ?_,
      U.isOpen.isOpenMap_subtype_val _ (hopen r), ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact hz
    · exact ⟨⟨x, hxU⟩, hx, rfl⟩
  · intro r x
    obtain ⟨U, hxU, _, hlevels⟩ := hlocal x
    exact ⟨U, U.isOpen.mem_nhds hxU, U.isOpen, hlevels r⟩

end AlgebraicGeometry.Scheme

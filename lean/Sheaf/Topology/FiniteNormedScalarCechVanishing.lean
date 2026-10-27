/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C7
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.CategoryTheory.SiteCechComplex
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Analysis.Normed.Module.FiniteDimension
import Sheaf.Topology.NormedScalarProfiniteCechExact

/-! # Finite-family continuous scalar Čech vanishing

Source: Bhatt--Scholze, Lemma 4.3.9(2)--(4), finite disjoint-union reduction.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace Profinite

/-- Positive Čech cohomology of continuous finite p-adic scalar functions vanishes
for every nonempty finite jointly surjective family, for any choice of its fibre products.
Source: Bhatt--Scholze, Lemma 4.3.9(2)--(4), and step 1 of
lem-sfb-finite-normed-scalar-section-acyclicity.
(blueprint: lem-sfb-finite-normed-scalar-cech-vanishing).

Proof: Reindex the finite family by a finite ordinal; this makes its disjoint union
u-small even when the original indexing type lives in a larger universe.
Form the finite topological disjoint union of the covering sources and its
surjection to V. Its equal-image (n+1)-tuples split into clopen pieces indexed by
(n+1)-tuples of summands. Each piece is the corresponding iterated fibre product;
the universal property identifies it with the chosen object in S. Restriction and
finite clopen gluing give inverse additive maps between continuous cochains on the
surjection and the family cochains. Deleting coordinates commutes with these maps,
so they identify the alternating differentials. The extending norm on the finite
extension agrees with the spectral norm. Apply normedScalarProfiniteCech_exact to
any positive-degree cocycle and transport its primitive to the family complex.
Thus the complex is exact in positive degrees and its homology is zero.
If V is empty, joint surjectivity has empty sources; all continuous functions on the
corresponding tuple spaces are zero, as covered by the same primitive theorem. -/
theorem finiteNormedScalar_cech_vanishing (l : ℕ) [Fact l.Prime]
    (E : Type u) [NormedField E] [NormedAlgebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (V : Profinite.{u}) (T : Type v) [Finite T] [Nonempty T] (W : T → Profinite.{u})
    (f : ∀ t, W t ⟶ V) (hf : ∀ v : V, ∃ t, ∃ w : W t, f t w = v)
    (S : SiteCechComplex W f) (q : ℕ) (hq : 0 < q) :
    IsZero ((S.cohomologyFunctor q).obj (continuousMapRingObjOfUniverse E).obj) := by
  sorry

end Profinite

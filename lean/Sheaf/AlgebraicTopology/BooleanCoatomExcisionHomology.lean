/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.AlgebraicTopology.BooleanCoatomExcisionDerived
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology

/-! # Homology of Boolean coatom excision

Source: the agent-written combinatorial extraction below paragraph (3) of the latest
blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability` direct-images proof;
the paragraph is contextual motivation only, not the combinatorial assertion.
The homology and shift conventions are Stacks Project, Tags 010V, 011G, 011H,
05RR and 05RU (blueprint: lem-sfb-boolean-coatom-excision-homology).

The derived assertion is already stated by `BooleanCoatom.excision`. This module
states its per-degree consequence for the same augmented strict-chain complexes.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory

namespace AlgebraicTopology.AugmentedPosetChains.BooleanCoatom

private noncomputable def reversalHomologyIso
    (K : ChainComplex (ModuleCat.{u} ℚ) ℤ) (q p : ℤ) (h : -q = p) :
    (reversal.obj K).homology q ≅ K.homology p :=
  K.restrictionHomologyIso ComplexShape.embeddingUpIntDownInt
    (q - 1) q (q + 1) (by simp) (by simp)
    (i' := p + 1) (j' := p) (k' := p - 1)
    (by change -(q - 1) = p + 1; omega) h
    (by change -(q + 1) = p - 1; omega) (by simp) (by simp)

/-- Removing one element of a finite Boolean interval lowers augmented homology degree by one.
Source: the agent-written extraction from direct-images paragraph (3), per-degree
consequence of derived Boolean coatom excision; Stacks Tags 010V, 011G, 011H, 05RR, 05RU
(blueprint: lem-sfb-boolean-coatom-excision-homology).

Proof: (1) Fix n and use `lem-sfb-boolean-coatom-excision-derived`, with exactly the
same finite set and chosen element. Choose the standard derived-category localization
of rational modules and apply its H^(-n) functor to `derivedComparison a hcard` and
its inverse. Functoriality gives an isomorphism of rational modules.
(2) The factorization of cohomology through Q identifies the source with H_n(B_E).
For the target, the specified `reversalSuspensionIso` identifies the cochain shift
with the reversal of the actual suspension: both have term (B_v)_(-q-1) and
differential -d. At q=-n the cycles modulo boundaries are therefore
ker(-d_(n-1))/im(-d_n). Negating a differential leaves its kernel unchanged, and
-d(y)=d(-y) gives equality of its image with that of d. The identity on the term
thus identifies this quotient with H_(n-1)(B_v), including all zero-term degrees.
(3) Compose these source and target identifications with H^(-n) of the derived
isomorphism. Composing the inverse identifications with H^(-n) of its inverse gives
the inverse rational linear map, proving the stated isomorphism. -/
theorem excision_homology {E : Type u} [DecidableEq E] [Fintype E]
    (a : E) (hcard : 2 ≤ Fintype.card E) (n : ℤ) :
    Nonempty ((booleanComplex (Finset.univ : Finset E)).homology n ≅
      (booleanComplex (coatom a)).homology (n - 1)) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} ℚ)
  have : IsIso (derivedComparison a hcard) :=
    (excision a hcard).2.2.2.2.2.2
  exact ⟨(reversalHomologyIso (booleanComplex (Finset.univ : Finset E))
      (-n) n (by omega)).symm ≪≫
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} ℚ) (-n)).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} ℚ) (-n)).mapIso
      (asIso (derivedComparison a hcard)) ≪≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} ℚ) 0).shiftIso
      1 (-n) (1 - n) (by omega)).app _ ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} ℚ) (1 - n)).app _ ≪≫
    reversalHomologyIso (booleanComplex (coatom a)) (1 - n) (n - 1) (by omega)⟩

end AlgebraicTopology.AugmentedPosetChains.BooleanCoatom

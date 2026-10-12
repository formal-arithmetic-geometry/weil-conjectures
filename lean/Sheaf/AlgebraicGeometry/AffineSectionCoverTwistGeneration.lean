/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
import Sheaf.AlgebraicGeometry.AffineFiniteTypeGeneratingSections
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators

/-! # Eventual generation from a finite affine section cover

Source: EGA II, proof of Proposition 4.5.5, local-generator extension paragraphs;
Stacks Project, Properties, Proposition 01Q3, (1) ⇒ (5).
(blueprint: lem-weil-pbc-affine-section-cover-twist-generation).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite affine cover by section loci of one invertible module gives finite global
 generators for all sufficiently large powers of that module, after tensoring with a
 finite type quasi-coherent module. No ampleness assumption or residue argument is used.

Source: EGA II, proof of Proposition 4.5.5, paragraphs extending the local generators;
Stacks Project, Properties, Proposition 01Q3, (1) ⇒ (5), using Lemma 01PW.
(blueprint: lem-weil-pbc-affine-section-cover-twist-generation).

Proof:
1. Restrict G to the affine opens U_i = X minus the support of the zero locus of s_i.
   Finite type and quasi-coherence restrict to opens. The affine finite-generator
   theorem gives finitely many sections t_ij generating G on each U_i.
2. Apply clearing denominators (01PW) on the compact separated scheme X to each t_ij:
   obtain an exponent a_ij and a global section of G tensor M^a_ij whose restriction
   is t_ij tensor s_i^a_ij. Take K to be the maximum of these finitely many exponents,
   taking zero when there are no generators.
3. For k >= K multiply each lifted section by s_i^(k-a_ij), using the tensor-power
   addition isomorphism. The resulting global sections of G tensor M^k restrict to
   t_ij tensor s_i^k. On U_i the section s_i freely generates M, and every tensor
   power of this free generator freely generates M^k (including k = 0).
4. Tensoring by that generator identifies G|U_i with (G tensor M^k)|U_i, so these
   restrictions generate on U_i. The finite union of all the lifted sections gives
   an evaluation map from a finite free sheaf. On each U_i its image contains the
   generating family indexed by i, hence it is locally surjective. Since the U_i
   cover X, the evaluation map is epi, giving a finite GeneratingSections family.
   The empty scheme and zero module cause no exception: the empty family is epi. -/
theorem exists_finite_generatingSections_tensorPow_of_affine_section_cover
    (X : Scheme.{u}) [CompactSpace X] [X.IsSeparated]
    (M G : X.Modules) [M.IsInvertible] [G.IsQuasicoherent] [G.IsFiniteType]
    {I : Type u} [Finite I] (s : I → (𝟙_ X.Modules ⟶ M))
    (haff : ∀ i, IsAffineOpen (Hom.zeroLocus (s i)).support.compl)
    (hcover : (⨆ i, (Hom.zeroLocus (s i)).support.compl) = ⊤) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∃ σ : (tensorObj G (M.tensorPow k)).GeneratingSections, σ.IsFiniteType := by
  sorry

end AlgebraicGeometry.Scheme.Modules

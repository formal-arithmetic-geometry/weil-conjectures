/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q153
-/
module

public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import Sheaf.RingTheory.ColimitCategoryFpAlgebras
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.FinitePresentation
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! # Existence of group embeddings over an algebraically closed field

Source: Stacks Project, Limits Tag 01ZM (2)--(3) and Algebra Tag 00FV;
the affine spreading and specialization consequence
(blueprint: lem-sfb-algclosed-group-embedding-existence-descent).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Existence of a closed group embedding descends along any field extension of an
algebraically closed field. This does not descend a specified embedding.
Source: Stacks Project, Limits Tag 01ZM (2)--(3), Algebra Tags 00FP, 05N9 and 00FV
(blueprint: lem-sfb-algclosed-group-embedding-existence-descent).

Proof:
1. Base change an embedding over `F`. Closed immersions are stable under base change
   (lem-weil-pbc-closed-immersion-base-change), and base change preserves the group laws
   (def-pc-base-change, def-sc-group-scheme).
2. Conversely put `B = F[G]`, `C = F[H]`. These are finitely generated
   (lem-pc-affine-finite-type-algebra), hence finitely presented over the Noetherian field
   `F` (def-weil-pbc-noetherian-ring, lem-weil-pbc-finite-type-noetherian-finite-presentation).
   The embedding over `L` corresponds to a surjection `C ⊗ L → B ⊗ L`
   (def-weil-affine-spectrum, lem-weil-pbc-fibre-product-affine-spectra,
   def-weil-closed-immersion).
3. The finitely generated `F`-subalgebras `R` of `L` are directed, contain `F`, and have
   union and colimit `L`: each element belongs to `F[l]`, and compatible maps glue
   uniquely, with ring operations checked in a common stage. Descend the algebra map
   to such an `R` by lem-weil-pbc-colimit-category-fp-algebras (2).
4. For every `F`-vector space `V`, the map `V ⊗ R → V ⊗ L` is injective, as a basis
   identifies it with a direct sum of `R → L`. Apply this to `V = B ⊗ B` to descend
   the comultiplication equation. The tensor reassociation sends
   `(b ⊗ r) ⊗ (b' ⊗ s)` to `(b ⊗ b') ⊗ rs`, with inverse
   `(b ⊗ b') ⊗ r ↦ (b ⊗ r) ⊗ (b' ⊗ 1)`. Thus the descended map respects group laws
   (def-sc-group-scheme, def-weil-affine-spectrum,
   lem-weil-pbc-fibre-product-affine-spectra, def-pc-base-change).
5. Choose preimages over `L` of finitely many generators of `B`; enlarge `R` by their
   finitely many tensor coefficients. The preimage equations already hold over `R`
   by the same injectivity with `V = B`. The map is then surjective, including when
   there are zero generators, and its spectrum is a closed immersion
   (def-weil-pbc-finite-type-algebra, def-weil-closed-immersion, def-pc-base-change).
6. Choose a maximal ideal of the nonzero ring `R`
   (lem-weil-common-extension-fields-maximal-ideal). Its closed point has residue field
   `F` (lem-weil-pbc-closed-point-residue-field-base), giving an `F`-algebra map `R → F`.
   Specialize the embedding along this map; closed immersions remain closed
   (lem-weil-pbc-closed-immersion-base-change). The identification
   `(A ⊗ R) ⊗ F ≃ A` sends `(a ⊗ r) ⊗ t` to `a * a_R(r) * t`, with inverse
   `a ↦ (a ⊗ 1) ⊗ 1`, and respects multiplication. This yields the required group
   embedding over `F` (def-pc-base-change, def-sc-group-scheme). -/
theorem exists_closed_group_embedding_iff_of_isAlgClosed
    {F L : Type u} [Field F] [IsAlgClosed F] [Field L] [Algebra F L]
    (G H : Grp (Over (Spec (.of F))))
    [IsAffine G.X.left] [IsAffine H.X.left]
    [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom] :
    (∃ j : G ⟶ H, IsClosedImmersion j.hom.hom.left) ↔
      ∃ j' : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).mapGrp.obj G ⟶
          (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap F L)))).mapGrp.obj H,
        IsClosedImmersion j'.hom.hom.left := by
  sorry

end AlgebraicGeometry

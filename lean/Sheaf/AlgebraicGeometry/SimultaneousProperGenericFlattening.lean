/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Compactification.StrictTransform
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.GenericFlatFinitePresentation
import Sheaf.AlgebraicGeometry.FlatteningByAdmissibleBlowup

/-! # Simultaneous generic flattening of two proper families

Source: Stacks Project, Tag 081R, Lemma `lemma-flat-after-blowing-up`, applied to a
finite disjoint union after Tag 052A, Proposition `proposition-generic-flatness`;
Tag 080D, Definition `definition-strict-transform`. ILO, Expose X, Theorem 3.4,
proof Step 2, printed p. 160 (blueprint: lem-trf-simultaneous-proper-generic-flattening).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Two proper families over an integral Noetherian scheme admit one admissible blowup
whose strict transforms are flat and finitely presented. `Fin 2` indexes the two families;
no nonemptiness is required of either source. The preserved open is the complement of
`B.I.support`, which may be larger than `U`. The strict transforms are the schematic
closures of the open loci by the definition of `strictTransform`. Agreement with the
original families is expressed by the source projections being isomorphisms over that
open. The coproduct comparison respects both projections, so it identifies the closed
subschemes in the base-changed disjoint union, including their nilpotent structure.

Source: Stacks Project, Tags 081R, 052A and 080D; ILO, Expose X, Theorem 3.4,
proof Step 2 (blueprint: lem-trf-simultaneous-proper-generic-flattening).

Proof:
1. Form the disjoint union `W = ∐ X` and its map `Sigma.desc f` using
   `lem-weil-pbc-scheme-coproduct-family`. Properness gives finite type for each family.
   Combining their finite affine covers proves finite type of this map, including when
   one or both covers are empty (`def-weil-finite-type-morphism`).
2. `lem-weil-pbc-finite-type-over-noetherian` makes `W` Noetherian.
   `lem-weil-pbc-locally-noetherian-quasi-separated` gives quasi-separatedness of `S`
   and `W`. `lem-weil-pbc-qcqs-morphism-permanence` gives relative quasi-separatedness.
3. Apply `lem-sbc-generic-flat-finite-presentation` to obtain a nonempty open `U` where
   the union is flat and locally finitely presented. The descending-chain condition from
   `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` makes the topology Noetherian;
   `lem-sfb-noetherian-space-compact-subsets` makes `U` and every later open compact.
4. Apply `lem-trf-flattening-by-admissible-blowup` to obtain a finite-type centre `B.I`,
   unit on `U`, with flat finitely presented union strict transform. Its defining open
   is over `V = B.I.support.compl`, and it is the schematic closure of that open locus.
5. The base change of the union is the union of the base changes, with disjoint clopen
   summands (`lem-weil-pbc-scheme-coproduct-family`). The inclusion of the open locus over
   `V` is quasi-compact: `V` is compact and the base is Noetherian, and quasi-compactness
   is stable under base change (`lem-weil-pbc-qcqs-morphism-permanence`). Thus its closure
   ideal is the literal kernel of the structure-sheaf restriction map
   (`def-nagata-scheme-theoretic-image`). Restricting this map and its kernel to each
   clopen summand gives exactly its own schematic closure. These are the individual
   strict transforms (`def-nagata-strict-transform`), giving the displayed coproduct
   isomorphism compatibly with the source and modified-base projections.
6. The individual transforms are clopen in the union transform. Flatness and local
   finite presentation restrict to them. On every affine of the modified base their
   preimages are closed in a quasi-compact preimage, hence quasi-compact. Their relative
   diagonals are base changes of the union diagonal, hence quasi-compact by
   `lem-weil-pbc-qcqs-morphism-permanence`; thus they are quasi-separated. These are
   precisely the three finite-presentation conditions.
7. Apply `lemma-nagata-admissible-blowup-over-open` to the centre complement `V`.
   The blowup is an isomorphism there, and on this open the closure kernel is zero
   (`def-nagata-scheme-theoretic-image`). The source projection therefore identifies
   each transform over `V` with its original family over `V`. Empty summands stay empty
   throughout the same kernel construction. -/
theorem exists_simultaneous_flat_finitePresentation_strictTransform_admissibleBlowup
    {S : Scheme.{u}} [IsIntegral S] [IsLocallyNoetherian S] [CompactSpace S]
    (X : Fin 2 → Scheme.{u}) (f : ∀ i : Fin 2, X i ⟶ S) [∀ i : Fin 2, IsProper (f i)] :
    ∃ U : S.Opens, (U : Set S).Nonempty ∧ IsCompact (U : Set S) ∧
      ∃ B : IsAdmissible S U,
        (∀ i : Fin 2,
          Flat (strictTransformMap (f i) B.I.blowupMap B.I.support.compl) ∧
          LocallyOfFinitePresentation
            (strictTransformMap (f i) B.I.blowupMap B.I.support.compl) ∧
          QuasiCompact (strictTransformMap (f i) B.I.blowupMap B.I.support.compl) ∧
          QuasiSeparated (strictTransformMap (f i) B.I.blowupMap B.I.support.compl) ∧
          IsIso ((strictTransformToSource (f i) B.I.blowupMap B.I.support.compl) ∣_
            (f i ⁻¹ᵁ B.I.support.compl))) ∧
        ∃ e : (∐ fun i : Fin 2 ↦ strictTransform (f i) B.I.blowupMap B.I.support.compl) ≅
            strictTransform (Sigma.desc f) B.I.blowupMap B.I.support.compl,
          ∀ i : Fin 2,
            Sigma.ι (fun j : Fin 2 ↦ strictTransform (f j) B.I.blowupMap
                B.I.support.compl) i ≫ e.hom ≫
                strictTransformToSource (Sigma.desc f) B.I.blowupMap B.I.support.compl =
              strictTransformToSource (f i) B.I.blowupMap B.I.support.compl ≫ Sigma.ι X i ∧
            Sigma.ι (fun j : Fin 2 ↦ strictTransform (f j) B.I.blowupMap
                B.I.support.compl) i ≫ e.hom ≫
                strictTransformMap (Sigma.desc f) B.I.blowupMap B.I.support.compl =
              strictTransformMap (f i) B.I.blowupMap B.I.support.compl := by
  sorry

end AlgebraicGeometry

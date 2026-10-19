/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.FiniteLocallyFreeStructureSheaf
import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
import WeilConjectures.RingTheory.HenselianEtaleRetraction
import Sheaf.RingTheory.FilteredColimitFiniteData
import Sheaf.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.FiniteFreeAlgebraSpectrum
import Sheaf.AlgebraicGeometry.DescendFiniteLocallyFree
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.FiniteStability
import Sheaf.AlgebraicGeometry.CompletelyDecomposedEtaleFiniteSubcover
import Sheaf.AlgebraicGeometry.OrdinaryHenselianPointedNeighbourhoodLimit

/-!
# Exchanging finite flat maps and completely decomposed étale families

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II, proof of Theorem 3.2.3,
printed pp. 30--31, and Corollary 2.2.4, printed p. 27
(blueprint: lem-per-finite-flat-cd-etale-exchange).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- Exchange a finite locally free map of positive rank prime to `ell` with a finite completely
 decomposed separated étale family. No reducedness or integrality is required of the schemes.
Source: ILO, Exposé II, proof of Theorem 3.2.3, printed pp. 30--31 (the printed `W_j` in
`Z_j → W_j` means `U_j`), and Corollary 2.2.4, printed p. 27
(blueprint: lem-per-finite-flat-cd-etale-exchange).

Proof:
1. Around `x : X`, choose an affine neighbourhood on which `f_* O_Y` is free of rank `d`
   (`lem-pc-flf-properties`). Use the ordinary henselian pointed-neighbourhood limit
   (`lem-per-ordinary-henselian-pointed-neighbourhood-limit`) with residue field `κ(x)`.
   The finite algebra over its henselian local limit ring splits into nonzero henselian local
   factors (`lem-weil-pbc-finite-over-henselian-local-product`). Each is a direct summand of a
   free module, hence free over the local ring by
   `lem-weil-pbc-finite-projective-standard-free-cover`.
2. The positive ranks of the factors sum to `d`, so one factor has positive rank `e` prime to
   `ell`. Its closed point maps to `y : Y`. Complete decomposition supplies a lift to some
   `V_i` with unchanged residue field; extending this rational point to the residue field of
   the factor gives a rational point of the corresponding étale pullback.
3. Choose an affine open around that lift. Étale composition/cancellation and base change
   (`lem-weil-pbc-etale-composition-cancellation`, `lem-weil-pbc-etale-ring-base-change`)
   give an étale algebra over the chosen henselian local factor. The rational point gives a
   retraction (`lem-weil-pbc-henselian-etale-retraction`), hence a section into `V_i`.
4. Descend the idempotent selecting the factor using
   `lemma-nagata-filtered-colimit-finite-data`. The clopen factor and the chosen affine étale
   neighbourhood are finitely presented over the affine base, by
   `lem-weil-pbc-lfp-affine-opens-finite-presentation` and
   `lem-weil-pbc-finite-presentation-base-change-composition`. Identify the affine limit by
   `lem-weil-pbc-limit-affine-transition`; descend the section with `thm-pd-spreading-out`.
5. The limiting factor has constant finite locally free rank `e`
   (`lem-weil-pbc-finite-free-algebra-spectrum`). Descend that property and rank by
   `lem-weil-pbc-descend-finite-locally-free`, retaining the morphism into `V_i`.
6. Compose the resulting separated étale neighbourhood with the original affine open of `X`.
   This open immersion is quasi-compact because `X` is Noetherian
   (`lem-weil-pbc-noetherian-open-subscheme-noetherian`), hence finite type by
   `lem-weil-pbc-qc-open-immersion-finite-type`. Composition preserves étaleness and finite type
   (`lem-weil-pbc-etale-composition-cancellation`,
   `lem-sfb-finite-type-composition-base-change`); separatedness follows from the diagonal.
   The pointed neighbourhood still has a lift of `x` with residue field `κ(x)`.
7. Positive rank makes each finite locally free map surjective: each fibre is the spectrum
   of a nonzero finite-dimensional algebra over a field. The neighbourhoods are completely
   decomposed by their designated lifts. Retain finitely many using
   `lem-per-completely-decomposed-etale-finite-subcover`, together with their ranks and maps.
   For empty `X`, take the empty family. -/
theorem finite_flat_cd_etale_exchange
    (X Y : Scheme.{u}) [IsNoetherian X]
    (ell : ℕ) (hell : ell.Prime) (f : Y ⟶ X) (d : ℕ)
    (hf : f.IsFiniteLocallyFreeOfDegree d) (hd : 0 < d) (hcoprime : Nat.Coprime d ell)
    {I : Type w} [Finite I] (V : I → Scheme.{u}) (v : ∀ i, V i ⟶ Y)
    (hv : ∀ i, IsSeparated (v i) ∧ Etale (v i) ∧
      LocallyOfFiniteType (v i) ∧ QuasiCompact (v i))
    (hcd : ∀ y : Y, ∃ (i : I) (z : V i),
      v i z = y ∧ IsIso ((v i).residueFieldMap z)) :
    ∃ (n : ℕ) (U Z : Fin n → Scheme.{u})
      (u : ∀ j, U j ⟶ X) (c : ∀ j, Z j ⟶ U j)
      (r : Fin n → ℕ) (index : Fin n → I) (g : ∀ j, Z j ⟶ V (index j)),
      (∀ j, IsSeparated (u j) ∧ Etale (u j) ∧
        LocallyOfFiniteType (u j) ∧ QuasiCompact (u j)) ∧
      (∀ x : X, ∃ (j : Fin n) (z : U j),
        u j z = x ∧ IsIso ((u j).residueFieldMap z)) ∧
      (∀ j, (c j).IsFiniteLocallyFreeOfDegree (r j) ∧
        Surjective (c j) ∧ 0 < r j ∧ Nat.Coprime (r j) ell) ∧
      (∀ j, g j ≫ v (index j) ≫ f = c j ≫ u j) := by
  sorry

end AlgebraicGeometry

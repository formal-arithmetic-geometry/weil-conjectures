/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Topology.NoetherianSpace

import Sheaf.Topology.NoetherianGoodStratificationRefinement
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.Paper.ReducedSourceFactors
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Finite open filtrations with finite constant models on reduced strata

Source: Stacks Project, Topology, Tag 09Y5
(`lemma-noetherian-partition-refined-by-stratification`), and Pro-etale Cohomology,
Tag 09AH (`lemma-ses-associated-to-open`)
(blueprint: lem-sfb-finite-model-stratum-filtration).
Re-recorded by group NS on 2026-10-18; the statement and constructions are unchanged.

The auxiliary functors name the actual extension-by-zero pieces and closed-stratum
pieces. Cokernels in the functor category express naturality with the opens fixed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical piece `v_! v^*`, for the inclusion of an open subscheme.
Source: Stacks Tag 09AH, first term of the localization sequence
(blueprint: lem-sfb-finite-model-stratum-filtration). -/
noncomputable def openFiltrationPiece {X : Scheme.{u}} (V : X.Opens) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  upperStar Λ V.ι ⋙ openImmersionLowerShriek Λ V.ι

/-- The counit of the specified extension-by-zero/restriction adjunction.
Source: Stacks Tag 09AH, injection of the open-supported piece
(blueprint: lem-sfb-finite-model-stratum-filtration). -/
noncomputable def openFiltrationCounit {X : Scheme.{u}} (V : X.Opens) :
    openFiltrationPiece Λ V ⟶ 𝟭 _ :=
  (openImmersionLowerShriekUpperStarAdjunction Λ V.ι).counit

/-- The functor `v_! t_* t^* v^*` for a closed stratum in an open subscheme.
Source: Stacks Tag 09AH, closed term of the localization sequence, extended by zero
(blueprint: lem-sfb-finite-model-stratum-filtration). -/
noncomputable def openFiltrationStratum {X : Scheme.{u}} (V : X.Opens)
    {S : Scheme.{u}} (t : S ⟶ V.toScheme) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
  upperStar Λ V.ι ⋙ upperStar Λ t ⋙ lowerStar Λ t ⋙ openImmersionLowerShriek Λ V.ι

/-- Finite open filtration of a constructible module with finite scalar local models.
Source: Stacks Tag 09Y5 and Tag 09AH; blueprint constructibility, clauses (1)--(2)
(blueprint: lem-sfb-finite-model-stratum-filtration).

Proof plan:
1. `lem-sfb-noetherian-space-compact-subsets` makes all subsets compact. This gives
qcqs for the scheme and all open immersions and allows the finite-stratification
clause of `sk-def-sfb-constructible` to be applied to F.
2. `lem-sfb-noetherian-good-stratification-refinement` gives a finite good refinement
of that partition, including the empty partition for the empty scheme.
3. Order maximal strata first. Their prefixes are open by the closure formula of
Tag 09Y0. Give each difference its reduced closed structure by
`lem-weil-pbc-reduced-induced-closed-subscheme`. Compactness of subsets gives qcqs.
4. The reduced-source factorization lemma factors each new stratum through its old
stratum. Composition of module pullbacks identifies the restrictions. Base change
of the trivializing pro-etale cover and the monoidal inverse image, using
`lem-sfb-alpha-iso`, pull back the same finite scalar presentation, even with torsion.
5. Apply `lem-weil-pbc-proetale-ringed-open-closed` to every open and its reduced
closed complement. The internal/sectionwise module equivalence and alpha comparison
identify its open extension with the specified module lower shriek. Its counit is
monic; the empty and total opens give the zero and whole objects.
6. Apply the same localization sequence inside each successive open and its exact
extension by zero to X. The composite left-adjoint comparison, with
`def-sfb-module-upper-star-comp`, identifies the first term with the preceding
piece and identifies its map to F with the preceding counit. Thus the cokernel
is the ordinary closed direct image of the stratum restriction, extended by zero.
7. All localization maps and adjunction comparisons are natural in the module.
Taking cokernels in the functor category gives the displayed natural isomorphisms.
-/
theorem exists_finiteModelStratumFiltration (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hF : IsConstantModelConstructible Λ X F) :
    ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens),
      Monotone V ∧ V 0 = ⊥ ∧ V (Fin.last r) = ⊤ ∧
      ∃ (S : Fin r → Scheme.{u}) (t : ∀ k : Fin r, S k ⟶ (V k.succ).toScheme),
        (∀ k : Fin r, IsClosedImmersion (t k) ∧ IsReduced (S k) ∧
          Set.range (t k) = {x | (V k.succ).ι x ∉ V k.castSucc}) ∧
        (∀ k : Fin r, HasFiniteConstantLocalModel Λ (S k)
          ((upperStar Λ (t k)).obj ((upperStar Λ (V k.succ).ι).obj F))) ∧
        (∀ k : Fin (r + 1), QuasiCompact (V k).ι ∧ QuasiSeparated (V k).ι) ∧
        (∀ k : Fin r,
          QuasiCompact ((V k.succ).ι ⁻¹ᵁ V k.castSucc).ι ∧
          QuasiSeparated ((V k.succ).ι ⁻¹ᵁ V k.castSucc).ι) ∧
        (∀ k : Fin (r + 1), Mono ((openFiltrationCounit Λ (V k)).app F)) ∧
        IsZero ((openFiltrationPiece Λ (V 0)).obj F) ∧
        IsIso ((openFiltrationCounit Λ (V (Fin.last r))).app F) ∧
        ∃ d : ∀ k : Fin r,
          openFiltrationPiece Λ (V k.castSucc) ⟶ openFiltrationPiece Λ (V k.succ),
          (∀ k : Fin r,
            d k ≫ openFiltrationCounit Λ (V k.succ) =
              openFiltrationCounit Λ (V k.castSucc)) ∧
          (∀ k : Fin r, Mono ((d k).app F)) ∧
          (∀ k : Fin r,
            Nonempty (cokernel (d k) ≅ openFiltrationStratum Λ (V k.succ) (t k))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing

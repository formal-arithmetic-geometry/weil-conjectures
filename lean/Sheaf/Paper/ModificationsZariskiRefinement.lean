/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q85
-/
module

public import Sheaf.Paper.OrgogozoInductionData
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Topology.Defs.Filter

import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Blowup.AdmissibleBlowup
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.Density
import WeilConjectures.Blowup.Extension
import WeilConjectures.Compactification.StrictTransform
import WeilConjectures.Compactification.EliminationOfIndeterminacy
import Sheaf.Compactification.NagataSketchBlowups

/-!
# Common refinements of modifications on a finite Zariski cover

Source: Orgogozo, Modifications et cycles proches sur une base générale, §2.1, p. 3,
finite-cover globalization; Stacks Project Tags 081S, 081T, 080M and 080N
(blueprint: lem-trf-modifications-zariski-refinement).

The modification predicate is the one of `OrgogozoInductionData`, including density of the
inverse image of the isomorphism locus. No compatibility on overlaps is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Orgogozo

/-- Modifications on a finite open cover of an integral Noetherian scheme have a global
modification refining each one over its open base. Source: Orgogozo §2.1, p. 3; Stacks
Tags 081S, 081T, 080M and 080N (blueprint: lem-trf-modifications-zariski-refinement).

Proof plan, following the node's seven steps:
1. The minimal-closed-subset argument of
`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` makes every open of `S`
quasi-compact. Open subschemes are consequently qcqs, using
`def-weil-quasi-separated-morphism` and `def-weil-pbc-quasi-compact-scheme`.
2. Discard empty opens. Choose dense isomorphism opens from
`def-trf-orgogozo-induction-data`. Their finite intersection `W` is nonempty and dense in
`S` and in each remaining open by integrality (`def-pc-integral-scheme`).
3. Apply `sk-lem-nagata-sketch-elimination` to each proper local modification. It yields
`W`-admissible blow-ups with open-immersion strict transforms and dense inverse image of
`W` (Tags 081S, 081T; `def-nagata-admissible-blowup`).
4. The strict transform is closed in the fibre product (`def-nagata-strict-transform`).
Its image in the blow-up is closed by properness (`def-weil-proper-morphism`) and contains
the dense inverse image of `W`, so the open immersion is surjective and hence an
isomorphism (`def-weil-open-immersion`). Its inverse gives the local factorization.
5. Extend each blow-up to `S` and dominate the finite family by one `W`-admissible blow-up,
using both clauses of `sk-lem-nagata-sketch-blowups` (Tags 080M, 080N).
6. Restrict the domination maps to each open and compose with step 4. The fibre-product
universal property (`def-pc-fibre-product`) gives the displayed equation over that open.
For an empty open the source is empty and its unique morphism gives the factorization.
7. The global blow-up is proper (`lemma-nagata-blowup-proper`), is an isomorphism over `W`
(`lemma-nagata-admissible-blowup-over-open`), and has dense inverse image of `W`
(`lemma-nagata-conrad-dense-in-admissible-blowup`), exactly `IsModification`.
-/
theorem exists_modification_zariski_refinement (S : Scheme.{u})
    [IsIntegral S] [IsNoetherian S] (n : ℕ) (U : Fin n → S.Opens)
    (hcover : (⨆ i, U i) = ⊤) (V : Fin n → Scheme.{u})
    (q : ∀ i : Fin n, V i ⟶ (U i).toScheme)
    (hq : ∀ i : Fin n,
      @IsModification (V i) (U i).toScheme inferInstance inferInstance
        (isCompact_iff_compactSpace.mp
          (TopologicalSpace.NoetherianSpace.isCompact (U i : Set S))) (q i)) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S), IsModification p ∧
      ∀ i : Fin n, ∃ a : pullback p (U i).ι ⟶ V i,
        a ≫ q i = pullback.snd p (U i).ι := by
  sorry

/-- Finitely many modifications of an integral Noetherian scheme have a common modification,
with every domination map over that scheme. Source: Orgogozo §2.1, p. 3, the finite-family
consequence (blueprint: lem-trf-modifications-zariski-refinement).

Proof: for a nonempty family apply `exists_modification_zariski_refinement` with every open
set equal to `⊤`. Identify the pullback along the full-open inclusion with the source;
the factorization equations give `a ≫ q i = p`. This is step 7 of the node, after the
qcqs, common-open, elimination, strict-transform, extension and restriction steps explained
in that theorem's docstring. For the empty family take the identity of `S`, which is proper
by `def-weil-proper-morphism`, is an isomorphism over `S`, and has dense inverse image of
`S`. The factorization condition is then vacuous. -/
theorem exists_common_modification_refinement (S : Scheme.{u})
    [IsIntegral S] [IsNoetherian S] (n : ℕ) (V : Fin n → Scheme.{u})
    (q : ∀ i : Fin n, V i ⟶ S) (hq : ∀ i : Fin n, IsModification (q i)) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S), IsModification p ∧
      ∀ i : Fin n, ∃ a : S' ⟶ V i, a ≫ q i = p := by
  sorry

end AlgebraicGeometry.Orgogozo

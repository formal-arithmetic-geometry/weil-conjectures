## Worker report

The module `Sheaf.Paper.FiniteConstantStratifiedZariskiLocality` states
`AlgebraicGeometry.ProEtale.finiteConstantStratified_zariski_locality` as a conjunction
of the three assertions in the node, with one `sorry` and no new definition.
The node changes only in `lean`; its statement, dependencies and proof are unchanged.
The current source was read at
`literature/blueprint/latest/blueprint/sec-proetale-coefficients/sk-def-sfb-constructible/_section.md`,
clause 2, together with Topology 005J, 09YD, 053W and the geometric part of the
finite-affine-cover argument of Etale Cohomology 095E. The latter's discrete
Noetherian coefficient hypothesis is not imported: this node uses only its geometric
stratification argument and the separate arbitrary-condensed-coefficient model-pullback
lemma.

Clause-by-clause correspondence:

- Arbitrary commutative condensed coefficients: the explicitly bound
  `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `[MonObj Λ]`
  and `[IsCommMonObj Λ]` is the unbundled ring-object form of
  `Profinite.CondensedRing`. It assumes no topological presentation, field or nonzero ring.
- Every scheme is in `Scheme.{u}`; `Y` is arbitrary. The small pro-etale module category
  is `Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)`.
  Thus `M` is exactly an internal module over the pulled-back ring `Λ_Y`.
- Restriction to an open `W : Y.Opens` is the genuine module inverse image
  `((CondensedRing.upperStar Λ W.ι).obj M)`. Opens specify the canonical open subschemes
  and open immersions, with no arbitrary chosen map or additional hypothesis.
- Stratified constructibility throughout is the existing `IsFiniteConstantStratified`.
  Its `Scheme.Stratification` has finite index `Fin S.n`, locally closed and
  constructible strata, coverage and pairwise disjointness, actual immersion domains,
  and `HasFiniteConstantLocalModel` for the inverse image on every domain. It therefore
  contains exactly the finite-stratification witnesses of the node, including its
  constructible-subset requirement. No copy of any of these notions is introduced.
- (1) The first conjunct is `CompactSpace Y → QuasiSeparatedSpace Y →
  IsFiniteConstantStratified Λ Y M → ∀ W : Y.Opens, IsCompact (W : Set Y) → ...`.
  `CompactSpace` is quasi-compactness without Hausdorffness; `QuasiSeparatedSpace Y`
  is equivalent to `QuasiSeparated (terminal.from Y)`. Compactness of the subset W is
  quasi-compactness of its open subscheme. Its quasi-separatedness follows from that
  of Y, as in proof step 1, so no extra hypothesis is placed on W.
- (2) The second conjunct starts with arbitrary `W : Y.Opens`, its compactness and
  `QuasiSeparatedSpace W.toScheme`; it does not assume that Y is qcqs. The integer
  `r : ℕ` and `U : Fin r → W.toScheme.Opens` encode the finite open cover of W.
  `(∀ k, IsCompact (U k : Set W.toScheme))` is precisely quasi-compactness of every
  covering open, and `(⋃ k, (U k : Set W.toScheme)) = Set.univ` is coverage.
  Each local hypothesis is `IsFiniteConstantStratified Λ (U k).toScheme` of
  `((CondensedRing.upperStar Λ ((U k).ι ≫ W.ι)).obj M)`, the direct restriction from Y.
  The conclusion is the same predicate for W and `W.ι`-pullback of M. The direct and
  successive restrictions are canonically isomorphic by `CondensedRing.upperStarComp`.
- The final conjunct requires qcqs Y and states the biconditional between the global
  predicate and `∀ V : Y.Opens, IsAffineOpen V →` the predicate on `V.ι`-pullback of M.
  This is the stated affine-local equivalence. On qcqs Y the definition
  `IsConstantModelConstructible` selects precisely its `IsFiniteConstantStratified`
  branch, so this gives the requested agreement of its two readings.
- No Noetherian, nonemptiness, positive-rank or nonzero-module hypothesis occurs.
  `set_option autoImplicit false` and `universe u` make all parameters explicit.

Dependency declarations read and used:

- `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ProfiniteCondensedRing`,
  `Profinite.CondensedRing`; its transparent bundled ring-object type agrees with
  the unbundled `Λ`, `MonObj Λ` convention of the constructibility module.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `sk-def-sfb-pulled-back-coefficients`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing` and `condensedRingObj` (unbundled form).
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `AlgebraicGeometry.Scheme.ProEt` and `Scheme.ProEt.topology`.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`; the open-subscheme maps here are `W.ι` and `(U k).ι`.
- `sk-def-sfb-module-pushforward-pullback`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `AlgebraicGeometry.ProEtale.CondensedRing.upperStar` and `upperStarComp`; the module's
  recorded primary `lowerStar` is the pushforward companion of these declarations.
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`, `CompactSpace`
  and `IsCompact`.
- `def-weil-quasi-separated-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, `AlgebraicGeometry.QuasiSeparated`
  and `quasiSeparatedSpace_iff_quasiSeparated`.
- `def-constructible-stratification`:
  `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`,
  `AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification` describes the underlying
  finite immersed locally closed partition. The already recorded constructibility
  predicate uses the more structured upstream `Scheme.Stratification`, which adds
  precisely the constructibility required by this item; it was inspected in
  `WeilConjectures.ConstructibleSheaf.Defs` and `WeilConjectures.Topology.Stratification`.
- `def-weil-constructible-subset`: its `mathlib_match`, `Mathlib.Topology.Constructible`,
  `Topology.IsConstructible`; it is a field of the upstream stratification.
- `det-def-sfb-constructible-local-model`:
  `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`,
  `AlgebraicGeometry.ProEtale.finiteConstantLocalModel_iff_exists_cover` identifies the
  existing `HasFiniteConstantLocalModel` predicate with the scalar-extension formulation.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
  `IsFiniteConstantStratified`, `HasFiniteConstantLocalModel`,
  `IsConstantModelConstructible` in namespace `AlgebraicGeometry.ProEtale`.

The statement dependency modules are publicly imported, either directly or through
these public imports. Plain proof imports include
`WeilConjectures.ConstructibleSheaf.Pullback` (`Scheme.Stratification.pullback`),
`Sheaf.Paper.PullbackFiniteConstantLocalModel` (`pullback_finiteConstantLocalModel`),
and `WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore`
(`Scheme.exists_global_stratification_factoring_local`). The Mathlib proof dependencies
on the affine basis, affine qcqs, quasi-separated affine covers, constructible open
restriction and fibre products are available through this import closure. The complete
six-step proof is recorded in the theorem docstring; only its proof is postponed.

Edge cases checked before writing:

- For Y or W empty, `Scheme.Stratification.n = 0` is allowed; coverage is possible
  on the empty space. No inhabited stratum or scheme is assumed anywhere.
- For `r = 0`, the union condition forces W empty; the local-model assumptions are
  vacuous and the conclusion has the zero-stratum witness. No `Nonempty (Fin r)` occurs.
- Empty individual covering opens and strata are permitted by the definitions.
- For `M = 0`, the identity stratum and cover with rank-zero scalar presentation
  provide the required model; the statement makes no nonzero assumption on M or Λ.
- For a nonempty non-qcqs ambient Y, clause (2) still applies to its qcqs open W.
- Non-Noetherian qcqs schemes retain the explicit constructible-subset condition
  through `Scheme.Stratification.isConstructible_stratum`.

Searches for an existing statement (all via the prescribed wrapper, plus source reads):

- LeanFinder: `Finite constant stratified constructibility of pro-etale module sheaves
  is local for finite Zariski open covers on qcqs schemes`: eight hits, on finite-type
  sheaves and locally finitely presented morphisms; no matching theorem.
- Loogle: `"IsFiniteConstantStratified"`: zero hits.
- Mathlib grep: `IsFiniteConstantStratified|HasFiniteConstantLocalModel|[Cc]onstructible.*[Zz]ariski`:
  zero hits.
- LeanSearch: `Constructible sheaves are local for finite open covers`: eight hits,
  including `Topology.IsLocallyConstructible.of_isOpenCover` and variants, concerning
  subsets or sheaf conditions, not finite constant scalar models on pro-etale strata.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for those predicates and the item id:
  found the existing definitions and model-pullback theorem, isomorphism invariance
  and zero-module helpers, but no theorem giving these three locality clauses.
  `WeilConjectures` has geometric stratification and discrete/locally-finitely-presented
  constructibility statements, not this arbitrary-condensed finite-scalar-model result.

No statement dispute, missing notion or dependency repair was found. No new nodes or
dependency modules are needed. Server compilation with the required `scompile.py`
passed both sandbox and library modes (1.8 s and 1.9 s), with no reported error or
unexpected warning.

## Second reading by Q121

A fresh self-check was performed against the source node and completed module; no
other agent was started, as the dispatched brief prohibits delegation. Independent
mathematical review is left to the maintainer's delivery reviewer.

I checked the nested conjunction boundaries explicitly: the hypotheses that Y is
qcqs belong only to clauses (1) and (3), while clause (2) assumes qcqs only for W.
The cover lives in `W.toScheme.Opens`, so every member really is a subscheme of W;
its composite immersion into Y gives exactly `M|_{W_k}`, rather than an unrelated
module on the member. The final affine quantifier ranges over all affine opens of Y.
The predicate's actual definition was reopened: it uses constructive immersed
strata with `Topology.IsConstructible`, not just locally closed strata and not the
older arbitrary-local-matrix finite-presentation predicate. The index `Fin r` admits
zero, all universes are explicitly bound, and there is exactly one postponed theorem.
No mismatch or correction was found. The JSON signature was extracted verbatim from
the final source and all other node fields were preserved.

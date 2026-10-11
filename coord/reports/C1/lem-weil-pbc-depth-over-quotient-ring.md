## Worker report

The module states `IsLocalRing.depth_over_quotient_ring`, the quotient-ring invariance
of depth for a finite module annihilated by `I`. The binders `[CommRing R]`,
`[IsNoetherianRing R]`, and `[IsLocalRing R]` render the Noetherian local ring
hypotheses. `I : Ideal R` and `hI : I ≤ maximalIdeal R` render
`I ⊆ m`. `M`, `[AddCommGroup M]`, `[Module R M]`, and `[Module.Finite R M]`
render a finite R-module. The supplied quotient module structures and
`[Module.Finite (R ⧸ I) M]` render the statement's assertion that M is finite over
R/I; `hsmul` explicitly gives the action `(r mod I) • m = r • m`. `hIM` renders
`IM = 0`. The conclusion is existentially packaged over the induced local-ring
instance on `R ⧸ I`, and equates `IsLocalRing.depth` over R/I with that over R.
This package is needed because the quotient local-ring and quotient module instances
are not inferable from the hypotheses in the pinned Mathlib.

Dependencies used: `Sheaf.RingTheory.Depth`, declarations `Ideal.depth` and
`IsLocalRing.depth`; Mathlib `IsNoetherianRing`, `Ideal`, `maximalIdeal`, and
`Ideal.Quotient.mk`.

Edge cases checked: `M = 0` is allowed (the depth definition gives infinity when
`IM = M`); `I = ⊥` and `I = maximalIdeal R` are allowed when their hypotheses hold;
the empty regular sequence is included by `Ideal.depth`; no characteristic or
nontriviality assumption is introduced.

Searches made: `msearch.py C1 lem-weil-pbc-depth-over-quotient-ring leanfinder
"depth of module killed by ideal over quotient ring"` (no exact project declaration);
`msearch.py ... loogle "Ideal.depth, IsLocalRing.depth, quotient depth"` (only
pinned `Sheaf.RingTheory.Depth` definitions); `msearch.py ... grep "depth.*quotient"
Mathlib/RingTheory` (no theorem matching this statement); `rg -n "depth.*quotient"
WeilConjectures` (no declaration); `rg -n "depth_over_quotient_ring" lean/Sheaf`
(found no prior target declaration). The existing `Sheaf.RingTheory.Depth` dependency
was read in full and used directly.

No `STATEMENT-DISPUTED` issue.

## Earlier second reading (a previous round; superseded)

The node's local-ring, ideal-containment, finite-module, annihilation, and quotient
action clauses are each present as explicit binders. The equality is stated using
the dependency's `IsLocalRing.depth` on both rings. The existential quotient local
instance and explicit quotient finite-module structure make all Lean objects
well-typed while expressing the node's assertion that these structures are induced
by the quotient construction.

## Second reading by C1

The node introduces a Noetherian commutative local ring `(R, m)`, an ideal `I ⊆ m`, and a finite R-module `M` annihilated by `I`, with the induced finite quotient-module action. The Lean binders `(R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]`, `(I : Ideal R) (hI : I ≤ maximalIdeal R)`, and `(M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]` render these objects and hypotheses. `[Module (R ⧸ I) M]`, `[Module.Finite (R ⧸ I) M]`, `hsmul`, and `hIM` render the induced quotient action, its finiteness, and annihilation. The existential `hQ : IsLocalRing (R ⧸ I)` renders quotient locality; the first conjunct equates the two depths for M, and the second conjunct explicitly renders the node's in-particular case `M = R ⧸ I`.

The source place is Stacks Algebra, Tag 0AUK, applied to the quotient map. The empty regular sequence and `M = 0` remain covered by `Ideal.depth`; `I = ⊥` and `I = maximalIdeal R` are permitted when `hI` holds; no characteristic, nontriviality, or universe restriction was added. Searches in the project, Mathlib, and slopmaster2 found no existing depth-over-quotient declaration; the existing `Sheaf.RingTheory.Depth` declaration is used directly. The previous module omitted the explicit quotient-ring special case from the node's conclusion; I changed the conclusion to a conjunction containing both equalities, updated its docstring, and synchronized the node's `lean.statement`. The corrected file compiles cleanly with `scompile.py`.

## Reviewer fix (R-dqr0939, stage 2)

The delivered statement took an arbitrary `[Module (R ⧸ I) M]` with a compatibility
equation `hsmul`, an extra hypothesis `[Module.Finite (R ⧸ I) M]` (a consequence in the
node, not a hypothesis), a redundant `hIM`, and packaged the locality of `R ⧸ I` as an
existential `∃ hQ`. Restated: `hIM : Module.IsTorsionBySet R M I` (IM = 0), the R/I-action is
Mathlib's `hIM.module` ((r mod I)·m = r·m, `Module.IsTorsionBySet.mk_smul`), finiteness over
R/I is derived by `Module.Finite.of_restrictScalars_finite`, and `R ⧸ I` is local by
`IsLocalRing.of_surjective'` with nontriviality from `I ≤ m` (as landed
`quotient_complete_local`). Conclusion unchanged: both equalities of
`IsLocalRing.depth` (def-weil-pbc-depth). Docstring now carries the node's proof.

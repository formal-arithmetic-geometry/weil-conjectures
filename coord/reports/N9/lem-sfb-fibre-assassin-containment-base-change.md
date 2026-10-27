## Worker report

The module `Sheaf.AlgebraicGeometry.FibreAssassinContainmentBaseChange` states
`AlgebraicGeometry.Scheme.Modules.associatedPoints_fiber_subset_open_iff_baseChange`.
Its only theorem proof is `sorry`. It introduces no definitions and changes only
`lean` in the item JSON. The accepted stage-1 statement and proof split are preserved.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 05KQ,
`lemma-base-change-assassin-in-U`, statement and proof (lines 7025–7052).
The source gives exactly this equivalence under arbitrary scheme base change.
The current `coord/brief-stage2.md` §0 explicitly permits this stage-2 handoff:
Q128's stage-1 review is not a prohibition on adding the Lean statement.
`coord/queue.tsv` lists the item in stage 2; there is no repair note for it and
no existing Lean attachment. The inherited BLOCKED ending concerned an unchanged
stage-1 delivery, not the statement delivery supplied here.

Hypothesis and clause correspondence:

- Schemes `X`, `S`, `S'` are `{X S S' : Scheme.{u}}`, with `u` explicitly declared.
- The morphism is `(f : X ⟶ S)` and local finite type is `[LocallyOfFiniteType f]`.
  No quasi-compactness, finite presentation, separatedness or base Noetherianity is added.
- The module is `(F : X.Modules)`. The hypothesis
  `(hF : F.IsQuasiCoherentFiniteType)` uses the dependency's conjunction of
  `SheafOfModules.IsQuasicoherent F` and `SheafOfModules.IsFiniteType F`.
  Finite presentation/coherence is not substituted for finite type.
- The open subscheme is represented by `(U : X.Opens)`: its canonical restricted
  scheme has the specified underlying open set. This allows every open subscheme
  of the source statement, including the empty and total opens.
- The arbitrary base change is `(h : S' ⟶ S)`, with no property instance on `h`.
- `X'` is the chosen categorical `pullback f h`; `h_X` is `pullback.fst f h`,
  and its structure map `f'` is `pullback.snd f h`.
- `F'` is exactly `((tensorPullback (pullback.fst f h)).obj F)`.
  This is the existing sheaf tensor pullback, not Mathlib's unrelated `Modules.pullback`.
- `(s' : S')` is arbitrary and the downstairs point `s` is written `h s'`.
  The source defines `s` as this image, so no additional point or equality is needed.
- `X_s` is `f.fiber (h s')` and its projection is `f.fiberι (h s')`.
  Thus `F_s` is `((tensorPullback (f.fiberι (h s'))).obj F)`.
- The first side of the equivalence is `associatedPoints` of this `F_s`, contained
  in `(f.fiberι (h s')) ⁻¹' (U : Set X)`, exactly the point set of `U_s`.
- `X'_{s'}` is `(pullback.snd f h).fiber s'`; its projection into `X'` is
  `(pullback.snd f h).fiberι s'`. Applying `tensorPullback` of this projection
  to `F'` gives precisely the source's `F'_{s'}`.
- The second side uses `associatedPoints` of that iterated pullback and contains
  it in `((pullback.snd f h).fiberι s') ⁻¹'
  ((pullback.fst f h) ⁻¹' (U : Set X))`. The inner inverse image is `U'`,
  the outer inverse image is its fibre `U'_{s'}`.
- `↔` preserves both directions of the asserted equivalence. There is no auxiliary
  comparison hypothesis, arbitrary map, chosen module isomorphism, or extra conclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion`; `U : X.Opens` uses the canonical open subscheme.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the node's scheme
  base-change convention is `pullback f h`, with its standard `fst`/`snd` projections.
  `moduleBaseChange` concerns modules over varying `Over S` objects, so here the
  direct recorded `tensorPullback` is the correct expression for `F'`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: publicly exposes the
  upstream `AlgebraicGeometry.Scheme.Modules.tensorPullback`. Its construction was
  read in `WeilConjectures.AlgebraicGeometry.TensorPullback`: inverse image followed
  by change of rings and sheafification, with actual data.
- `Sheaf.AlgebraicGeometry.RelativeAssassin`:
  `AlgebraicGeometry.Scheme.Modules.associatedPoints` and `relativeAssassin`.
  The former is exactly the associated-point definition required in the conclusion.

The proof-only imports follow the accepted split: `Mathlib.AlgebraicGeometry.Fiber`
(`Scheme.Hom.fiber`, `fiberι`, `fiberHomeo`),
`Sheaf.AlgebraicGeometry.RelativeAssassinBaseChange`
(`Scheme.Modules.relativeAssassin_baseChange_iff`),
`Mathlib.RingTheory.TensorProduct.Nontrivial`
(`Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain`),
`Mathlib.RingTheory.Ideal.MinimalPrime.Basic` (`Ideal.nonempty_minimalPrimes`),
and `Mathlib.RingTheory.Spectrum.Prime.Topology`
(`PrimeSpectrum.zeroLocus_minimalPrimes`). The fibre API is already publicly exposed
by the relative-assassin dependency. The docstring writes all four accepted proof
steps, including choosing a residual generic lift for the reverse implication.

Edge cases checked mathematically before writing:

- `F = 0`: both fibre pullbacks are zero and have empty associated-point sets.
- An empty downstairs fibre remains empty under residue-field extension, so both
  containments are vacuous. If `S'` is empty there is no `s'`, as in the source.
- `U = ⊤`: both inverse-image opens are total; both containments hold.
- `U = ⊥`: the assertion is equivalence of emptiness of the fibre associated-point
  sets. A residual tensor of field extensions is nonzero, and a minimal prime gives
  the generic lift needed for reflection; this does not claim every lift is associated.
- Identity base change and arbitrary transcendental residue-field extensions are
  included. No characteristic, nonemptiness, or finite degree is imposed.

Searches actually run using
`/home/ubuntu/weil-launcher-all/batch2/msearch.py N9
lem-sfb-fibre-assassin-containment-base-change`:

- LeanFinder: `Associated points of a fibre are contained in an open subset if and
  only if they are contained after arbitrary base change` — eight hits, concerning
  generalizing maps, open inverse images and restrictions; no associated-point
  containment theorem.
- Loogle: `associatedPrimes, AlgebraicGeometry.Scheme.Hom.fiber` — zero hits.
- Mathlib grep: `associatedPoints|relativeAssassin|assassin`, restricted to
  `AlgebraicGeometry` — zero hits.
- LeanSearch: `Associated points of a scheme fibre contained in an open subset are
  preserved and reflected under arbitrary base change` — eight hits concerning
  universal closedness, open-subscheme stalks and stability of morphism properties;
  none states this equivalence.
- `rg` across project `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `associatedPoints`, `relativeAssassin` and assassin/base-change containment names
  found the recorded definitions, the relative-assassin base-change theorem and
  different associated-point results; none states Tag 05KQ.
- `grep -rn` for the exact item id in `lean/WeilConjectures` returned no match.
- `rg` for the proposed declaration name in `dag/lean_names_upstream.json`, Mathlib,
  `lean/WeilConjectures` and `lean/Sheaf` returned no match.

No statement correction, new node, dependency repair, or disputed statement is needed.

Validation: the prescribed `scompile.py` compiled the file as both sandbox and
library modules, with no errors or warnings (4.7 and 5.7 seconds respectively).
Every binder and universe is explicit; the file starts with `module`, uses public
imports for statement dependencies, and contains no diagnostic commands.

## Second reading by N9

A separate rereading in this worker session compared the finished Lean signature
with the live node and the full statement of 05KQ. No second agent was started,
as the dispatch brief explicitly forbids doing so; independent maintainer review
remains the external review of this delivery.

Checked the finite-type hypothesis against the actual definition: `hF` retains
both quasi-coherence and finite type. Checked the order of both pullbacks: first
`h_X` pulls `F` to `X'`, then the upstairs fibre inclusion pulls it to `X'_{s'}`.
The downstairs fibre is over `h s'`, rather than a free unrelated point. Checked
that the outer preimage upstairs uses that same fibre projection and the inner
preimage uses `h_X`; these are exactly `U'_{s'}`. Both conclusions are subset
statements about the recorded stalk-associated-point notion, connected by an iff.
No hidden flatness instance is required for `h`. No mismatch was found and no
statement change was made after this reading. The JSON signature was extracted
verbatim from the theorem text before `:=`.

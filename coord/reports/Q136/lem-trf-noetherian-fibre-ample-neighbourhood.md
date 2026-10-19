## Worker report

The module `Sheaf.AlgebraicGeometry.NoetherianFibreAmpleNeighbourhood` states
`AlgebraicGeometry.Scheme.Modules.exists_affine_isAmple_of_fiber_of_noetherian`.
Its only proof is `sorry`; it defines no new notion. The theorem follows Stacks Project,
Cohomology of Schemes, Tag 0D2N (`coherent.tex`, lemma-ample-in-neighbourhood,
lines 6090–6154), with an affine open refinement. No statement correction is needed.

Clause-by-clause reading:

- Schemes Z and S and their morphism f: `{Z S : Scheme.{u}} (f : Z ⟶ S)`.
- Properness: `[IsProper f]`.
- The base is Noetherian in the node's specified sense:
  `[IsLocallyNoetherian S] [CompactSpace S]`.
- An invertible O_Z-module: `(L : Z.Modules) [L.IsInvertible]`.
- A point of the base: `(s : S)`.
- The scheme-theoretic fibre and its canonical projection are `f.fiber s` and
  `f.fiberι s`, the recorded Mathlib fibre construction.
- Pullback to the fibre uses `(tensorPullback (f.fiberι s)).obj L`, exactly the
  tensor-formula pullback in the dependency record.
- Fibre ampleness is `hL : @IsAmple (f.fiber s) ... ...`, using the recorded absolute
  ampleness predicate, not the separate projective-over-a-field predicate.
- Existence of an open neighbourhood is `∃ V : S.Opens, s ∈ V ∧ ...`.
- Affineness of that neighbourhood is `IsAffineOpen V`.
- Absolute ampleness on the inverse image is
  `@IsAmple (f ⁻¹ᵁ V).toScheme ((tensorPullback (f ⁻¹ᵁ V).ι).obj L) ...`.
  The inclusion of this actual open subscheme is the restriction map.

Both explicit final arguments of `@IsAmple` are the invertibility witness
`((invertible_pullback_tensor g).1 L).2`. They are theorem applications, not additional
assumptions or new definitions. Invertibility witnesses are proofs of a proposition.
This avoids silently requiring an instance on tensor pullback that the API does not register.
All variables and the universe `u` are explicit, and `autoImplicit` is false.

Dependency declarations used (their full signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.TensorPullback`:
  `AlgebraicGeometry.Scheme.Modules.tensorPullback`; current server source read via
  `scompile.py --source`, since this migrated module is absent from the older checkout.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (no Hausdorff condition).
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` and `Scheme.Hom.fiberι`.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple`; current server source read via
  `scompile.py --source`.
- `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`:
  `AlgebraicGeometry.Scheme.Modules.invertible_pullback_tensor`; current server source read
  via `scompile.py --source`, providing the already recorded proof-dependency interface.

The module imports recorded proof-dependency modules as nonpublic imports, except the
pullback/tensor theorem which appears in the public signature and is therefore public.
The following proof nodes currently have neither a Lean module nor a Mathlib match and
so supply no import: `lem-trf-ample-fibre-section-lifting`,
`lem-trf-projective-bundle-quotient-geometry`, and
`lem-trf-proper-finite-fibre-finite-near`. They are proof prerequisites only, and none is
needed to type this statement. The docstring retains all nine proof steps, including
both proper-image shrinkings, the high positive-power choice, and the affine-chart test.

Edge cases checked mathematically:

- An empty base has no point s; the statement requires none to exist.
- Z or the fibre may be empty. No `Nonempty` assumption is introduced. For an empty
  fibre, closedness of the proper image gives an affine neighbourhood with empty inverse
  image, where the recorded ampleness condition holds vacuously.
- Nonclosed points s are allowed; the fibre is over the actual residue field at s.
- No irreducibility, reducedness, field characteristic, relative dimension, or
  nontriviality of the module is assumed.
- The conclusion is absolute ampleness on the inverse-image scheme, not merely relative
  ampleness and not projectivity. Refining to an affine neighbourhood gives exactly the
  node's conclusion from the source.
- No new tensor exponent is part of the theorem statement, so no zero-exponent case is
  silently excluded; positive powers occur only in the proof of the ampleness criterion.

Searches for an existing declaration:

- `msearch.py` LeanFinder: “For a proper morphism over a Noetherian scheme a line bundle
  ample on one fibre is ample over an affine neighbourhood of the base point”. Eight
  hits concern target-affine locality, affine morphisms, or properness of Proj; none
  states the ampleness neighbourhood lemma.
- `msearch.py` LeanSearch: “A line bundle ample on a fibre of a proper morphism over a
  Noetherian scheme is ample over an affine neighbourhood”. Eight hits concern affine
  fibres, affine locality, and locally Noetherian schemes; no matching statement.
- `msearch.py` Loogle: `"IsProper", "IsAmple"` returned zero hits.
- `msearch.py` grep: `\b(IsAmple|ample|ampleness)\b` in `AlgebraicGeometry` returned zero
  Mathlib hits.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf` for ampleness together
  with fibre/fiber/neighbourhood found no exact theorem. The existing
  `ProperFibrewiseAmpleProjective` concerns positive geometric-fibre degrees everywhere
  and a global projective conclusion, with different hypotheses.
- Exact item-id search in upstream returned no hits; exact proposed declaration-name
  search in `dag/lean_names_upstream.json`, upstream and project sources returned no hits.

Validation: `scompile.py Q136 lem-trf-noetherian-fibre-ample-neighbourhood` compiled
both the sandbox and exact library-path module cleanly on the server (2.7 s and 2.8 s).
No warnings or errors remain. The node copy differs from the base only in `lean`, and
its `lean.statement` is byte-for-byte the theorem signature in the module.

No new nodes, dependency repairs, or statement faults were needed.

## Second reading by Q136

Independent maintainer second reader, 2026-10-18, reviewing immutable commit
`57ba40ab758b9836d451fa4ffa8bbcb9e00f2afb`. I did not write or previously second-read
this delivery. This section replaces the original acknowledgement that there had been
no independent worker reading. I read the item, all eight statement-dependency records,
the delivered module and both docstrings, the report, Stacks 0D2N, and the exact
underlying declarations. No mathematical mismatch was found.

Clause-by-clause verdicts:

- `{Z S : Scheme.{u}} (f : Z ⟶ S)` introduces exactly the two schemes and their
  morphism. `Scheme` and `Scheme.Hom` are the recorded Mathlib notions. Match.
- `[IsProper f]` is precisely properness: separated, universally closed, locally
  finite type; universal closedness supplies quasi-compactness, hence finite type.
  It does not require the base to be separated or either scheme to be nonempty. Match.
- `[IsLocallyNoetherian S] [CompactSpace S]` is exactly the stated Noetherian
  assumption. The locally Noetherian class is equivalent to the affine-cover
  presentation, and CompactSpace imposes no Hausdorff condition. Match.
- `(L : Z.Modules) [L.IsInvertible]` is the recorded locally free rank-one module
  notion, and `(s : S)` is an arbitrary point, including a nonclosed point. Match.
- `f.fiber s` is the pullback along `S.fromSpecResidueField s`, with projection
  `f.fiberι s`. Thus `(tensorPullback (f.fiberι s)).obj L` is the actual tensor-formula
  module pullback to the scheme-theoretic fibre. Match.
- `hL : @IsAmple ...` uses the recorded absolute predicate: quasi-compactness and
  affine nonvanishing neighbourhoods from sections of positive tensor powers.
  It is not the distinct proper-over-a-field very-ample-power predicate. Match.
- `∃ V : S.Opens, s ∈ V ∧ IsAffineOpen V ∧ ...` gives exactly an affine open
  neighbourhood of the specified point. Match.
- The final `@IsAmple` concerns `(f ⁻¹ᵁ V).toScheme`, and its module is pulled back
  along the actual open inclusion `(f ⁻¹ᵁ V).ι`. This is restriction to the inverse
  image, with absolute ampleness as required. Match.
- Both explicit invertibility arguments are `((invertible_pullback_tensor g).1 L).2`.
  I checked the full current declaration: its first conjunct gives invertibility of
  the tensor pullback of any invertible module. These are proofs in Prop, impose no
  new hypothesis, and select no arbitrary module or map. Match.

Dependency audit: the repaired `def-pc-module-pullback` record points to
`Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`; I read that module too.
It publicly imports the same upstream `tensorPullback` used here and adds its uniquely
section-normalized adjunction, rather than introducing another pullback. This theorem
uses the underlying functor only, so no adjunction choice or interface repair is needed.
The current TensorPullback, Ample and InvertiblePullbackTensor sources were also read
through `scompile.py --source` to resolve sources absent from the older checkout.
All other notions use the dependency records' declarations. No new helper, new node,
unusable statement dependency, or source-based statement correction is needed. The
three unformalized proof-only nodes named in the worker report are not missing objects
in this signature; their future proofs are not stage-2 typing prerequisites.

Source and proof audit: `coherent.tex:6090–6154`, Tag 0D2N, assumes a proper map,
Noetherian base and invertible module ample on the fibre. Its conclusion is relative
ampleness near the point; the node refines to an affine neighbourhood, where the
standard affine projective charts in its nine-step proof give absolute ampleness.
The module docstring carries all nine node steps, including the empty-fibre case,
arbitrarily large positive exponent, both proper-image shrinkings, finite-locus
argument and final affine nonvanishing cover. The source and blueprint markers are
present in both docstrings. The delivered file introduces no definition and contains
one theorem, whose entire proof is `by sorry`.

Edge cases: empty base makes the point binder uninhabited; empty source and empty fibre
are allowed, with the proper-image complement yielding an empty inverse image. The
empty scheme is quasi-compact and its pointwise ampleness criterion is vacuous. There
is no Nonempty, reducedness, irreducibility, characteristic, dimension or field
assumption. No tensor exponent is quantified in the theorem; positivity belongs to
the existing ampleness definition. The arbitrary universe `u` consistently supports
schemes, modules, fibres and opens. No universe equality or independent undersized test
universe was added, and `autoImplicit false` leaves no unbound variables.

Search audit: I independently searched Mathlib algebraic geometry and both project
and upstream algebraic-geometry trees for IsAmple/ampleness and fibre/fiber/neighbourhood
variants. No existing copy of this theorem was found. The other IsAmple notion in
Modules/VeryAmple is over a field and is different. ProperFibrewiseAmpleProjective has
all-fibre degree hypotheses and a different conclusion. The worker's recorded
LeanFinder, LeanSearch, Loogle and grep searches are real searches with results.

Record and route checks: `lean.statement` equals the file's theorem signature byte
for byte. The immutable commit changes the item node only by adding `lean`, and the
snapshot module, node and report match that commit. The namespace, import families
and all line lengths satisfy the stage-2 conventions. None of the statement or proof
dependencies occurs in the route-pivot dropped list. There is no route-pivot repair
note for this item and no enhanced, dg, model-category or pro-etale substitute.

Compiler reproduction on the immutable snapshot:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q136 lem-trf-noetherian-fibre-ample-neighbourhood snapshot/lean/Sheaf/AlgebraicGeometry/NoetherianFibreAmpleNeighbourhood.lean`

Exit code 0; sandbox `Sheaf/Stage2/Sandbox0.lean` passed in 31.0 seconds and exact library
module `Sheaf/AlgebraicGeometry/NoetherianFibreAmpleNeighbourhood.lean` passed in 50.7
seconds. Both emitted no diagnostics. The installed wrapper currently invokes the
server overlay, which reports private artifacts under
`/dev/shm/nt-tmp/nt-local-compile-uyl8lu57/.lbuild`; this is the prescribed wrapper's
actual behavior, not a direct compiler or SSH invocation by the reviewer. No global
build, live Lean write, repository mutation or delivery action was performed.

Finding and repair: H11, the original section expressly stated that no independent
reading took place and did not map the clauses itself. This independent reading now
supplies that missing record. The complete replacement report retains the Worker
report and the prior repair note; no Lean or JSON change is required.

## Repair note

The returned delivery contained no substantive statement, source, or compile finding; its
`--apply-fixes` packet was rejected solely because it named the report with a full
`coord/reports/Q136/...` path. I retained the reviewed signature and refreshed the stale
Lean-record date to 2026-10-18, the UTC date of this repair, as required by the stage-2
record format. No mathematical clause or dependency changed.

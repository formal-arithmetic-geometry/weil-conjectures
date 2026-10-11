## Worker report

Module: `Sheaf.AlgebraicGeometry.IsFiniteLocallyFreeOfRankRelativeDifferentials`.
Declaration: `AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials`.
This states the whole node for any morphism smooth of constant relative dimension `d`.
Its only proof is `sorry`, as required in stage 2. No definitions or auxiliary results are added.

Hypothesis and clause correspondence:

- Schemes X and S: `{X S : Scheme.{u}}`, with `universe u` explicitly declared.
- The morphism f:X→S: `(f : X ⟶ S)`, Mathlib's actual scheme morphisms.
- Nonnegative integer d: `(d : ℕ)`. This covers exactly the nonnegative integers,
  includes zero, and introduces no finiteness, characteristic, or nonemptiness restriction.
- Smooth of relative dimension d: `[SmoothOfRelativeDimension d f]`. This is precisely
  the dependency's recorded Mathlib class, defined by standard smooth affine charts of
  dimension d at every source point. Its `smooth` theorem implies `Smooth f`, so a separate
  smoothness binder would be redundant. The dependency node records the identification
  with pointwise fibre dimension via Stacks 02G1/02G2.
- The O_X-module Omega^1_{X/S} with the specified affine descriptions:
  `f.relativeDifferentials`. This is the existing definition, not a fresh arbitrary module.
  `relativeDifferentialsSpecIso` identifies its affine restriction with the associated
  sheaf of `CommRingCat.KaehlerDifferential φ`; `relativeDifferentialsRestrictIso` and
  `relativeDifferentialsCompIso` give restriction to source and target open charts.
  The ring differential module is the recorded `KaehlerDifferential` (the same object
  bundled for a ring map as `CommRingCat.KaehlerDifferential`).
- Conclusion, locally free of constant rank d:
  `SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
  (R := X.ringCatSheaf) f.relativeDifferentials d`. The rank is d everywhere,
  not just locally constant or unspecified. The dependency's class is over the Zariski
  topology of X; `Scheme.Modules.IsFiniteLocallyFreeOfRank.exists_restrict_iso_free`
  and `isFiniteLocallyFreeOfRank_of_restrict_iso_free` identify it with exactly the
  open-cover/free-rank-d formulation of the node.

Dependency declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme`; the locally ringed space/local affine structure
  and the complete Hom definition were inspected.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.SmoothOfRelativeDimension`,
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`; the full chart signature and
  `SmoothOfRelativeDimension.smooth` were read.
- `def-weil-pbc-kahler-differentials`: `KaehlerDifferential`, `KaehlerDifferential.D`,
  `KaehlerDifferential.linearMapEquivDerivation`, `Mathlib.RingTheory.Kaehler.Basic`;
  the quotient definition and universal derivation/equivalence signatures were read.
  Used through the existing relative differential construction and affine comparison,
  rather than by duplicating the ring module or its universal property.
- `def-amb-finite-locally-free-module`: `SheafOfModules.IsFiniteLocallyFreeOfRank`,
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`; the class
  and docstring were read. Its finite generating sets are equivalent to `Fin d`.
- `def-sc-relative-differential-sheaf`: `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`,
  `WeilConjectures.AlgebraicGeometry.Modules.Differentials`; definition, docstring,
  and the affine/restriction comparison signatures were read. This already landed node
  is added to stmt_deps under STMT_DEPS MAY GAIN LANDED NODES (brief-stage2 §5).
  It is not a new node, and its own record/file is not modified.

The single import is `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
this exposes all the dependencies above, including the locally free class used directly.
All universes/variables are bound explicitly; auto-bound implicits are not used.

Source checked: [Stacks Project, Lemma 29.35.12, Tag 02G1]
(https://stacks.math.columbia.edu/tag/02G1).
The local checkout has no `literature/stacks-project/morphisms.tex`, so the source was read
on the official Stacks website. It gives finite local freeness with rank equal to the
pointwise fibre dimension. The constant-d specialization is the node's exact statement.
The docstring includes both DAG proof steps and their dependency ids: affine freeness
of rank equal to fibre dimension, then associated-sheaf trivializations on a covering.

Edge cases checked: d=0 gives the zero differential module for etale morphisms and the
rank-zero conclusion. For empty X the smooth relative dimension condition and covering
condition are vacuous for every d, which is correct. Empty S forces empty X. No nontrivial
ring hypothesis is added, so empty affine charts from the zero ring are allowed.
Disconnected X is allowed, with rank fixed at the same d on every component; no
connectedness, properness, separatedness, base field or characteristic assumption is added.
The arbitrary universe u includes all schemes under the dependency's usual encoding.

Searches made (2026-10-11):

- `msearch.py leanfinder`: "Relative differential sheaf of a smooth scheme morphism is
  locally free of rank its relative dimension". Eight hits: affine algebra freeness/rank
  and the smooth relative dimension class; no scheme differential sheaf theorem.
- `msearch.py loogle`: "KaehlerDifferential, Module.Free". Seven hits, including
  `Algebra.IsStandardSmooth.free_kaehlerDifferential`; all are ring/algebra statements.
- `msearch.py leansearch`: "sheaf of relative differentials of smooth scheme morphism
  is finite locally free". Service unavailable (Internal Server Error), recorded as such.
- `msearch.py grep`: "relativeDifferentials|finite locally free" in AlgebraicGeometry.
  Zero hits in Mathlib. Earlier local rg also inspected sheaf differential/free predicates.
- `rg` of the source's `WeilConjectures` and the project's `lean/Sheaf` for
  `relativeDifferentials`, `IsFiniteLocallyFree`, and
  `relativeDifferentials.*[Ff]ree|[Ff]ree.*relativeDifferentials`: source has the differential
  definition and the dimension-one invertibility result. Projective space has a rank-d
  theorem restricted to projective space; it does not state this node for arbitrary f.
  The project has the diagonal conormal comparison but no theorem for this node.
- `rg` for the exact item id in source `WeilConjectures`: no hits.
- `rg` of dag/nodes for relativeDifferentials located the already recorded
  `def-sc-relative-differential-sheaf`; reused it instead of creating a duplicate notion.
- The proposed full name was checked against the source/project search results:
  the projective-space theorem has a different namespace; no name conflict exists.

No statement correction, dependency module, new node, or disputed statement is needed.
Server compilation via `scompile.py` succeeded, exit code 0, in 2.2 seconds, without warnings.

## Second reading by M1

The node introduces a morphism of schemes `f : X ⟶ S`, schemes `X S : Scheme.{u}`,
and an integer `d ≥ 0`; it assumes that `f` is smooth of relative dimension `d`.
The Lean binders `{X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ)
[SmoothOfRelativeDimension d f]` render exactly these objects and hypothesis.  The
`ℕ` binder is precisely the node's nonnegative integer and imposes no extra
assumption.  The node's relative differential sheaf, including its affine
Kähler-differential description, is rendered by the existing declaration
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials` and is cited through
`def-sc-relative-differential-sheaf`; the theorem uses `f.relativeDifferentials`.
The conclusion is rendered verbatim by
`SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
(R := X.ringCatSheaf) f.relativeDifferentials d`, so it asserts finite local
freeness with constant rank `d`, with the same quantifier order and no additional
clause.  The declaration is in the namespace
`AlgebraicGeometry.Scheme.Hom`, and all universe variables are explicit.

I checked the dependency declarations for schemes, smooth relative dimension,
Kähler differentials, finite locally free modules, and relative differentials.
No dependency was unusable and no duplicate definition exists in Mathlib,
`WeilConjectures`, or the project.  Searches used LeanFinder, Loogle,
LeanSearch, and `rg`/grep; they found only affine algebra results and the
already-landed relative-differentials definition.  The LeanSearch service was
unavailable, as recorded in the worker report.

Edge cases remain covered: `d = 0`, empty `X` (vacuous smoothness and cover),
empty `S`, disconnected schemes, arbitrary characteristic, and every universe
`u`.  No extra noetherian, separated, finite-type, connectedness, field, or
nonemptiness assumption appears.  No mismatch was found. The worker already added the citation to
`def-sc-relative-differential-sheaf` for the `f.relativeDifferentials` term;
this is permitted reuse of a landed node. The Lean and node required no change.  No statement correction, new node, or
dependency module was needed.  Compilation with `scompile.py` passed without
errors or warnings.

Independent source check: Stacks Tag 02G1 assumes only a smooth morphism
of schemes and concludes finite local freeness with pointwise rank equal to
the fibre dimension. There is no ambient base-field or Noetherian assumption.
Specializing to constant relative dimension gives exactly this node. I read
`SmoothOfRelativeDimension`'s affine-chart field and its `smooth` implication,
`IsFiniteLocallyFreeOfRank`'s generator-index equivalence with `Fin r`, and
both directions of the scheme open-cover/free-module characterization.
I also read the affine and source/target restriction comparison signatures
of `relativeDifferentials`. The presheaf-inverse-image construction's TODO
does not obstruct this node: its proved affine/restriction comparisons already
identify the module with the affine characterization used here.

My independent searches (2026-10-11): LeanFinder query "Zariski locally
trivial cotangent sheaf for a smooth map of schemes with fixed dimension"
returned eight affine smoothness/rank results, no matching scheme theorem;
Loogle query "KaehlerDifferential, LinearEquiv" returned twelve universal-property
and polynomial results, no matching theorem. The msearch grep query
"cotangent|differentials" in AlgebraicGeometry returned four Mathlib import
or ideal-cotangent hits, none matching. Local `rg` in `WeilConjectures` and
`lean/Sheaf` found the dimension-one invertibility theorem and the projective-
space rank theorem only; the latter's signature applies to the structural
morphism of projective space, not arbitrary smooth morphisms.
The node's `lean.statement` equals the file signature verbatim (excluding `:=`).
The only proof is `by sorry`, no definition was introduced, both source
docstrings and both proof steps are present, and every Lean line is at most
100 characters. Second reading changed only this report.

## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceGenericFreeness` states
`AlgebraicGeometry.AlgebraicSpace.exists_generic_free_open`, with its sole proof
`sorry`. Its docstring carries all four steps of the DAG proof. The mathematical
statement, proof and proof dependencies of the node are unchanged. Two already
landed definition nodes are added to stmt_deps: scheme-chart restriction and module
support. No definition, dependency repair, or statement correction is needed.

Hypothesis and conclusion correspondence:

- The base scheme is `{S : Scheme.{u}}`, and the space is `X : AlgebraicSpace S`.
  This uses the recorded fppf-sheaf definition, representable diagonal and atlas,
  and the small étale ringed site, without choosing an atlas.
- Locally Noetherian on all étale scheme charts is `hln`, quantifying over every
  `T : X.EtaleSite` and applying `IsLocallyNoetherian` to its underlying scheme.
- Quasi-compactness is `hqc : CompactSpace (Point X.obj.obj)` in the atlas topology.
- Quasi-separatedness is exactly the scheme-test quasi-compactness of the diagonal:
  `hqs : IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
  (prod.lift (𝟙 X.obj.obj) (𝟙 X.obj.obj))`. This keeps the node's relative diagonal
  over S; it does not impose separatedness or a condition on S.
- Reducedness is `hred`, requiring `IsReduced` on every étale chart. Scheme
  reducedness is equivalent to reduced local rings and does not require normality.
- Nonemptiness and irreducibility are both in `hirr : IrreducibleSpace
  (Point X.obj.obj)`; Mathlib's class includes `toNonempty` explicitly.
- `F : X.Modules` is a module sheaf on the small étale structure ring.
  `[F.IsQuasicoherent]` is the recorded Mathlib local-presentation predicate.
- `hF` requires `RingedSpace.IsCoherent` on the canonical ordinary module
  `((X.schemeRestriction T).obj F)` for EVERY étale scheme chart. This is finite
  type with finite-type kernels, not merely quasi-coherent and finite type.
- Full geometric-stalk support is `hsupp : moduleSupport F = Set.univ`, using
  the existing nonzero-geometric-germ definition with the same point classes.
- The conclusion quantifies over `U : AlgebraicSpace S` and `j : U ⟶ X` with
  `IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left) j.hom.hom`. Thus U is
  an open subspace, presented by its inclusion rather than by a chosen subfunctor.
  Open immersions are monomorphisms, so no additional embedding axiom is needed.
- `hj : IsEtale j.hom.hom` is the étaleness proof needed to form the existing
  restriction functor. Every representable open immersion is étale, so this
  witness adds no mathematical restriction on the open subspace.
- `Nonempty (Point U.obj.obj)` asserts the open is nonempty.
- `r : ℕ` and `1 ≤ r` express the positive integer rank, with no dimension bound.
- `Nonempty ((pullback j hj).obj F ≅ (∏ᶜ fun _ : Fin r ↦
  SheafOfModules.unit U.structureSheaf))` is an actual module-sheaf isomorphism
  on U. Finite products of modules are canonically their finite direct sums.
  A single global isomorphism is asserted, not unrelated local trivializations.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`,
  `etaleForget`, `Modules`, `structureSheaf`, `IsRepresentableWith`, `IsEtale`,
  and `pullback`. These are the recorded algebraic-space dependency interface.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: the specialization
  of `SheafOfModules.IsQuasicoherent` to this site and its slice instances.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: public
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`. The latter definition was read:
  finite type and finite-type kernels of maps from finite free modules on opens.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`:
  `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace` on `Point`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction`:
  `AlgebraicGeometry.AlgebraicSpace.schemeRestriction`, canonical restriction to
  Zariski opens with the canonical regular-function comparison.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport`:
  `AlgebraicGeometry.AlgebraicSpace.moduleSupport`.

All recorded proof dependencies that have declarations are imported, privately:
`AlgebraicSpaceDenseSchemeOpen`, `SchemeZariskiEtaleQuasiCoherentEquivalence`,
Mathlib `FunctionField`, upstream `CoherentGenericLocalFreeModel`, and the public
Noetherian/Properties modules. Their signatures and source proof descriptions
were read. No import is omitted to avoid a cycle.

Source checked directly: `literature/stacks-project/spaces-cohomology.tex`,
`lemma-prepare-filter-irreducible`, especially its second proof paragraph: choose
a dense schematic open, shrink until free. Full support makes its rank positive.

Edge cases checked before writing: the empty space is excluded by irreducibility's
nonemptiness; the zero module cannot satisfy full support on a nonempty space;
rank zero would contradict any stalk on the open; arbitrary base schemes and all
characteristics remain allowed; no geometric irreducibility, properness, normality,
or global schematicness is assumed. Torsion coherent modules with full support,
and nonnormal integral spaces, are allowed: only generic freeness is concluded.
A reducible space or a nonreduced space is outside the stated hypotheses.

Searches actually run with msearch.py under group Q134/item:

- LeanFinder: "A coherent module with full support on a reduced irreducible
  Noetherian algebraic space is free of positive finite rank on a nonempty open".
  Eight hits: `Module.isOpen_freeLocus`, `Module.freeLocus`, rank-at-stalk
  results and scheme integrality. None states this algebraic-space result.
- Loogle: `"IsCoherent", "IsLocallyFree"`: zero hits.
- Mathlib grep: `AlgebraicSpace|generic.*free|free.*generic`, subdirectory
  `AlgebraicGeometry`: zero hits.
- LeanSearch: "A full-support coherent sheaf on an integral Noetherian algebraic
  space is free on a nonempty open": eight hits, including `SheafOfModules.free`
  and module free-locus statements. No exact theorem.
- `rg -n 'generic.*free|free.*generic|lem-sfb-space-generic-freeness'` in both
  `lean/WeilConjectures` and `lean/Sheaf`: scheme generic-free-neighbourhood and
  local-free-model results, ring generic freeness and the consumer
  `SpaceGenericMultipleEmbedding`; no algebraic-space generic-freeness theorem.
- `rg -n 'lem-sfb-space-generic-freeness' lean/WeilConjectures`: no hit.
- The existing support and scheme-restriction modules and their DAG nodes were
  opened rather than recreated.

Initial compilation diagnosed that `SheafOfModules.free` on this large site
needs a global sheafification instance not supplied by the existing interface.
The final statement uses the existing finite product, canonically the same finite
direct sum in module sheaves, so neither a new hypothesis nor an interface repair
is necessary.

No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q134

I reread the node and the final signature clause by clause; this is the worker's
self-check, with the independent maintainer review supplied by the dispatcher.
The dispatcher's explicit instruction forbids starting another agent.
The diagonal hypothesis retains scheme-test quasi-compactness; `hirr` includes
nonemptiness, while `hred` tests all charts. The coherence clause uses the full
finite-type-kernel predicate exposed by the recently repaired dependency, rather
than the weaker conjunction in its primary declaration. Support uses the landed
geometric-germ predicate. The conclusion is a single isomorphism on a nonempty
open subspace of positive finite rank; finite products equal finite sums here.
The étaleness witness only allows the existing restriction construction to be
applied to the open immersion. All variables, including universe u, are explicit,
and autoImplicit is disabled. No mathematical mismatch was found; the only change
from the first draft replaced the finite free constructor by the finite product
to avoid an unavailable sheafification instance. No source statement changed.

Validation: scompile.py compiled both the sandbox and named library module cleanly
(1.6 seconds each). deliver2.py --no-push passed server preflight and compilation,
printing `OK (dry run)` for commit 4777608b03f. Only the expected theorem proof is
postponed; no other warnings or errors remain.

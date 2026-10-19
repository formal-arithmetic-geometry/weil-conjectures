## Worker report

The item is stated by
`AlgebraicGeometry.AlgebraicSpace.isQuasicoherent_moduleDirectImage_of_quasiCompact_separated`
in `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward`. Its proof is `sorry`.
The natural-language proof in its docstring carries all four DAG steps.
The statement is unchanged; no statement dispute or correction is needed.

Clause-by-clause correspondence:

- A scheme S: `{S : Scheme.{u}}`, using `AlgebraicGeometry.Scheme` from
  `Mathlib.AlgebraicGeometry.Scheme` (def-pc-scheme).
- Algebraic spaces X and Y over S: `{X Y : AlgebraicSpace S}`, using
  `AlgebraicGeometry.AlgebraicSpace` from `Sheaf.AlgebraicGeometry.AlgebraicSpace`.
  Their morphism is `(f : X ⟶ Y)` in that full subcategory of fppf sheaves.
- Quasi-compactness: `hqc : IsQuasiCompactPresheafMap f.hom.hom`.
  Separatedness: `hsep : IsSeparatedPresheafMap f.hom.hom`.
  These are exactly the definitions in `Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal`
  recorded by lem-trf-space-qc-separated-etale-local: quasi-compact scheme atlases
  over each affine scheme test and closed-immersion representability of the diagonal.
- Any quasi-coherent module F on the small étale ringed site:
  `(F : X.Modules) [F.IsQuasicoherent]`. `Modules` uses the explicit regular-function
  structure sheaf of `AlgebraicSpace.lean`; the predicate is Mathlib's
  `SheafOfModules.IsQuasicoherent` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`, as recorded by
  def-trf-space-quasi-coherent-module. Its `QuasicoherentData` has a covering family
  and local presentations by arbitrary coproducts. The dependency repair below makes
  that exact existing predicate available, without assuming its missing instances.
- The conclusion `((moduleDirectImage f).obj F).IsQuasicoherent` says that f_*F
  is quasi-coherent on Y_et. `moduleDirectImage` is the recorded canonical functor
  from `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`.
  Its diagram consists of F(T) restricted along the actual regular-function map
  `moduleChartScalar`; the limit projections are linear over O_Y(V). Thus its
  O_Y action is the specified action from O_Y → f_*O_X, not an arbitrary module
  structure or a Zariski direct image. The already-landed definition node
  def-trf-space-etale-module-functors is added to stmt_deps explicitly.

Dependency sources and full signatures/docstrings were read. Stated proof dependencies
are imported non-publicly: the étale module restriction comparison, algebraic-space
fibre products, scheme Zariski/étale quasi-coherent equivalence, and Mathlib closed
immersion base-change stability. The atlas equalizer and scheme étale kernel nodes
have no Lean records, so no import is available for them; their exact roles remain
in the theorem's proof docstring. They are proof prerequisites, not missing notions
needed to state this item.

Sources checked directly: spaces-morphisms.tex, lemma-pushforward (03M9), including
all three proof paragraphs; spaces-properties.tex, equation-push-pull and following
étale pullback description; sites-modules.tex, definition-site-local (03DL), clause (6).
The source's qcqs theorem applies because a closed diagonal is quasi-compact.
The node deliberately restricts it to separated maps; this restriction is retained.

Edge cases checked before stating: empty X and empty base are allowed by the binders;
for empty Y any existing f has empty source. Identity maps, affine morphisms between
affine schemes, and closed immersions give the expected cases. The zero module and
infinite-generator presentations are included. There is no nonemptiness, no finiteness,
no noetherian hypothesis, and no separate equality of object/morphism/section universes.
The scheme/section universe remains u while the site object universe remains u+1.
The slice repair also covers empty chart schemes: its equivalent small étale site has
the same empty coverings and zero additive sheaves as the original slice.

Searches for an existing statement and helpers:

- msearch LeanFinder: "Direct image of a quasi coherent module on the small etale site
  under a quasi compact separated morphism of algebraic spaces is quasi coherent".
  Eight hits: scheme pushforward and Mathlib quasi-coherence predicates/data; none
  state the algebraic-space assertion.
- msearch Loogle: "AlgebraicSpace, IsQuasicoherent". Zero hits; AlgebraicSpace is
  unknown in the search index.
- msearch grep: `AlgebraicSpace|quasi.?coherent.*pushforward|pushforward.*quasi.?coherent`
  in AlgebraicGeometry. Two Tilde.lean hits, dealing with affine scheme pushforward.
- msearch LeanSearch: "Quasi compact separated morphism of algebraic spaces pushforward
  preserves quasi coherent modules on small etale sites". Eight hits: scheme
  pushforward and scheme quasi-separatedness; no algebraic-space theorem.
- rg in upstream WeilConjectures and side lean/Sheaf for the node id, algebraic spaces,
  quasi-coherent pushforward, and the proposed names: only scheme pushforward results
  upstream; the side project has the algebraic-space definitions and operations used
  here, but no quasi-coherent direct-image theorem. The upstream declaration index
  has no match for the node or theorem name. The proposed slice helper names and QCoh
  were absent from the algebraic-space modules; the scheme comparison module's
  smallEtaleModuleOverHasWeakSheafify and smallEtaleModuleOverWEqualsLocallyBijective
  apply to a different site and supply the model for the slice repair.

Compilation: the initial consumer failed on the missing slice HasWeakSheafify instance,
which justified the dependency repair. After repair, scompile.py compiled BOTH delivered
modules separately and the consumer against the sibling overlay, with no diagnostics.
The consumer compilation validates that the repaired interface supplies both input and
output quasi-coherence for arbitrary X,Y, with no added typeclass assumptions.

## Dependency modules

`def-trf-space-quasi-coherent-module`: the Mathlib match correctly gives the general
local-presentation notion, but its claimed one-line specialization to algebraic spaces
fails to elaborate in the intended section universe u: the slice HasWeakSheafify
and WEqualsLocallyBijective instances are not provided. Under §1(B),
`Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule` supplies two named supporting
instance theorems, with `sorry` proofs and source/proof docstrings. Each slice over an
étale scheme chart T is equivalent to T_et; its affine étale basis supplies small
sheafification and the usual locally bijective characterization. It defines
`AlgebraicGeometry.AlgebraicSpace.QCoh X` with real data as
`(SheafOfModules.isQuasicoherent X.structureSheaf).FullSubcategory`.
The general-site predicate is still the exact Mathlib declaration; there is no new
quasi-coherence definition. Only the dependency node's lean field is changed; its
mathlib_match, natural statement, status, and dependencies are retained. The three
module declarations belong to this definition node's interface. The two postponed
proofs establish the construction infrastructure, not additional assumptions on X.

Author self-check: reopened both modules and node copies after compilation. The target
has precisely the two geometric hypotheses and the quasi-coherent module hypothesis,
with the canonical module direct image in its conclusion. The dependency module uses
Mathlib's local presentation predicate and the existing small étale structure sheaf;
its QCoh abbreviation is a full subcategory, as required. No mathematical statement
was altered. Independent review is left to the maintainer as the dispatcher brief requires.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

Q135 states `AlgebraicGeometry.Scheme.Modules.exists_isFinitePresentation_neighbourhood_iff_etale_pullback`
in `Sheaf.AlgebraicGeometry.EtaleModuleFinitePresentationLocal`. The only theorem proof is
`sorry`; no definition or helper theorem is introduced. The node changes only in `lean`.

Hypothesis and clause audit against the node:

- The schemes are arbitrary `{X' X : Scheme.{u}}`, with explicit universe `u`.
- The morphism of schemes is `(g : X' ⟶ X)` and its étaleness is `[Etale g]`.
- Both marked points are retained as `(x' : X') (x : X)`, with `(_hg : g x' = x)`.
- The induced residue-field map is exactly Mathlib's `g.residueFieldMap x'`.
  `[IsIso (g.residueFieldMap x')]` requires that map to be an isomorphism, rather than
  merely assuming that the two fields are abstractly isomorphic. Its source is
  `X.residueField (g x')`, identified with `X.residueField x` by `_hg`.
- The module is `(M : X.Modules)` with `[M.IsQuasicoherent]`. No finite-type,
  coherence, Noetherian, separatedness, or quasi-compactness assumption is added.
- Finite presentation on some open neighbourhood of `x` is exactly
  `∃ U : X.Opens, x ∈ U ∧ (M.over U).IsFinitePresentation`.
- The reverse condition uses the actual recorded tensor pullback:
  `∃ U' : X'.Opens, x' ∈ U' ∧ (((tensorPullback g).obj M).over U').IsFinitePresentation`.
- The connective is `↔`, so both directions and independent choices of neighbourhood
  are present. The residue-field hypothesis is retained even though the proof does not use it.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale` for
  `def-weil-etale-morphism`; its affine-local ring-map definition and
  `Etale.iff_flat_and_formallyUnramified` match the node's notion.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` for `def-weil-residue-field`. The latter is the
  map induced by the local ring stalk map, with the direction κ(g(x')) → κ(x').
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` for `pqf-def-coherent`, publicly
  importing `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` and
  `Mathlib.AlgebraicGeometry.Modules.Sheaf`. Its recorded
  `Scheme.Modules.IsQuasiCoherentFiniteType` is a conjunction; this item only needs
  its first notion, the existing `SheafOfModules.IsQuasicoherent`. Using the whole
  conjunction would add a hypothesis absent from this item. The dependency's full
  module was read; no duplicate quasi-coherence notion or dependency repair is needed.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsFinitePresentation` for `def-weil-pbc-module-finite-type-presentation`.
  The recorded module `Generators` only defines the finite-type half; the finite-presentation
  module specified in its `mathlib_match` is explicitly imported here. The class is
  local existence of presentations with finitely many generators and relations.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback` for `def-pc-module-pullback`, retained by that
  module's public upstream import. The section-normalized adjunction and canonical
  composition comparisons are also available for the node's proof.
- Restriction is the existing `SheafOfModules.over` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`, read in full at
  its declaration: restriction to the over site on U, with the restricted structure ring.

Proof-only imports preserve the stated proof plan: `Mathlib.AlgebraicGeometry.Sites.Fpqc`
(`Scheme.fpqcPrecoverage`), `Mathlib.AlgebraicGeometry.Cover.QuasiCompact`
(`QuasiCompactCover.exists_hom`), `Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen`
(`Scheme.Hom.isOpenMap`), `WeilConjectures.AlgebraicGeometry.Descent`
(`isFinitePresentation_of_toDescentData_iso`), and
`Sheaf.AlgebraicGeometry.TensorPullbackFinitePresentation`
(`Scheme.Modules.isFinitePresentation_tensorPullback`, source read with
`scompile.py --source`). Étale composition, open immersions and cancellation are in
its public Mathlib Étale import. The docstring spells out all four DAG proof steps,
including the finite affine refinement establishing the singleton fpqc covering
without imposing quasi-compactness on g.

Source read: `literature/stacks-project/flat.tex`, label
`lemma-devissage-finite-presentation`, especially the paragraph introducing (4),
pullback preservation, openness of g, and descent along U' → g(U'). This is Tag 057T.
The node's top-level `source.place` retains inherited old cross-reference tags,
while its detailed proof has the verified Tags 01BQ, 05B0, 03WT, 0218 and 022B.
The Lean docstrings use Tag 057T and the actual (1) iff (4) paragraph. No statement
fault or dispute was found; no correction is needed.

Edge cases checked before writing: the zero module is allowed and finite presentations
may have zero generators or relations; no positivity appears. The empty scheme admits
no marked point, so the corresponding universally quantified instances are vacuous,
as in the node. An empty open cannot witness a neighbourhood because membership is
required. Identity maps and open immersions are allowed, as are non-quasi-compact
étale morphisms. Nothing assumes characteristic, a field base, or finite type of M.
Both schemes and their usual sheaves of modules use the arbitrary scheme universe `u`.

Searches for an existing statement:

- `msearch.py ... leanfinder` query: "A quasi-coherent module is finitely presented on
  a neighbourhood of a point if and only if its etale pullback is finitely presented
  near a point above it". Eight hits: ring étaleness/finite presentation and sheaf
  presentation data; no matching neighbourhood equivalence.
- `msearch.py ... leansearch` query: "Finite presentation of a quasi-coherent sheaf
  is local under etale pullback near marked points". Eight hits on the existing
  sheaf presentation notions; no theorem matching this node.
- `msearch.py ... loogle` query `SheafOfModules.IsFinitePresentation, AlgebraicGeometry.Etale`:
  zero hits. Query `SheafOfModules.IsFinitePresentation`: five hits supplying the
  existing class and its finite-type/quasi-coherence consequences, no matching theorem.
- `msearch.py ... grep` query `IsFinitePresentation|finitePresentation`, subdirectory
  `AlgebraicGeometry`: 25 hits on morphism finite presentation; no matching theorem.
- `rg` of the upstream `WeilConjectures` and side `lean/Sheaf` trees for finite
  presentation and étale-related names found tensor pullback preservation, fpqc
  descent, and the consuming elementary-devissage theorem, but no existing theorem
  with this node's equivalence. `grep -rn` for the exact item id in upstream gave no hits.
- `rg` in `dag/lean_names_upstream.json` for the item and candidate names gave no
  matching existing declaration. The chosen full declaration name has no pre-existing hit.

Validation: prescribed `scompile.py Q135 lem-trf-etale-module-finite-presentation-local
<file>` compiled both the sandbox and library-path versions cleanly (3.3 s each),
with no errors or warnings.

## Second reading by Q135

Author self-check under the dispatcher's direct-delivery brief; independent review belongs
to the maintainer. I reopened the node and Lean file and compared each binder and both
existentials: g is étale, x' lies above x, the induced residue map is an isomorphism,
and M is quasi-coherent; each side asserts finite presentation of the indicated restricted
module on an open containing its own marked point. In particular, I checked that
`M.IsQuasiCoherentFiniteType` was not used, that the right side uses tensor pullback,
and that no global finite-presentation or affine-neighbourhood condition replaced the
node's local condition. No mismatch was found and no statement change was made.
The proof docstring matches the four proof steps, and all recorded proof modules with
available statements are imported. No new nodes or dependency modules are delivered.

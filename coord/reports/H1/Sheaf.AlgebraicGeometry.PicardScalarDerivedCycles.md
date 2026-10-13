## What changed

Reduced `AlgebraicGeometry.Scheme.picard_scalar_derived_cycles` to two independent
parts of its existing argument, with its statement and public imports unchanged.
The derived comparison has no scalar basis, affine, marked-point, or differential-vector
hypotheses. The ordinary scalar calculation has no derived object, model isomorphism,
negative-support hypothesis, or derived-category instance. Neither restates the item.
The original module contains the complete combining proof, including construction of the
residue additive equivalence, agreement of the two residue factorizations through U,
and transport of the local ordinary cycle through the comparison.

Added actual definitions `picardOrdinaryModelCycles` and
`picardOrdinaryModelRestriction`. The former is the additive kernel of postcomposition
with the outgoing differential; the latter conjugates tensor pullback by composition
comparisons obtained from the existing pinned adjunctions. They contain no holes or
new arbitrary witness choices. `Modules.overEquiv` and tensor pullback are reused.

Also proved the generic homological ingredient
`DerivedCategory.connective_single_hom_bijective` using Mathlib alone: bounded right
fractions give surjectivity, and zeroth homology plus naturality give injectivity.
It applies to arbitrary abelian categories and requires no projectivity. Its import
belongs to the proof plan of the remaining derived comparison.

All five sandbox modules compile cleanly together with lcompile.py. Mathlib/source
searches were made through msearch.py and local rg, and the relevant Stacks pages
0BF2, 06YJ, 0D5S, 06Z0, 0096, 08C4 and 05RR were read online because this clone has
no literature/stacks-project directory. The unit realization record was read:
sk-prop-av-cube has no realized nodes in its statement or step slots; the reduction
retains the existing cube proof route and changes no unit or chapter record.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.picard_scalar_derived_cycles`
(node `lem-sc-picard-scalar-derived-cycles`). No sorry remains in the item's module.
This is a decomposition, not a completed proof of the mathematical result.

Added exactly two holes, each a named public theorem with proof exactly `:= by sorry`:

- `AlgebraicGeometry.Scheme.picard_connective_model_comparison`
  (node `lem-sc-picard-connective-model-comparison`, module
  `Sheaf.AlgebraicGeometry.PicardConnectiveModelComparison`).
- `AlgebraicGeometry.Scheme.picard_ordinary_scalar_coordinates`
  (node `lem-sc-picard-ordinary-scalar-coordinates`, module
  `Sheaf.AlgebraicGeometry.PicardOrdinaryScalarCoordinates`).

The generic theorem `DerivedCategory.connective_single_hom_bijective`
(node `lem-sc-connective-single-hom`) is fully proved and has no sorry dependencies.
The ordinary-cycle definitions (node `def-sc-picard-ordinary-model-cycles`) have no sorry
in their bodies. Their canonical adjunctions are the existing library adjunctions.
There are no other added holes. Counting this delivery alone: one hole closed,
two holes added, net minus one; no claim of positive sorry-ledger progress is made.

## No longer needed

Removed the proof imports `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`,
`Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`, and
`Sheaf.AlgebraicGeometry.DerivedPullbackStructureSheaf` from the item's module.
The last two remain needed by the new derived-comparison proof plan and are imported
there; their nodes are not pruned from the argument.

The full derived affine equivalence, node `lem-pc-affine-qcoh-derived-equivalence`,
module `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`, is no longer needed by
this argument. Its ordinary affine tilde/Gamma ingredient suffices for the scalar
calculation. That calculation imports the ordinary source module
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`, not the derived equivalence.
The derived-equivalence core, shift compatibility, and unbounded-derived bound are
therefore not additional obligations introduced by this route; whether those modules
remain reachable from other targets is for the global queue to determine.

All other original dependency notions remain used: the derived category, strict
perfectness, residue fields, derived model sections/restriction, bounded-flat pullback,
structure-sheaf pullback, and canonical pullback composition. The latter three move
under the generic comparison; the ordinary affine adjunction and tensor unit replace
the derived affine step. No other existing nodes are claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG's affine derived-equivalence step is stronger than needed: the scalar bases
are sheafified by the ordinary affine adjunction. Also, none of the original imported
statements directly provides the degree-zero Hom-to-cycles equivalence or its
compatibility with the specifically chosen composition comparison. Those two
interfaces must be exposed rather than obtained by applying an arbitrary existence
of an isomorphism. The new derived comparison states the required naturality.

Edge cases were checked mathematically against the new signatures. With m=0 the
outgoing finite free module is zero and all scalars are cycles. The coordinate lemma
does not assume V affine: sheaf bases restrict to arbitrary smaller opens. A marked
point excludes empty U and V. The generic derived comparison also allows empty T or U,
where the relevant module-sheaf categories and cycle groups are zero; it never assumes
that global sections on a nonaffine scheme are exact. For K concentrated in degree
zero the generic homological lemma reduces to full faithfulness of the single functor;
for positive target support both sides vanish. No statement was found false or changed.

A newer source wrapper `TensorPullbackCompositionIso` was visible in the clone but
its compiled module was unavailable. No copy of that declaration was added. The
ordinary restriction definition writes the canonical conjugate-of-pushforward
expression directly using the existing `exists_tensorPullbackAdjunction`,
`pushforwardComp`, and `pushforwardCongr` interfaces.

## New nodes

`lem-sc-connective-single-hom` records the proved generic localization bijectivity
and its Mathlib-only proof in `ConnectiveSingleHom.lean`.

`def-sc-picard-ordinary-model-cycles` records the actual additive kernel of the
pulled-back outgoing differential and the raw composition restriction, with both
Lean declarations listed, in `PicardOrdinaryModelCycles.lean`.

`lem-sc-picard-connective-model-comparison` records the derived-to-ordinary comparison
and its naturality, with no affine or scalar assumptions. It is the first remaining
hole and uses the proved generic localization lemma.

`lem-sc-picard-ordinary-scalar-coordinates` records the ordinary affine basis and
residue-evaluation calculation, independently of E and of negative support. It is
the second remaining hole. The item combines it with the derived comparison.

Each new node has three actual logged Mathlib search kinds, its source, proof in
words, and the unchanged parent chapter/unit. LeanSearch returned Internal Server
Error and is recorded as unavailable. Blueprint keyword searches for degree zero
cycles, connective single, and scalar coordinates found no imported blueprint match;
local DAG and library searches found related ingredients but no duplicate of these
interfaces. No change record is required: no existing statement, definition, visibility,
or public import changed, and no existing module was adapted.

## Second reading by H1

1. I compared the delivered item with the repository version. The theorem signature is
   byte-for-byte unchanged; only its proof and proof-only imports changed. Verdict: pass.
2. I compiled all five sandbox modules with `lcompile.py --all`. The files compile cleanly;
   the only remaining `sorry`s are the two named split-off theorems listed above. The
   generic connective theorem is proved and no forbidden declarations or hollow
   definitions occur. Verdict: pass.
3. I checked both split-off statements against their docstrings, edge cases (including
   rank zero and empty-support cases), and local/library searches. They are true,
   strictly smaller than the parent, and needed by the combining proof; neither merely
   restates the parent. Verdict: pass.
4. I checked the proof route and pruning. The combining proof retains the derived model,
   strict-perfect, residue, and composition route, while replacing the unnecessary
   derived affine equivalence with the ordinary affine calculation. The unit route is
   unchanged. Verdict: pass.
5. I checked all changed node records: statements match Lean declarations, proof steps
   and dependencies match the imports and applications, and each new node has source,
   search, origin, and Lean metadata. Verdict: pass.

I added this second-reading record only; no Lean source or statement was changed during
the review.

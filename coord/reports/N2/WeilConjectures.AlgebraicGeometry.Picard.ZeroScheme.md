## What changed

Reduced `AlgebraicGeometry.nonempty_arrowIso_pullback_directImageCounit`, the only
original sorry in `WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme`, to the generic
canonical degree-zero comparison
`AlgebraicGeometry.Scheme.Modules.isIso_counitBaseChange_of_invertibleDirectImage`.
The latter is in the new proof-only import
`Sheaf.AlgebraicGeometry.Picard.CounitBaseChangeIsIso`.

The original module constructs the pullback-composition isomorphism, specializes the
comparison to the cartesian square for `i`, proves the inverse-adjoint identity, and
constructs the Arrow isomorphism. Its codomain edge explicitly identifies the pullback
module with the skeleton representative used by `Pic.map`. Counit naturality proves the
commuting square. All original declarations and their statements are preserved.
The now-unneeded geometric-integrality assumption is retained in the original theorem;
its unused-section-variable linter is disabled locally to preserve that signature.

Updated `lem-pc-arrow-iso-pullback-counit` with this proof route and its original
source-library declaration, replacing the record of the separate tensorPullback theorem.
The unit route is retained: the zero-scheme dictionary, universal normalized module,
open locus, and inverse-composite arguments are unchanged.

## Proved and sorry left

The original module has no sorry left. Its one former sorry,
`AlgebraicGeometry.nonempty_arrowIso_pullback_directImageCounit`, is proved from the
new comparison lemma plus the existing Mathlib categorical infrastructure.
This is a reduction, not an unconditional closure of its transitive axioms.

One sorry remains in the delivery, exactly the whole proof of the public theorem
`AlgebraicGeometry.Scheme.Modules.isIso_counitBaseChange_of_invertibleDirectImage`
(node `lem-pc-counit-base-change-is-iso`). It states only invertibility of the canonical
ordinary direct-image comparison, for arbitrary proper flat families locally of finite
presentation. It has no Picard class, rational point, curve, zero scheme, or Arrow-isomorphism
conclusion. The original proof supplies the adjunction and representative-transport steps.

Local compilation of both modules in dependency order passes without warnings.
The new statement was checked against empty bases, identity base changes, and arbitrary
nonflat base-change maps: flatness is assumed of the family, and invertibility of R^0
makes its derived pullback ordinary, so no flatness of `i` or nonemptiness is required.

## No longer needed

No original import was removed. The new import is proof-only.

The proof does not import or use
`Sheaf.AlgebraicGeometry.Picard.ArrowIsoTensorPullbackCounit`,
`Sheaf.AlgebraicGeometry.Picard.AdjunctionBaseChange`,
`Sheaf.AlgebraicGeometry.TensorPullback`, or
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction`.
The explicit-tensor pullback composition node
`lem-pc-module-pullback-identity-composition` is unnecessary for this route:
Mathlib `Scheme.Modules.pullbackComp` and `pullbackCongr` already provide the needed
composition isomorphism. Likewise no proof of the sectionwise tensor-adjunction node
`lem-pc-module-pullback-adjunction` is used by the compiled Arrow construction;
Mathlib `pullbackPushforwardAdjunction` provides the canonical adjunction directly.
These are local proof-route exclusions, not claims that those modules have no other users.
The other old direct proof dependencies `def-pc-f-subfunctor`,
`def-pc-invertible-in-degree-zero`, and `def-sc-invertible-module` are no longer
listed as separate steps: the proof reads their data directly from `ℒ` and passes
it to the comparison lemma. Their definitions and modules remain in use.
The generic derived base-change argument `lem-pc-rf-base-change-flat-module` remains
in the new comparison node's mathematical proof and is not globally pruned.

## Where the brief, the DAG or earlier work was wrong

The module's one sorry was not directly attached by a node's current lean record:
`lem-pc-arrow-iso-pullback-counit` pointed instead to a separate tensorPullback theorem.
That theorem assumes the custom `IsSmoothProjectiveCurve` class, uses an explicit
change-of-rings tensor pullback and chosen adjunction, and its codomain is the actual
pullback module rather than the representative used by `Pic.map`. It does not directly
supply the required canonical Mathlib-pullback statement. This delivery uses Mathlib's
existing adjunction and composition isomorphisms, and updates the node's lean record.

The existing `exists_isFiniteFreeComplex_higherDirectImage` docstring expressly says
its isomorphisms are not required to be canonical or compatible with base change.
Consequently it cannot identify the particular mate used here. Likewise the existing
`nonempty_derivedBaseChange_iso_of_isFlatOver` statement gives an unspecified isomorphism
and uses a different pullback/derived-category construction. The new lemma isolates the
canonical degree-zero comparison, including its identification with the ordinary mate;
its proof sketch retains the canonical Cech comparison, rather than inferring canonicity
from an unspecified isomorphism.

Searches were run with the required search wrapper: LeanFinder returned morphism-property
base-change infrastructure, Loogle found no adjunction pattern, and Mathlib grep found only
generic adjunction usage. LeanSearch was unavailable (Internal Server Error); that failure
is recorded without claiming a negative search result. Repository searches found no
existing canonical module comparison theorem with the required statement.

## New nodes

`lem-pc-counit-base-change-is-iso` is the first, geometric step of the existing
counit-base-change plan. Its module is
`lean/Sheaf/AlgebraicGeometry/Picard/CounitBaseChangeIsIso.lean`.
The statement specifies the actual comparison as the adjoint of the pulled-back counit
precomposed with the inverse pullback-composition isomorphism. Its proof sketch checks
relative flatness, derives the degree-zero comparison, and identifies it with this mate.
No definitions, existing signatures, or target statements changed; no change record is needed.

## Second reading by N2

1. Compared the complete original module with the repository using `diff -u`: the
   sole declaration-body change is the formerly open
   `nonempty_arrowIso_pullback_directImageCounit`. Every existing signature and
   definition is unchanged, including the geometric-integrality section binder.
   The added comparison import is plain `import`, so it is proof-only. No change
   record is required.
2. Compiled both delivered modules in dependency order without errors or warnings.
   The only remaining `sorry` is the whole named theorem
   `Scheme.Modules.isIso_counitBaseChange_of_invertibleDirectImage`. No forbidden
   declarations or hollow definitions occur. Explicit axiom checks of the two
   relevant declarations and the delivery tool's all-declaration probe are used
   below; dependency `sorryAx` is expected and is not an unconditional proof claim.
   Both explicit `#print axioms` checks returned exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`.
3. Read the new comparison statement against its node and the source theorem's
   base-change paragraph, and read `RelativelyFlatDerivedBaseChange`,
   `BaseChangeMapCech`, and `FlatComplexDerivedPullback`. Properness supplies
   separatedness and quasi-compactness; flatness of f and invertibility of M
   supply relative flatness. No flatness of g is assumed or needed. Vanishing of
   positive direct images and invertibility of degree zero allow arbitrary
   tensor base change. The square is cartesian, and c has exactly the direction
   needed by the mate. Identity base change reduces to the identity comparison;
   empty schemes have zero module categories; for an affine identity family the
   result is ordinary pullback of a line bundle. These cases expose no excluded
   characteristic, nonemptiness, or flat-base-change condition. Repeated searches
   with “Beck Chevalley”, adjunction/IsIso patterns, and isIso/baseChange found
   generic categorical infrastructure, not this geometric comparison. Repository
   and upstream searches found the original sorry and the previously reported
   tensorPullback variants, which do not directly give this canonical map. The
   split is the geometric comparison alone: the original file genuinely proves
   the adjunction square and transports both edges to the Pic.map representative.
4. Checked c, b, hb, and e in the Lean proof: hb is the inverse-adjoint identity,
   e is the inverse skeleton counit, and counit naturality verifies Arrow.isoMk.
   No shorter available theorem closes the geometric step. Original imports
   serve the remaining declarations; the added module's imports serve its public
   statement. The pruning section now accounts for every old proof dependency.
   Read `dag/units/sk-thm-picard-f-representable.json`: its realized lists are
   currently empty; this delivery does not alter them or bypass its normalized
   universal module, open locus, zero-scheme dictionary, or inverse construction.
5. Checked that the existing node's proof names the canonical comparison and
   the actual original Lean declaration; its proof_deps agree with those steps.
   The new node has its source, statement dependencies, proof steps, union of
   proof dependencies, searches, provenance, chapter/unit, and Lean record. The
   new lemma's docstring supplies the geometric proof, not an unspecified choice
   of isomorphism. Its Cech comparison is the canonical mate by the section map
   s tensor b ↦ b times pullback(s), as in lem-pc-base-change-map-cech.

Changes by this reader: added the missing module-docstring blueprint marker,
expanded the new theorem's proof sketch to state affine locality and the flat
bounded Cech complex, and completed the old-dependency accounting above. The
compiled categorical proof was retained.

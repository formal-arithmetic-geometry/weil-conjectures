## What changed

Proved `AlgebraicGeometry.newBase_open_mate_factorization` with its signature unchanged.
The proof first identifies `q ≫ e.hom = r` for canonical pullback associativity `e`,
using both projection equations and monicity of the open inclusion. It constructs
an arrow isomorphism using naturality of the supplied arbitrary `δ`, applies the
horizontal pasting comparison on the canonical iterated pullback, then transports
the result using derived pullback composition and its naturality at the outer mate.

Added `Sheaf.AlgebraicGeometry.HorizontalDualityMatePasting`, isolating only the
horizontal pasting calculation on canonical pullbacks. It has no open subscheme,
restriction functor, `q`, `r`, or `δ`. The target module contains a real proof of all
these additional geometric and naturality transports. Updated both DAG records.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.newBase_open_mate_factorization`, node
`lem-sc-new-base-open-mate-factorization`. No sorry remains in the item module.

Added one hole: `AlgebraicGeometry.horizontal_duality_mate_pasting`, node
`lem-sc-horizontal-duality-mate-pasting`. This is a decomposition, with net holes
closed minus added equal to zero; it is not claimed as a sorry-free proof of the
horizontal pasting law. The new theorem has a full document-based argument in its
docstring and node. Its ordinary base-change invertibility hypotheses replace the
Tor-independence that Stacks 0ATR uses only to establish those invertibilities.

Edge cases: no step assumes invertibility of a duality mate. Empty W and zero K
are included; the geometric equality follows from pullback uniqueness even in
these cases, and the arrow comparisons follow solely from naturality of natural
isomorphisms. The horizontal theorem similarly covers empty schemes and zero K.

## No longer needed

Removed the proof import `Sheaf.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`
from the item module: its declaration is not used by the open transport proof.
It remains a proof dependency of the new horizontal pasting item, which imports it.
Consequently no module is claimed pruned from the overall targets' closure.

The item does not need to construct a canonical `δ₀`, prove exact restriction is
open pullback, or compare `δ` to `δ₀`: naturality of the supplied `δ` directly
constructs the first arrow isomorphism. The public statement imports are retained.
All source endpoint and target endpoint mate-pasting work remains on the new node,
so no unit route is bypassed.

The complete old proof-dependency difference is:
`def-pc-derived-base-change-map`, `def-pc-derived-open-restriction-maps`,
`def-sc-duality-equation-base-change-map`, `lem-pc-derived-direct-image-composition`,
`lem-pc-qcqs-derived-direct-image-right-adjoint`. These are no longer direct proof
steps of this item: the definition modules remain public statement imports, and
all except open restriction remain in the new node's statement or proof
context. Derived pullback composition is retained. This supplements
`## No longer needed`; it does not assert removal from the target import closure.


## Where the brief, the DAG or earlier work was wrong

The existing dependency declarations give derived composition, QCoh right adjoints,
and the canonical mates, but none states horizontal pasting of these particular
canonical duality mates. Mathlib's `mateEquiv_hcomp`, `mateEquiv_vcomp` and conjugate
composition laws are generic ingredients, not the full derived comparison theorem.
The existing upper-left pasting theorem `schemeDerivedBaseChange_pasting` has a
different diagram shape and does not directly close this gap.

The original plan's construction of `δ₀` is unnecessary: the hypothesis `δ` itself
and its naturality suffice. No statement or definition was changed.

The cited local Stacks TeX files were absent. The source was read from the official
[0ATR](https://stacks.math.columbia.edu/tag/0ATR),
[0E9S](https://stacks.math.columbia.edu/tag/0E9S), and
[0ATM](https://stacks.math.columbia.edu/tag/0ATM) pages.

## New nodes

`lem-sc-horizontal-duality-mate-pasting`, module
`lean/Sheaf/AlgebraicGeometry/HorizontalDualityMatePasting.lean`, records the
horizontal canonical-pullback calculation needed before the proved open-subscheme
transports. It is strictly the pasting part of the original argument and has fewer
kinds of input data. Its node states the full setup independently and records the
source, proof, dependencies, and three kinds of Mathlib searches; LeanSearch was
unavailable with Internal Server Error. No interface change or change record.

## Second reading by M3

1. Interface: PASS. I diffed every delivered module against the repository. The
   existing `newBase_open_mate_factorization` signature is byte for byte unchanged
   (also checked by an exact string comparison). The horizontal theorem is new;
   no existing definition or signature changes, and no change record is needed.

2. Proof: PASS as a decomposition. Both modules compile together with
   `lcompile.py --all`, without errors or warnings. The target proof uses pullback
   hom-extensionality, monicity of the open inclusion, naturality of the supplied
   δ, and naturality of derived composition to compose three Arrow isomorphisms.
   The only new hole is the named `horizontal_duality_mate_pasting`, exactly
   `:= by sorry`; it has a source, proof docstring and node. There are no new
   definitions, forbidden declarations, or arbitrary chosen data in definitions.
   Axiom probes are recorded below. One upper hole closed and one lower hole added
   is net zero; the canonical horizontal pasting calculation remains open.

3. New statement: PASS. I read Stacks 0ATR, 0ATM and 0E9S and checked the canonical
   mate definition. The 0ATR argument requires ordinary base-change invertibility,
   which is explicitly assumed here; it does not invert the duality mates.
   Identity base maps, empty schemes, and zero K have no excluded cases. Arbitrary
   supplied right adjoints are compared through uniqueness respecting adjunctions.
   I repeated searches with different terms via LeanFinder, Loogle and grep and
   read `rightAdjoint_mate_successive_baseChange`: its conclusion inserts an
   arbitrary existential middle isomorphism e₁, so does not assert the actual
   composite with identity at the equal middle endpoints required here. The proved
   `schemeDerivedBaseChange_pasting` is upper-left pasting with a unit, not this
   horizontal comparison. Generic Mathlib conjugate/mate laws alone do not supply
   the scheme-derived coherence. The new statement is the canonical pasting part
   of the argument, omitting all open, q, r and δ transports, rather than a
   renamed statement of the original item. Closing it requires more than a short
   tactic application to an existing theorem.

4. Route and pruning: PASS with a report correction. The target's unused proof
   import of direct-image composition was removed; the new node retains that
   planned step. All five old proof dependencies removed from the target are
   listed under `## No longer needed`. The unit `sk-thm-picard-duality` has empty realized statement and
   step lists; neither item is a realized unit step. This is a refinement below
   the unit, preserving its route. No overall closure pruning is claimed.

5. DAG: PASS after repair. The target node describes exactly the geometric
   equality and three Arrow transports of the Lean proof. The new node records
   the remaining canonical pasting calculation, source, searches, creation and
   blueprint origin. I changed its `lean.statement` from a whitespace-normalized
   string to the verbatim Lean signature and recorded the near-match search.

Second reading changed the target proof by giving the horizontal comparison an
explicit type in terms of μ, ν, lam, p and e, then extracting its witness locally
with Classical.choice. This avoids tactic inference of the large expanded
comparison type. I also replaced dependent-tuple destruction of
`exists_derivedPullbackComposition` by a typed local projection to its composition
isomorphisms, retaining all of its implicit scheme parameters. The complete set
then compiled cleanly. The delivery compile still varied near its deadline,
so I restored normal transparency for backward type comparison locally to this
theorem (`backward.isDefEq.respectTransparency true`). This prevents unnecessary
unfolding of the canonical derived data; the target compiled cleanly in 18.6
seconds. Both extractions occur only inside
a theorem proof, not inside a definition. No theorem signature or mathematical argument was changed.
Metadata and report were also corrected. The original module docstring describes a longer valid argument
than the proof now uses, while the updated node and report describe the actual
shorter δ-naturality route.

Axiom probes of both declarations compiled successfully and each printed exactly
`[propext, sorryAx, Classical.choice, Quot.sound]`. The `sorryAx` is expected from
remaining named lower statements, including the horizontal pasting hole; no
additional axiom appeared.

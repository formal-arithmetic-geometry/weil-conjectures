## Worker report

The module `lean/Sheaf/AlgebraicGeometry/AmplePullback.lean` states that for schemes
`Y` and `X`, an affine morphism `g : Y ⟶ X`, and an invertible module `L : X.Modules`,
the tensor pullback `(tensorPullback g).obj L` is ample on `Y`. The `letI` binder supplies
its invertibility using the first clause of `invertible_pullback_tensor`.

The hypotheses are rendered as follows: `{X Y : Scheme.{u}}` gives the two schemes;
`(g : Y ⟶ X)` gives the morphism in the direction of the node; `[IsAffineHom g]`
expresses affineness; `(L : X.Modules)` gives the invertible module; and
`[L.IsInvertible]` gives its invertibility. The conclusion is
`IsAmple Y ((tensorPullback g).obj L)`, with the displayed local instance for the
pulled-back module. The proof is `sorry` as required at stage 2.

Dependencies used: `Sheaf.AlgebraicGeometry.Ample`, declaration
`AlgebraicGeometry.Scheme.Modules.IsAmple`; `Sheaf.AlgebraicGeometry.TensorPullback`,
declaration `AlgebraicGeometry.Scheme.Modules.tensorPullback`; Mathlib's
`AlgebraicGeometry.Scheme` and `AlgebraicGeometry.IsAffineHom`; and
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`, declaration
`AlgebraicGeometry.Scheme.Modules.IsInvertible`. The invertibility instance is supplied
by `Sheaf.AlgebraicGeometry.Modules.InvertiblePullbackTensor`, declaration
`AlgebraicGeometry.Scheme.Modules.invertible_pullback_tensor`, a proof dependency named
in the node.

Edge cases checked: the source and target schemes may be empty; an affine morphism need
not be surjective; the identity morphism is affine; and positive tensor powers in the
ampleness definition exclude only power zero as required by the definition. No extra
hypothesis on quasi-compactness is introduced: it is part of `IsAmple`.

Searches made: LeanSearch query “pullback of an ample invertible sheaf along a
quasi-affine morphism is ample” (no corresponding theorem); LeanFinder with the same
query (no match); grep for `pullback-ample`, `IsAmple`, and `ample` in Mathlib and
`WeilConjectures` (no absolute ampleness pullback theorem; the source `IsAmple` is a
different relative very-ample notion). `rg` over project modules found the existing
`IsAmple`, `tensorPullback`, and `invertible_pullback_tensor` declarations used above.

## Earlier second reading (a previous round; superseded)

Read the node and source place (Stacks Morphisms Lemma 0892(2), affine specialization).
The Lean statement preserves every clause: affine `g`, invertible `L` on `X`, the
specified tensor pullback, and ampleness on `Y`; no object, direction, or hypothesis is
added or omitted.

## Second reading by F1

Read the node, its two proof steps, all five statement dependency nodes and their
recorded declarations, and the module independently. The repository's literature
contains only citation lists, so I fetched the Stacks `morphisms.tex` into the item's
scratchpad and read `lemma-pullback-ample-tensor-relatively-ample`, lines 8828–8885,
and the introduction of the relatively ample section, lines 8615–8624. Tag 0892(2)
(https://stacks.math.columbia.edu/tag/0892) requires an ample invertible module and
a quasi-affine morphism; this node is its affine specialization. No ambient field,
Noetherian, finite-type, surjectivity or properness assumption occurs. I also read
Properties Definition 01PS (https://stacks.math.columbia.edu/tag/01PS).

Object/hypothesis/conclusion checklist, with verdicts:

- Two arbitrary schemes X and Y: `{X Y : Scheme.{u}}`. PASS. Mathlib's Scheme
  extends LocallyRingedSpace with local affineness; no additional structure assumed.
- Morphism from Y to X: `(g : Y ⟶ X)`. PASS; orientation matches the node.
- Affine morphism: `[IsAffineHom g]`. PASS. Opened Mathlib's signature: inverse
  images of every affine open are affine. This is pqf-def-affine-morphism exactly.
- An O_X-module L: `(L : X.Modules)`. PASS. `Modules` is the Zariski
  `SheafOfModules` category of the structure sheaf, not an unrelated sheaf category.
- Invertibility of L: `[L.IsInvertible]`. PASS. Opened the recorded upstream
  class: local restriction is isomorphic to the structure module near every point.
  This is local freeness of rank one (hence quasi-coherent); it matches the node.
- Ampleness of L: `(hL : IsAmple X L)`. FAIL in the original delivery, REPAIRED.
  The original theorem had no such hypothesis and asserted ampleness for every
  invertible L, contradicting even the identity morphism on P^1 with O(-1).
  The added binder renders precisely the node's existing ampleness hypothesis.
  Opened `Sheaf.AlgebraicGeometry.Ample`: quasi-compactness and, at each point,
  an affine nonvanishing locus of a global section of a positive tensor power.
  This is the absolute 01PS notion, with neither projectivity nor a base field.
- Pullback g^*L: `((tensorPullback g).obj L)`. PASS. Opened the recorded
  TensorPullback module: inverse-image module followed by change of rings,
  O_Y tensor over g^{-1}O_X; its data are concrete, not sorry.
- Conclusion, ampleness on Y: `@IsAmple Y ((tensorPullback g).obj L)
  ((invertible_pullback_tensor g).1 L).2`. PASS. The last argument is the
  derived invertibility proof, not a new hypothesis. Opened the recorded
  `invertible_pullback_tensor` theorem: its first conjunct indeed provides
  this invertibility for arbitrary g and invertible L. Removed the original
  `letI` from the statement in accordance with the no-let convention.

Edge cases: empty Y and empty X are allowed (a map to empty X forces empty Y);
no Nonempty assumption is introduced. The zero module is invertible only where
local rank-one triviality permits it, in particular on the empty scheme; it is
not incorrectly admitted on a nonempty scheme. The identity and nonsurjective
affine morphisms are included. There is no index family in the statement.
Power zero remains available in the dependency's tensor-power definition but
is correctly excluded from the ampleness witness by `0 < n`. No characteristic
restriction or field is present. The arbitrary shared scheme universe u is the
universe of the recorded scheme/module category; there are no auxiliary test
universes, cardinal bounds, unbound variables, or additional instances.

Independent searches: LeanFinder query “affine morphism preserves ampleness
invertible module pullback” returned generic affine/base-change theorems only;
Loogle query `IsAmple` returned no hits (unknown identifier in Mathlib).
LeanSearch query “An affine morphism pulls back an ample line bundle to an
ample line bundle” was unavailable with an internal service error; no verdict
is inferred from that unavailable search. `rg` over Mathlib, WeilConjectures,
and project Sheaf modules with `isAmple.*[Pp]ullback`,
`IsAmple.*tensorPullback`, `affine.*[Aa]mple`, and `ample.*pullback` found no
exact theorem. Opened upstream Modules/Ample.lean: its `IsAmple` is relative
to a field and includes projectivity; `IsAmple.pullback` assumes a closed
immersion and uses the upstream pullback. Neither is this absolute affine
pullback theorem. Project AmpleOnReductionNoetherian and AmpleSquareZeroThickening
concern different special cases. No duplicate definition or theorem is needed.

Changes: added the missing ampleness hypothesis; removed the statement's letI
by supplying invertibility explicitly; expanded the docstring into the node's
two proof steps, including preservation of nonzero residue values, a finite
cover of X (not an assumed quasi-compact Y), affineness by permanence, and
quasi-compactness of Y from its finite affine cover. Updated lean.statement
verbatim (whitespace normalized) to the signature. The node's mathematical
statement is correct and unchanged; no statement_change is applicable.
No new nodes or dependency modules are in this delivery. All imports serve
these declarations, the only proof is sorry, and no new definition is present.
The original Worker report is retained above; its claims of a complete
hypothesis match and its letI description are superseded by this reading.

Validation: scompile.py compiled AmplePullback.lean in 1.7 seconds, exit 0,
with no errors or warnings. The declaration and universe binders were also
checked by eye. Delivery preflight is recorded below if further changes arise.

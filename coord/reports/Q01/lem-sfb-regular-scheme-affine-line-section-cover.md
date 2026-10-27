## Worker report

The module `Sheaf.AlgebraicGeometry.RegularSchemeAffineLineSectionCover` states
`AlgebraicGeometry.exists_affine_nonvanishingLocus_of_isRegularScheme`, with `sorry` as
its whole proof. No definitions, additional hypotheses, node corrections, or new nodes
are introduced. The node copy changes only `lean`.

Source read: Stacks `divisors.tex`, lemma-regular-ample-family (0GML), including its
finite integral-component reduction and the canonical section of the boundary divisor;
lemma-complement-open-affine-effective-cartier-divisor (0BCW), including its proof;
`morphisms.tex`, definition-family-ample-invertible-modules (0FXR). The node is the
separated specialization of the affine-diagonal result, with the positive tensor power
absorbed into A. The six-step DAG proof is included in the declaration docstring.

Clause-by-clause correspondence:

- A scheme X is `(X : Scheme.{u})`, for arbitrary explicitly declared universe u.
- Quasi-compactness is `[CompactSpace X]`; this has no Hausdorff requirement.
- Regularity is `(hX : IsRegularScheme X)`. The recorded definition unfolds to
  `IsLocallyNoetherian X ∧ IsRegular X`, so local Noetherianity is included.
- Separatedness is `[X.IsSeparated]`. Mathlib defines this by separatedness of
  `terminal.from X`, hence a closed-immersion diagonal over the terminal scheme Spec Z.
- Every point is the binder `(x : X)`, before the existential witnesses.
- The invertible O_X-module is `∃ A : X.Modules, A.IsInvertible ∧ ...`. This is the
  recorded scheme-module local-rank-one predicate, with no private replacement.
- The global section is `∃ t : A.val.presheaf.obj (Opposite.op ⊤), ...`.
- `∃ U : X.Opens` represents the open subscheme X_t; `x ∈ U` gives containment and
  `IsAffineOpen U` gives affineness.
- `(U : Set X) = A.nonvanishingLocus t` requires equality with the entire locus, not
  merely inclusion. The recorded definition uses the germ outside the maximal ideal
  times the stalk, exactly the node's residue-fibre nonvanishing condition. The explicit
  open witness also records the openness needed to view this set as a subscheme.
- A is quantified after x and may depend on it. There is no single common module or
  assertion of ampleness. No tensor exponent is required because A is already the
  chosen positive power as permitted by the source/node.

Statement dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` (locally affine locally
  ringed space), its `Hom`, and `Scheme.Opens`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`, via Separated:
  `AlgebraicGeometry.Scheme.IsSeparated` and `AlgebraicGeometry.IsSeparated`; the latter
  asks that `pullback.diagonal f` be a closed immersion. Properness is not assumed.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`, whose `exists_isoUnit` gives local
  trivializations on neighbourhoods of all points.
- `WeilConjectures.AlgebraicGeometry.Ample`:
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus`, and the `IsAmple` signature and
  docstring were inspected to check the interpretation of X_t.

Every statement-dependency module is a public import. The recorded proof dependencies
with declarations are non-public imports, including RegularNormalDecomposition,
AffineOpenBoundaryCodimensionOne, RegularLocalUFDBoundaryFactorization, the reduced
induced closed subscheme, EffectiveCartier, and Modules.ZeroLocus. Mathlib proof leaves
are imported by their recorded source modules. The sole unstated proof dependency,
`lem-sfb-stalk-nonzerodivisor-cartier-spreading`, currently has neither a Lean record nor
a Mathlib match; no module is imported for it. It is mentioned in the proof docstring
and remains in proof_deps, as required by the rule to import proof nodes that are stated.
It is not a missing notion needed to type this statement.

Edge cases checked mathematically: the empty scheme requires no point witness; no
Nonempty assumption is imposed. On a field spectrum take the trivial module and section
1. On a regular affine scheme the trivial module and section 1 give U = X. On a DVR,
the section given by a uniformizer cuts out the generic-point open, while section 1
handles the closed point. When the chosen affine open is the whole integral component,
the boundary product is empty and gives the unit ideal, so its canonical section is
nonvanishing everywhere there. For disconnected X the clopen extension uses section
zero on the other components; the statement imposes no unintended nonvanishing there.
Projective-space hyperplane complements give the familiar nontrivial line-module case.
There is no characteristic, dimension, connectedness or nonemptiness restriction.

Searches actually run via msearch.py:

- grep: `regular.*[Aa]mple|[Aa]mple.*regular|affine.*section.*cover` in `AlgebraicGeometry`. Service successful: 0 hits. No match.
- loogle: `AlgebraicGeometry.Scheme, "regular", "ample"`. Service successful: 0 hits. No match.
- leanfinder: `A quasi compact regular separated scheme has affine open neighborhoods given by nonvanishing global sections of invertible modules`. Service successful: 8 hits. Hits concern ordinary affine/basic opens, quasi-affine criteria, and structure-sheaf section localization; none assert the line-module result for regular separated schemes.
- leansearch: `Every regular separated quasi compact scheme has affine neighborhoods defined by global sections of invertible modules`. Service successful: 8 hits. Hits concern ordinary affine/basic opens, quasi-affine criteria, and structure-sheaf section localization; none assert the line-module result for regular separated schemes.

Additional direct rg searches in both `lean/WeilConjectures` and `lean/Sheaf` for
`regular.*[Aa]mple|[Aa]mple.*regular|HasAmpleFamily|affine_line_section` and the item id
found no exact result. The candidate
`WeilConjectures.AlgebraicGeometry.Modules.AmpleFamily` was opened: `Scheme.HasAmpleFamily`
asks for ONE invertible module with finitely many sections, so it is stronger than the
pointwise varying modules here and must not replace this statement. The exact proposed
declaration name was also searched in both source roots and `dag/lean_names_upstream.json`;
there was no collision. There was no repair-note file for this item.

Validation: single-file server compilation via the prescribed scompile.py; final
preflight and delivery results are recorded below. All variables and universes are
explicit, `autoImplicit` is false, and the theorem's proof is only `sorry`.

No STATEMENT-DISPUTED issue or node fault was found.

The required deliver2.py --no-push dry run passed server preflight and compilation
(commit 410bca03695; nothing pushed in the dry run).

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

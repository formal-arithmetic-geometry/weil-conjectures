## Worker report

The module `lean/Sheaf/AlgebraicGeometry/SeparatedOpenInduction.lean` states
`AlgebraicGeometry.separated_quasiCompact_open_induction`. It uses `X.Opens` as the
notion of an open subscheme of `X`, with `U.toScheme` the restricted scheme and
`U.ι` its open immersion.

The node's hypotheses are rendered as follows. The ambient scheme is
`(X : Scheme.{u})` with `[CompactSpace X]` (quasi-compact) and
`[QuasiSeparatedSpace X]` (quasi-separated). The property is
`(P : X.Opens → Prop)`. The affine hypothesis is
`h_affine : ∀ U : X.Opens, IsAffine U.toScheme → P U`. The gluing hypothesis is
`h_glue : ∀ (U V : X.Opens), QuasiCompact U.ι → IsAffine V.toScheme →
P U → P V → P (U ⊓ V) → P (U ⊔ V)`. The conclusion quantifies a separated
quasi-compact open as `(W : X.Opens)`, `hW_qc : QuasiCompact W.ι`, and
`hW_sep : W.toScheme.IsSeparated`, and concludes `P W`.
The proof is `sorry`, as required for a stage-2 statement.

Dependency declarations used: `AlgebraicGeometry.Scheme` from Mathlib for
`Scheme` (the `def-pc-scheme` leaf); `CompactSpace`, `QuasiSeparatedSpace`,
`Scheme.Opens`, `Scheme.Opens.toScheme`, `Scheme.Opens.ι`, `QuasiCompact`,
`IsAffine`, and `Scheme.IsSeparated` from Mathlib. The conventions node
`def-weil-pbc-scheme-conventions` fixes these meanings but has no declaration.

Edge cases checked: the empty open and the empty scheme are included by
`X.Opens`; affine opens satisfy the affine premise; the one-affine case is the
base case and two affines use `U ⊓ V`; no nonemptiness or dimension assumptions
are introduced. The universe `u` is explicit.

Searches made: `msearch.py ... leanfinder "induction principle for separated
quasi-compact open subschemes"` found Mathlib's more general
`AlgebraicGeometry.compact_open_induction_on`, but it has a different empty-open
and compact-open formulation and does not state the separated conclusion;
therefore it is not an exact match. `msearch.py ... loogle "QuasiCompact
IsAffine Opens induction gluing"` returned no hits (unknown identifier in the
query). `msearch.py ... grep "separated_quasiCompact_open_induction|finite
affine cover" AlgebraicGeometry` returned no hits. `rg` over
`WeilConjectures/` and `lean/Sheaf/` found no declaration of this statement.

No `STATEMENT-DISPUTED` issue or node fault found.

## Earlier second reading (a previous round; superseded)

Pending the independent second reading required by the delivery workflow.

## Second reading by E1

I reread the node `lem-sc-invert-s-cohomology-separated-induction`, its source place
(Cohomology of Schemes, Lemma 08DR, proof's first induction), and the complete Lean
module. The correspondence is:

- The object (X), a quasi-compact and quasi-separated scheme, is
  `(X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]`; these are the
  underlying-space and diagonal conditions used by the Mathlib scheme API.
- The property (P) of open subschemes is `(P : X.Opens → Prop)`. This is the
  standard Lean encoding of a predicate on opens; the hypotheses and conclusion
  restrict its required applications to quasi-compact opens.
- “P holds for every affine open” is
  `h_affine : ∀ U : X.Opens, IsAffine U.toScheme → P U`.
- The gluing premise, with the source's (U) quasi-compact, (V) affine, and
  all three input instances of (P), is exactly
  `h_glue : ∀ (U V : X.Opens), QuasiCompact U.ι → IsAffine V.toScheme →
  P U → P V → P (U ⊓ V) → P (U ⊔ V)`.
- The conclusion's separated quasi-compact open (W) is introduced as
  `(W : X.Opens) (hW_qc : QuasiCompact W.ι)
  (hW_sep : W.toScheme.IsSeparated)`, and the conclusion is `P W`.

No hypothesis is added or omitted, and the quantifier order matches the node. The
source's finite-affine-cover and induction details occur in the statement's proof
docstring and are left as `sorry`, as required for stage 2. Empty opens and empty
schemes are admitted by `X.Opens`; zero or one affine in the cover is not excluded,
and the one-affine case is exactly `h_affine`. No characteristic, dimension,
nonemptiness, or extra finiteness assumption is present. The explicit universe `u`
allows all universes represented by the node.

I checked the dependency declarations and their signatures: `AlgebraicGeometry.Scheme`,
`CompactSpace`, `QuasiSeparatedSpace`, `Scheme.Opens`, `Scheme.Opens.toScheme`,
`Scheme.Opens.ι`, `QuasiCompact`, `IsAffine`, and `Scheme.IsSeparated` are the
Mathlib notions used by the module; the conventions dependency contributes no
separate declaration. Searches with `msearch.py` (LeanFinder and Loogle queries)
and `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf` found no exact statement.
Mathlib's `AlgebraicGeometry.compact_open_induction_on` is more general in a
different direction (compact opens and an explicit empty-open case), so it is not an
exact match and was not substituted.

No mismatch was found and no source or node correction was needed. The module was
compiled with `scompile.py` and compiled cleanly; its only proof is the required
`sorry`.

## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmoothSurjectiveFppfLocality`
states `AlgebraicGeometry.AlgebraicSpace.smooth_surjective_fppf_locality`, with its
entire proof postponed by `sorry`. There are no new definitions or auxiliary theorems.
The mathematical statement and proof plan of the item are unchanged. Four existing,
already landed definition nodes were added to `stmt_deps` to own the interfaces used:
`def-sfb-space-morphism-properties`,
`def-trf-algebraic-space-jointly-surjective-family`,
`def-sfb-space-sheaf-fibre-product`, and `def-trf-scheme-algebraic-space`.

Sources read: Stacks `spaces-descent.tex`, `lemma-descending-property-smooth`
(Tag 0429) and `lemma-descending-property-surjective` (Tag 041Q);
`spaces-morphisms.tex`, `lemma-base-change-smooth` (Tag 03ZE) and
`lemma-base-change-surjective` (Tag 03MH). These state fpqc locality and arbitrary
base-change stability; the item asks for their fppf specialization. The theorem docstring
includes all five steps of the accepted proof plan and their dependency citations.

Hypothesis and clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`. Scheme morphisms are Mathlib
  `Scheme.Hom`, and `X Y Y' : AlgebraicSpace S` are the recorded full subcategory of
  big fppf sheaves, with no chosen atlas or representability assumption on `f`.
- `MapIsLocally (@Smooth) f` means exactly that every compatible pair of representable
  etale scheme charts has a smooth scheme map. Its definition quantifies `U V : Over S`,
  chart maps `a b`, and `h : U ⟶ V`, with both etaleness hypotheses and the commuting
  square. `Smooth` is the existing scheme smoothness class from the smoothness node.
- Surjectivity on field-valued point classes is
  `IsJointlySurjective (fun _ : Unit ↦ f.hom.hom)`. Unfolding the recorded predicate
  says that every section over `Spec K` lifts through `f` after some field extension
  `K →+* L`. The unique index adds no condition. This is the field-class surjectivity
  specified by the item, including nonrepresentable space maps. It does not use the
  stronger representable-map predicate `AlgebraicSpace.IsSurjective`.
- Conjunct 1 quantifies arbitrary `f : X ⟶ Y` and `g : Y' ⟶ Y`, with smoothness
  as its only premise and smoothness of `enlargedFibreProductFst g f` as conclusion.
- Conjunct 2 has the same arbitrary maps, with point-surjectivity as its only premise
  and point-surjectivity of that projection as conclusion. Neither clause assumes
  the other property.
- In conjuncts 3 and 4 the scheme target is `T : Over S`, embedded by `schemeSpace T`;
  `X : AlgebraicSpace S` and `f : X ⟶ schemeSpace T` remain arbitrary.
  The family has arbitrary `{I : Type w}`, `Tᵢ : I → Over S`, and
  `g : ∀ i, Tᵢ i ⟶ T`. Its covering hypothesis is precisely membership of
  `Presieve.ofArrows (fun i ↦ (Tᵢ i).left) (fun i ↦ (g i).left)` in
  `Scheme.fppfPrecoverage T.left`, hence jointly surjective flat locally finitely
  presented maps. No quasi-compactness of individual family arrows is imposed.
- Conjunct 3 is the smoothness iff for all members; conjunct 4 is the separate
  point-surjectivity iff. In both clauses the scheme cover arrow is its Yoneda map
  bundled by `ObjectProperty.homMk`, and its base change is
  `enlargedFibreProductFst` of that arrow and `f`.
- This projection is literally `Limits.pullback.fst` of the two underlying sheaf
  maps, bundled as a space. Its ordering is `Y' ×_Y X → Y'`, canonically the same
  base-change projection as the item's `X ×_Y Y' → Y'`.
- All schemes and fields use the same explicit `u`, and covering indices use an
  arbitrary explicit `w`. No field test is restricted to a smaller universe.
  There are no finite type, separation, quasi-compactness, nonemptiness, or
  finite-dimensionality hypotheses on `f`.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith`, and `IsEtale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
  The dependency's recorded declaration names the existing class. Relative dimension
  and etaleness are additional clauses of that dependency, not conditions of this item.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsLocally`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`: `IsJointlySurjective`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`. These justify the sheaf fibre products and point usage.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `enlargedFibreProduct`, and `enlargedFibreProductFst`, whose actual data were read.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage` and
  `Scheme.fppfTopology`. The size-convention dependency is metatheoretic and introduces
  no separate declaration or import.

The plain proof imports expose the recorded presentation criterion, etale scheme
locality, representable-etale scheme tests, point representatives, the scheme fpqc-family
property-descent theorem, proper/smooth base change, smooth fpqc descent, and residue
fields. Mathlib leaf proofs for fppf base change and fppf-to-fpqc covering inclusion
are supplied through the existing Fpqc imports. All postponed work is the one theorem
matching this DAG node.

Edge cases checked: an empty covering forces the target scheme empty, and then the
source space is empty as well; both iff statements remain true. Empty members of a
nonempty covering are allowed. Empty sources are smooth, while surjectivity requires
an empty target. A map to the empty target has empty source. Arbitrary space base
change includes identity and empty base change. Positive-dimensional smooth maps
need not be representable, so point-surjectivity must allow arbitrary space maps and
field extensions. Disconnected and non-quasi-compact maps are not excluded. Both
properties are treated independently throughout. No statement dispute was found.

Searches actually run with `msearch.py Q21 lem-sfb-space-smooth-surjective-fppf-locality`:

- LeanFinder: “Smoothness and surjectivity of algebraic space morphisms are stable
  under base change and local on a scheme target for fppf coverings”. Eight results
  concerned scheme surjectivity, precoverages and stalks; none states this space theorem.
- Loogle: `AlgebraicGeometry.Smooth, AlgebraicGeometry.AlgebraicSpace.MapIsLocally`.
  Zero hits; the service reported unknown identifier for the project predicate.
- Mathlib grep: `AlgebraicSpace|[Ss]mooth.*[Dd]escent|[Ss]urjective.*[Dd]escent`
  in AlgebraicGeometry. One hit, the scheme surjectivity fpqc descent docstring in
  `Morphisms/FlatDescent.lean`; no space theorem.
- LeanSearch: “Smoothness of morphisms of algebraic spaces descends along fppf
  covering families”. Eight hits on scheme smoothness and scheme flat descent,
  none states the space assertion.
- Direct `rg` searches of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `smooth_surjective_fppf_locality` found no existing
  declaration; grep for this item's id in `lean/WeilConjectures` found no attachment.
  Broader smooth/fppf/locality searches found related theorem docstrings and the
  sibling `flat_proper_fp_locality`, but no exact statement. Searches for chartwise
  smoothness, surjectivity, schemeSpace and enlargedFibreProduct found the reused
  definitions above. The existing singleton-family predicate supplies surjectivity
  without a new alias or new definition node.

Validation: `scompile.py` compiled the sandbox and library module cleanly (3.9 s and
2.4 s on the server). The exact final module is also compiled by delivery dry run.

## Second reading by Q21

This section records the worker's own second pass; the maintainer performs the
independent review after delivery. No other agents were started, as the brief requires.
Reopened the node, all four Lean conjuncts, and the definitions MapIsLocally,
IsJointlySurjective, schemeSpace and enlargedFibreProductFst. The two separate
implications have only their respective property as premise; the two fppf equivalences
use exactly the same family and canonical projection. Verified that the singleton
surjectivity predicate allows field extensions and does not require representability,
that the fibre product order only swaps factors, and that arbitrary empty index types
and source/target emptiness remain included. Checked that autoImplicit is false,
universes are explicitly declared, the signature is recorded verbatim, and the only
sorry is the entire named theorem proof. No mathematical mismatch found; added direct
public imports of Fpqc and the fibre-product dependency for the final module header.

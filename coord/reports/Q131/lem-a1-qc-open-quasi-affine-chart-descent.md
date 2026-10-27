## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiCompactOpenQuasiAffineChartDescent` states
`AlgebraicGeometry.isQuasiAffineHom_quasiCompact_open_of_affine_charts`, with its single
proof postponed by `sorry`. It gives both the relative conclusion and the final absolute
conclusion. No definition, new node, dependency repair, or statement correction is needed.

Read the item's full statement, source and five proof steps; all three statement-dependency
nodes and their recorded source declarations/docstrings; the five proof-dependency records;
and Stacks `more-morphisms.tex`, definition-ind-quasi-affine and
lemma-ind-quasi-affine-alternative-definition (Tags 0AP6 and 0F1U). The source's
(3) implies (4), together with its affine-target equivalence (1) iff (2), gives this node.
There is no repair-note file for this item in the read clone. The prescribed CompactObject
example module is now withdrawn, so the current QuasiAffineTargetLocality module and the
standing brief supply the module-mode conventions.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Schemes X and Y, and a scheme morphism f | `{X Y : Scheme.{u}} (f : X ⟶ Y)` |
| Affine open cover indexed by I | `{I : Type v} (U : I → Y.Opens)`, `hU : ∀ i : I, IsAffineOpen (U i)`, and `hcover : iSup U = ⊤` |
| Every quasi-compact open in each inverse-image chart is quasi-affine | `hlocal : ∀ (i : I) (L : (f ⁻¹ᵁ U i).toScheme.Opens), IsCompact (L : Set (f ⁻¹ᵁ U i).toScheme) → L.toScheme.IsQuasiAffine` |
| Quasi-compact target open V | `(V : Y.Opens) (hV : IsCompact (V : Set Y))` |
| Quasi-separatedness of V itself | `[QuasiSeparatedSpace V.toScheme]` |
| Open K inside the inverse image of V | `(K : (f ⁻¹ᵁ V).toScheme.Opens)` |
| Quasi-compactness of K | `hK : IsCompact (K : Set (f ⁻¹ᵁ V).toScheme)` |
| The induced K → V is quasi-affine | `IsQuasiAffineHom (K.ι ≫ (f ∣_ V))` |
| If V is affine, K is a quasi-affine scheme | second conjunct `IsAffineOpen V → K.toScheme.IsQuasiAffine` |
| No compactness or separation imposed on X, Y, f | no such binders; all size, compactness and separation hypotheses appear above |

`IsCompact` means finite-subcover compactness, without a Hausdorff assumption. For an open
subscheme it is equivalent to compactness of its subtype space. Nested opens therefore give
exactly the opens in the node, rather than imposing compactness on the enclosing inverse
image. Mathlib's `Scheme.IsQuasiAffine` includes compactness and the canonical affine
embedding, and is exactly the node's quasi-compact-open-in-an-affine notion. In particular
it does not mean arbitrary, possibly non-quasi-compact opens in affine schemes.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, and
  `Scheme.Opens` for the scheme and morphism dependency `def-pc-scheme`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`:
  `AlgebraicGeometry.IsQuasiAffineHom`, the exact recorded declaration of
  `def-nagata-quasi-affine-morphism`. Its field is the absolute quasi-affineness of every
  affine-open preimage. Its public Mathlib import provides `Scheme.IsQuasiAffine`.
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`: `AlgebraicGeometry.QuasiSeparated`
  and `quasiSeparated_iff_quasiSeparatedSpace` validate the scheme specialization
  `QuasiSeparatedSpace V.toScheme` of `def-weil-quasi-separated-morphism`.
- The existing `morphismRestrict` and `Scheme.Opens.ι` give the actual induced morphism;
  no arbitrary morphism or new map definition replaces it.

The statement modules are publicly imported. For the proof plan the file also imports
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` for `def-weil-finite-type-morphism`
(`QuasiCompact`), `Mathlib.AlgebraicGeometry.AffineScheme` for
`lem-weil-pbc-affine-opens-basis` (`Scheme.isBasis_affineOpens`), and
`Sheaf.AlgebraicGeometry.QuasiAffineTargetLocality` for
`lem-a1-quasi-affine-target-locality`
(`isQuasiAffineHom_iff_of_affine_open_cover`). The publicly imported QuasiSeparated
module also provides `quasiCompact_of_compactSpace` for
`lem-weil-pbc-qcqs-morphism-permanence`. The declaration docstring reproduces all five
proof steps and their named dependencies.

Edge cases checked before writing: I may be empty (the cover equality then forces Y,
and hence X and K, empty); V and K may be empty; no nonemptiness assumption is added.
Infinite affine covers are allowed, with independent index universe v. Arbitrary
non-quasi-separated X and Y are allowed; only V is quasi-separated. No separation or
quasi-compactness of f is assumed. Intersections of cover charts with V are not presumed
affine or compact: the proof uses affine refinements and compactness of K → V instead.
The node explicitly assumes compactness of V, so `hV` is retained even though its proof
can use the weaker input of a quasi-separated V. No finite-type hypothesis is present.

Searches for an existing statement, using the prescribed msearch.py wrapper:

- LeanFinder query: "For a scheme morphism and an affine cover of the target, if all
  quasi compact opens in the inverse images are quasi affine then a quasi compact open
  over a quasi separated open is quasi affine over it". Eight hits, including
  `Scheme.IsQuasiAffine.of_isAffineHom`, `quasiCompact_iff_forall_isAffineOpen`,
  `quasiCompact_iff_forall_affine`, `quasiSeparated_over_affine_iff`, and
  `Scheme.IsQuasiAffine.of_isImmersion`; none states the chart-descent implication.
- Loogle query: `"IsQuasiAffine", "IsAffineOpen"`. No hits.
- Mathlib grep query: `IsQuasiAffine|quasiAffine` in
  `AlgebraicGeometry/QuasiAffine.lean`. Five hits, the absolute quasi-affine definition
  and introductory/instance lines, not the item.
- LeanSearch query: "quasi affineness of compact opens descends from affine target
  charts for any scheme morphism". Eight hits, including the absolute constructor,
  immersion and affine-morphism criteria, `IsQuasiAffine.of_forall_exists_mem_basicOpen`,
  and quasi-compact preimage criteria; no exact match.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for `QuasiAffine`, `quasiAffine`,
  and `qc_open` found the recorded upstream class, target-locality statement,
  ind-quasi-affine permanence, and unrelated quasi-affine results. Read the class,
  target-locality and permanence modules. The permanence theorem does not give this
  precise quasi-compact/quasi-separated-open conclusion as an existing declaration.
- Direct rg across both source trees and `dag/lean_names_upstream.json` for
  `lem-a1-qc-open-quasi-affine-chart-descent|quasi_affine_chart|quasiAffineChart|quasiAffine.*cover`
  found no existing statement/name; the exact item id had no upstream occurrence.

Search results are also recorded by msearch.py in the sandbox's searches.jsonl.
No statement dispute or node fault was found.

## Second reading by Q131

Author's second pass (no separate agent was started, as the dispatcher brief forbids it):
reopened the node and the generated Lean file and checked every row of the correspondence
table. Both quasi-affine meanings use their recorded canonical definitions. Compactness of
V, quasi-separatedness of V, and compactness of K are all retained separately. The local
quantifier ranges over every open of each inverse-image scheme, not only opens pulled
back from the target; the induced map uses the actual restriction of f. The two conjuncts
retain both conclusions. The independent cover universe does not restrict the schemes,
and no nonempty or finite cover is assumed. No mismatch or change was needed.

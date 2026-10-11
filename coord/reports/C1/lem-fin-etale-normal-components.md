## Worker report

The module `lean/Sheaf/AlgebraicGeometry/EtaleNormalComponents.lean` states
`AlgebraicGeometry.Etale.exists_clopen_normal_integral_components`, with its sole proof
`sorry`. No new definition, dependency module, or statement correction is needed.

Hypotheses and conclusions, matched individually:
- Schemes W and Y and their morphism: `{W Y : Scheme.{u}} (f : W ⟶ Y)`.
- The morphism is etale: `[Etale f]`, the Mathlib notion specified by the convention node.
- W is Noetherian: `[IsNoetherian W]`, locally Noetherian and quasi-compact, without any
  Noetherian assumption on Y.
- Y is normal integral: `hY : IsNormalScheme Y`. This dependency definition includes
  `IsIntegral Y` and `IsDomain` and `IsIntegrallyClosed` at every stalk, so a second
  integrality binder is unnecessary.
- Finitely many pieces: `∃ (n : ℕ) (U : Fin n → W.Opens)`.
- Each piece is open: its type is `W.Opens`; its scheme is the actual restriction
  `(U i).toScheme`, with the canonical open immersion into W.
- Each piece is closed: `∀ i, IsClosed (U i : Set W)`.
- The union is disjoint: `∀ i j, i ≠ j → Disjoint (U i) (U j)`.
- The pieces cover W: `(⨆ i, U i) = ⊤`.
- Each piece is normal and integral: `∀ i, IsNormalScheme (U i).toScheme`.
  Thus these are genuine clopen subschemes of W, rather than unrelated schemes with the
  same topological spaces. A disjoint open cover gives exactly the scheme disjoint union.

Dependency declarations read and used:
- `def-weil-pbc-scheme-conventions` is a convention record with no module/declaration.
  Its etale entry is Mathlib `AlgebraicGeometry.Etale`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` (imported through NormalScheme).
  The full class signature/docstring defines etaleness on affine section ring maps.
- `def-sbc-normal-dominant-galois`: `Sheaf.AlgebraicGeometry.NormalScheme`,
  `AlgebraicGeometry.IsNormalScheme`. Read its full definition and docstring: integrality
  together with every stalk being an integrally closed domain. Other bundled declarations
  of this dependency concern unused notions and are not needed here.
- `Mathlib.AlgebraicGeometry.Noetherian`, `AlgebraicGeometry.IsNoetherian`: locally
  Noetherian plus compact, read class signature/docstring.
- `Mathlib.AlgebraicGeometry.Restrict`, `AlgebraicGeometry.Scheme.Opens.toScheme`:
  restriction to the given open subset, read definition/docstring.
- `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral` (used by the
  normal definition), read signature/docstring and the reducedness instance.

Edge cases: W may be empty, with `n = 0`; no Nonempty or positive-n binder excludes it.
A singleton decomposition is permitted. Each indexed piece is nonempty because the
normal definition includes integrality. Empty pieces therefore cannot be inserted into
an otherwise nonempty decomposition. No finite, separated, surjective, or dominant
hypothesis is imposed on f. No field or characteristic is fixed. Schemes have arbitrary
explicit universe u; using Fin n loses no finite family in any universe. Y cannot be
empty, exactly as its integrality hypothesis requires.

Searches (2026-10-11):
- msearch leanfinder: "An etale scheme over a normal integral scheme with Noetherian source
  is a finite disjoint union of open and closed normal integral schemes". Eight hits:
  normalization instances, `IsEtale.of_comp`, etale-locus and etale algebra over a field
  results; none is the statement. The field result is a special case.
- msearch loogle: `AlgebraicGeometry.IsNoetherian, AlgebraicGeometry.Etale`: zero hits.
- msearch grep: `normal.*etale|etale.*normal|[Dd]isjoint.*[Cc]omponent`, AlgebraicGeometry:
  zero hits.
- msearch leansearch: "Noetherian etale scheme over a normal integral scheme is a finite
  disjoint union of clopen normal integral schemes": service unavailable, Internal
  Server Error; other search kinds were used.
- rg of the source WeilConjectures and this project's lean/Sheaf for normal/etale and
  disjoint/finite components. Read the closest source theorem,
  `Etale.exists_opens_isOpenImmersion_and_henselianLocalRing_stalk` in
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale`: it adds separatedness and a
  separably closed function field and concerns open immersions, so is not a match.
  Topological component results do not state scheme normality ascent.
- rg of WeilConjectures for `lem-fin-etale-normal-components`: no occurrence.
- rg of Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  `exists_clopen_normal_integral_components|exists_clopen.*normal`: no name collision.

Source inspection: the referenced blueprint document is absent on this machine.
The node contains its statement and complete two-step proof, which the docstring follows.
Opened https://stacks.math.columbia.edu/tag/033C: Lemma 10.163.9 says normality ascends
along smooth ring maps; it supplies the normality input (etale maps are smooth), not the
whole finite component decomposition. The node's proof uses its exact etale-ring helper
`lem-weil-pbc-etale-over-normal-ring-normal`. No statement fault or disputed statement.

Validation: server single-file compilation passed in 1.7 seconds with no warnings or errors.
The delivery dry run printed OK: compilation and preflight passed except for the independent
second reading, which the second reader writes. Nothing was pushed.
The independent second reader must supply the second-reading section and deliver.

## Second reading by C1

Independent second reader, 2026-10-11. I opened the item node and delivered Lean,
then both statement-dependency nodes and the complete normal-scheme definition.
The statement is unchanged and matches the node clause by clause:

| Object, hypothesis or conclusion in the node | Lean rendering | Verdict |
| --- | --- | --- |
| Schemes W, Y and a morphism W to Y | `{W Y : Scheme.{u}} (f : W ⟶ Y)` | Same objects and quantifier order. |
| The morphism is etale | `[Etale f]` | Exact convention, no finiteness or separatedness added. |
| W is Noetherian | `[IsNoetherian W]` | Locally Noetherian plus compact; no assumption on Y. |
| Y is normal integral | `(hY : IsNormalScheme Y)` | Includes integrality and normal domain stalks. |
| Finitely many pieces | `∃ (n : ℕ) (U : Fin n → W.Opens)` | Any finite decomposition can be enumerated this way. |
| Open subschemes of W | `W.Opens` and `(U i).toScheme` | Actual restrictions of W, with canonical inclusions. |
| Pieces are closed as well as open | `∀ i, IsClosed (U i : Set W)` | Exact closedness of the underlying subsets. |
| Disjoint union | `∀ i j, i ≠ j → Disjoint (U i) (U j)` | Pairwise disjoint pieces. |
| The union equals W | `(⨆ i, U i) = ⊤` | Covers the whole scheme. A disjoint open cover is a scheme disjoint union. |
| Each piece is normal integral | `∀ i, IsNormalScheme (U i).toScheme` | Both clauses, using the dependency notion. |

Dependency verification: `def-weil-pbc-scheme-conventions` is a pointer bundle,
so I followed its etale pointer to `def-weil-etale-morphism`. Its recorded
`AlgebraicGeometry.Etale` is the affine-local ring-map class in Mathlib
`Morphisms/Etale.lean:41`. I read `Etale.iff_flat_and_formallyUnramified` as well:
it gives flatness, formal unramifiedness and local finite presentation, matching
the convention's definition through the diagonal criterion recorded there.
`def-sbc-normal-dominant-galois` defines normal here to include integral, exactly
as `NormalScheme.lean:33` does: `IsIntegral S` and `IsDomain` plus
`IsIntegrallyClosed` at every stalk. No other declaration of that bundle enters
this theorem. I read Mathlib's `IsIntegral`, its equivalence with irreducibility
and reducedness, `IsNoetherian`, and `Scheme.Opens.toScheme` and its canonical
open immersion. The delivered module uses the existing definitions throughout.
No new node or dependency module is delivered, so H12/H13 introduce no extra review.

Source verification: the blueprint file is absent locally, and its pinned raw
GitHub path returns HTTP 404. The item node preserves the blueprint statement
and its two proof steps. I independently opened Stacks Tag 033C and fetched
`algebra.tex` into this item's scratchpad, reading `lemma-normal-goes-up` at
line 46563. It assumes only a smooth ring map and a normal source ring; its
Noetherian case is followed by the general case, so it does not justify adding
Noetherianness of Y. I also fetched `properties.tex` and read
`lemma-normal-locally-finite-nr-irreducibles` (Tag 0357) and
`lemma-normal-Noetherian` immediately after it. These give the disjoint union
of normal integral schemes and its finite version for a Noetherian scheme.
Their normality means normal domain stalks without global integrality; the
item correctly applies integrality only to Y and the individual components,
not to W. The docstring follows both DAG proof steps: affine normality ascent,
then finitely many disjoint irreducible components, clopenness and integrality.

Edge cases: empty W permits n = 0 and the empty supremum equals top precisely
on the empty space. Nonempty W cannot be covered with n = 0. Empty indexed
pieces are excluded by their integrality, which loses no decomposition because
empty pieces can be discarded. A single component is permitted. Y is nonempty
because the node assumes integral. No field, characteristic, dominance,
surjectivity, separatedness or finiteness of f is assumed. Universe u is
explicitly bound and arbitrary; Mathlib scheme morphisms use a common universe,
and Fin n can index any finite family irrespective of the components' universe.
No unbound section variable or implicit universe remains.

Independent searches, using different wording from the first reader:
- `msearch leanfinder`: "A locally Noetherian scheme with domain local rings has
  disjoint irreducible components which are open and closed". Eight results;
  the closest is `finite_irreducibleComponents_of_isNoetherian`, which gives
  only finiteness, not etale normality ascent or the decomposition theorem.
- `msearch loogle`: `AlgebraicGeometry.IsIntegral, AlgebraicGeometry.Etale`:
  zero results.
- `msearch grep`: `IsIntegrallyClosed.*stalk|clopen.*integral|integral.*components|components.*normal`:
  four unrelated results, no scheme theorem.
- `msearch leansearch`: "Etale morphism from a Noetherian scheme decomposes the
  source into finitely many integral normal open subschemes when the base is
  normal integral": service unavailable, Internal Server Error.
- Direct rg over WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for `exists_clopen_normal_integral_components|clopen.*normal|normal.*components|components.*normal|IsNormalScheme`.
  The existing normal definition is reused. I opened the nearby source results
  `Etale.exists_opens_isOpenImmersion_and_henselianLocalRing_stalk` and
  `Etale.exists_finite_opens_isOpenImmersion_of_isSepClosed_functionField`:
  both require separatedness and a separably closed function field and assert
  open immersions into the base, so neither states this node. The Smooth
  module's component discussion concerns dimension over a field, also not a match.

Mismatches and changes: none in the node or Lean. I appended this independent
review and left the worker report and correct statement intact. There are no
hollow definitions or proved auxiliary statements in the delivery: the sole
proof is `sorry`. Module and declaration docstrings give the source place and
blueprint id. The recorded `lean.statement` was checked programmatically to
be verbatim equal to the signature in the file. Server single-file compilation
via scompile passed (exit 0, 1.7 seconds), with no errors or warnings.

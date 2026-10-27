## Worker report

States `CategoryTheory.spectralSequence_stationary_bottom_row` in
`Sheaf.CategoryTheory.StationaryBottomRow`, with proof `sorry`. The node is unchanged
except for its `lean` record. There are no new notions, nodes, dependency repairs,
or statement corrections.

Hypotheses and objects:

- `{C : Type u} [Category.{v} C] [Abelian C]` is the arbitrary abelian category;
  object and morphism universes are independent and explicitly declared.
- `E : E₂CohomologicalSpectralSequence C` is exactly Mathlib's
  `SpectralSequence C (fun r ↦ ComplexShape.up' (r,1-r)) 2`. Its indices are
  integer pairs, its differential has bidegree `(r,1-r)`, and `E.iso` is the
  specified homology-to-next-page isomorphism, with the orientation in the node.
- `hsupport : ∀ (r : ℤ) (hr : 2 ≤ r) (p q : ℤ), p < 0 ∨ q ≠ 0 →
  IsZero ((E.page r hr).X (p,q))` is the entire all-page support hypothesis.
  No convergence, abutment, or page-two-only hypothesis is substituted for it.
- Mathlib's `(E.page r hr).sc (p,q)` is the short complex through this entry.
  For shape `up' (r,1-r)`, its previous and next indices are
  `(p-r,q+r-1)` and `(p+r,q-r+1)`. `cycles`, `iCycles`, `homology` and
  `homologyπ` are its actual canonical cycles and homology, with the kernel
  inclusion and homology quotient from the node. No auxiliary choice of maps
  or independent short complex is introduced.

Conclusions, clause by clause:

- The first conjunct quantifies all integer `p,q,r`, with `hr : 2 ≤ r` and
  `max p (q+1) < r`. It asserts that the incoming and outgoing differentials
  at the exact indices above equal zero and that `iCycles` and `homologyπ`
  are isomorphisms.
- The second conjunct supplies isomorphisms `T p q r hr hl s hs hsl` between
  every pair of late pages. It includes `T r r = Iso.refl`, the composition
  law `T r s ≪≫ T s t = T r t` in arbitrary orders, and the consecutive-page
  normalization `iCycles ≫ (T r (r+1)).hom = homologyπ ≫ (E.iso ...).hom`.
  Since the first conjunct makes `iCycles` invertible, this is exactly
  `t_r = i_r⁻¹ ≫ π_r ≫ e_r`, not an unspecified existence of an isomorphism.
  Induction using the composition law expresses each forward `T` as the finite
  composite of those `t_r`; the identity and composition laws fix reverse `T`
  as inverses. Thus these are the node's canonical iterated comparisons.
- The final conjunct supplies isomorphisms `a n k` from `E₂^(n,0)` to
  `E_(k+2)^(n,0)`, for every `n,k : ℕ`. Natural `n` covers precisely every
  integer `n ≥ 0`, and the page encoding `k+2` covers precisely all pages `r ≥ 2`.
  Every `a n k` is an actual categorical isomorphism, not merely a morphism.
- `∀ n, a n 0 = Iso.refl _` is `a_(n,2) = 1`.
- For every `n,k`, the final five-part conjunction states both adjacent
  differentials vanish, the actual cycles inclusion and homology quotient are
  isomorphisms, and
  `iCycles ≫ (a n k).inv ≫ (a n (k+1)).hom = homologyπ ≫ e_(k+2)`.
  Cancellation of `iCycles` shows `(a n k).inv ≫ (a n (k+1)).hom = t_(k+2)`;
  composing with `(a n k).hom` gives exactly the node's successor recursion.
  Where the late-page `T` is available, its identical consecutive normalization
  makes these consecutive maps equal to `T` as well.
- Taking `k=n` gives the specified isomorphism to page `n+2`, which is the
  stable representative because `n+2 > max(n,1)`. This arithmetic description
  requires no new definition of an infinity page or any abutment. Taking `n=0`
  and `k=0` gives the required `a_(0,2) = 1` on page two itself.

Dependencies read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`; read the full class signature/docstring.
- `def-sp-spectral-sequence`: `CategoryTheory.SpectralSequence`,
  `Mathlib.Algebra.Homology.SpectralSequence.Basic`; read its structure, `page`,
  `iso`, morphism structure and the cohomological/page-two specializations.
  This is the sole public import, which also publicly imports the homology and
  abelian interfaces below.
- `lem-weil-pbc-short-complex-zero-homology` (proof dependency, Mathlib leaf):
  `CategoryTheory.ShortComplex.isZero_homology_of_isZero_X₂` and
  `CategoryTheory.ShortComplex.isIso_homologyπ` from
  `Mathlib.Algebra.Homology.ShortComplex.Homology`, and
  `CategoryTheory.ShortComplex.isIso_iCycles` from
  `Mathlib.Algebra.Homology.ShortComplex.LeftHomology`. Read all full signatures.
  The automatic homology instance is
  `CategoryTheory.categoryWithHomology_of_abelian` in
  `Mathlib.Algebra.Homology.ShortComplex.Abelian`. These are already imported
  through the public spectral sequence module, so no duplicate import is needed.

Source checks: read `literature/stacks-project/homology.tex`, definitions
`definition-spectral-sequence` and `definition-limit-spectral-sequence`
(Tags 011N and 011O), including the specified-isomorphism and starting-page
conventions. Read the statement and proof of `lemma-weil-pbc-cancellation` in
`literature/blueprint/latest/`; its row-collapse sentence uses these stationary
comparisons, while the present node intentionally assumes no abutment.
The declaration docstring records all four DAG proof steps and their uses.

Edge cases checked before writing: at `r=2,q=0` the incoming row is `1` and
outgoing row `-1`, so both differentials vanish. At `q≠0` the middle object
vanishes even if an adjacent object is in row zero. Negative `p` is allowed;
negative `q`, arbitrary integer bidegrees and any zero category are included.
The late-page bound is retained verbatim. `n=0,k=0` gives identity and stable
page two; arbitrary `k` covers all bottom-row pages. Both orders of late-page
comparison and equal pages are included by `T`, with composition in all orders.

Searches (all through the prescribed tools, before writing):

- `msearch.py ... leanfinder`, query: "A spectral sequence supported on row zero
  has canonical isomorphisms between consecutive pages and coherent finite
  composites". Eight hits, including `HomologicalComplex.isoSc'`,
  `xNextIsoSelf`, `xNextIso`, `xPrevIsoSelf`, `doubleXIso₀` and
  `ChainComplex.mkXIso`; none states this node.
- `msearch.py ... loogle`, query:
  `CategoryTheory.SpectralSequence.iso, CategoryTheory.ShortComplex.iCycles,
  CategoryTheory.ShortComplex.homologyπ`. Zero hits for the combined query;
  the actual declarations were read directly in Mathlib.
- `msearch.py ... grep`, query:
  `stationary|degener|pageXIso|isIso_iCycles|isIso_homologyπ`, subdirectory
  `Algebra/Homology`. Twenty-five hits, including the short-complex lemmas,
  `pageXIsoOfEq`, and spectral-object-specific page comparisons. None provides
  the entire support argument and canonical coherent page comparisons here.
- `msearch.py ... leansearch`, query: "Canonical stationary page isomorphisms
  of a cohomological spectral sequence supported in row zero". Eight hits,
  including `CochainComplex.fromSingle₀Equiv`, `HomologicalComplex.pOpcyclesIso`,
  `CochainComplex.isoHomologyπ₀` and group-cohomology degree-zero comparisons;
  none states this node.
- `rg` across `lean/WeilConjectures`, `lean/Sheaf`, Mathlib spectral-sequence
  sources and `dag/lean_names_upstream.json` for spectral-sequence, stationary,
  bottom-row and row-zero names; `grep -rn` for the item id in
  `lean/WeilConjectures` found no existing attachment. Read
  `WeilConjectures.CategoryTheory.SpectralSequenceNatRowZero` and
  `Sheaf.CategoryTheory.FirstQuadrantRowCollapse`: these assume an abutment
  and give edge/abutment conclusions, rather than the full present statement.
  `FilteredStationaryCycleComparison` concerns a filtered-complex quotient,
  while `FirstQuadrantLowestRowEdge` concerns a different survival locus and
  convergence data. No duplicate declaration was found.

Validation: the prescribed `scompile.py NJ lem-weil-pbc-stationary-bottom-row`
compiled the delivered module both as the sandbox module and at its final
library module path, with no errors or warnings. All theorem proofs are `sorry`;
there are no definitions with postponed data or unbound implicit variables.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

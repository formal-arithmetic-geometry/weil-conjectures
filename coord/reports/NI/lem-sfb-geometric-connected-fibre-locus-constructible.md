## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricConnectedFibreLocusConstructible` states
`AlgebraicGeometry.isLocallyConstructible_geometricConnectedComponentCount_levelSet`,
with its whole proof postponed by `sorry`. No definition or extra theorem is added.
The node is unchanged except for its `lean` record.

Source read: `literature/stacks-project/more-morphisms.tex`, Tag 055I,
`lemma-nr-geom-connected-components-constructible`, both the statement and the two
proof paragraphs (lines 8093–8132). The second paragraph explicitly proves the
Noetherian global clause. The declaration docstring gives the node's four proof
steps, including their dependency IDs.

Hypothesis and clause correspondence:

- Schemes Y and T and their morphism are `{Y T : Scheme.{u}} (f : Y ⟶ T)`.
- “Of finite presentation” is exactly `[LocallyOfFinitePresentation f]
  [QuasiCompact f] [QuasiSeparated f]`, as the recorded finite-presentation
  dependency's comparison clause specifies. These are properties of f itself.
- Every integer m ≥ 0 is covered by `(m : ℕ)`, including zero.
- For t in T the geometric fibre is
  `pullback f (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t)
  (AlgebraicClosure (T.residueField t)))) ≫ T.fromSpecResidueField t)`.
  This is precisely the pullback occurring in the recorded
  `geometricComponentCount_baseChange`, evaluated at the canonical algebraic
  closure. That theorem's first conjunct proves that any other algebraically
  closed residue-field extension gives the same count. There is no requirement
  that an arbitrary extension itself be algebraic.
- `ConnectedComponents` is the quotient by equality of connected components,
  not irreducible components. Each class corresponds to a maximal nonempty
  connected subset. `ENat.card` records an infinite number as infinity and zero
  exactly for an empty component type. Thus the displayed set comprehension,
  with equality to `(m : ℕ∞)`, is exactly E_m(f).
- The first conjunct is `Topology.IsLocallyConstructible` of that set.
  Its Mathlib definition is `∀ x, ∃ U ∈ 𝓝 x, IsOpen U ∧
  IsConstructible (U ↓∩ E)`: constructibility in the subspace U, exactly the
  node's open-neighbourhood formulation.
- The second conjunct is `IsNoetherian T → Topology.IsConstructible` of the
  identical set. Mathlib's `IsNoetherian` extends `IsLocallyNoetherian` and
  `CompactSpace T`, exactly the node's locally Noetherian and quasi-compact
  definition. This condition is only on the global clause, not the first clause.
- There is no smoothness, properness, flatness, section, normality, surjectivity
  or nonemptiness assumption, and no finiteness-of-components assumption.

Recorded statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`; the finite-presentation
  conjunction uses the standard `QuasiCompact` and `QuasiSeparated` classes.
- `lem-weil-pbc-geometric-component-count-base-change`:
  `Sheaf.AlgebraicGeometry.GeometricComponentCountBaseChange`,
  `AlgebraicGeometry.geometricComponentCount_baseChange`. Its full signature and
  docstring were read. Its `ENat.card (ConnectedComponents (pullback ...))`
  expression is used verbatim with the canonical algebraic closure substituted.
- `def-weil-constructible-subset`: its `mathlib_match` is
  `Mathlib.Topology.Constructible`, `Topology.IsConstructible`. The same module's
  `Topology.IsLocallyConstructible` provides exactly the required local notion.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`. That module also supplies the exact
  bundled `AlgebraicGeometry.IsNoetherian` used in the second conjunct.

All already stated proof dependencies are imported: generic constancy from
`Sheaf.AlgebraicGeometry.GeometricConnectedCountGenericConstancy`, the criterion
from `Sheaf.AlgebraicGeometry.NoetherianConstructibleSubsetCriterion`, affine
Noetherian approximation from
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`, and family
descent from `Sheaf.AlgebraicGeometry.FinitePresentationFamilyDescent`.
The remaining Mathlib proof interfaces (finite type, qcqs permanence, finite
type over a Noetherian base, affine qcqs, constructible preimages) are supplied
by the existing finite-presentation, quasi-separated and Noetherian imports.
No proof import was omitted for an import cycle.

Edge cases checked before writing: T empty makes the local clause vacuous and
its level set empty; Y empty gives count zero on all T, so E_0 = T and positive
level sets are empty. At any empty fibre the count is zero. Infinite component
types have `ENat.card = ⊤` and cannot satisfy equality to a finite m; `Nat.card`
was deliberately not used. Non-Noetherian T is allowed by the first conjunct.
No characteristic or field-size restriction is present: the canonical algebraic
closure of each residue field lives in the same universe u as that field and
schemes, and base-change independence is the existing theorem. The arbitrary
scheme universe u is explicit; auto-implicit and relaxed auto-implicit binding
are both disabled.

Searches made for an existing exact statement (2026-10-24):

- `msearch.py`, leanfinder: “For a morphism of finite presentation of schemes
  each finite level set of the number of geometric connected components of the
  fibres is locally constructible”. Eight hits: Chevalley images/preimages,
  local finite presentation/type, finite fibres and local quasi-finiteness.
  None states the count-level-set assertion.
- `msearch.py`, leansearch: “The finite level sets of geometric connected
  component counts for a morphism of finite presentation are locally
  constructible”. Eight hits: the definition of local constructibility and its
  closure properties, Chevalley images, and local-to-global constructibility.
  No count theorem.
- `msearch.py`, loogle: `AlgebraicGeometry.GeometricallyConnected,
  Topology.IsLocallyConstructible`. Zero hits.
- `msearch.py`, grep: `([Cc]onnected.*[Cc]onstructible|[Cc]omponent.*[Cc]ount)`
  in Mathlib/AlgebraicGeometry. Zero hits.
- `rg -n` across `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for connected/constructible, component/count
  and geometric component names: found the recorded base-change and generic
  constancy statements, proper-flat semicontinuity and proper-smooth local
  constancy. The trace-formula generic theorem counts irreducible components.
  Relative-section-component constructibility is a different locus. None is
  this general finite-presentation assertion. Searching the exact chosen new
  declaration name in Mathlib and both project roots found no collision.
- `grep -rn` for the item ID in `lean/WeilConjectures`: no match.

There is no statement correction, disputed statement, dependency repair or new
node. The suggested old CompactObject example module is withdrawn; its node now
points to the upstream `WeilConjectures.CategoryTheory.CompactObject`, which was
read for the current module/public-import/docstring conventions.

Validation: `scompile.py NI lem-sfb-geometric-connected-fibre-locus-constructible`
compiled this module against the published live library, both the sandbox and
library-name checks, cleanly (7.9 s and 9.7 s); no errors or non-sorry warnings.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

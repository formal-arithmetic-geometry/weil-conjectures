## Worker report

The module `Sheaf.AlgebraicGeometry.GroupoidSourcePullbackTranslation` states
`AlgebraicGeometry.groupoid_source_pullback_translation`, with one `sorry` and no new
helper definitions or theorems. The DAG statement is unchanged; only its `lean` record
is added. The sources read were Stacks `groupoids.tex`, Tag 02YE
(`lemma-diagram`, the two lower cartesian squares) and Tag 03BI
(`lemma-finite-locally-free-disjoint-free`, the comparison of fibre degrees).
There is no repair note for this item and no statement dispute.

Hypothesis and clause correspondence:

- Arbitrary schemes `U,R` are `{U R : Scheme.{u}}`, with the universe explicitly declared.
  The five structural morphisms are the explicit binders `s t`, `e`, `i`, `c`.
  Composition has domain `pullback s t`, and the exact recorded groupoid predicate is
  `hG : IsGroupoidScheme s t e i c`.
- The schemes called `P` and `Q` in the node are written directly as `pullback s t` and
  `pullback s s`. Their second projections are `pullback.snd s t` and `pullback.snd s s`.
  No alternative fibre products or groupoid definitions are introduced.
- `∃ F : pullback s t ≅ pullback s s` is the asserted scheme isomorphism. Its two forward
  projection equations give `(c,p₂)`; in particular, its second projection equation says
  that it lies over `R`. For every test scheme `H`, precomposition by `H ⟶ P` gives
  exactly `F(a,b)=(c(a,b),b)` by the pullback universal property.
- The inverse first-projection equation is
  `F.inv ≫ pullback.fst s t = pullback.lift (pullback.fst s s)
  (pullback.snd s s ≫ i) h ≫ c`. Together with the inverse second-projection equation
  it says precisely `G(d,b)=(c(d,i(b)),b)`, also after any test-scheme precomposition.
  The existential equality `h` supplies only the well-definedness of this particular
  fibre-product lift: `q₁ s = q₂ s = q₂ i t` by the pullback relation and
  `hG.inverse_target`. It does not restrict the groupoid, and no arbitrary map replaces
  composition. Both scheme-morphism inverse identities are the fields of `F : P ≅ Q`;
  there is no merely pointwise bijection here.
- The first conjunct contains no finite, flat, affine, finite-presentation or mono
  assumption. The conditional second conjunct starts with `s.IsFiniteLocallyFree →`,
  exactly the node's additional hypothesis, and makes no assumption on `t`.
- The node's `d(x)` is `(s.fiberToSpecResidueField x).finrankΓ`. The existing definition
  `finrankΓ` is `Module.finrank` of the global sections, with scalar structure
  `ΓAlgebra` induced by the displayed structural morphism to `Spec κ(x)`. Thus this is
  literally the node's residue-field dimension. It is used instead of `fiberDegree`
  because the latter requests an affine-morphism instance even to form its type;
  `finrankΓ` allows the conditional hypothesis to remain an ordinary implication.
- `∀ z : R, ... (t z) ... = ... (s z) ...` is exactly `d(t(z))=d(s(z))`.
- For every `r : ℕ` (including zero), `∃ V : U.Opens` with
  `∀ x, x ∈ V ↔ ... = r` identifies the open rank stratum without choosing another
  definition. `s ⁻¹ᵁ V = t ⁻¹ᵁ V` is equality in `R.Opens`, so it is equality of
  canonical open subschemes, not merely abstractly isomorphic schemes. This supplies
  the equivalent rank-stratum assertion, together with openness as stated in the node.

Recorded dependencies and their declarations read:

- `def-a1-groupoid-scheme`: `Sheaf.AlgebraicGeometry.GroupoidScheme`, full structure
  `AlgebraicGeometry.IsGroupoidScheme`. Read its six morphism equations and all five
  test-point laws, including their compatibility-proof binders. Its source convention
  is `c(a,b)=a ∘ b`, with `s(a)=t(b)`, as used here.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`, locally affine locally ringed spaces and their morphisms.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`, and their universal
  property. Schemes have the required pullbacks through the recorded groupoid import.
- `def-pc-finite-locally-free`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`,
  `Scheme.Hom.IsFiniteLocallyFree`, extending exactly `IsFinite`, `Flat`, and
  `LocallyOfFinitePresentation`; read also `IsFiniteLocallyFreeOfDegree`,
  `ΓAlgebra`, `finrankΓ`, `fiberAlgebra`, and `fiberDegree`.
- `def-weil-residue-field`: `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.residueField` and `Scheme.Hom.residueFieldMap`; the former is the quotient
  of the stalk by its maximal ideal and is the field used by the fibre morphism.
- Proof leaf `lem-weil-pbc-finite-flat-rank-iso` has no Lean record, as appropriate
  for its Mathlib status. Read its `mathlib_match` declarations in
  `Mathlib.AlgebraicGeometry.Morphisms.FlatRank`, including `Scheme.Hom.finrank`,
  `Scheme.Hom.finrank_of_isPullback`, and `Scheme.Hom.isLocallyConstant_finrank`.
  Its module is explicitly imported as a non-public proof import.

Edge cases checked before writing: the identity groupoid gives the identity translation;
a group scheme over a field gives the usual shearing isomorphism; the pair groupoid gives
`((x,y),(y,z)) ↦ ((x,z),(y,z))`, with the displayed inverse. The empty object scheme and
empty test scheme are allowed. There is no excluded positive-characteristic case, no
finite-type condition on translation, and rank zero is included. For a groupoid with
finite locally free source the identity section in fact makes the degree-zero stratum
empty, but no extra positivity conclusion is imposed. No relation-monomorphism
assumption is used. The universal morphism equations determine the test-point formulas
also on nonreduced test schemes, not just geometric points.

Searches actually run with `msearch.py` under this item:

- LeanFinder: `In an internal groupoid of schemes composition identifies composable
  pairs with pairs with the same source, and source fibre degree is invariant`.
  Eight hits: `Scheme.Cover.comp_idx_apply`, `Scheme.Cover.comp_app`,
  `Scheme.comp_base`, `Scheme.comp_coeBase`, `Scheme.Cover.exists_of_trans_eq_trans`,
  `Scheme.Hom.comp_base`, `Scheme.Cover.LocallyDirected.trans_comp`,
  `Scheme.comp_base_apply`. None states the requested groupoid isomorphism or degree
  invariance.
- Loogle: `"Groupoid", "pullback"`. Zero hits.
- Mathlib grep: `groupoid.*(pullback|degree|rank)|(pullback|degree|rank).*groupoid`.
  Zero hits.
- LeanSearch: `Composition in an internal groupoid of schemes gives an isomorphism of
  the source pullbacks and preserves finite locally free source degree`. Eight hits
  concerning chosen-pullback composition, core-category composition, finite-morphism
  composition, sheaf/module pullback composition and over-site pullback composition;
  none is this statement.
- `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `groupoid.*(pullback|degree|rank)|(pullback|degree|rank).*groupoid`, case-insensitively,
  and for the item id. The existing affine invariant-rank-strata theorem specializes
  to affine schemes, assumes both maps finite locally free and does not state this
  translation. `FieldGroupoidPointTranslation` concerns an automorphism over a field
  arising from one point with invertible residue maps, also a different statement.
  `AffineGroupoidInvariantNorm` contains a private cartesian-square lemma for another
  groupoid predicate, but no public declaration of this statement. The finitely
  presented rank-filtration module mentions this item only in its proof plan.
- Exact candidate declaration and module names were searched in both Lean roots and
  `dag/lean_names_upstream.json`: no collision. A node-id search under
  `lean/WeilConjectures` has no matching declaration.

The prescribed `scompile.py` server compilation passed in both sandbox and library
module modes with no errors or unexpected warnings. Every variable and universe is
explicitly bound; there is no file-local notation, instance, hidden choice or new data
definition. The only postponed proof is the named theorem above, and its docstring
records all four DAG proof steps.

## Delivery review

The worker delivers directly under the dispatcher's instructions. The maintainer's
independent review is the second reading; no independent worker reading is claimed here.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

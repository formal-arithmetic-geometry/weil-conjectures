## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteEtaleClosedSubschemeSection` states
`AlgebraicGeometry.Etale.exists_finite_clopen_opens_and_section_of_closedImmersion`.
It has one theorem with proof `sorry`, no definitions, and no auxiliary theorems.
The node changes only in `lean`; no new nodes or dependency modules are required.

Source checked directly: [Stacks 09ZA](https://stacks.math.columbia.edu/tag/09ZA),
Lemma 59.80.6, statement and both proof paragraphs. The local Stacks TeX is absent
on this machine, so the official page was read. The source agrees with the node;
there is no statement correction or disputed statement.

The hypotheses and clauses correspond as follows:

- Schemes `X`, `Z`, and `V`: `{X Z V : Scheme.{u}}`, with explicit universe `u`.
- `X` affine: `[IsAffine X]`.
- `X` integral: `[IsIntegral X]`, including nonemptiness, reducedness and
  irreducibility; its function field therefore has Mathlib's canonical field structure.
- Every local ring of `X` a normal domain: `hX : ∀ x : X,
  IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)`.
  This uses precisely the normal-domain clause of `def-weil-pbc-normal-ring`,
  without introducing a second normality predicate. The domain component also
  follows from integrality, but is retained to render the node's wording explicitly.
- Function field separably closed: `[IsSepClosed X.functionField]`.
  Mathlib `Scheme.functionField` is literally the stalk at the generic point,
  as specified by the node, not a separately chosen field extension.
- Closed subscheme `Z ⊆ X`: `(i : Z ⟶ X) [IsClosedImmersion i]`.
- Étale morphism `V → Z`: `(p : V ⟶ Z) [Etale p]`.
- `V` affine: `[IsAffine V]`.
- Finite number of components: `∃ (n : ℕ) (W : Fin n → V.Opens)`.
- Each component open in `V`: `W j` is already an element of `V.Opens`, and
  `(W j).ι` is the canonical open-subscheme inclusion with its restricted structure sheaf.
- Each component closed in `V`: `∀ j, IsClosed (W j : Set V)`.
- Disjointness: `∀ j k, j ≠ k → Disjoint (W j) (W k)`.
- Their union is all of `V`: `(⨆ j, W j) = ⊤`.
  Pairwise disjoint open subschemes covering `V` express its scheme coproduct
  decomposition; this is the same finite disjoint union, not just a cover with overlaps.
- Each restriction to `Z` an open immersion:
  `∀ j, IsOpenImmersion ((W j).ι ≫ p)`. Thus each component is isomorphic to an
  open subscheme of `Z`; no extra affineness of the components is required.
- If `p` is surjective and finite étale, it has a section:
  `Surjective p → IsFinite p → ∃ s : Z ⟶ V, s ≫ p = 𝟙 Z`.
  Étaleness is the shared `[Etale p]` hypothesis. The arrow equation says exactly
  `p ∘ s = id_Z`, with Lean's diagrammatic composition order.
- The two conclusions are joined by `∧`; the finite/surjective hypotheses are
  confined to the second clause and are not imposed on the decomposition clause.

Dependency declarations read and used (including full signatures and docstrings):

| Node | Module | Declaration used |
| --- | --- | --- |
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme, Scheme.Hom |
| def-pc-integral-scheme | Mathlib.AlgebraicGeometry.Properties | AlgebraicGeometry.IsIntegral |
| def-weil-pbc-normal-ring | Mathlib.RingTheory.IntegralClosure.IntegrallyClosed | IsIntegrallyClosed, IsDomain |
| def-pc-separably-closed | Mathlib.FieldTheory.IsSepClosed | IsSepClosed |
| def-weil-closed-immersion | Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion | AlgebraicGeometry.IsClosedImmersion |
| def-weil-etale-morphism | Mathlib.AlgebraicGeometry.Morphisms.Etale | AlgebraicGeometry.Etale |
| def-weil-open-immersion | Mathlib.AlgebraicGeometry.OpenImmersion | AlgebraicGeometry.IsOpenImmersion |
| def-weil-surjective-morphism | Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap | AlgebraicGeometry.Surjective |
| def-weil-finite-integral-morphism | Mathlib.AlgebraicGeometry.Morphisms.Finite | AlgebraicGeometry.IsFinite |

Additionally, `Mathlib.AlgebraicGeometry.FunctionField` supplies
`AlgebraicGeometry.Scheme.functionField`; `Mathlib.AlgebraicGeometry.AffineScheme`
supplies `AlgebraicGeometry.IsAffine`. Both signatures and docstrings were read.
Imports reach Scheme, Properties, AffineScheme, UnderlyingMap and OpenImmersion
transitively; the explicit imports provide the notions used in the signature.

Edge cases checked before writing:

- `X` cannot be empty because the node requires integrality, and `IsIntegral`
  includes `Nonempty X`; no extra hypothesis is added here.
- Empty `Z` and empty `V` are allowed. Taking `n = 0` gives the empty family;
  its supremum is bottom, which equals top on the empty scheme.
- If `V` is empty and `Z` nonempty, the first clause still allows `n = 0`,
  while surjectivity in the second clause fails, exactly as required.
- If both are empty, the unique map `Z → V` is a section; the conclusion
  does not exclude this case or require a positive number of components.
- Components are not assumed nonempty; pullback of the nonempty components
  upstairs may be empty, so imposing nonemptiness would add a needless restriction.
- The morphism may be affine étale without being finite or surjective: only
  the second conjunct asks for these additional properties.
- No characteristic, Noetherian, connectedness of `Z`, or algebraic-closedness
  hypothesis is imposed. Separably closed is used exactly as in the source.
- The same explicit universe covers arbitrary schemes and their opens; finite
  indexing by `Fin n` does not bound the universe of the schemes or points.

Searches for an existing theorem (run with `msearch.py E1` and this item):

- LeanSearch query `finite etale covers of closed subschemes of normal affine
  schemes with separably closed function field admit sections`: service unavailable,
  Internal Server Error. This is recorded as unavailable, not a negative result.
- LeanFinder query `An affine etale scheme over a closed subscheme of an affine
  normal integral scheme with separably closed function field is a finite disjoint
  union of open subschemes and finite surjective etale covers have sections`:
  eight hits concerning étale morphisms, étale algebras over fields, and normalization;
  none gives this theorem over a closed subscheme.
- Loogle query `AlgebraicGeometry.Etale, AlgebraicGeometry.IsFinite`:
  one hit `AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt`, which is a
  quasi-finite étale-neighborhood theorem, not this decomposition/section result.
- Mathlib grep query `finite.*etale.*section|etale.*normal|IsSepClosed.*functionField`
  in `AlgebraicGeometry`: no hits.
- `rg` of that function-field/normality vocabulary in the source project found
  `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/Etale.lean`, whose three
  09Z9 decomposition theorems were read in full. They require the base itself
  to be integral and normal, whereas here the base `Z` is a closed subscheme
  and need not be integral, normal or reduced. They do not state 09ZA.
- `rg` for this node id in the source project: no declaration.
- `rg` for normality and separably closed function fields in `lean/Sheaf`:
  no matching theorem. The related `FiniteClopenOpenCoverSection.lean` was read:
  it assumes a decomposition and gives a section, so it does not state this node.
- `rg` for the new declaration and module names in Mathlib, the source project,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no clash.

Validation: `scompile.py E1 lem-weil-pbc-gabber-finite-etale-section` compiled
this 73-line module on the server in 1.8 seconds, exit code 0, with no warnings.
The proof docstring carries all five steps of the node's proof and their dependency ids.

## Second reading by E1

Independent statement check against the node and Stacks 09ZA (Lemma 59.80.6):

- The objects are rendered by `{X Z V : Scheme.{u}}`, with `X` affine via
  `[IsAffine X]`, integral via `[IsIntegral X]`, and `X` locally normal by
  `hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
  IsIntegrallyClosed (X.presheaf.stalk x)`. The function-field condition is
  `[IsSepClosed X.functionField]`, using Mathlib's `Scheme.functionField`.
- The closed subscheme is `(i : Z ⟶ X) [IsClosedImmersion i]`; the etale map is
  `(p : V ⟶ Z) [Etale p]`, and `V` is affine by `[IsAffine V]`.
- The first conclusion is rendered by `∃ n : ℕ, ∃ W : Fin n → V.Opens`, followed
  by each `W j` closed in `V`, pairwise disjointness, `(⨆ j, W j) = ⊤`, and
  `IsOpenImmersion ((W j).ι ≫ p)` for every `j`. Since `V.Opens` already means
  open subschemes, this is exactly the finite clopen disjoint decomposition and
  open-immersion restrictions in the node.
- The second conclusion is rendered separately as
  `Surjective p → IsFinite p → ∃ s : Z ⟶ V, s ≫ p = 𝟙 Z`, with etaleness shared
  by the preceding instance. Composition order gives `p ∘ s = id_Z`.

No mismatch was found, so no source or Lean change was needed. The empty index
case `n = 0` is available (and covers empty `V`), empty `Z` and `V` remain
allowed, and no characteristic, Noetherian, connectedness, or extra finiteness
hypothesis is introduced. The single universe `u` covers all schemes and their
opens.

The existing-declaration searches were rechecked with `msearch.py` (LeanSearch,
LeanFinder, Loogle and Mathlib grep), plus `rg` over `WeilConjectures/`,
`lean/Sheaf/`, and `dag/lean_names_upstream.json`; they found no declaration of
this result. The nearby 09Z9 decomposition theorems and
`FiniteClopenOpenCoverSection` have different hypotheses or conclusions.

The exact module was recompiled with `scompile.py`; it compiled cleanly with only
the permitted `sorry` proof. The node's `lean.statement` remains verbatim equal
to the theorem signature.

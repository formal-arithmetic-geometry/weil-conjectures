## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleComponents` states
`AlgebraicGeometry.EtaleComponents.exists_component_functors` with one `sorry`.
It changes only the item's `lean` field. No statement correction, dependency module,
or new independent notion is needed. Its four helpers only package existing notions
for indexing the functor and its comparisons. They contain real data, with their
property fields obtained from existing Mathlib instances; none uses a postponed proof.

Source read: `literature/milne-algebraic-groups_iAG2017.pdf`, printed pp.15-16,
Propositions 1.29, 1.30(a,b), 1.31(a,b), and Remark 1.33. Proposition 1.29 and the
following paragraph give the finite étale scheme and universal morphism; Proposition
1.30 gives products and arbitrary field extension, and the sentence after its proof
specifically identifies the quotient maps after extension. Proposition 1.31 gives the
component fibres and their geometric connectedness.

Hypotheses and clauses, in order:

- A field k: every clause quantifies `(k : Type u) [Field k]`.
- Separated finite-type k-schemes: `Input k` is Mathlib's
  `ObjectProperty.FullSubcategory` of `Over (Spec (.of k))`, with predicate
  `IsSeparated X.hom ∧ LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom`.
  The over-category packages precisely the structure morphism and k-morphisms.
- Existence of Π and q: existential variables `P` and `q`; `(P k).obj X` is Π_k(X),
  and `(q k).app X` is q_X, a morphism in the over-category, hence over k.
  The theorem asserts existence and properties simultaneously; it does not define
  scheme data using a choice from an unconstrained existence statement.
- Finite étale: `IsFinite ((P k).obj X).hom ∧ Etale ((P k).obj X).hom`.
- Every finite étale E: quantify `E : Over (Spec (.of k))` with
  `[IsFinite E.hom] [Etale E.hom]`. `Function.Bijective` of
  `fun h : (P k).obj X ⟶ E ↦ (q k).app X ≫ h` is exactly the displayed Hom bijection,
  with its actual composition map specified.
- Functoriality: `P k` is a `Functor`; identity and composition laws are fields of
  that structure. `q k` is a natural transformation from the full-subcategory
  inclusion `ObjectProperty.ι` to `P k`. Its naturality law is exactly
  `f ≫ q_Y = q_X ≫ Π(f)` for every k-morphism between the given schemes.
- Terminal comparison: `pointInput k` is `Over.mk (𝟙 (Spec (.of k)))`.
  The existential over-category isomorphism e is accompanied by
  `(q k).app (pointInput k) ≫ e.hom = 𝟙 (pointInput k).obj`.
  Since the quotient is universal, this equation characterizes the canonical
  comparison, rather than merely asserting an unrelated isomorphism of objects.
- Product comparison: `productInput X Y` has the actual Mathlib fibre product
  `pullback X.obj.hom Y.obj.hom` and its structure map through `pullback.fst`.
  The comparison e is an isomorphism in `Over (Spec k)` to the fibre product of
  the two component schemes. The two equations explicitly give its composite
  with both projections after q as `pullback.fst ≫ q_X` and `pullback.snd ≫ q_Y`.
  Together with universality these characterize the canonical comparison and
  its compatibility with q. The second input Y has the same exact hypotheses as X.
- Every field extension: quantify `k L : Type u`, `[Field k] [Field L] [Algebra k L]`.
  The morphism is `Spec.map (CommRingCat.ofHom (algebraMap k L))`.
  `baseChangeInput` is precisely `Over.pullback` along that map, with preserved
  separatedness and finite type. The comparison is an over-L isomorphism
  from `(P L).obj (baseChangeInput X)` to the pullback of `(P k).obj X`.
  Its equation identifies `(q L).app (baseChangeInput X) ≫ e.hom` with the image
  of `(q k).app X` under that same `Over.pullback` functor, including the identity
  extension and all other extensions.
- Every point t: quantify `t : ((P k).obj X).left`, and assert
  `Nonempty (((q k).app X).left.fiber t)` for the recorded scheme-theoretic fibre.
- After every residue-field extension: quantify L, Field L, and
  `Algebra (((P k).obj X).left.residueField t) L`, then assert `ConnectedSpace`
  of the pullback of `fiberToSpecResidueField t` along Spec of its algebra map.
  `ConnectedSpace` includes `Nonempty`, so both nonemptiness and connectedness
  are asserted after every extension, not only after an algebraic closure.
- Underlying fibres exactly components: for every x of X, the final clause says
  `q_X ⁻¹' {q_X x} = connectedComponent x`. Combined with the preceding nonempty
  fibre assertion for every t, this covers all fibres and all components, without
  allowing an unused point of the component scheme.

Dependency declarations used (all recorded interfaces were usable):

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-pc-scheme`: `Scheme` and `Scheme.Hom`, `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` and `QuasiCompact`,
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.QuasiCompact`.
  Finite type is their conjunction, exactly as the recorded note specifies.
- `def-weil-proper-morphism`: its separatedness declaration `IsSeparated`,
  exposed by `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
  Properness and universal closedness are not hypotheses of this item.
- `def-weil-finite-integral-morphism`: `IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
- `def-weil-etale-morphism`: `Etale`, `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
- `def-weil-affine-spectrum`: `Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-fibre-product`: `pullback`, `pullback.fst`, `pullback.snd`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`.
- `def-pc-scheme-fibre`: `Scheme.Hom.fiber` and
  `Scheme.Hom.fiberToSpecResidueField`, `Mathlib.AlgebraicGeometry.Fiber`.
- `def-weil-residue-field`: `Scheme.residueField`,
  `Mathlib.AlgebraicGeometry.ResidueField`.
- `def-weil-connected-scheme`: `ConnectedSpace`,
  `Mathlib.Topology.Connected.Basic`; `connectedComponent` is used in the final clause.

The additional APIs `Over`, `Over.pullback`, `ObjectProperty.FullSubcategory`,
`ObjectProperty.ι`, functors and natural transformations are existing categorical
packaging, not replacements for a scheme or morphism notion. The recorded stated
proof dependencies are imported privately. The currently unstated algebraic
`lem-sfb-maximal-ind-etale-field-base-change` is a proof dependency only; no declaration
from it is needed to type this statement. Its step remains in the proof docstring.

Edge cases checked before writing and again against the compiled signature:

- Empty X is an input: neither `Input` nor the theorem requires Nonempty X.
  Its component scheme can be empty, the point-fibre quantifier is vacuous, and the
  Hom bijection holds for maps from the empty scheme. Products with it remain empty.
- X = Spec k is included, and its comparison is normalized to the identity after q.
- A connected scheme need not have a rational point: no rational point is required;
  its component scheme can be the spectrum of a nontrivial finite separable field.
- Imperfect fields, positive characteristic, nonreduced X, purely inseparable and
  transcendental extensions are not excluded by any hypothesis.
- For a geometric fibre with a residue field different from k, the extension
  algebra is over that residue field itself. Nonemptiness is included after every
  extension through `ConnectedSpace`, not inferred from preconnectedness.
- Universe u is arbitrary, and fields, schemes, finite étale test objects and all
  extensions are in the same arbitrary size convention. There is no smaller
  independent universe for test objects or a restriction to algebraic extensions.
  The functor's domain is the full subcategory, so no k-morphisms have been lost.

Searches on 2026-10-24:

- `msearch.py ... leanfinder`: "A finite type scheme over a field has a universal
  finite etale connected component scheme commuting with products and field
  extensions". Eight hits; finite étale algebras, étale site, and residue-field
  point equivalences, no universal component scheme.
- `msearch.py ... leansearch`: "universal finite etale scheme of connected components
  over a field". Eight hits; `Algebra.Etale.iff_exists_algEquiv_prod` and abstract
  pre-Galois decomposition are related but do not state this scheme theorem.
- `msearch.py ... loogle`: "AlgebraicGeometry.Scheme, ConnectedComponents, Etale"
  returned no hits (unqualified Etale unknown). Retried with
  "AlgebraicGeometry.Etale": twelve hits, étale-morphism APIs and stability, no match.
- `msearch.py ... grep`: `componentScheme|etaleComponents|connectedComponentsFunctor|piZero|pi₀`
  in `AlgebraicGeometry`: only an incidental gluing functor hit, no match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` and Mathlib algebraic geometry
  for those names and finite-type over-category combinations found existing
  over-category usage, not this construction or theorem. Searching the item ID in
  `lean/WeilConjectures` found no declaration. A second name-clash search for
  `namespace EtaleComponents|exists_etaleComponents|def ComponentSchemeInput|SeparatedFiniteTypeScheme`
  found no existing API with these names.

Validation: `scompile.py Q133 lem-sfb-algebraic-scheme-etale-components` compiled
the sandbox and library module cleanly (5.5 s and 2.4 s on the successful pass).
The initial pass exposed opaque over-category projections during instance search;
the helpers now give the exact underlying morphism to `inferInstanceAs`.
All variables and universe u are explicit, `autoImplicit` is disabled, and there
are no diagnostic commands or file-local notation. No disputed statement found.

## Second reading by Q133

A separate pass by the same dispatcher worker re-opened the node and Lean file;
no other agent was started, as the assignment explicitly forbids that.
The twelve source hypotheses/notions were checked against the recorded dependency
declarations and the clause mapping above. The existential P is one assignment for
all fields in the chosen arbitrary universe, so the field-extension clause compares
the same assignment on both fields. The existential q is natural on all morphisms
in the full domain; this supplies the node's functoriality and its displayed equation.
The three comparison clauses supply over-base isomorphisms with the equations that
make them canonical. The final pointwise component equation, together with nonempty
scheme fibres for every target point, states equality of all underlying fibres and
components. The residue-field extension clause uses the actual fibre projection,
and `ConnectedSpace` gives the required nonemptiness after extension. The helpers
do not impose extra mathematical hypotheses. No missing or strengthened clause,
private copy of a dependency, or needed statement correction was found.

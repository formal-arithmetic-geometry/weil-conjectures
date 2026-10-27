## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceQcOpenSchematicClosure` states
`AlgebraicGeometry.AlgebraicSpace.exists_qcOpen_schematicClosure`, with one postponed
proof and no definitions or additional nodes. The node is unchanged except for `lean`.
The inherited Q16 PASS is a stage-1 split review, not a Lean statement review: the
current node has no `lean` or `reviewed_lean`, and its queue entry is stage 2. No repair
note exists for this item.

Source read: Stacks `spaces-morphisms.tex`, lemma-scheme-theoretic-image (082X),
lemma-quasi-compact-scheme-theoretic-image (082Z), and
`definition-scheme-theoretically-dense`. The source constructs the smallest closed
factorization and gives étale base change and topological density. For the open
immersion, the factor is open by base change, and schematic density follows from
minimality using the kernel ideal. The full seven-step accepted proof is in the
theorem docstring, with its DAG citations.

Clause-by-clause correspondence:

- The scheme S is `{S : Scheme.{u}}`; the algebraic spaces are `{O B : AlgebraicSpace S}`.
  `AlgebraicSpace` is the published full subcategory of fppf sheaves with representable
  diagonal and a representable surjective étale scheme atlas. All scheme tests use
  the same universe u. The explicit `universe u` and `autoImplicit false` bind all
  variables and retain the size convention without a new size restriction.
- `j : O ⟶ B` is a quasi-compact open immersion precisely by `hj`, using the existing
  `IsRepresentableWith` with the scheme property
  `IsOpenImmersion p.left ∧ QuasiCompact p.left`. This tests on every scheme over S.
  It does not assume B or O is quasi-compact or quasi-separated.
- `∃ (C : AlgebraicSpace S) (c : C ⟶ B) (q : O ⟶ C)` supplies the closed subspace and
  its factor map. The first conjunct tests that c is a closed immersion on schemes;
  `q ≫ c = j` gives the factorization. For every algebraic space D and closed immersion
  d into B through which j factors, the next conjunct supplies `b : C ⟶ D` with
  `b ≫ d = c`. This is inclusion as closed subspaces and states smallest, rather than
  merely a closed set containing the point image. Closed immersions are monomorphisms,
  so the factorization maps are unique and two smallest subspaces are isomorphic over B.
- The scheme-test predicate on q states both open immersion and quasi-compactness.
- `Dense (pointImage q.hom.hom)` is density in the existing atlas topology on the
  existing field-valued point classes of C.
- The next conjunct, quantified over every `V : C.EtaleSite` and functions a,b on V,
  states that equality of their restrictions to every étale scheme chart T of O over
  V forces a=b. The triangle
  `T.obj.hom ≫ q.hom.hom = yoneda.map p ≫ V.obj.hom` says that T is a chart of O ×_C V;
  `(Scheme.Γ.map p.left.op).hom` is the actual pullback of regular functions. Sections
  of the direct image structure sheaf are compatible families over precisely these
  charts. Equality is componentwise, so the implication is exactly injectivity of
  O_C(V) → (q_* O_O)(V), for every V, equivalently the stated sheaf injection. It
  introduces no arbitrary ring map, choice of functions, or additional hypothesis.
- For every algebraic space V and `g : V ⟶ B` which is étale or an open immersion,
  the subsequent conjunct says that the sheaf pullback of c is closed and is contained
  in every closed subspace of V through which the pullback of j factors. The original
  q and its commuting triangle canonically induce the factorization of that pullback
  through the pullback of c. Thus this is exactly formation of the smallest closed
  factorization commuting with étale base change and with every open restriction.
  Sheaf pullbacks are algebraic spaces by the recorded fibre-product theorem. Using
  pullbacks in the sheaf category retains their full universal property and scheme
  structure. The explicit disjunction includes open restrictions without requiring
  an additional proof argument that an open immersion is étale.
- The last conjunct applies to every open g for which the pulled-back j is closed.
  It supplies an isomorphism between C ×_B V and O ×_B V commuting with their maps to V.
  This is equality as closed subspaces, not just equality of their point images.
- The preliminary explanations in the node about geometric points and geometric
  fibres, quasi-separatedness, separatedness, integrality and étaleness fix meanings;
  they impose no hypotheses on j beyond its stated quasi-compact open immersion.
  The actual predicates use the recorded scheme notions. No geometric-point,
  integral, separatedness or quasi-separatedness assumption has been added.

Dependency declarations used/read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `EtaleSite`, `structureSheaf`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointImage` and
  `pointTopologicalSpace`, on the `Point` classes from AlgebraicSpacePointClasses.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace` (also read `etaleCover_pullback` and
  `etale_fibreProduct_isScheme`). The pullbacks in the signature are the sheaf
  fibre products whose algebraicity this node establishes.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale` is used inside the recorded
  `IsEtale`; `Mathlib.AlgebraicGeometry.Morphisms.Integral`: `IsIntegralHom` and
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` are the node's background
  conventions, with no occurrence imposing extra hypotheses in this signature.
  The recorded geometric point is the inline algebraically closed field and Spec
  morphism, with `Scheme.SpecToEquivOfField` supplying the point/residue description.
- Proof imports are the available recorded
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentPushforward` and
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction`.
  Their main declarations are respectively
  `isQuasicoherent_moduleDirectImage_of_quasiCompact_separated` and
  `etale_module_pushforward_restriction`. Other proof dependencies have no Lean
  record in the current DAG, so no module was invented or imported for them.

Edge cases checked before writing: O empty gives the empty closed subspace; O=B gives
C=B and q the identity. A clopen O has closure O, including on every open restriction.
For D(f) in Spec A, the closure ideal is the kernel of A → A_f, which may be nonzero;
the statement therefore retains closed scheme structure rather than taking a reduced
closure. A nonreduced target is permitted. For an empty inverse-image chart, the
schematic-density clause forces its regular-function ring to have at most one element,
exactly as injectivity into the zero ring requires; it is not a vacuous density clause.
Empty targets and empty open restrictions are included. No finiteness or nonemptiness
hypothesis is added. No statement correction or disputed statement is needed.

Searches:

- `msearch.py leanfinder`: "Schematic closure of a quasi compact open subspace of an
  algebraic space commutes with etale base change and is schematically dense". Eight
  hits: scheme image, dominance and quasi-compactness lemmas, no algebraic-space result.
- `msearch.py loogle`: `AlgebraicGeometry.Scheme.Hom.image,
  AlgebraicGeometry.QuasiCompact`. Six hits for scheme image factors, injectivity and
  immersions. They do not state the assertion for algebraic spaces.
- `msearch.py grep`: `schematic|toImage`, in `AlgebraicGeometry/IdealSheaf`.
  Nine scheme-only hits in Subscheme and Functorial.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for schematicClosure,
  SchematicClosure, schematicallyDense, SchematicallyDense, schematic closure and
  the exact node id. No matching algebraic-space theorem; existing schematic-density
  and closure results concern schemes. Searches for scheme-test open/closed immersion
  predicates confirmed `IsRepresentableWith` is the established common interface.

Validation: scompile.py compiled the delivered module as a sandbox and as its library
module, each separately, with no errors or warnings other than the permitted sorry.
No theorem was proved and no data definition contains sorry.

## Second reading by Q18

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

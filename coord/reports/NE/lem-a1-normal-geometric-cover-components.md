## Worker report

The module `Sheaf.AlgebraicGeometry.NormalGeometricCoverComponents` states
`AlgebraicGeometry.normalGeometricCoverComponents`, with its sole proof `sorry`.
No definition, auxiliary theorem, dependency record, or natural statement was changed.
The source was read directly in Bhatt--Scholze, Definition 7.3.1(3), p. 66,
and the entire proof of Lemma 7.4.10, p. 71, using pdftotext. The normality input
was checked in Stacks `properties.tex`, lemma-normal-geometrically-unibranch (0BQ3).

Hypotheses and clauses, in the order of the node:

- The schemes and morphism are `{X Z : Scheme.{u}}` and `(q : Z ⟶ X)`.
- Nonempty connected `X` is `[ConnectedSpace X]`. This class includes nonemptiness;
  an empty base is therefore excluded exactly as in the node.
- Locally Noetherian `X` is `[IsLocallyNoetherian X]` and quasi-compact `X` is
  `[CompactSpace X]`, with no separation assumption on its topological space.
- Integrally closed local domains are the literal conjunction in `hnormal`,
  `∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)`.
- The étale map is `[Etale q]`. There is no quasi-compactness hypothesis on `Z` or `q`.
- The unique valuation lifting hypothesis is `(hval : ValuativeCriterion q)`.
  I read `ValuativeCommSq`, `ValuativeCriterion`, and `CommSq.LiftStruct` in Mathlib:
  a square has a valuation domain `R`, field `K`, `Algebra R K`, and
  `IsFractionRing R K`, together with `a : Spec K ⟶ Z`, `b : Spec R ⟶ X` and
  `a ≫ q = Spec.map (algebraMap R K) ≫ b`. Its lift has exactly the equations
  `Spec.map (algebraMap R K) ≫ lift = a` and `lift ≫ q = b`.
  `Nonempty (Unique LiftStruct)` expresses existence and uniqueness of that lift,
  not quasi-compactness or an additional properness assumption. Both rings are in
  the scheme universe `u`, following Mathlib's size convention for this criterion.
- The conclusion quantifies over exactly the connected components, using
  `ConnectedComponents Z`. The existential family `C : ConnectedComponents Z → Z.Opens`
  is tied to those components by `(C c : Set Z) = ConnectedComponents.mk ⁻¹' {c}`.
  Mathlib's `connectedComponents_preimage_singleton` identifies this fibre with
  `connectedComponent z` for any representing point `z`; these are the maximal
  nonempty connected subsets of the node.
- Each component is open because it is a `Z.Opens`, and closed by `IsClosed (C c : Set Z)`.
  `(C c).toScheme` is its induced open subscheme and `(C c).ι ≫ q` is its restricted
  structure morphism. `ConnectedSpace (C c).toScheme` records connectedness/nonemptiness.
- Each restricted morphism is `IsFinite`, `Etale`, and `Surjective`, as three explicit
  conjuncts. These are precisely the finite étale object conditions of the dependency's
  `(@IsFinite ⊓ @Etale).Over ⊤ X` interface; the theorem does not need to construct a
  second bundled finite étale category.
- The disjoint union conclusion is `Nonempty (IsColimit (Cofan.mk Z ...))`, whose
  legs are the actual open immersions `(C c).ι`. Their composites with `q` are the
  structure maps just stated, so this is also the decomposition over `X`.
- Nothing requires `Finite (ConnectedComponents Z)` or `Nonempty Z`.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme` and
  its morphisms; the open subscheme is Mathlib's `Scheme.Opens.toScheme`/`ι`.
- `def-weil-connected-scheme`: its Mathlib match `ConnectedSpace`,
  `Mathlib.Topology.Connected.Basic`, reexported by the public Clopen import.
- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`.
- `def-weil-pbc-quasi-compact-scheme`: `CompactSpace`,
  `Mathlib.Topology.Defs.Filter`, available through the geometry imports.
- `def-weil-pbc-normal-ring`: `IsDomain` and `IsIntegrallyClosed` from
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, applied to the actual stalks.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`.
- `def-trf-valuation-ring`: Mathlib's `ValuationRing`, used inside the existing
  `ValuativeCommSq` interface in `Mathlib.AlgebraicGeometry.ValuativeCriterion`.
- `def-weil-pbc-finite-etale-category`: read `MorphismProperty.Over` in
  `Mathlib.CategoryTheory.MorphismProperty.Comma`; its finite étale object conditions
  are `IsFinite` and `Etale`, used directly on each component's map.
- `def-weil-surjective-morphism`: `AlgebraicGeometry.Surjective`,
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.

Proof-plan imports: `WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite`
provides `IsFinite.iff_isProper_and_finite_preimage_singleton`; the current source
was read with `scompile.py --source` because the older local upstream copy lacks it.
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` provides `Scheme.Hom.isOpenMap`.
The existing finite closed-image/fibre results are in the imported geometry closure
(`Scheme.Hom.isClosedMap`, `Scheme.Hom.finite_preimage_singleton`). The two new proof
children `lem-a1-normal-etale-components-clopen` and
`lem-a1-geometric-cover-component-qc-proper` currently have no Lean records, so their
future proof imports are omitted. Neither is needed to type this stage-2 statement.

Edge cases checked before writing: empty `Z` gives empty `ConnectedComponents Z`,
the empty component family, and the initial-object coproduct assertion. For any
infinite disjoint union of copies of `X`, the index is allowed to be infinite while
each component map is finite étale surjective. No global finiteness or properness
of `q` is asserted. Over a field, this is the ordinary decomposition into finite
separable field spectra. An étale open immersion missing a specialization fails
the valuation lifting hypothesis and cannot incorrectly satisfy the finiteness claim.
No field characteristic, base separatedness, finite index, or connectedness of `Z`
is imposed. The sole universe `u` is explicitly declared; there are no auto-implicit
variables, file-local notation, or local instances.

Searches for an existing statement (all via the prescribed wrapper unless specified):

- LeanFinder: `An etale geometric covering of a connected normal noetherian scheme is a
  disjoint union of finite etale connected components`. Eight hits: Scheme.Etale,
  abstract PreGaloisCategory finite decompositions, small étale site constructions,
  and normalizationOpenCover; none says this theorem. The abstract Galois decomposition
  assumes a Galois-category object and gives a finite index, which is not this assertion.
- LeanSearch: `A connected geometric covering of a connected normal locally noetherian
  quasi compact scheme is finite etale and surjective`. Eight hits on Scheme.Etale,
  IsEtale, IsFinite, finite-map instances, smallEtaleTopology and Surjective; no theorem.
- Loogle: `"ValuativeCriterion", "Etale"`: zero hits.
- Mathlib grep: `geometric.?cover|connectedComponent.*[Ee]tale|valuative.*[Ee]tale`,
  subdirectory AlgebraicGeometry: zero hits.
- Direct `rg` of the same geometric-cover/connected-component pattern and the item id
  in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`: zero hits.
- Direct `rg` in `lean/Sheaf/AlgebraicGeometry` for geometric coverings, ValuativeCriterion,
  and connected finite étale maps found valuation-criterion imports and unrelated
  geometric-generic-cover/finite-cover statements, not this component theorem.
  The existing smooth-curve connected coproduct lemma was read: it concerns a finite
  decomposition of a quasi-compact smooth curve, with no geometric-cover hypothesis.
- Direct `rg` of `normalGeometricCoverComponents|normal_geometricCover_components` in
  `dag/lean_names_upstream.json`, Mathlib, upstream WeilConjectures, and `lean/Sheaf`:
  zero hits before creating this module.

No statement fault or STATEMENT-DISPUTED issue was found. No new nodes or dependency
repairs are required. `scompile.py NE lem-a1-normal-geometric-cover-components <file>`
compiled the sandbox and library-shaped module cleanly (1.6 s and 1.8 s respectively).

## Second reading by NE

This is the author's self-check; the maintainer supplies the independent review.
I reopened the node and the final Lean statement. `[ConnectedSpace X]` includes the
node's nonemptiness; `[IsLocallyNoetherian X]`, `[CompactSpace X]`, and `hnormal`
match all base assumptions. `[Etale q]` plus `ValuativeCriterion q` matches exactly
étaleness and unique valuation lifts; there is no assumption of quasi-compact `Z`.
I checked the full valuative square and lift fields rather than inferring their meaning
from the name. In the conclusion, the equality with the quotient fibres ensures that
`C` cannot select arbitrary opens or omit components. Their type supplies openness,
`IsClosed` supplies closedness, and `toScheme` is the induced structure. The three
map properties are applied to the actual restriction `(C c).ι ≫ q`, and the cofan
uses the same inclusions. Hence every component and the disjoint union clause are
present. Empty and infinite component indices remain permitted. No mismatch was found
and no statement correction was made; the proof remains exactly `sorry`.

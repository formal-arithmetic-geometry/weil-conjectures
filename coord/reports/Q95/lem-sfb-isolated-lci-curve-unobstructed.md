## Worker report

The module `Sheaf.AlgebraicGeometry.IsolatedLCICurveUnobstructed` states
`AlgebraicGeometry.isolated_lci_curve_unobstructed`, with one `sorry` and no
new definitions. It expands the unobstructedness condition exactly as the
item itself defines it. The node is unchanged except for its `lean` record.
No statement correction, dependency replacement, or new node is needed.

Source checked: `literature/stacks-project/examples-defos.tex`,
`lemma-curve-isolated-lci` (Tag 0DZQ), its complete proof,
`example-schemes`, and `section-general`. The latter fixes the coefficient
category; the node restricts it to local Noetherian coefficient rings whose
residue field is exactly k. The chosen residue-field algebra equivalence
makes the map from Λ to k surjective, hence finite as in that section.

Hypothesis and clause correspondence:

- Field and scheme: `(k : Type u) [Field k] (X : Scheme.{u})` with structure
  morphism `(s : X ⟶ Spec (.of k))`.
- Separatedness: `[IsSeparated s]`; finite type:
  `[LocallyOfFiniteType s] [QuasiCompact s]`. No properness is assumed.
- Dimension at most one: `hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)`.
- Local complete intersection: `hlci` quantifies an index `I`, commutative
  coordinate rings `C i`, their k-algebra structures `aC`, finite-generation
  witnesses `ftC`, and chart maps `φ`. The four conjuncts require open
  immersions, compatibility with s and the actual algebra maps, covering
  every point, and `Algebra.IsLocalCompleteIntersection` for every chart.
  This is the same affine-cover presentation as the recorded affine-open
  locality dependency and the existing isolated-lci smoothing modules.
- Smooth except at finitely many points: `hsmooth` gives a finite set `P`
  and a smooth open neighborhood of each point outside P. Closedness of
  these exceptional points is not added as an assumption: the proof derives
  it for the actual nonsmooth locus by the Jacobson argument in step 1.
- Arbitrary Noetherian local coefficient ring: `Λ : Type v`, with
  `[CommRing Λ] [IsNoetherianRing Λ] [IsLocalRing Λ]`, its map to k given
  by `[Algebra Λ k]`, and its specified residue identification `eΛ`.
- Objects of the coefficient category: `A' A : Type u`, their commutative,
  Artinian, local ring instances, Λ-algebra structures, and the specified
  Λ-algebra residue-field isomorphisms `eA'` and `eA` to k. `IsArtinianRing`
  is the descending-chain condition on ideals and `IsLocalRing` is the
  nontrivial local-ring predicate.
- Arrows and surjectivity: `π : A' →ₐ[Λ] A`, `[IsLocalHom π.toRingHom]`,
  `hπ : Function.Surjective π`. The equality `hπk` says that the two
  maps A' → k agree, hence that π induces the identity under the specified
  residue-field identifications. No k-algebra structure on A or A' is used.
- An arbitrary marked deformation: `Y`, `f : Y ⟶ Spec (.of A)`, `[Flat f]`,
  `ι` from its actual pullback to Spec k to X, and `hι` requiring that this
  isomorphism is over k. Y is not assumed affine, proper, or separated.
- A lifted deformation: the existential `Y'`, `f'`, and `Flat f'`.
  The isomorphism `α` identifies the actual reduction along `Spec.map π`
  with Y; `hα` makes it an A-isomorphism.
- Its marking: `ι'` identifies the special fibre along the composite
  Spec k → Spec A → Spec A' with X. The following equation makes it a
  k-isomorphism. The composite equals the specified A'-residue morphism
  by `hπk`, exactly as in `exists_affine_lci_artinian_lift`.
- Compatibility of the marked fibres: the last equation is
  `α_k ≫ ι.hom = ι'.hom`. Here `α_k` is written out using
  `pullbackLeftPullbackSndIso` and `pullback.map`; its map is determined by
  α and the identity maps of Spec k and Spec A. The equalities supplied
  to `pullback.map` are precisely hα and the identity square. Thus this is
  compatibility of the actual markings, not just existence of an abstract
  isomorphism of their sources.
- Every coefficient ring, every surjection, and every deformation is an
  arbitrary theorem parameter, so the existential conclusion is exactly
  the unobstructedness property defined in the node. No separate category
  implementation is needed to express that specified lifting property.

Dependency declarations read and reused:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `.Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-proper-morphism`: the separatedness clause
  `AlgebraicGeometry.IsSeparated`, publicly available from
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` (defined in `.Separated`).
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`
  and `AlgebraicGeometry.QuasiCompact`, in the `.FiniteType` and
  `.QuasiCompact` modules. Finite type is their conjunction as recorded.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim` in
  `Mathlib.Topology.KrullDimension`.
- `def-weil-pbc-complete-intersection-over-field`:
  `Algebra.IsLocalCompleteIntersection` in
  `WeilConjectures.RingTheory.CompleteIntersectionOverField`, using its
  actual explicit finite-type instance argument in the affine cover.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`; the current name in the
  dependency record and source is used, rather than its deprecated alias.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`.
- `def-weil-flat-morphism`: `AlgebraicGeometry.Flat` in
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `.Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, its projections,
  and `pullback.map`; `Mathlib.AlgebraicGeometry.Pullbacks` supplies the
  actual scheme pullbacks. Pasting uses the canonical Mathlib isomorphism.

The module imports recorded proof dependencies that have modules:
`Sheaf.TraceFormula.LciAffineOpenLocality` and
`Sheaf.AlgebraicGeometry.AffineLciArtinianLift`, and the Mathlib modules
for smooth locality/restriction, Jacobson spaces, and Artinian nilpotence.
The current nodes `lem-sfb-isolated-curve-two-affine-cover` and
`lem-sfb-smooth-open-coefficient-lift` have no recorded declarations and
are proof prerequisites only; neither is needed to type this statement.
Their proof steps remain named in the theorem docstring. The maintainer
can add their proof imports when their statements land.

Edge cases checked before drafting and again after reading the signature:
empty X (dimension is minus infinity, the empty cover and P are allowed,
and empty flat lifts work); dimension zero; disconnected schemes; smooth X
(P empty); imperfect fields; mixed-characteristic Λ; arbitrary residue
identifications; π an identity or an isomorphism; deformations Y not
assumed affine. Local coefficient rings cannot be the zero ring, correctly
because their residue field is k. Affine charts may have zero coordinate
algebra, as the existing lci definition permits. Index types, fields,
coordinate rings, and test rings all use u, so there is no smaller
independent test universe making the statement vacuous. Λ may have the
independent universe v. Larger instances are covered by uniform universe
enlargement, as with the existing scheme and affine-lifting interfaces.

Searches (all on 2026-10-24):

- `msearch.py ... leanfinder "Separated finite type local complete
  intersection curves with finitely many nonsmooth points have
  unobstructed deformations over Artinian local coefficient rings"`:
  8 hits, about smoothness and smooth loci, no matching statement.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme,
  Algebra.IsLocalCompleteIntersection"`: 0 hits; the search service does
  not index the project's lci definition (`unknown identifier`). Its
  recorded local source was read directly instead.
- `msearch.py ... leansearch "Unobstructed deformations of separated
  local complete intersection curves"`: 8 hits, smoothness, properness,
  and formal unramifiedness, no matching deformation theorem.
- `msearch.py ... grep "unobstructed|Unobstructed|isolated.*lci"
  AlgebraicGeometry`: 0 Mathlib hits.
- `rg -n 'unobstructed|Unobstructed|isolated.*lci'` in the project's
  `lean/WeilConjectures` and `lean/Sheaf`: no upstream unobstructedness
  theorem; Sheaf hits are the distinct smoothing and moduli-open
  theorems and references to this currently unstated node.
- `rg -n 'lem-sfb-isolated-lci-curve-unobstructed' lean/WeilConjectures`:
  no hits. Searches for the chosen new declaration name in both source
  roots and `dag/lean_names_upstream.json` also return no matches.

No STATEMENT-DISPUTED issue was found. No helper definitions are copied:
the affine cover and lifting property are expanded propositions using the
recorded notions and actual canonical fibre products.

## Second reading by Q95

A separate second pass compared the complete node statement to the file,
with both open. This is a manual rereading by this dispatcher worker;
no other agent was started, as the assignment expressly forbids it.
The maintainer's independent delivery review remains separate.

The check paired separatedness, finite type and the dimension bound with
the three morphism classes and hdim; it checked all four affine-cover
conjuncts, including the k-structure square and finite-type witnesses;
it checked that hsmooth assumes only a finite exceptional set and does
not demand closedness. It checked that eΛ/eA'/eA are algebra equivalences
for the same Λ-action, that π is local and surjective, and that hπk
identifies the two actual residue maps. It then checked both the domain
and codomain of ι and α and their base-map equations, and the direction
of the pasting inverse in α_k. The conclusion asserts no affineness or
properness of Y'. All listed edge cases survive. No mismatch or change
was found in this second pass. In particular the extra affine conclusion
of the proof dependency is not imposed on this global lift.

Validation: the prescribed scompile.py and deliver2.py checks are recorded
below after they complete.

Validation results: `scompile.py Q95 lem-sfb-isolated-lci-curve-unobstructed`
compiled both the sandbox check and the module under its final library name,
with exit code 0 and no diagnostics. `deliver2.py ... --no-push` printed
`OK (dry run): commit 2f78178212c passes the preflight and compiles; nothing pushed`.
Only the report, the item's node JSON, and its single module were staged.

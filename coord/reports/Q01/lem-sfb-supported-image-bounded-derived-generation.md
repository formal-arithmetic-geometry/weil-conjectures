## Worker report

The module `Sheaf.Paper.SupportedImageBoundedDerivedGeneration` states
`AlgebraicGeometry.ProEtale.CondensedRing.supported_image_mem_bounded_derived_generation`
with proof `sorry`. Its two real helper definitions express the explicit hull already
introduced by this same node: `IsSupportedImageGenerationClass` and
`supportedImageGenerationHull`. No independent notion or new definition node is introduced.
The full seven-step DAG proof, with its dependencies, is in the theorem docstring.

Hypothesis and clause correspondence:

- A prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`. The coefficient `Λ` is a commutative ring
  object in condensed abelian groups, with `[MonObj Λ] [IsCommMonObj Λ]`.
- `hΛ` is exactly the six coefficient alternatives, up to ring-object isomorphism:
  finite discrete commutative rings killed by an ell power, `ℤ_[ℓ]`, the valuation ring
  of a finite intermediate field, `ℚ_[ℓ]`, a finite intermediate field, and
  `PadicAlgCl ℓ`. Each topological ring is encoded by its continuous-map condensed
  ring. In particular the final clause is `continuousMapRingObj (PadicAlgCl ℓ)`,
  not `padicAlgClRingObj ℓ`. The fixed algebraic closure is `PadicAlgCl ℓ`; the
  existential finite intermediate field in the corresponding cases represents any
  fixed finite subextension. No relation between unused coefficient choices is needed.
- Schemes are `Scheme.{u}`, the site is exactly `Scheme.ProEt.topology`, sheaves take
  values in `Ab.{u + 1}`, and modules are the existing internal
  `Mod ... (condensedRingObj Λ X)`. Products and filtered diagrams are indexed in
  `Type (u + 1)`, consistently with the size convention and the existing closed
  restriction operations interface. `DerivedCategory` and `DerivedCategory.Q` are
  the ordinary uncompleted localization of cochain complexes. No global sections
  assumption is imposed: the actual sections convention is publicly imported from
  `CondensedQcqsPushforwardContinuity` but is not used in the conclusion of this node.
- Qcqs of the root is `[CompactSpace X] [QuasiSeparatedSpace X]`.
- The support chain is `(tree : QcqsOpenClosedTree X) (p : tree.Path S)`. Every edge
  of a path is an actual quasi-compact open immersion or closed immersion with
  quasi-compact complementary open. Conversely any chain from the node can be
  completed to a tree by adding the complementary reduced closed subscheme at an
  open edge, or the complementary open at a closed edge, and making those siblings
  leaves. All resulting schemes are qcqs, by the node's first proof step. Thus this
  encoding adds no hypothesis to chains. Arbitrary closed subscheme structures are
  allowed in the existing tree. `p.extension Λ` is the recursively constructed
  composite of the recorded module open lower shriek and ordinary closed lower star.
  The root path implements the empty chain and identity functor.
- `hL` and `hM` are separate `HasFiniteConstantLocalModel` hypotheses, so their covers
  and scalar presentations may differ. This dependency chooses a finite presentation
  over the condensed point and pulls it back after restriction to each cover member;
  maps between free rank-one point modules are scalar sections, so its finite
  presentations are precisely the stated discrete scalar finite presentations.
- `u : L ⟶ M` is any actual morphism of module sheaves. There is no scalar-entry,
  finite-subextension-entry, closed-image or completeness assumption on `u`.
- A full class is an `ObjectProperty`. Its repleteness is
  `P.IsClosedUnderIsomorphisms`; `P.IsTriangulated` supplies zero, every integer shift,
  and distinguished-triangle extensions, exactly the recorded Mathlib match.
- Retracts are explicitly quantified `i : K ⟶ L`, `p : L ⟶ K` with `i ≫ p = 𝟙 K`.
  The Lean composition order gives the source's p composed with i.
- For every small family `K`, every `Fan K` with `IsLimit c` and all components in P
  has `P c.pt`. This is closure under derived products, including the empty product,
  independent of which product cone is chosen.
- The generator clause quantifies over all tree paths and all finite scalar local
  models on their sources; it contains
  `(DerivedCategory.singleFunctor _ 0).obj ((p.extension Λ).obj L)`.
- Filtered closure uses a strict functor `D : I ⥤ CochainComplex ... ℤ`, with
  `[SmallCategory I] [IsFiltered I]`, a single integer `a`, and
  `∀ i, (D.obj i).IsStrictlyGE a`. This is a common termwise lower bound, not merely
  a cohomological bound. `c : Cocone D` with `IsColimit c` is the termwise module
  colimit of complexes. If every `Q(D.obj i)` lies in P, the clause gives `P (Q c.pt)`.
  Using every colimiting cocone is equivalent to the node's chosen colimit by
  repleteness and uniqueness up to isomorphism; it introduces no existence hypothesis
  on the main theorem or substitute derived colimit.
- `supportedImageGenerationHull` is `fun K ↦ ∀ P, IsSupportedImageGenerationClass ... P → P K`.
  This is exactly intersection over the specified classes, without extra operations.
- The conclusion is membership of the degree-zero complex on
  `(p.extension Λ).obj (image u)`. `Limits.image u` is the abelian module-sheaf image.
  Image is taken before extension, as required.

Dependency declarations used:

- `Sheaf.Paper.CondensedConstantConstructibility`:
  `AlgebraicGeometry.ProEtale.HasFiniteConstantLocalModel` (read with its full definition
  and docstring; the same module owns the recorded constructibility predicate).
- `Sheaf.Paper.QcqsOpenClosedTree`:
  `AlgebraicGeometry.ProEtale.QcqsOpenClosedTree`, its `Path`, and `Path.extension`.
  The already landed owner `def-sfb-qcqs-open-closed-tree` is added to stmt_deps, as
  authorized for existing landed definition nodes; its statement is unchanged.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek`, through the
  path construction; its data is extension by zero of module objects.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:
  `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`, through the path construction;
  its underlying sheaf is ordinary direct image with coefficient action via eta.
- `Sheaf.Paper.LocalizingAdmissibleCoefficients`: the recorded admissibility interface
  is publicly imported. Its predicate has an extra finite-subextension-valued algebraic
  closure case, so the theorem explicitly spells out precisely this node's six cases,
  following the existing supported-image comparison consumer. No second coefficient
  predicate or replacement dependency declaration is defined.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`: existing ordinary module-object derived
  category context and recorded derived pushpull interface, publicly imported.
- `Sheaf.Paper.CondensedQcqsPushforwardContinuity`: `condensedModuleSections`, the
  recorded sections convention, publicly imported; no comparison claim is assumed.
- Mathlib `CategoryTheory.ObjectProperty.IsTriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Subcategory`, `Fan`/`IsLimit` in the products
  interface, `Cocone`/`IsColimit` in `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.IsFiltered`, `DerivedCategory`, `DerivedCategory.Q`,
  `DerivedCategory.singleFunctor`, and `Limits.image` are used directly.
- Scheme, immersion, quasi-compactness and site declarations are the recorded Mathlib
  declarations, supplied through the existing modules. The two convention dependencies
  have no mathematical declaration; explicit universes and the specified properties
  implement them.

All recorded project proof-dependency modules and the recorded Mathlib short-exact
triangle module are imported without `public`, unless already used as a public statement
import. The two new stage-1 hull prerequisites have no declaration and are documented
in the proof plan, rather than invented or proved here. They are proof dependencies,
not notions needed to type the statement.

Edge cases checked by reading the definitions: root paths allow empty support chains;
leaf and split constructors allow empty schemes and empty complements; zero modules
have the zero finite presentation; separate local-model covers have no common-cover
hypothesis; a zero map has zero abelian image; an identity has its original module
image up to isomorphism, which repleteness accommodates. The finite ring case allows
the zero ring, including exponent zero. No nonzero-coefficient, Noetherian, torsion
comparison, dimension, closed-pair, or finite-field-entry assumption occurs. The finite
scalar modules include integral torsion models. Products allow an empty index type;
filteredness includes its usual nonemptiness, and the termwise bound is uniform.

Searches made before writing:

- `msearch.py leanfinder`, query: “In the derived category of condensed module sheaves
  on a qcqs scheme, images of morphisms of finite scalar local models belong to the
  closure of supported models under shifts triangles retracts products and bounded
  below filtered colimits”. Eight hits, including `CondensedMod.IsSolid` and ordinary
  derived t-structure bounds; none states this generation lemma or this hull.
- `msearch.py loogle`, query:
  `CategoryTheory.ObjectProperty.IsTriangulated, CategoryTheory.Limits.image, DerivedCategory.singleFunctor`.
  Zero hits. The relevant declarations were then inspected directly in Mathlib.
- `msearch.py grep`, query:
  `supportedImage|supportedHull|SupportChain|IsClosedUnderRetracts`, in CategoryTheory.
  Zero hits.
- `rg` of both project source roots for support chains, supported hulls, derived
  generation, and the new declaration names; `rg` of upstream for the item id:
  no existing exact theorem or hull. The existing supported-image comparison theorem
  cites this obligation and uses `QcqsOpenClosedTree.Path`, which is reused here.
- DAG search for the tree and hull terminology found the already landed
  `def-sfb-qcqs-open-closed-tree`, and statement-only consumers and prerequisites.
  The profinite relation hull and the supported-hull descent statement do not provide
  the current conclusion. No duplicate notion is introduced.

The source blueprint's refinement proof was read at `literature/blueprint/latest`.
The lemma is explicitly an agent-formulated independent structural input with exact
reference WANTED, as recorded in the DAG; this delivery does not claim it is a theorem
of the cited source. No counterexample or typing defect was found. No statement change,
dependency repair, or new node is needed.

Validation: prescribed `scompile.py` compiled the file cleanly both under its sandbox
name and its actual library module name, with no unexpected warnings. All declarations
and universes are explicitly bound, `autoImplicit` is false, helper data is fully written,
and the only postponed proof is the named theorem matching this DAG node.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

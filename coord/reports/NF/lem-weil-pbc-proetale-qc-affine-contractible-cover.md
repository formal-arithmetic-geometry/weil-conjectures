## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleQcAffineContractibleCover` states
`AlgebraicGeometry.Scheme.ProEt.exists_affine_weaklyContractible_cover`.
Its sole proof is `sorry`; no definitions or proofs were added.

Clause-by-clause correspondence:

- A scheme X is `(X : Scheme.{u})`.
- An object T → X of the small pro-etale site is `(T : X.ProEt)`;
  its structural morphism is `T.hom`, weakly etale by its object property.
- Quasi-compactness of the scheme T is `[CompactSpace T.left]`.
  Mathlib compactness does not impose separation; no quasi-separatedness is assumed.
- The chosen covering object and its morphism are `∃ (V : X.ProEt) (f : V ⟶ T)`.
  In particular this is a morphism over X, and V lies in the same full site.
- A covering family consisting of precisely this one morphism is
  `Presieve.singleton f ∈ precoverage X T`. The small-site precoverage is
  the comap of `Scheme.proetalePrecoverage` along the forgetful functor to schemes.
  Thus this clause gives the actual pro-etale covering family, including the
  affine-open finite-witness condition, rather than merely a topological surjection.
- V is affine is `IsAffine V.left`.
- Weak contractibility is rendered directly as the node defines it:
  `∀ (F G : Sheaf (topology X) (Type (u + 1))) (η : F ⟶ G),
  Epi η → Function.Surjective (η.hom.app (op V))`.
  F and G are sheaves on the full site of X, not the slice over T or V.
  `η.hom.app (op V)` is exactly the induced function F(V) → G(V).
- The size convention is the explicit universe `u`, schemes in `Scheme.{u}`,
  the Mathlib site `X.ProEt`, and sets in the containing universe `Type (u + 1)`.
  This follows the existing pro-etale hypercover encoding. All variables are bound.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`
  (def-pc-scheme); the affine predicate is `AlgebraicGeometry.IsAffine` in
  `Mathlib.AlgebraicGeometry.AffineScheme`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` (recorded dependency module):
  its `Scheme.proEtaleDerivedCategory` docstring explicitly records the underlying
  small site as `Scheme.ProEt` and `Scheme.ProEt.topology` in
  `Mathlib.AlgebraicGeometry.Sites.Proetale`. The statement uses that very site,
  its `precoverage`, and Mathlib `CategoryTheory.Sheaf`, `Epi` and
  `Presieve.singleton`; it does not need a derived category or coefficients.
- def-weil-size-convention and def-weil-pbc-scheme-conventions are recorded
  metatheoretic/convention nodes with no standalone declaration. Compactness is
  Mathlib `CompactSpace`, read in `Mathlib.Topology.Defs.Filter`.
- The proof dependencies def-weil-pbc-proetale-covering and
  def-weil-weakly-etale-morphism match `Scheme.proetalePrecoverage` and `WeaklyEtale`,
  already transitively imported. The two proof lemmas
  lem-weil-pbc-proetale-affine-wcontractible-covering-family and
  lem-weil-pbc-proetale-qcqs-finite-family-geometry have no lean records yet,
  so there are no statement modules for them to import. Their roles and all four
  proof steps are retained in the theorem docstring.

Sources inspected: local proetale.tex, lemma-weakly-contractible-cover (0F4P),
including the finite-subfamily argument; lemma-proetale-enough-w-contractible
(0990); sites.tex, lemma-w-contractible (090K), condition (2), and
 definition-w-contractible (090L). The framework note
`coord/pefw-upstream-framework.md` was read; no module-object replacement is needed.

Edge cases checked: the empty T is permitted (the empty finite disjoint union
is affine, its identity singleton covers, and sections are singletons).
No nonemptiness, reducedness, separatedness or quasi-separatedness is imposed.
X can also be empty. The sheaf quantifiers range over the whole site, with a
sufficient containing universe. The source agrees with the node, so there is
no statement correction or disputed clause.

Searches performed:

- msearch.py leanfinder, query “Every quasi compact object of the pro etale site
  has an affine weakly contractible singleton cover”: eight results concerning
  quasiCompactCover, affine open covers and affine transition limits; none asserts
  a weakly contractible singleton cover.
- msearch.py loogle, query `Scheme.ProEt, Sheaf, Epi`: zero hits; unknown identifier
  Scheme.ProEt in that index.
- msearch.py grep, query `WeaklyContractible|weaklyContractible|wContractible`:
  zero Mathlib hits.
- msearch.py leansearch, query “A quasi compact pro etale object admits a single
  affine weakly contractible covering”: unavailable, Internal Server Error.
- rg searches of the upstream WeilConjectures tree, side framework and lean/Sheaf
  for contractibility and covering names: upstream has IsWContractibleRing,
  a ring-theoretic notion, not this sheaf-theoretic existence statement. Side
  ProEtaleAffineAcyclicHypercover cites this item in its proof and spells out the
  same evaluation condition, but asserts a hypercover, not this statement.
  ProEtaleFiniteCoproductEvaluation gives the section-product geometry only.
- rg of dag/lean_names_upstream.json for the contractibility names had no hits.
  Searching the upstream source for this node id had no hits. The proposed full
  declaration name did not occur in any searched source.

Validation: scompile.py compiled the delivered module on the server cleanly
(1.4 seconds, nice 19, two threads, 60-second limit). Dry-run outcome is recorded below.


## Second reading by NF

Independent second reading against the sandbox node, proetale.tex
lemma-weakly-contractible-cover (0F4P), its preceding enough-objects lemma
(0990), and sites.tex lemma-w-contractible (090K) and definition-w-contractible
(090L). The source assumes only that the base is a scheme. Its final assertion
requires quasi-compactness of the object, without quasi-separatedness.

The complete object/hypothesis/conclusion checklist is:

1. An arbitrary base scheme X: `(X : Scheme.{u})`. PASS. Read
   `AlgebraicGeometry.Scheme` and `Scheme.Hom` in Mathlib's Scheme.lean:
   locally ringed spaces locally isomorphic to spectra, with scheme morphisms.
2. The small pro-etale site of X: `(T : X.ProEt)`. PASS. Read the recorded
   dependency ProEtaleDerivedCategory.lean and then Mathlib Sites/Proetale.lean.
   `Scheme.ProEt` is `MorphismProperty.Over @WeaklyEtale ⊤ X`:
   objects are weakly etale maps and arrows are all X-morphisms. The imported
   derived-category abbreviation uses this same site; no coefficient ring or
   derived-category structure is assumed in this theorem.
3. T quasi-compact as a scheme: `[CompactSpace T.left]`. PASS. Read CompactSpace
   in Topology/Defs/Filter.lean: compactness of the whole space, explicitly
   without separation. It does not assert quasi-compactness of T.hom or impose
   quasi-separatedness on T or X. There are no other instance hypotheses.
4. Existence of one object V and an arrow over X to T:
   `∃ (V : X.ProEt) (f : V ⟶ T)`. PASS. These choices precede all sheaf
   quantifiers, so one V and one f work for every epimorphism.
5. The singleton family is a covering:
   `Presieve.singleton f ∈ precoverage X T`. PASS. Read the definition of
   ProEt.precoverage: the comap of Scheme.proetalePrecoverage under the scheme
   forgetful functor. The latter is propQCPrecoverage WeaklyEtale, hence
   qcPrecoverage intersected with jointly surjective weakly etale families.
   Read Sites/QuasiCompact.lean and its affine-witness characterization:
   it gives the finite affine-open witnesses in the node, as well as weak
   etaleness of f. This is precisely the family condition in the node.
6. V affine: `IsAffine V.left`. PASS. Mathlib AffineScheme.lean defines this by
   the canonical map to Spec of global sections being an isomorphism, the
   standard affine-scheme predicate used by def-pc-scheme.
7. Weak contractibility in the full site: for every
   `F G : Sheaf (topology X) (Type (u + 1))` and `η : F ⟶ G`,
   `Epi η → Function.Surjective (η.hom.app (op V))`. PASS. These are full-site
   sheaves of sets and categorical epimorphisms, and the function is evaluation
   at the chosen V. This is exactly the explicit definition in the node and
   condition (2) of 090K, not a property of a slice or of a ring.
8. Universes: `universe u`, `Scheme.{u}`, and sets in `Type (u + 1)`.
   PASS. All scheme objects have the same chosen bound; the site is small in
   the containing universe, whose sets are used for sheaves. This is the size
   convention recorded by the dependency and the existing hypercover theorem.
   No independent smaller test-object universe makes a hypothesis vacuous.

Edge cases: empty T is allowed; take empty V and its identity arrow. The empty
scheme is affine (the zero ring), its singleton identity is a covering, and
any sheaf has singleton sections there because the empty family covers it.
The product argument in the proof also allows the empty index set. Empty X
therefore causes no exception. Zero rings and arbitrary characteristics are
allowed; no field or nontriviality hypothesis occurs. There is no n-parameter.
All universes and variables are explicitly bound.

Independent searches (with different query wording):

- LeanFinder via msearch: "A quasi compact object of the small proetale site
  admits an affine projective cover for sheaf evaluation". Eight hits, involving
  ordinary quasi-compact covers and affine-transition limits. No full-site
  weak-contractibility existence statement.
- Loogle via msearch: `"contractible"`. Twelve hits, concerning contractible
  triangles and compiler eta contraction, not this result.
- msearch grep: `projective.*cover|weaklyContractible|wContractible`, zero hits.
- LeanSearch via msearch: "Every quasi compact object of the pro etale site has
  an affine cover on which epimorphisms of sheaves are surjective on sections".
  Service returned Internal Server Error; unavailable, no mathematical verdict.
- Direct rg searches in Mathlib algebraic geometry and Sites, upstream
  WeilConjectures, the group's exact lean/WeilConjectures pro-etale framework,
  and lean/Sheaf, using projective cover, enough projectives, evaluation
  surjectivity and contractibility variants. The upstream WContractible.lean
  results concern ring-theoretic IsWContractibleRing, not this theorem.
  Opened the group's ProEtale/AlgClosedFieldSite.lean surjective_app_of_epi_of_iso:
  it requires an isomorphism to Spec of an algebraically closed field and gives
  evaluation at the identity object only. It is not this existence theorem.
  Opened ProEtaleAffineAcyclicHypercover.lean: it has an extra quasi-separatedness
  hypothesis and asserts an entire hypercover, citing this item in its proof.
  It does not replace this statement. No existing exact match was found.

H4/H5/H6/H8/H9 and dependencies: read every statement/proof dependency node
and each recorded declaration used. The two proof-lemma nodes still have no
Lean record; their roles remain in the four proof steps of the docstring.
WeaklyEtale and proetalePrecoverage are Mathlib declarations already imported.
The size and scheme conventions are explicitly recorded convention nodes.
There are no new definition nodes or dependency modules in this delivery,
no private definitions, no hollow data, no proved theorem, and only the named
existence theorem uses sorry. The module and theorem docstrings cite the source
and blueprint; all four proof steps, including finite extraction and the empty
product, match the node. All lines are at most 100 characters. An exact text
comparison confirmed lean.statement equals the theorem signature verbatim.
No statement_change exists or is needed: source, node and Lean agree.

Mismatches found: none. Changes: appended this independent second-reading
report only; retained the correct Lean module and node unchanged.

Second-reader validation: scompile.py passed cleanly on the server in 1.3 s,
nice 19, two threads, limit 60 s. deliver2.py --no-push printed OK: preflight
and compilation passed (dry-run commit 98a3678f75).

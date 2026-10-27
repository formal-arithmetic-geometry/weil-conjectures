## Worker report

States `AlgebraicGeometry.semiabelian_geometric_power_integrality` in
`Sheaf.AlgebraicGeometry.SemiabelianGeometricPowerIntegrality`. Its sole theorem has
proof `sorry`; there are no new definitions, helper theorems, or dependency modules.
The declaration docstring gives all seven proof steps and their named DAG inputs.
The accepted natural-language statement and proof split are unchanged.

The previous worker's stage-1 live-wins blocker does not apply to this stage-2
assignment. The current `coord/brief-stage2.md` §0 explicitly distinguishes the
stages. The node is split, reviewed by Q40, has no Lean record, and appears in
`coord/queue.tsv` at stage 2. No repair note is present for this item.

Hypotheses and clauses, read against the complete node:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- G is a group scheme over F: `G : Grp (Over (Spec (.of F)))`, using the actual
  `GrpObj` group law on `G.X`. Its underlying scheme is `G.X.left` and its
  structure map is `G.X.hom`.
- Commutative G: `[IsCommMonObj G.X]`; smooth: `[Smooth G.X.hom]`;
  separated: `[IsSeparated G.X.hom]`, whose defining field says the diagonal
  is a closed immersion. Finite type: `[LocallyOfFiniteType G.X.hom]` together
  with `[QuasiCompact G.X.hom]`, exactly the recorded finite-type convention.
- Rank r is a nonnegative integer: `r : ℕ`. The kernel source
  `MultiplicativeType.splitTorus F r` is the existing recursive finite product
  of `StandardGroupSchemes.multiplicative F`. The latter is Spec of the Laurent
  polynomial algebra F[t,t⁻¹] with t mapped to t⊗t, 1 and t⁻¹ in its Hopf maps.
  Its rank-zero case is the tensor unit, with no positivity assumption.
- B is a group scheme over F: `B : Grp (Over (Spec (.of F)))`; its commutativity,
  properness, smoothness and geometric connectedness are respectively
  `[IsCommMonObj B.X]`, `[IsProper B.X.hom]`, `[Smooth B.X.hom]` and
  `[GeometricallyConnected B.X.hom]`. The last class uses `ConnectedSpace`
  after every field base change, which includes nonemptiness.
- The two arrows in the exact sequence are the actual group homomorphisms
  `i : MultiplicativeType.splitTorus F r ⟶ G` and `q : G ⟶ B` in bundled group
  objects. They have no arbitrary or independently chosen group laws.
- Exactness at the left and middle: `hker : IsPullback i.hom.hom
  (toUnit (MultiplicativeType.splitTorus F r).X) q.hom.hom η[B.X]`.
  This is the full kernel square in schemes over F: i identifies the prescribed
  split torus with the inverse image of the identity section. It includes the
  zero-composite equation and the universal identification, rather than only
  that equation or only injectivity on F-points.
- Exactness at B: `hepi : Presheaf.IsLocallySurjective
  (Scheme.fppfTopology.over (Spec (.of F))) (yoneda.map q.hom.hom)`.
  By the definition of local surjectivity, every section on every F-scheme lifts
  after an fppf cover. It imposes neither a global section nor surjectivity only
  on geometric points. The image sieve is covering in the generated fppf topology.
- For every n ≥ 0: `∀ n : ℕ`. The power is
  `(∏ᶜ fun _ : Fin n ↦ G.X).left`, the categorical finite product in `Over Spec F`,
  hence the n-fold fibre product over F. Its empty product is the terminal object
  of this slice, canonically Spec F. This uses the existing product construction;
  no private power definition is needed.
- The entire conclusion is `IsIntegral` of that scheme. Mathlib's recorded
  `IsIntegral` includes nonemptiness and domain sections, equivalently reducedness
  and irreducibility. The explanatory final clause is therefore fully retained.

Dependency declarations used (their defining signatures and docstrings were read):

- `Field` in Mathlib.Algebra.Field.Defs and `IsAlgClosed` in
  Mathlib.FieldTheory.IsAlgClosed.Basic, for def-weil-field and
  def-weil-algebraic-closure. No algebraic closure object is needed in the signature.
- `AlgebraicGeometry.Scheme` in Mathlib.AlgebraicGeometry.Scheme, for def-pc-scheme.
- `CategoryTheory.GrpObj`, bundled `Grp`, `IsCommMonObj` and bundled group
  homomorphisms from Mathlib.CategoryTheory.Monoidal.Grp/Mon, for
  def-sc-group-scheme. The upstream GroupScheme.Defs documentation confirms
  precisely this encoding over Spec F.
- `Smooth` in Mathlib.AlgebraicGeometry.Morphisms.Smooth, for
  def-sbc-smooth-morphisms; `LocallyOfFiniteType` and `QuasiCompact` from their
  Mathlib morphism modules, for def-weil-finite-type-morphism.
- `Scheme.fppfTopology` and `fppfPrecoverage` in Mathlib.AlgebraicGeometry.Sites.Fpqc,
  with `GrothendieckTopology.over` in Mathlib.CategoryTheory.Sites.Over, for
  def-pc-fppf-site. `Presheaf.IsLocallySurjective` is the canonical local-lifting
  predicate in Mathlib.CategoryTheory.Sites.LocallySurjective.
- `GeometricallyConnected` in Mathlib.AlgebraicGeometry.Geometrically.Connected,
  the connectedness component of def-pc-geometrically-irreducible's exact match.
- `IsProper` and `IsSeparated` in Mathlib.AlgebraicGeometry.Morphisms.Proper and
  Separated, for def-weil-proper-morphism.
- `IsIntegral` in Mathlib.AlgebraicGeometry.Properties, for def-pc-integral-scheme.
- `Limits.pullback` in Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  for def-pc-fibre-product. `IsPullback` states the kernel universal property;
  `Limits.piObj` in Mathlib.CategoryTheory.Limits.Shapes.Products supplies finite
  iterated fibre products through the existing slice finite-limit structure.
- `MultiplicativeType.splitTorus` in
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType. The owning landed node
  def-sfb-tori-multiplicative-type is added to stmt_deps, so the source of this
  prescribed group construction is explicit. All older stmt_deps are retained.

The proof-only imports cover the already stated proof dependencies: finite
presentation, affine morphism permanence, proper and smooth base-change and smooth
composition, Yoneda full faithfulness, surjective base change and scheme fibres,
quotient-topology connectedness, the algebraically closed connectedness test, and
geometrically connected product components. The four proof dependencies with no
recorded statement (diagonalizable criteria, smooth affine torsor representability,
large algebraically closed Jacobson extension, smooth connected fibre integrality)
are referenced in the proof docstring but supply no module to import yet. They are
proof prerequisites, not notions required to type this statement.

Edge cases checked: n=0 gives Spec F, integral because F is a field; n=1 recovers
G; r=0 is allowed and its kernel is the trivial group; B=Spec F permits a split
torus; G=B=Spec F and r=0 give trivial groups throughout. Positive characteristic
is unrestricted. Nonreduced groups such as alpha_p are excluded by the explicit
smoothness of G, not by an unstated characteristic restriction. The empty G cannot
satisfy its group structure (the identity is a section); geometric connectedness
of B already includes nonemptiness. No extra field, dimension, chosen point,
torsor trivialization or finite-product existence hypothesis is imposed. Universe
u is explicit and shared by the field, schemes and big site; test F-schemes and
all field extensions in that size convention are included.

Source checks: read Stacks groupoids.tex, lemma-characterize-trivial-pseudo-torsors
(0499), lemma-torsor (049B), lemma-connected-group-scheme-over-field-irreducible
(0B7Q); topology.tex lemma-connected-fibres-quotient-topology-connected-components
(0377); varieties.tex lemma-smooth-geometrically-normal (056T). The statement is the
node's extracted consequence; no claim that one tag states all of it is made.

Searches: msearch.py LeanSearch query "Finite powers of a smooth semiabelian group
over an algebraically closed field are integral" returned general integral-algebra,
integral-morphism and smooth-algebra results, no exact match. LeanFinder query
"Finite powers of a smooth semiabelian group scheme over an algebraically closed
field are integral" returned `IsIntegral` and general integrality facts, no exact
semiabelian-power theorem. Loogle query "AlgebraicGeometry.IsIntegral,
AlgebraicGeometry.GeometricallyConnected" returned zero hits. Mathlib grep
"semiabelian|semi.abelian|connected.*group.*integral" in AlgebraicGeometry returned
zero hits. These searches are logged by msearch.py in this sandbox.

Direct rg searches of lean/WeilConjectures and lean/Sheaf for semiabelian,
Semiabelian, splitTorus, finite powers and the exact node id found no existing
statement. They did find the split torus construction, HasSemiabelianGeometricFibres,
and geometric_semiabelian_split_quotient, which were opened. The first defines the
kernel; the latter two concern geometric fibres and descent of a quotient and do
not assert integrality of finite powers. The planned declaration name has no
upstream/DAG-name match. No new definition nodes are needed and no statement fault
or STATEMENT-DISPUTED flag was found.

Validation: scompile.py compiled the single delivered module against the published
live library, in both sandbox and library module contexts (1.9 s each), with no
errors or warnings. Every variable and universe is explicitly bound and
`autoImplicit` is false. Delivery dry run is performed after this report.

## Second reading by Q139

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

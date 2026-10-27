## Worker report

Q141, 2026-10-22. Stage 2, not a re-split. The live node has Q28's reviewed
stage-1 ten-step proof and no `lean` record. The previous worker's stale-dispatch
reason confused that stage-1 completion with the present stage-2 statement task.
I preserved the whole live node, including its statement, proof, status, review
and dependency lists, and added only `lean`. No repair note for this item is
present. No live source or launcher script was edited, no direct Git command
was run, and no other agent was started.

The module is
`Sheaf.AlgebraicGeometry.FundamentalGroup.PointedGaloisLimitGeometry`.
Its main declaration is
`AlgebraicGeometry.Scheme.UniversalCover.exists_pointedGaloisLimitGeometry`.
The only postponed proof is that theorem's `sorry`; its docstring gives all ten
steps of the node's proof and the nodes used. The two helper definitions
`normalSectionDiagram` and `normalSectionAlgebraMap` have real data and belong
to this very affine-chart clause. There is no new notion requiring a new DAG
node, no dependency replacement, and no statement correction.

### Hypotheses and objects, clause by clause

- A scheme X: `{X : Scheme.{u}}`.
- Nonempty and connected: `[ConnectedSpace X]`. Mathlib's class includes
  `Nonempty X`; no separate weaker preconnected hypothesis is substituted.
- Quasi-compact and quasi-separated: `[CompactSpace X] [QuasiSeparatedSpace X]`.
- The geometric point: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `(x : Spec (.of Ω) ⟶ X)`.
- The profinite fundamental group and its left action: `(G : ProfiniteGrp.{u})`,
  `[∀ Y : X.FiniteEtale, MulAction G ((FiniteEtale.fiber x).obj Y)]` and
  `[IsFundamentalGroup (FiniteEtale.fiber x) G]`. This is the existing supported
  model interface, not an arbitrary compact group or a monodromy hypothesis.
  `toAutContinuousMulEquiv` identifies G with the natural automorphism group of
  the fibre functor with its evaluation topology. `exists_isFundamentalGroup`
  supplies such a small model for the essentially small finite étale category;
  it does not impose a new mathematical assumption on X or x. The recorded
  `exists_fiber_flc_equivalence` identifies this group with the automorphisms
  of `flcFiber x`; the definition node explicitly permits the finite-etale
  version of its fibre functor.
- Compatible universes and small systems: all schemes, Ω, G and the index
  `Index x` use u. `Index x` is the published `SmallModel` of the category of
  pointed Galois objects. The arbitrary small cofinal systems use
  `(J : Type u) [SmallCategory J]`. No independent smaller index universe,
  artificial site-universe equality or assumed existence of a limit is used.

### The covers, transitions and cofinality

- The indicated covers exist: the conclusion quantifies
  `E : OpenNormalSubgroup G ≌ Index x`. Set
  `Y_N := (diagram x).obj (E.functor.obj N)` and
  `y_N := (point x (E.functor.obj N)).left`.
  The `Index`, `obj`, `point`, `diagram`, `p`, and `indexEquiv` declarations
  are all the existing upstream construction. There is no new choice of an
  unrelated family of schemes or of an arbitrary limiting object.
- The stipulated left coset identification is the family `q N` of equivalences
  from the actual finite geometric fibres to `G ⧸ N.toSubgroup`.
  The first equation sends the marked point to `QuotientGroup.mk 1` (the N coset).
  The next equation is left equivariance
  `q N (g • s) = QuotientGroup.mk g * q N s`.
- A transition for M ≤ N is `(diagram x).map (E.functor.map f)` with
  `f : M ⟶ N`. The quotient compatibility equation uses the actual
  `QuotientGroup.map ... (MonoidHom.id G) (leOfHom f)`, sending aM to aN.
  Point preservation and the identity/composition laws are already part of
  `point`, `map_point`, and functoriality. They are not supplied as new assumptions.
- These covers are exactly a small cofinal system of pointed connected Galois
  covers: `E` is an equivalence with the existing small model of the entire
  pointed Galois category, stronger language here meaning precisely the
  normal-subgroup classification in the node. It is not an arbitrary embedding
  assumed to be cofinal. `indexEquiv` compares it with arbitrary representatives.
- Unique pointed arrows: the `Subsingleton` conjunct; existence precisely for
  M ≤ N: the following `Nonempty (...) ↔ M ≤ N` conjunct. For M,N the existing
  `M ⊓ N` is again an open normal subgroup with `inf_le_left` and `inf_le_right`.
  Applying this equivalence gives exactly the specified common refinement.
  The whole group is the explicit index `⟨⟨⊤, isOpen_univ⟩, inferInstance⟩`.
- Galois in the stated geometric sense: the `∀ N s t, ∃! a : Aut ...` conjunct
  asserts simple transitivity of X-automorphisms on the finite geometric fibre.
  The separate `ConnectedSpace` stage conjunct supplies connectedness and
  nonemptiness. `Aut` is in the finite-etale category, so its arrows are exactly
  the X-automorphisms, with no extra automorphism condition.

### Limits, geometry and the marked point

- T is the published `cover x := limit (diagram x)`; its existence is already
  an instance in `UniversalCoverConstruction`. The first `Nonempty (IsLimit ...)`
  says the SAME cone on T is limiting after restriction along E.
- The limit in schemes over X is the `IsLimit (Over.liftCone ...)` conjunct,
  using the existing natural transformation `pNatTrans x`, structure map
  `proj x` and equations `π_p x`.
- Independence of every small cofinal system is the universal conjunct over J
  and `F : J ⥤ Index x` with `[Functor.Initial F]` (the correct direction for
  inverse limits). It asserts the restricted cone on the same T is a limit,
  both in schemes and in `Over X`. Thus the canonical comparison is the one
  characterized by its projections, not just an unnormalized isomorphism of
  underlying schemes. Systems presented in the full category transport through
  `indexEquiv`; systems in the N-category transport through E.
- Every Y_N is qcqs: the stage `CompactSpace` and `QuasiSeparatedSpace` conjuncts.
- Every structure map is finite étale surjective: stage conjuncts
  `IsFinite (p ...)`, `Etale (p ...)`, `Surjective (p ...)`.
- Every transition is finite étale surjective: the corresponding universal
  conjunct over `f : M ⟶ N`.
- Every projection is affine and surjective: the stage conjuncts
  `IsAffineHom (limit.π ...)` and `Surjective (limit.π ...)`.
- The marked point t is the actual `pt x`, constructed upstream by lifting
  the cone of the y_N. The point-stage equations are explicitly restated for
  every N and followed by `pt x ≫ proj x = x`.
- T is nonempty connected qcqs: `ConnectedSpace (cover x)`,
  `CompactSpace (cover x)`, `QuasiSeparatedSpace (cover x)`. Connectedness
  includes nonemptiness, as it does in the node.
- The map v is the actual `proj x`; the conclusion includes `IsAffineHom`,
  `Flat`, `Surjective` and `WeaklyEtale` of this map. WeaklyEtale is Mathlib's
  conjunction of flatness of the morphism and its diagonal, not merely formal
  étaleness or an ind-étale label on unspecified rings.

### The affine chart and covering clauses

- `U : X.AffineZariskiSite` ranges over EVERY affine open V, with base ring
  `Γ(X, U.toOpens)` and its canonical chart `U.2.fromSpec`. Every presentation
  V ≅ Spec A is obtained from this by the usual section-ring identification.
- `normalSectionDiagram x G E U` is literally E.op followed by the upstream
  `AffineOverLimit.diagram (diagram x) (p x) (map_p x)` and evaluation at U.
  Its N-th ring is `Γ(Y_N, (Y_N → X) ⁻¹ᵁ U.toOpens)`, which is the sections
  of `Y_N ×_X V`. Its arrows are the existing induced pullbacks on sections.
  No arbitrary ring diagram or unrelated map stands in for the one in the node.
- `normalSectionAlgebraMap` pulls a base section to the whole-group stage and
  then into this ring colimit. The universal stage-factorization equation
  makes its normalization independent of that index and asserts that every
  colimit inclusion is a base-algebra map.
- Each displayed stage algebra is étale: the `∀ N, (...).hom.Etale` conjunct.
  `RingHom.Etale` is `Algebra.Etale` for that ring map's induced algebra;
  `Algebra.Etale` includes finite presentation. Thus these are precisely the
  stated finitely presented étale base-algebras.
- The displayed colimit base-algebra is ind-étale: the existing recorded
  predicate `RingHom.IndEtaleAcrossUniverses` applied to this concrete base map.
  It is the existing filtered-colimit definition, transported canonically by
  `RingHom.ulift`; it is not a new private predicate.
- The affine-limit identification is
  `∃ e : (proj x ⁻¹ᵁ U.toOpens).toScheme ≅ Spec (colimit ...)`.
  The first equation makes e an identification over the given affine base.
  The second, for every N, makes its composites with `Spec.map (colimit.ι ...)`
  equal the actual limit projections followed by inclusion in T. These
  characterize the canonical limit identification in the displayed formula.
- The singleton cover is exactly
  `Presieve.singleton (proj x) ∈ proetalePrecoverage X`.
  This is the existing fpqc precoverage restricted to weakly étale arrows;
  its induced small site is `Scheme.ProEt`. It expresses the finite-affine-open
  covering condition, not merely surjectivity or membership in a weaker topology.

### Dependencies read and reused

Each statement dependency's full node statement and its record or mathlib_match
was read. The actual declarations and docstrings were read, including the
finite-etale specialization explained by the recorded fibre-functor node.

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and its morphisms.
- `def-weil-connected-scheme`: `Mathlib.Topology.Connected.Basic`,
  `ConnectedSpace` (includes nonemptiness).
- `def-weil-pbc-quasi-compact-scheme`: `Mathlib.Topology.Defs.Filter`,
  `CompactSpace` (no Hausdorff condition).
- `def-weil-quasi-separated-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`,
  `QuasiSeparated` and its scheme form `QuasiSeparatedSpace`.
- `def-weil-geometric-point`: `Mathlib.FieldTheory.IsAlgClosed.Basic`,
  `IsAlgClosed`; `Mathlib.AlgebraicGeometry.ResidueField`,
  `Scheme.SpecToEquivOfField`, with geometric point written inline.
- `def-galois-fibre-functor`:
  `Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber`, `Scheme.flcFiber`,
  which explicitly reexports the finite-etale fibre interface;
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`,
  `Scheme.FiniteEtale.fiber`. The recorded proof dependency
  `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`,
  `Scheme.FiniteEtale.exists_fiber_flc_equivalence`, compares the two.
- `def-weil-pbc-finite-etale-category`: its mathlib_match is
  `CategoryTheory.MorphismProperty.Over` and `.Over.pullback` in
  `Mathlib.CategoryTheory.MorphismProperty.Comma` and `OverAdjunction`.
  The published `Scheme.FiniteEtale` is the equivalent existing nested full
  subcategory of étale objects where `IsFinite` holds, with all X-arrows;
  this is the exact category used by the dependency fibre functor. I use it
  directly, rather than create a competing finite-etale category.
- `def-weil-pbc-ind-etale-algebra`:
  `Sheaf.RingTheory.IndEtaleUniverseTransport`,
  `RingHom.IndEtaleAcrossUniverses`, reusing `Algebra.IndEtale` and
  `Algebra.Etale`. I read `IndPrincipalZariski` and the original
  `WeilConjectures.RingTheory.ProEtale.IndEtale` definitions too.
- `def-weil-pbc-proetale-site`: `Mathlib.AlgebraicGeometry.Sites.Proetale`,
  `Scheme.ProEt`, `Scheme.proetalePrecoverage` and `Scheme.ProEt.topology`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `Flat`.
- `def-weil-surjective-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, `Surjective`.
- `def-weil-weakly-etale-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`, `WeaklyEtale`.
- `pqf-def-affine-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `IsAffineHom`.
- `def-weil-size-convention`: the node's metatheoretic convention has no
  declaration or module; explicit u and the existing SmallModel implement it.

The public imports expose the statement's dependencies. The proof-only imports
are the recorded `FiberEquivalence`, `OpenSubgroups`, `LimitAffineTransition`,
`FiniteEtaleTraceDegree`, `LimitFibreProducts`, and `EtaleComparison` modules.
Other proof dependencies are Mathlib declarations already reached by these
imports, rather than independent unstated modules. The published
`UniversalCoverConstruction` is reused publicly for the actual construction;
its `Index`, `point`, `diagram`, `p`, `proj`, `cover`, `pt`, and `pNatTrans`
were all read. The section-ring machinery and `AffineOverLimit.chart` were
read in `WeilConjectures.AlgebraicGeometry.Limits.AffineOverLimit`.

### Edge cases checked

- Trivial fundamental group (e.g. separably closed base field): the whole-group
  index exists, its quotient is a singleton, and the identity cover occurs.
  The construction does not demand a proper open subgroup or a nontrivial cover.
- A finite fundamental group: the trivial subgroup can occur as an open normal
  subgroup and gives a final refinement in the inverse-system sense.
- General infinite profinite groups: the whole group and binary intersections
  exist; no finite generation, countability or sequence hypothesis is imposed.
- Empty X is excluded exactly by the node's connected/nonempty hypothesis.
  Nonempty T is present through ConnectedSpace, with the explicit geometric point.
- Empty affine open V is allowed; its section ring is the zero ring and its
  inverse image is empty. CommRingCat and Spec allow this, and no nontrivial-ring
  hypothesis was added to the chart assertion.
- Identity transitions are included. Their stated finite étale surjectivity and
  quotient identity equations have the expected meaning.
- Arbitrary characteristic is allowed. No coefficient prime or normality of X
  is introduced; the only normality is normality of the open subgroups.
- Every small cofinal diagram is quantified, including the identity indexing,
  equivalently presented skeletons and systems with repeated representatives.
- X need not be affine, noetherian, integral or separated. Affine charts are
  treated one at a time, so affineness of v is not mistaken for affineness of T.

### Searches actually run

All four msearch calls used the required wrapper and this group/item.

1. LeanFinder: `The pointed Galois inverse limit of finite etale covers is
   connected affine surjective weakly etale with ind etale affine charts`.
   Eight hits: étale site objects/forgetful functors, general affine-transition
   infrastructure, and étale algebra descent. No theorem has all the clauses.
2. Loogle: `AlgebraicGeometry.Scheme.UniversalCover.cover,
   AlgebraicGeometry.WeaklyEtale`. Zero hits; the service reported the project
   identifier unknown. This is recorded as a limitation, not an exact absence
   result; direct source inspection supplied the actual existing construction.
3. Grep through msearch, subdirectory AlgebraicGeometry:
   `PointedGalois|surjective_of_isLimit|connectedSpace_cover`. Zero Mathlib hits.
4. LeanSearch: `An inverse limit of pointed connected finite Galois etale
   covers is an affine surjective weakly etale connected scheme`.
   Eight hits: general affine-limit and compact-limit theorems and profinite-space
   limits; none includes the pointed normal-subgroup representation and all clauses.
5. Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for
   `PointedGalois|pointedGalois|pointed_galois|normalSectionDiagram|
   pointedGaloisLimitGeometry`. This found the published construction and
   `PointedLimitCech`, which were read. The construction supplies the objects
   and some geometry, while the old parent Čech theorem has extra splitting,
   deck, simplicial and component conclusions and omits the explicit stage
   qcqs/projection/chart data of this item. Neither is an exact existing match.
6. `grep -rn 'lem-sfb-pointed-galois-limit-geometry' lean/WeilConjectures`
   returned no matches. The upstream names index was also searched for the
   pointed Galois terminology. No competing declaration of the new names exists.

Sources checked locally: `literature/stacks-project/limits.tex` at
`lemma-directed-inverse-system-has-limit`, the affine schemes limit lemma,
`lemma-limit-nonempty`, and `lemma-descend-opens`; `pione.tex` at
`theorem-fundamental-group`; `proetale.tex` at `definition-ind-etale` and
`lemma-ind-etale-implies`. These are the recorded source, not an alternative route.

No STATEMENT-DISPUTED issue or statement fault was found. The module-mode
compiler probes revealed only namespace/API issues (`evaluation` needed its
category-theory namespace, and the explicit whole-group open normal subgroup
needed both constructor layers); these were corrected without changing the
mathematical statement. All variables are bound with autoImplicit disabled.

## Second reading by Q141

The dispatcher prohibits another agent, so this is a second reading by the author;
the maintainer's later independent review remains necessary. I reopened the node
and final module side by side and checked the hypotheses and every conclusion
as matched above, including all helpers. I did not claim an independent reader.

The main subtlety is that the canonical limit already exists upstream. Reusing
it is essential: the existential E and q identify its stages with the prescribed
normal-subgroup covers. q fixes the identity coset and the LEFT monodromy action;
the equation for each transition fixes aM ↦ aN. E being an equivalence gives all
pointed Galois covers, while the explicit simple-transitivity and connectedness
clauses give the node's geometric Galois meaning.

I checked the cofinality direction (Initial for limits), and included the
cofinal limit statement in Over X as well as schemes. I checked the affine
identification is over the specified base and commutes with every stage
projection, so it cannot be an arbitrary abstract Spec isomorphism. I made the
étale stage-ring clause explicit; finite presentation is part of its existing
Algebra.Etale predicate. The stage/base factorization equations ensure the
ring colimit is the one of base-algebras in the node. The empty-open case works
because neither the ring predicates nor Spec require a nontrivial ring.

No node text, hypothesis, dependency or proof was changed on this reading.
The helper definitions have no sorry or proof choice; the only sorry is the
main theorem. The mathematical statement is neither replaced by the stronger
old parent Čech theorem nor reduced to a subset of its geometric conclusions.

### Validation

The prescribed scompile.py server wrapper compiled the module separately in
sandbox mode and in its library module path, with exit 0 and no diagnostics.
After the final stage-ring clause was made explicit, compilation was rerun;
the dry run and delivery results are recorded below when obtained.

Final compile: both sandbox and library module modes passed with exit 0 and no
compiler diagnostics after the stage-ring clause was included. The dry run
`deliver2.py Q141 lem-sfb-pointed-galois-limit-geometry --no-push` printed
`OK (dry run): commit c16619b6b0c passes the preflight and compiles; nothing pushed`.
The delivery command repeats those gates before its authorized push.

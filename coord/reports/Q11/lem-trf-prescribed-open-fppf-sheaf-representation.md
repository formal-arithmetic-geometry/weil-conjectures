## Worker report

The module `Sheaf.AlgebraicGeometry.PrescribedOpenFppfSheafRepresentation` states
`AlgebraicGeometry.Scheme.existsUnique_prescribedOpen_fppfSheaf_representation`.
It introduces no definitions and proves nothing: its single theorem has proof `sorry`.
The node is unchanged except for its `lean` record. No statement correction or disputed
statement is needed. No new nodes or dependency repairs are needed.

Source read: `literature/stacks-project/spaces-descent.tex`, lines 1497–1541,
`lemma-descending-property-open-immersion` (Stacks Tag 041X), especially the final
paragraphs gluing a section over the descended open and factoring arbitrary scheme-valued
points through it. The node already explicitly supplies the big-fppf-sheaf formulation.

Hypotheses and conclusions, clause by clause:

- A scheme T: `T : Scheme.{u}`. A sheaf of sets on the big fppf site over T:
  `F : Sheaf (fppfTopology.over T) (Type (max u v))`. This is the slice topology on
  `Over T`, not the small fppf site. Both scheme and value universes are explicit.
- A set-indexed family: `I : Type w`, `Tᵢ : I → Scheme.{u}`,
  `q : ∀ i, Tᵢ i ⟶ T`. The index universe is arbitrary; there is no finiteness or
  nonemptiness requirement. Étaleness is `[∀ i, Etale (q i)]`. Joint surjectivity is
  `hq : ∀ t : T, ∃ i, ∃ s : Tᵢ i, q i s = t`.
- The specified actual open subscheme: `U : T.Opens`, with scheme `U.toScheme`
  and its canonical open immersion `U.ι`. There is no extra hypothesis on U.
- The base change U_i: `pullback U.ι (q i)`, viewed over T_i through
  `Over.mk (pullback.snd U.ι (q i))`.
- Each supplied local isomorphism is `αᵢ i`. Its source is that object's Yoneda
  presheaf, composed with `uliftFunctor.{v}`; its target is
  `(Over.map (q i)).op ⋙ F.obj`. The latter evaluates on W over T_i by composing
  its structure morphism with q_i, exactly the restriction in the node. The lift
  merely puts Hom sets into the sheaf's value universe; it imposes no size equality.
- The global natural isomorphism is the existentially quantified `α`, from the
  lifted `yoneda.obj (Over.mk U.ι)` to `F.obj`. Thus the representing object is U,
  not an unspecified scheme or an arbitrary map.
- The first conjunct prescribes every local restriction. For every W over T_i
  and a : W → U_i over T_i, `Over.map (q i)` sends a to a T-map, and composing
  with `Over.homMk (pullback.fst U.ι (q i)) pullback.condition` sends it to the
  corresponding map W → U. The equality of evaluations with `(αᵢ i).hom.app`
  is exactly the fibre-product identification. It specifies all components.
- The second conjunct quantifies over every isomorphism β satisfying just those
  local restriction equalities and asserts `β = α`. Uniqueness is therefore not
  restricted to competitors additionally assumed to satisfy the later formulas.
- The node's b is rendered in full as
  `α.hom.app (op (Over.mk U.ι)) ⟨𝟙 (Over.mk U.ι)⟩`. Its type is F(U).
  The third conjunct says that α on a : Z → U equals `F.obj.map a.op` applied
  to b: precisely a^*b. Naturality itself is already part of the isomorphism.
- The fourth conjunct, for every test object Z and x ∈ F(Z), is
  `∃! a : Z ⟶ Over.mk U.ι, x = F.obj.map a.op b`. An arrow of `Over T` is
  exactly a morphism a to U with a ≫ U.ι = Z.hom. This supplies the stated
  unique factorization and the equality x = a^*b, without reducedness of Z.
- The final conjunct asserts `Nonempty F(Z) ∧ Subsingleton F(Z)` if that
  factorization type is nonempty, and `IsEmpty F(Z)` otherwise. This expresses
  singleton versus empty literally; `Subsingleton` alone would not assert existence.
- No compatibility of the α_i, quasi-compactness, finiteness, separatedness,
  reducedness, or algebraic-space structure is imposed.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme`, `Scheme.Hom`; their full structures and docstrings read.
- `def-pc-fppf-site`: `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
  `Scheme.fppfPrecoverage` and `Scheme.fppfTopology` (flat, locally finitely
  presented, jointly surjective families). The existing record explicitly directs
  slice consumers to `Mathlib.CategoryTheory.Sites.Over`,
  `GrothendieckTopology.over`, used here.
- `def-weil-pbc-sites-and-cohomology`:
  `Sheaf.CategoryTheory.SiteCoveringAxioms`, `Precoverage.IsSiteForCoverings`.
  Its full definition/docstring read. Its record retains Mathlib's `Sheaf` for
  the sheaf component; that standard definition is used, rather than duplicating it.
- `def-weil-size-convention`: a metatheoretic convention with no declaration;
  rendered by explicit `universe u v w`, schemes in u, values in max u v,
  and covering indices in w.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale`, full class and docstring read; used on q_i.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`, full abbreviation/docstring read.
  The statement uses its canonical instance on the inclusion of `T.Opens`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `Limits.pullback`, `pullback.fst`, `pullback.snd`, full signatures/docstrings
  read. `Mathlib.AlgebraicGeometry.Pullbacks` provides scheme pullbacks.
- All other proof dependencies are already Mathlib matches: the full signatures of
  `Precoverage.mem_coverings_of_isPullback` (Precoverage),
  `IsOpenImmersion.mono`, `IsOpenImmersion.lift`, `lift_fac`, `lift_uniq`
  (OpenImmersion) were read. Their modules are already imported transitively by
  the public statement dependencies, so no additional proof import is needed.
  The theorem docstring records all six proof steps from the node, including
  automatic overlap compatibility, the prescribed restriction calculation,
  factorization without reducedness, and uniqueness.

Edge cases checked before drafting and again against the signature:

- I empty: joint surjectivity forces T empty; no `Nonempty I` assumption is added.
  The empty-cover sheaf condition supplies the unique section on the empty scheme.
- U empty and T nonempty: every local representative is empty. A nonempty Z cannot
  factor, hence has no section, whereas the empty Z has a unique section.
- U = T: every Z factors, so the conclusion gives exactly one section of F(Z).
- Nonreduced and non-quasi-compact Z and T, infinite covering families: no typeclass
  excludes them, and the proof uses the open factorization criterion for all schemes.
- Different universes of values and morphisms: all Yoneda presheaves are canonically
  lifted into `Type (max u v)` rather than assuming those levels equal.

Searches actually run:

1. `msearch.py ... leanfinder` query: “An fppf sheaf locally represented by pullbacks
   of a fixed open subscheme is uniquely represented by that open with prescribed
   local isomorphisms”. Eight hits, chiefly `Scheme.LocalRepresentability` results.
2. `msearch.py ... leansearch` query: “An fppf sheaf locally represented by base
   changes of a fixed open subscheme is uniquely represented by the open subscheme”.
   Eight hits including `LocalRepresentability.isRepresentable`, `representableBy`,
   `yonedaIsoSheaf`, and open-restriction results. Read the representability
   declarations in `Mathlib/AlgebraicGeometry/Sites/Representability.lean`:
   they concern Zariski-locally surjective relatively representable open maps and
   a constructed glued scheme, not this prescribed-open étale-local statement.
3. `msearch.py ... loogle` query `CategoryTheory.yoneda, CategoryTheory.Over.map`:
   zero hits. The declarations were then read directly in Mathlib.
4. `msearch.py ... grep` query
   `prescribed|representation.*open|open.*representation`, directory
   `AlgebraicGeometry/Sites`: zero hits.
5. `rg` on `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
   for `prescribed.open|prescribedOpen|PrescribedOpen|` followed by the item id:
   only unrelated mentions of prescribed opens; no declaration for this item.
   An exact-name `rg` on Mathlib, both project trees, and the upstream name index
   found no `existsUnique_prescribedOpen_fppfSheaf_representation` clash.
6. A broader `rg` for fppf slice Yoneda usage found existing consumers using
   `fppfTopology.over`, `Over.map`, and the lifted Yoneda convention, including
   `FppfSmallLocalRepresentatives.lean`. These interfaces are reused directly.

Validation: the prescribed `scompile.py Q11 <item> <module>` completed both its
sandbox and library module checks successfully, with no errors or warnings.

## Second reading by Q11

The dispatcher forbids starting other agents and delegates independent review to
maintenance. This section records the worker's own second pass, not an independent
agent review. I reopened the node statement and the finished signature and checked
all the correspondences above. In particular, uniqueness quantifies over β having
only the prescribed restrictions; local evaluation uses the actual first pullback
projection; the target of each local iso composes its test structure map with q_i;
all test objects range over `Over T`; and the final singleton clause includes
existence. No mismatch was found, and no statement or dependency change was made.

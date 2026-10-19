## Worker report

The module `Sheaf.CategoryTheory.LocalWeakEquivalenceHomotopyLifting` states
`CategoryTheory.LocalSimplicialPresheaf.local_relative_homotopy_lifting` with a single
`sorry`. It introduces no definitions. Source read: Dugger--Isaksen, *Weak equivalences
of simplicial presheaves*, https://arxiv.org/pdf/math/0205025, Definitions 3.1 and 6.11,
Proposition 6.9, Theorem 6.15(a), and the combinatorial forward argument in Section 5.
The theorem docstring gives that argument, including degree zero and refinement of
the finitely many local choices. The node has empty `proof` and `proof_deps`; there
are no recorded proof-dependency imports to add.

Clause-by-clause correspondence:

- The small site is `{C : Type u} [SmallCategory C] (J : GrothendieckTopology C)`.
  Mathlib's `Sieve` is precomposition closed and `GrothendieckTopology` supplies the
  maximal-sieve, pullback and transitivity axioms. Explicit universes `u w` and
  `SSet.{max u w}` implement `def-weil-size-convention` and allow values at least as
  large as the chosen small site, with an arbitrary larger value universe.
- The two simplicial presheaves are `(F G : Cᵒᵖ ⥤ SSet.{max u w})` and the natural
  transformation is `(f : F ⟶ G)`. The objectwise Kan hypotheses are exactly `hF`
  and `hG`, quantified over every object of `C`. `SSet.KanComplex` means all horn
  fillers; its `hornFilling` lemma includes dimension one and every horn index.
- The component-sheaf isomorphism and every positive based homotopy-sheaf
  isomorphism are `hw : IsLocalWeakEquivalence J f`. This existing definition's
  first conjunct is literally `IsIso` of the component natural transformation
  mapped by `presheafToSheaf J (Type (max u w))`.
- Its second conjunct expresses local surjectivity on `Pi` in every degree `n+1`
  and at every object and vertex; the third expresses local injectivity. `Pi`
  is the existing Mathlib relative-cylinder-homotopy quotient of pointed
  simplices. For Kan values these are the underlying sets of the based homotopy
  groups. Isomorphism of sheafified group homomorphisms is detected on underlying
  sets. These local bijectivity criteria are equivalent to the associated-sheaf
  isomorphisms, as in DI Lemma 6.8 and Proposition 6.9 and Mathlib's
  `GrothendieckTopology.W_iff_isLocallyBijective`.
- This hypothesis covers every slice, not just global basepoints: for an object
  `r : W ⟶ V` in `C/V`, apply its quantifiers to `W` and the restricted vertex
  `(F.map r.op).app _ x`. A covering sieve over that slice object is a covering
  sieve on `W` with the induced slice topology. Naturality identifies the target
  basepoints, exactly as the definition's `HEq` in local surjectivity does.
- The universally chosen object and nonnegative dimension are `(V : C) (n : ℕ)`.
  The maps `a` and `b` have domains `SSet.boundary n` and
  `SSet.stdSimplex.obj ⦋n⦌`, respectively. Mathlib's boundary is the union of proper
  faces; `boundary_zero` makes it empty for `n = 0`.
- The given square is `hab : a ≫ f.app (op V) = (SSet.boundary n).ι ≫ b`.
- `∃ S : Sieve V, S ∈ J V ∧ ...` supplies exactly a covering sieve. Then
  `∀ (W : C) (r : W ⟶ V), S r → ∃ c H, ...` allows independent choices for every
  covering arrow, with no compatibility assertion.
- `c : SSet.stdSimplex.obj ⦋n⦌ ⟶ F.obj (op W)` is the requested simplex map.
  The first equation `(SSet.boundary n).ι ≫ c = a ≫ F.map r.op` states its exact
  boundary, not merely a homotopy condition.
- `H : SSet.stdSimplex.obj ⦋n⦌ ⊗ SSet.stdSimplex.obj ⦋1⦌ ⟶ G.obj (op W)` is
  the requested cylinder map. Mathlib's simplicial-set tensor is the degreewise
  cartesian product, as seen in `SSet.tensorHom_app_apply` and its monoidal instance.
- `SSet.ι₀ ≫ H = c ≫ f.app (op W)` and
  `SSet.ι₁ ≫ H = b ≫ G.map r.op` give the endpoints in the specified order.
  The source definitions of `ι₀` and `ι₁` use the constant vertices zero and one.
- The fourth equation restricts `H` by `(SSet.boundary n).ι ▷ ...`, and equals
  `fst _ _ ≫ a ≫ F.map r.op ≫ f.app (op W)`. This is precisely the constant
  boundary homotopy `(f_W r* a) pr₁`.
- No local fibration hypothesis on `f` occurs anywhere in the signature.

Dependency declarations read and used:

- `def-weil-size-convention`: recorded as a metatheoretic convention with no
  declaration; implemented by the explicit universe binders above.
- `def-weil-pbc-simplicial-set`: Mathlib `SSet`, the functor category of simplicial
  sets; the recorded `degenerate`, `nonDegenerate`, `Subcomplex` and `Finite`
  definitions were also inspected. Only `SSet` and `Subcomplex` are needed here.
- `def-weil-pbc-sheafification`: `CategoryTheory.presheafToSheaf`,
  `CategoryTheory.toSheafify` and `CategoryTheory.sheafificationAdjunction`, in
  `Mathlib.CategoryTheory.Sites.Sheafification`; used through the landed predicate.
- Added the already landed `def-cbc-local-simplicial-presheaf-maps` to `stmt_deps`.
  Its module `Sheaf.CategoryTheory.LocalSimplicialPresheafMaps` is publicly imported;
  its full declarations `CategoryTheory.LocalSimplicialPresheaf.Pi`, `piMap` and
  `IsLocalWeakEquivalence` were read. This reuses the existing notion, without
  adding a new node or changing a dependency interface. The theorem uses
  `IsLocalWeakEquivalence`; `Pi` and `piMap` occur in that definition.

Edge cases checked: `n = 0` has empty boundary and reduces to local component
surjectivity followed by an edge in a Kan target, with no chosen source basepoint
assumed in the theorem. For `n = 1` the boundary has both endpoints and the relative
condition fixes both throughout the homotopy. Empty values and the empty site
are not excluded: if a source value is empty, there need be no square in positive
degree, and degree-zero lifting is only required on a covering sieve (possibly
empty when that covers). Arbitrary covering sieves are allowed; no points,
enough-points assumption, representable cover, or nonempty-cover hypothesis is
introduced. There is no assumption that `F` or `G` is a sheaf. The `max u w` value
universe is the existing dependency's site size convention.

Searches made (2026-10-17):

- `msearch.py ... leanfinder` query "A local weak equivalence of Kan simplicial
  presheaves admits local lifts of boundary squares up to homotopy relative boundary":
  eight hits on abstract model-category Joyal-trick and ordinary horn-lifting
  infrastructure; no local simplicial-presheaf theorem.
- `msearch.py ... loogle` query
  `SSet.KanComplex, CategoryTheory.GrothendieckTopology`: zero hits.
- `msearch.py ... leansearch` query "simplicial presheaf homotopy groups on slice
  site and local weak equivalence": eight hits, including abstract localization,
  ordinary `SSet.hoFunctor` and one-hypercover homotopies; none states this theorem.
- `msearch.py ... grep` query
  `local.*weak.*equivalence|homotopy[Ss]heaf|homotopy.*[Pp]resheaf`: 25 unrelated
  abstract model-category weak-equivalence/homotopy hits.
- `rg` in `WeilConjectures` for homotopy-group/presheaf/sheaf names and local weak
  equivalences found no relevant declaration; searching the exact item ID found
  none. `rg` of the proposed theorem name in `dag/lean_names_upstream.json`,
  `WeilConjectures`, and `lean/Sheaf` found no collision.
- `rg` in `lean/Sheaf` found the landed `LocalSimplicialPresheafMaps` module and
  `HypercoverRelativeLifting` (the latter additionally assumes a local fibration
  and concerns hypercover refinement, so is a different statement). Its defining
  DAG record was read in full and its declaration is reused here.
- `rg` in `dag/nodes` and `tools/blueprint_refs.py search 'homotopy presheaf'`
  confirmed the existing local-map notion; the blueprint search itself returned
  zero matches. `blueprint_refs.py ancestor` returned `thm-cbc-finite-level-proetale`.

No statement correction or disputed statement is needed. No repair-note file for
this item was found. The local node copy initially has `status: unsplit` and empty
proof arrays; these inherited fields are preserved as required. Only `lean` and
the added landed definition dependency are changed.

Validation: the prescribed `scompile.py` compiled both the sandbox view and the
library module without errors or warnings (1.3 s and 1.5 s). The module contains
one theorem with `sorry`, no helper proofs or data definitions, and no implicit
universe or object binders. Delivery dry-run result follows below after execution.

Delivery dry run: `deliver2.py NC lem-cbc-local-weak-equivalence-homotopy-lifting
--no-push` printed `OK (dry run)` for commit `963e7a31cb`: compilation and server
preflight passed except for the independent second-reading section, which is
reserved for the second reader. Nothing was pushed.

## Second reading by NC

Independent second reader, 2026-10-17. I opened the sandbox node and Lean module,
the current repository node, and all four statement-dependency records. I read
the actual `LocalSimplicialPresheafMaps` declarations, including the bodies of
`Pi`, `piMap` and `IsLocalWeakEquivalence`, rather than relying on their names.
There are no new nodes or dependency modules in this delivery, no
`statement_change`, and no repair note for this item. The node's mathematical
statement needs no correction; the theorem signature is preserved.

Source checked: [Dugger--Isaksen](https://arxiv.org/pdf/math/0205025), Section 2's
pointed-simplex convention, Definition 3.1, Section 5, Section 6.1 and Convention
6.4, Section 6.5, Lemma 6.8, Proposition 6.9, Definition 6.11, and Theorem 6.15(a).
This node cites that paper, not a Stacks theorem. Section 6 works over a
Grothendieck site and assumes local fibrancy for the relevant theorem;
objectwise Kan values supply it using the maximal covering sieve. No enough
points assumption or local fibration assumption on the map is needed. I also
read Stacks `simplicial.tex`, Section `section-simplicial-set` and its standard
simplex example, and `sites.tex`, `proposition-sheafification-adjoint`, for the
two recorded foundational dependencies.

The following is my list of every introduced object, hypothesis and conclusion
clause, with its Lean rendering and verdict:

1. Small category and its universes: `{C : Type u} [SmallCategory C]`, with
   explicitly declared `universe u w`. Correct; no field, scheme, characteristic,
   finiteness or nonemptiness hypotheses are present.
2. Covering-sieve topology: `(J : GrothendieckTopology C)`. Correct. I checked
   `Sieve.downward_closed` and the topology's `top_mem'`, `pullback_stable'` and
   `transitive'` fields against the axioms spelled out in the node.
3. Simplicial presheaves and natural transformation:
   `(F G : Cᵒᵖ ⥤ SSet.{max u w})` and `(f : F ⟶ G)`. Correct. Mathlib's `SSet`
   is `SimplicialObject (Type _)`; presheaf morphisms are natural transformations.
4. Kan values at every object: `hF : ∀ V : C, SSet.KanComplex (F.obj (op V))`
   and the corresponding `hG`. Correct. I checked `KanComplex` and
   `KanComplex.hornFilling`, whose `n+1` and `Fin (n+2)` include every positive
   dimension and every horn index.
5. Isomorphism of associated component sheaves: the first conjunct of
   `hw : IsLocalWeakEquivalence J f` is exactly `IsIso` of the component map
   under `presheafToSheaf J (Type (max u w))`. Correct. I read `presheafToSheaf`,
   `toSheafify` and `sheafificationAdjunction` in Mathlib.
6. All positive based homotopy-sheaf isomorphisms, on every slice: the remaining
   two conjuncts of `hw` quantify over every `V`, vertex `x`, and degree `n+1`.
   They give local surjectivity and injectivity for `Pi`. Correct. `Pi` is
   Mathlib's `RelativeMorphism.HomotopyClass` for the boundary and the subcomplex
   generated by `x`. Its `Quot` imposes the equivalence relation generated by
   relative cylinder homotopy; `piMap` is actual postcomposition. These are the
   underlying based homotopy sets for Kan values. For an object `r : W ⟶ V`
   of a slice, apply the clauses at `W` and the restricted vertex. Conversely
   take the identity object of the slice. The induced slice covers are exactly
   covers on these domains, and `HEq` only transports the equal basepoints given
   by naturality. Thus this is equivalent to the stated slice sheaf condition;
   it does not restrict the hypothesis to global basepoints. I checked the
   Mathlib local-bijectivity criterion in `Sites/LocallyBijective.lean`.
7. Arbitrary object, nonnegative dimension, and boundary square:
   `(V : C) (n : ℕ)`, `a : SSet.boundary n ⟶ F.obj (op V)`,
   `b : SSet.stdSimplex.obj ⦋n⦌ ⟶ G.obj (op V)`, with `hab` asserting
   `a ≫ f.app (op V) = (SSet.boundary n).ι ≫ b`. Correct, including the
   orientation of the commutative square.
8. One covering sieve for this square: `∃ S : Sieve V, S ∈ J V ∧ ...`.
   Correct; the sieve is chosen after the object, degree, square and its
   commutativity witness.
9. Independent lifts along every covering arrow:
   `∀ (W : C) (r : W ⟶ V), S r → ∃ c H, ...`. Correct; no naturality or
   compatibility requirement is imposed on these choices.
10. The lifted simplex and cylinder have types
    `c : SSet.stdSimplex.obj ⦋n⦌ ⟶ F.obj (op W)` and
    `H : SSet.stdSimplex.obj ⦋n⦌ ⊗ SSet.stdSimplex.obj ⦋1⦌ ⟶ G.obj (op W)`.
    Correct. `Monoidal.lean` computes tensor degreewise as the product and
    `tensorHom_app_apply` computes the two factors separately.
11. Exact boundary: `(SSet.boundary n).ι ≫ c = a ≫ F.map r.op`. Correct;
    this is equality of maps, not a homotopy class.
12. Initial endpoint: `SSet.ι₀ ≫ H = c ≫ f.app (op W)`. Correct;
    `ι₀` uses the constant vertex zero of the interval.
13. Final endpoint: `SSet.ι₁ ≫ H = b ≫ G.map r.op`. Correct;
    `ι₁` uses the constant vertex one, so the endpoint order agrees with the node.
14. Relative boundary: `(SSet.boundary n).ι ▷ SSet.stdSimplex.obj ⦋1⦌ ≫ H =
    fst _ _ ≫ a ≫ F.map r.op ≫ f.app (op W)`. Correct. Whiskering is inclusion
    on the first product coordinate, and `fst` forgets the interval coordinate;
    hence this fixes the full boundary throughout the homotopy.
15. Absence of a local fibration hypothesis on `f`: correct; none occurs in the
    theorem or in `IsLocalWeakEquivalence`. The horn-fibration definition in the
    dependency module is a separate, unused predicate.

Edge cases: `n = 0` is included, and Mathlib's `boundary_zero` identifies its
boundary with the empty subcomplex; only local component surjectivity is needed.
For `n = 1`, both boundary vertices are fixed and the proof must use components
for the degree-zero obstruction. Empty site and empty Kan values are allowed;
an empty source value does not create a positive-dimensional boundary square,
and in degree zero a covering sieve may be empty if the topology permits it.
There is no index set, coefficient ring, scheme or characteristic to restrict.
The empty-cover case is preserved by `∀ r, S r → ...`. Values have universe
`max u w`, the size convention already used by the dependency. This allows
arbitrarily large values above the chosen small site. No new universe or
typeclass restriction was introduced.

Independent searches, using different wording from the worker:

- `msearch.py ... leanfinder "boundary inclusion local relative cylinder lifting
  for weak equivalences between fibrant simplicial presheaves"`: eight abstract
  cylinder/model-category results; no simplicial-presheaf local RHLP theorem.
- `msearch.py ... leansearch "A map of presheaves of Kan complexes inducing
  isomorphisms on homotopy sheaves has local homotopy lifting of simplicial
  boundaries"`: eight hits, including topological covering homotopy lifting,
  ordinary horn fibrations and sheafification lifts; no match.
- `msearch.py ... loogle "SSet.KanComplex, Sieve"` recognized no `Sieve`
  identifier in its index and supplied no usable result; I do not count this as
  a successful absence search. The successful LeanFinder search supplies that
  search category independently.
- `rg` in Mathlib's simplicial-set and sites sources and in upstream
  `WeilConjectures` for `local.*rhlp`, `relative.homotopy.lift`,
  `homotopy.sheaf`, and Kan/presheaf combinations found no matching statement.
  Wider searches in `lean/Sheaf` found the existing local-map definition and
  `HypercoverRelativeLifting`; I opened the latter's signature. It assumes a
  local fibration and concludes strict lifting after hypercover refinement,
  so it is a different statement. The enriched-category occurrences of local
  weak equivalences also concern a different notion. The proposed full theorem
  name does not occur in upstream sources, the upstream name index, or landed
  `lean/Sheaf` modules.

Mismatches found and repaired: the worker report's claims that the node has empty
`proof`/`proof_deps` and inherited `status: unsplit` are stale. The actual node
contains a nine-step proof and seven proof dependencies. I preserved its fields
and the correct signature, added ordinary imports for the recorded corner-map,
local-bijectivity, Kan-mapping-invariance, simplicial-homotopy-equivalence and
Kan-model-core proof tools, and expanded the theorem docstring to match all nine
steps. In particular it now explains the two homotopy extensions for changing a
square, the fixed-vertex nullhomotopy, the separate `n = 1` component argument,
the auxiliary horn-to-boundary construction, the face identities, and covering
sieve composition. I opened each of the three imported project proof modules
and read its signature and docstring. No mathematical statement was changed,
no duplicate definition or helper was added, and the sole theorem proof remains
`sorry`.

Mechanical verification: compared the sandbox node with the repository node;
only `lean` and addition of the landed local-map node to `stmt_deps` differ.
The recorded `lean.statement` is verbatim the signature in the file. All object
and universe variables are explicitly bound, every declaration has its source
and blueprint docstring, and all Lean lines have at most 100 characters.
The prescribed `scompile.py` passed with no errors or warnings for the final
module (sandbox 1.7 s, library 2.2 s).

## Worker report

The module `Sheaf.GroupTheory.InfiniteTameInverseLimit` states
`ProfiniteGrp.finiteExtension_inverseLimit_exact_pro_p`, with its sole theorem proof
`sorry`. It also constructs `ProfiniteGrp.finiteExtensionLimitMap` and
`ProfiniteGrp.finiteExtensionLimitKernel`, helpers belonging to this very statement.
Both have real data from existing Mathlib constructions. No independent notion or
additional DAG statement is introduced. The item's node is unchanged except for `lean`.

Sources read: Stacks Project `pione.tex`, Tag 0BUA,
`lemma-structure-decomposition`, including the inverse-system diagram, continuity and
surjectivity argument, and final inverse-limit exactness paragraph (lines 3175–3342);
current blueprint `main-20261015`,
`sec-six-functors-basics/sk-prop-a1-kummer/lem-exc-dvr-galois.proof.md`, especially its
second paragraph, “Taking inverse limits ... where P is pro-p”. The theorem docstring
contains all eight steps of the node's proof, including nonabelian fibre adjustment,
quotient topology, surjective kernel projections, and finite-coordinate factorization.

Hypothesis-by-hypothesis correspondence:

- Prime `p`: `(p : ℕ) (hp : p.Prime)`.
- Nonempty directed partially ordered index set: `{Λ : Type u} [PartialOrder Λ]
  [Nonempty Λ] [IsDirectedOrder Λ]`. `IsDirectedOrder` is Mathlib's abbreviation for
  `IsDirected Λ (· ≤ ·)` (`Order/Directed.lean:150`), precisely pairwise upper bounds.
  The index and the groups share universe `u` as required for these inverse limits.
- Finite groups `I_λ`, `C_λ` with discrete topologies: the objects of
  `(I C : Λᵒᵖ ⥤ ProfiniteGrp.{u})`, with the two pointwise `Finite` instances and the
  two pointwise `DiscreteTopology` instances. A finite discrete group is canonically
  profinite (`ProfiniteGrp.ofFiniteGrp`, Basic.lean:224), so bundling this way adds no
  mathematical hypothesis. Conversely, all objects here are explicitly finite discrete
  groups. Their homomorphisms are continuous automatically in the discrete topologies.
- Transition maps and their identity/composition laws: `I.map f`, `C.map f` and the
  functor laws. An arrow `j ⟶ k` in `Λᵒᵖ` means the original index of `j` is at least
  that of `k`, matching `u_{μλ}` and `v_{μλ}`. Thus all and only comparable pairs occur.
- Surjectivity of the transitions: `hIsurj`, `hCsurj`.
- Normal subgroups `P_λ`: `(P : ∀ j : Λᵒᵖ, Subgroup (I.obj j))` and the pointwise
  `(P j).Normal` instances.
- Their orders are powers of `p`: `hPorder : ∀ j, ∃ n : ℕ, Nat.card (P j) = p ^ n`.
  Subgroup finiteness is inherited from the ambient finite group.
- The surjective homomorphisms `θ_λ`: `(θ : I ⟶ C)` with `hθsurj`.
- The kernels are exactly `P_λ`: `hθker`, using the underlying `MonoidHom.ker`.
- Compatibility `θ_λ u_{μλ} = v_{μλ} θ_μ`: naturality of `θ`. Category composition
  runs left to right, so the naturality equality is the same commuting square.
- Surjectivity on the kernel subgroups: `hPsurj`, the subgroup image equality
  `(P j).map (I.map f).hom.toMonoidHom = P k`. This gives both preservation and
  surjectivity of the restricted transition.

Objects and every conclusion clause:

- `I = lim I_λ`, `C = lim C_λ`: Mathlib's `ProfiniteGrp.limit I` and `limit C`.
  Reading Basic.lean:317–385 shows their underlying types are the subgroup
  `limitConePtAux`, consisting of the actual compatible families in the product.
  Topologies are the inherited subtype topologies of the product topologies.
- `P` consists of those compatible families all of whose coordinates belong to `P_λ`:
  `finiteExtensionLimitKernel I P` is exactly
  `(Subgroup.pi Set.univ P).comap (limitConePtAux I).subtype`.
  `Subgroup.pi` and `Subgroup.comap` give this carrier, its group structure, and the
  ordinary subgroup subtype topology. Therefore these are exactly `lim P_λ`, with
  the node's subspace topology. No abstract replacement limit is chosen.
- The canonical map `θ((x_λ)) = (θ_λ(x_λ))` is the *constructed*
  `finiteExtensionLimitMap θ`, using
  `((limitConeIsLimit C).map (limitCone I) θ).hom`. This is Mathlib's universal-property
  map on its explicit limit cones, with no arbitrary map or choice from a mere
  existence assertion. The first conjunct records its coordinate formula for every
  `x` and `j`. Continuity and the homomorphism property are in its `→ₜ*` type.
- Surjectivity is the second conjunct,
  `Function.Surjective (finiteExtensionLimitMap θ)`.
- The kernel equality is the third conjunct,
  `(finiteExtensionLimitMap θ).toMonoidHom.ker = finiteExtensionLimitKernel I P`.
- Closedness is the fourth conjunct `IsClosed (... : Set (limit I))`.
- Normality is the witness `hnormal : (finiteExtensionLimitKernel I P).Normal`.
- The induced map `I/P → C` is an isomorphism of topological groups: the same
  conjunct supplies a `ContinuousMulEquiv`, using exactly the quotient by the
  coordinatewise subgroup, with `QuotientGroup.instTopologicalSpace`. Its group
  multiplication is supplied explicitly by
  `QuotientGroup.Quotient.group ... hnormal`, avoiding any hidden `let` or file-local
  instance. The formula `∀ x, e (QuotientGroup.mk x) = finiteExtensionLimitMap θ x`
  identifies this as the induced map, not an unrelated isomorphism. `ContinuousMulEquiv`
  contains multiplicativity, bijectivity, and continuity of both directions.
- Every finite continuous quotient of `P` has p-power order: the final conjunct
  quantifies over every group `Q : Type v`, `[Finite Q]`, `[TopologicalSpace Q]`,
  `[DiscreteTopology Q]`, and every `f : finiteExtensionLimitKernel I P →ₜ* Q`, with
  the sole extra premise `Function.Surjective f`, and concludes
  `∃ n : ℕ, Nat.card Q = p ^ n`. Universe `v` is independent. This is a condition on
  finite continuous quotients, never the false claim that the infinite kernel is a
  torsion p-group.

Dependency declarations read and used:

- `lem-galois-inverse-limit-surjective` has status `mathlib` and no `lean` record, as
  intended. Its `mathlib_match` names both clauses in
  `Mathlib.CategoryTheory.CofilteredSystem`:
  `nonempty_sections_of_finite_inverse_system` (root namespace, lines 111–113), whose
  full signature takes `[Preorder J] [IsDirectedOrder J]`, a functor
  `Jᵒᵖ ⥤ Type v`, and pointwise `Finite`/`Nonempty`, and concludes nonempty sections;
  `CategoryTheory.Functor.eval_section_surjective_of_surjective` (312–322), taking a
  cofiltered-or-empty category, pointwise `Finite`/`Nonempty`, surjectivity of each
  transition, and a chosen object, and concluding surjective evaluation of sections.
  I read both source declarations and docstrings, as well as the surrounding
  `[IsCofilteredOrEmpty J]` variable. They apply to the node's fibre systems (step 4)
  and kernel subgroup system (step 6); the actual compatible-family encoding agrees
  with their section encoding.
- The two proof-only Mathlib leaves were also read: `ProfiniteGrp.ofClosedSubgroup`
  in `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic` (249–251), specialized
  to `ProfiniteGrp.pi` of `ofFiniteGrp`; and
  `Topology.IsQuotientMap.of_surjective_continuous` in
  `Mathlib.Topology.Separation.Hausdorff` (682–684), with compact source, Hausdorff
  target, continuous map and surjectivity. The former module supplies the limit
  objects in the statement; CofilteredSystem and Hausdorff are proof-only imports.
- Additional Mathlib interfaces read: `ProfiniteGrp.limitConePtAux`, `limitCone`,
  `limitConeIsLimit`, `limit` (Basic.lean:317–385);
  `CategoryTheory.Limits.IsLimit.map` and `map_π` (Limits/IsLimit.lean:87–94);
  `Subgroup.pi` (Algebra/Group/Subgroup/Basic.lean:176–190);
  `ContinuousMulEquiv` (Topology/Algebra/ContinuousMonoidHom.lean:310);
  `QuotientGroup.Quotient.group` (GroupTheory/QuotientGroup/Defs.lean:72);
  `QuotientGroup.instTopologicalSpace`, `isQuotientMap_mk`, `continuous_mk`
  (Topology/Algebra/Group/Quotient.lean:32–46). These supply the objects rather than
  copied definitions of general notions.

Edge cases checked against the informal statement and Lean signature:

- Empty indexing sets are excluded by the node and exactly by `[Nonempty Λ]`.
  A singleton index is allowed, and specializes to the finite exact sequence and
  finite quotient p-power assertion.
- A directed partial order need not be a linear order, have a largest index, or have
  countably many indices. Only pairwise upper bounds are required.
- Trivial groups, every `P_λ = 1`, every `C_λ = 1`, and the trivial finite quotient are
  included; `Nat.card Q = p^0 = 1` is allowed.
- The finite-coordinate neighbourhood can involve an empty finite set: nonemptiness
  supplies an index, as stated explicitly in the proof docstring.
- Nonabelian finite groups are allowed. No commutativity instances appear; the fibre
  lifting in step 4 uses left multiplication and its correct inverse.
- An inverse limit such as `ℤ_p` can have infinite-order elements. The last clause
  quantifies over finite continuous quotients and does not use abstract `IsPGroup`
  on the inverse-limit group.
- Both kernel and quotient use the prescribed topologies. The codomain universe of
  the finite-quotient quantifier is unrestricted, and all variables/universes are
  explicitly bound. No `let`, private definition, or file-local instance is used.

Searches actually run (the tool log is `searches.jsonl`):

- LeanFinder: “Inverse limits of exact sequences of finite groups with surjective
  transition maps have pro p kernel and quotient homeomorphism”. Eight results,
  including `ProfiniteGrp.limitConePtAux`, reconstruction from finite quotients, and
  its surjectivity; no exact-sequence/pro-p theorem. The limit construction is used.
- LeanSearch: “Inverse limit exact sequence of finite groups and finite continuous p
  group quotients”. Eight results, including `ProfiniteGrp.limit`,
  `ProfiniteGrp.instHasLimit`, and reconstruction maps; none states this theorem.
- Loogle: `ProfiniteGrp, surjective` returned “unknown identifier 'surjective'”; then
  the corrected query `"ProfiniteGrp", "surjective"` returned only
  `ProfiniteGrp.toLimit_surjective`. This concerns reconstruction of a single
  profinite group and is not the item.
- The initial broad wrapper grep query
  `sectionsSubgroup|limitConePtAux|pro.?p|inverse.limit.*exact` returned 25 mostly
  unrelated matches (the `pro.?p` alternative was broad). The targeted wrapper grep
  `exact|surjective|limitConePtAux` in `Topology/Algebra/Category/ProfiniteGrp` returned
  15 matches; none gives the whole statement.
- Direct `rg` on Mathlib's Grp limits and ProfiniteGrp sources found
  `GrpCat.sectionsSubgroup` and `ProfiniteGrp.limitConePtAux`. Reading both showed
  the latter is the existing exact compatible-family topological group construction
  needed here; it is used, not redefined.
- Direct `rg` of `WeilConjectures` and `lean/Sheaf` for inverse limits, `pro.?p`,
  `IsProP`, finite quotients, and `limitConePtAux` found Tate modules and other
  inverse-limit uses, but no declaration stating the item. The literal item-id
  search in upstream `WeilConjectures` had no match. The expected full declaration
  and helper names were checked against Mathlib, upstream `WeilConjectures`,
  `lean/Sheaf`, and `dag/lean_names_upstream.json`; none already exists.

No statement correction, dependency repair, new node, or statement dispute is needed.
The first `scompile.py` check compiled the module cleanly, with no errors or
non-sorry warnings. The final dry-run result is recorded below after validation.

Validation: `deliver2.py N6 lem-exc-infinite-tame-inverse-limit --no-push` printed
`OK (dry run)` for commit `e2a94ab755`: the module compiles and the preflight passes
except for the independent second-reading section, which the second reader writes.
Nothing was pushed. Only the item's `lean` field differs from the base node; its
recorded signature is verbatim, and the module has exactly one theorem hole.

## Second reading by N6

The node's objects, hypotheses, and conclusions were matched against
`Sheaf/GroupTheory/InfiniteTameInverseLimit.lean` as follows.

- The prime is `(p : ℕ)` with `hp : p.Prime`.
- The index is `{Λ : Type u}` with `[PartialOrder Λ]`, `[Nonempty Λ]`, and
  `[IsDirectedOrder Λ]`; this is exactly a nonempty directed partially ordered set.
- The finite discrete groups `I_λ` and `C_λ` are the objects of
  `I C : Λᵒᵖ ⥤ ProfiniteGrp.{u}`, with pointwise `Finite` and `DiscreteTopology`
  instances. The reversed index category gives precisely the maps for `μ ≥ λ`.
- The transition homomorphisms and their identity/composition laws are the functor
  maps and functor laws of `I` and `C`; `hIsurj` and `hCsurj` state their
  surjectivity. No extra transition data or stronger law is assumed.
- The normal subgroups are `P : ∀ j : Λᵒᵖ, Subgroup (I.obj j)`, with
  `[∀ j, (P j).Normal]`, and `hPorder` states `Nat.card (P j) = p ^ n`.
- The finite quotient maps are the natural transformation `θ : I ⟶ C`; `hθsurj`
  gives componentwise surjectivity, and `hθker` identifies each component kernel
  with `P j`. Naturality is exactly the commuting-square hypothesis
  `θ_λ u_{μλ} = v_{μλ} θ_μ`.
- `hPsurj` is precisely surjectivity on kernels, expressed as
  `(P j).map (I.map f).hom.toMonoidHom = P k`; equality gives both preservation
  and onto-ness of the restricted map.
- `limit I` and `limit C` are Mathlib's compatible-family inverse limits, and the
  helpers `finiteExtensionLimitMap` and `finiteExtensionLimitKernel` are the
  canonical coordinatewise map and coordinatewise subgroup. The first conjunction
  records the coordinate formula; the second records continuity already carried by
  the `ContinuousMonoidHom` type and surjectivity; the third and fourth give the
  exact kernel and closedness.
- The existential normality witness and `ContinuousMulEquiv` use the quotient group
  and quotient topology and include the normalization
  `e (QuotientGroup.mk x) = finiteExtensionLimitMap θ x`, so the induced map is the
  stated one and is an isomorphism of topological groups.
- The final universal quantifier ranges over every universe `v`, every finite group
  `Q` with discrete topology, and every continuous surjective homomorphism from the
  kernel; it concludes exactly that `Nat.card Q` is a power of `p`.

The source is Stacks Project `pione.tex`, Tag 0BUA (`lemma-structure-decomposition`),
especially the finite Galois inverse system, the canonical finite-level maps, and the
paragraph taking inverse limits. The source assumes no additional commutativity,
linearity, countability, or characteristic hypothesis beyond the prime appearing in
the pro-`p` conclusion. The Lean statement introduces none.

Edge cases checked: `Λ` is nonempty (so the empty index is intentionally excluded by
the node), singleton systems are allowed, directedness need not be linear or have a
maximum, trivial groups and trivial subgroups are allowed, `p` is any prime including
2, and the finite quotient may be trivial (`p^0`). The inverse-limit kernel is not
asserted torsion; only its finite continuous quotients are constrained. The quotient
and kernel carry the prescribed subspace/quotient topologies, and all universes are
explicitly bound.

Searches were repeated with `msearch.py` (LeanFinder and Loogle), and with `rg` over
Mathlib, `WeilConjectures`, and `lean/Sheaf` for inverse-limit exactness, pro-`p`
groups, finite continuous quotients, and the helper names. They found only general
profinite limit APIs and unrelated Sylow results; no declaration states this theorem
or either helper. The recorded Mathlib dependencies were read at their declarations:
`ProfiniteGrp.ofClosedSubgroup`, the two cofiltered finite-system results, and
`Topology.IsQuotientMap.of_surjective_continuous`. No mismatch, hollow definition,
statement correction, dependency repair, or new node was found, so no source or Lean
change was needed.

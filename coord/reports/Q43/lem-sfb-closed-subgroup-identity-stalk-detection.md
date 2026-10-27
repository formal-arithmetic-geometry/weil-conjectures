## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ClosedSubgroupIdentityStalk` states
`AlgebraicGeometry.isIso_of_isIso_stalkMap_onePoint`, with its proof `sorry`.
The node is unchanged except for `lean`. No new definitions or dependency repairs are needed.

Clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| Algebraically closed field k | `{k : Type u} [Field k] [IsAlgClosed k]` |
| k-group schemes G and K | `(G K : Over (Spec (.of k))) [GrpObj G] [GrpObj K]` |
| G connected | `[ConnectedSpace G.left]` (includes nonemptiness) |
| G affine, isomorphic to the spectrum of a commutative ring | `[IsAffine G.left]`; its field is `IsIso G.left.toSpecΓ` |
| G of finite type over k | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, the recorded conjunction |
| Inclusion of a closed subgroup scheme j | `(j : K ⟶ G) [IsClosedSubgroupScheme j]` |
| Identity points e_K and e_G | `GrpObj.onePoint K` and `GrpObj.onePoint G`, the images of the unique point of Spec k under their unit sections |
| Induced homomorphism O_(G,e_G) → O_(K,e_K) is an isomorphism | `(hj : IsIso (j.left.stalkMap (GrpObj.onePoint K)))` |
| j is an isomorphism of k-group schemes | `IsIso j` in `Over (Spec (.of k))`; j is already a group homomorphism and its inverse preserves operations |
| Neither reducedness nor smoothness assumed; arbitrary characteristic | No `IsReduced`, `Smooth`, `CharZero`, or positive-characteristic binder |

The source of `j.left.stalkMap (GrpObj.onePoint K)` is the stalk at
`j.left (GrpObj.onePoint K)`. This point equals `GrpObj.onePoint G` because
`IsClosedSubgroupScheme` extends `IsSubgroupScheme`, which extends `IsMonHom`.
`IsMonHom.one_hom j` says the two unit-section composites are equal; evaluating at the
unique point of Spec k gives this identity. No point-identification hypothesis is added.
`Scheme.Hom.stalkMap` is intrinsically a local ring homomorphism and compatibility with
structure morphisms (j is in Over) makes it a k-algebra homomorphism. Bijectivity as a
commutative-ring morphism is equivalent to being an isomorphism of these local k-algebras:
the inverse to a bijective algebra-compatible ring map is again local and algebra-compatible.
Similarly an inverse to j in Over is a group homomorphism by cancellation. Mathlib's
`IsMonHom` instance for the inverse of an isomorphism records this standard fact.
Thus neither endpoint transport nor a separate group-isomorphism structure is missing.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs; `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic, as prescribed by the algebraic-closure leaf.
  No choice of an algebraic closure of another field is required by this item.
- `CategoryTheory.GrpObj` and `CategoryTheory.IsMonHom`,
  Mathlib.CategoryTheory.Monoidal.Grp and Mathlib.CategoryTheory.Monoidal.Mon;
  applied to Over as documented in the group-scheme node's recorded interface.
- `ConnectedSpace`, Mathlib.Topology.Connected.Basic.
- `AlgebraicGeometry.LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType;
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `AlgebraicGeometry.Spec`, Mathlib.AlgebraicGeometry.Scheme;
  `AlgebraicGeometry.IsAffine`, Mathlib.AlgebraicGeometry.AffineScheme.
- `AlgebraicGeometry.IsSubgroupScheme` and `AlgebraicGeometry.IsClosedSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: the latter includes the former and
  the recorded `AlgebraicGeometry.IsClosedImmersion j.left`, from
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.
- `AlgebraicGeometry.GrpObj.onePoint`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Basic; it is the existing identity-point
  construction. The same module supplies the proof's recorded translations and their inverses.
- `AlgebraicGeometry.Scheme.Hom.stalkMap`, Mathlib.AlgebraicGeometry.Scheme.

All recorded statement-dependency interfaces were read at their full declarations and
associated docstrings, including the subgroup definitions' inheritance. The module imports
the statement interfaces publicly and the additional recorded proof-dependency modules
privately. These include finite-type/Noetherian inputs, affine stalk localizations,
localization/quotient compatibility, locally ringed morphisms, Jacobson closed points and
residue-field comparison. The complete six-step DAG proof is in the theorem docstring.

Source: Milne, Algebraic Groups (2017), 1.8, printed p.9, read from the local PDF.
Translations are isomorphisms with inverse translation by the inverse rational point.
The criterion itself is the node's explicitly agent-formulated scheme-theoretic consequence,
not a numbered theorem attributed to Milne. In particular we use rational closed points
and actual local rings; Milne's maximal-spectrum convention is not substituted for the
all-prime scheme topology. The Noetherian generator/denominator argument and sheaf uniqueness
retain nilpotents.

Edge cases checked mathematically before drafting:

- K = G, including nonreduced connected groups: identity map satisfies the criterion.
- The trivial group Spec k: included; no nontriviality hypothesis.
- Empty G or K cannot be group schemes over a field because a unit section exists;
  connectedness explicitly also excludes empty G.
- Finite local nonreduced groups such as alpha_p and mu_p in characteristic p are included.
  The proper inclusion mu_p → mu_(p^2) does not have an isomorphic identity stalk:
  the local quotient map has nonzero kernel. The criterion does not mistake equal
  rational-point sets or residue fields for equal schemes.
- The identity subgroup of a disconnected finite constant group has isomorphic identity
  stalk but is not the whole group; this confirms the role of ConnectedSpace.
- A nontrivial finite subgroup of G_m does not satisfy the stalk-isomorphism hypothesis.
- The finite list of ideal generators in the proof may be empty (product = 1).
- `universe u` is explicit and arbitrary, with k and schemes in the library's standard
  common universe; all binders and instances are explicit, with no auto-bound variables.

Searches for an existing statement (also automatically recorded in searches.jsonl):

- `msearch.py ... leanfinder`: "A closed subgroup scheme of a connected affine group of
  finite type is an isomorphism if the stalk map at the identity is an isomorphism".
  Eight hits: all-stalk isomorphism criteria, closed immersion/global-section injectivity,
  reduced-target surjective closed immersions and the zero-kernel criterion. None is
  this identity-stalk criterion. Their returned signatures were read; the relevant
  OpenImmersion and ClosedImmersion source statements were also opened.
- `msearch.py ... loogle`: `"IsClosedSubgroupScheme", "stalkMap"`: zero hits.
- `msearch.py ... grep`: `subgroup.*stalk|stalk.*subgroup|isIso.*onePoint`, AlgebraicGeometry:
  one spurious Gluing.lean hit concerning a colimit cone point; no relevant theorem.
- `msearch.py ... leansearch`: "A closed subgroup scheme of a connected algebraic group
  is the whole group if its local ring map at the identity is an isomorphism".
  Eight hits: topological ClosedSubgroup declarations and general closed-immersion
  facts; none supplies this statement.
- `rg` in lean/WeilConjectures and lean/Sheaf for subgroup/stalk combinations:
  unrelated sheaf and inertia declarations only. No identity-stalk subgroup criterion.
- `rg` for this node id in lean/WeilConjectures: no hit. `rg` for the chosen declaration
  in WeilConjectures, Sheaf and dag/lean_names_upstream.json: no hit.
- Read GroupScheme/Basic.lean's existing dimension criterion: it requires reducedness
  and dimension equality, and therefore does not match this node.

Validation: scompile.py compiled this statement in both sandbox and actual module mode
without errors or warnings. The final import list is recompiled before delivery.
No node fault or disputed statement was found.

## Second reading by Q43

A separate second pass in this worker session checked the node against the actual Lean
signature and the full definitions used above. No sub-agent was started, as the dispatcher
expressly prohibits it; the maintainer performs the independent review of this delivery.

Rechecked every table row: finite type uses both recorded predicates, only G carries
connectedness and affineness assumptions, K is a group scheme and j a closed subgroup,
and the hypothesis is on the actual induced local-ring map at the identity of K.
Its domain's image point is the identity of G by the homomorphism's unit law, not an
arbitrary stalk. `IsIso j` asserts an inverse over the base; its group compatibility
follows from j's existing `IsMonHom` structure. No smoothness, reducedness or
characteristic restriction entered the signature. The universe and every variable
are bound explicitly. The six proof steps in the docstring were compared with the node,
including nilpotents, the empty ideal-generator list and the rational closed-point
argument. No semantic mismatch was found and no node statement was changed.

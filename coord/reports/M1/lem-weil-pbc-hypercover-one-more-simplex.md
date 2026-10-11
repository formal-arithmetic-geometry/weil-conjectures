## Worker report

The module `Sheaf.AlgebraicGeometry.HypercoverOneMoreSimplex` states
`AlgebraicGeometry.Scheme.isSemiRepresentableCovering_simplicialHomRestriction_one_more_simplex`.
Its only proof is `sorry`; it introduces no definitions or new nodes and changes only
`lean` in the item node. All universes and variables are explicitly bound.

Hypothesis and clause correspondence:

- The scheme is `{X : Scheme.{u}}`; the semi-representable simplicial object is
  `K : SimplicialObject (FormalCoproduct.{w} X.Etale)` and the hypercover condition is
  `hK : IsSemiRepresentableHypercover K`, including degree zero.
- The simplicial set is `V : SSet.{t}` and its simplicial subset is `U : V.Subcomplex`.
  Its underlying simplicial set is the recorded Mathlib `U.toSSet`.
- Finiteness and nonemptiness of every degree of both sets are exactly `hV` and `hU`.
  The classes `[V.Finite] [U.toSSet.Finite]` express finiteness of the sets of
  nondegenerate simplices. These finiteness clauses are partly redundant, as in the node;
  none is replaced by a stronger finiteness notion.
- The integer `n ≥ 0` is `n : ℕ`. The new simplex is `x : V.obj (op ⦋n⦌)` and
  `hx` says `x ∉ U.obj (op ⦋n⦌)`.
- Clause (1) is `hlower`: the subset in each degree below `n` is `Set.univ` in `V_i`.
  This states equality with the whole ambient degree without identifying a subtype
  with its parent type.
- Clause (2) is `hdegree`: `Set.univ = U.obj (op ⦋n⦌) ∪ {x}`.
- Clause (3) is `hhigher`: for every `j > n`, any ambient simplex outside `U_j`
  belongs to the recorded `V.degenerate j`.
- The fixed Hom objects are arbitrary `HV HU : FormalCoproduct.{w} X.Etale` with
  universal families `v` and `u`. The predicates `hv` and `hu` express precisely their
  representing universal properties. These binders expose the choices already part
  of the Hom-object definition; they add no condition on `K`, `V`, or `U`.
- The conclusion is `IsSemiRepresentableCovering (simplicialHomRestriction U v hu)`.
  This is exactly the dependency's restriction morphism between the fixed Hom pairs,
  without an independently defined map or a weaker pointwise lifting assertion.

Dependencies read and used:

- `Sheaf.AlgebraicGeometry.SemiRepresentableObject`:
  `AlgebraicGeometry.Scheme.IsSemiRepresentableHypercover` and
  `AlgebraicGeometry.Scheme.IsSemiRepresentableCovering` (transitively imported).
- Mathlib `Basic`, `Subcomplex`, `Degenerate`, `Finite` in
  `Mathlib.AlgebraicTopology.SimplicialSet`: `SSet`, `SSet.Subcomplex`,
  `SSet.Subcomplex.toSSet`, `SSet.degenerate`, `SSet.Finite`.
- `Sheaf.AlgebraicGeometry.SimplicialHomObject`:
  `AlgebraicGeometry.Scheme.SimplicialHomFamily`, `simplicialHomFamilyFunctor`,
  `simplicialHomRestriction`. Read their full signatures and docstrings.
- Mathlib `CategoryTheory.RepresentedBy`: `Functor.IsRepresentedBy`, whose
  `map_bijective` is the representing universal property used by the restriction.

Edge cases checked before writing: `n = 0` makes `hlower` vacuous, while `hdegree`
adds a vertex and `hhigher` allows only its degeneracies outside `U`; the degree-zero
matching map to the terminal family supplies the covering. For positive degrees the
new simplex has its faces in `U`, enabling the boundary pushout argument. Empty `U`
or `V` is excluded exactly by the node's nonempty-degree assumptions. The empty
scheme and empty formal families are not excluded. The index, scheme and simplicial
universes `w`, `u`, `t` are independent; no smallness condition was added.

Searches for an existing statement:

- `msearch.py leansearch`, query "restriction of Hom objects along addition of one
  simplex to a finite simplicial set is a covering for a hypercover": unavailable,
  Internal Server Error; no verdict inferred.
- `msearch.py leanfinder`, query "Adding one nondegenerate simplex restriction of
  simplicial Hom objects of a hypercover is a covering": eight zero/one-hypercover
  hits, including `ZeroHypercover.add`; none states the full simplicial result.
- `msearch.py loogle`, query `SSet.Subcomplex, SSet.degenerate`: two hits,
  `Subcomplex.mem_degenerate_iff` and `Subcomplex.degenerate_eq_top_iff`; these
  concern degeneracy in subcomplexes, not coverings.
- `msearch.py grep`, query
  `one_more_simplex|oneMoreSimplex|simplicialHomRestriction|IsSemiRepresentableHypercover`:
  no Mathlib hits.
- `rg -n` with that same pattern in the upstream `WeilConjectures` and project
  `lean/Sheaf`: only the existing hypercover predicate and restriction definition;
  no matching theorem. `grep -rn` for the item id in upstream: no hits.

Source checked: [Stacks Tag 01GM](https://stacks.math.columbia.edu/tag/01GM),
statement and proof. The repository lacks the indicated local `hypercovering.tex`,
so the authoritative online tag was read. The source only explicitly requires
finitely many nondegenerate simplices in `U`; the node's corresponding condition on
`V` follows from adding a single simplex and is retained. The module docstring
contains all seven node proof steps, including invariance under isomorphisms and
the separate degree-zero argument. No statement correction or disputed statement.

Validation: local compilation reported the recently landed `SimplicialHomObject`
olean missing; the prescribed fallback `scompile.py` compiled the module cleanly in
1.8 seconds, with no warnings or errors. The delivery dry run is the final check;
the independent second reader writes the second-reading section and delivers.

## Second reading by M1

Independently read the item JSON and Lean module, all three statement dependency
nodes, the full `SemiRepresentableObject` and `SimplicialHomObject` modules, and
Mathlib's definitions of subcomplexes, degeneracy, finite simplicial sets and
`Functor.IsRepresentedBy`. Also opened `SimplicialHomObjectExists`, `glue_simplex`
and `add_simplices` to check the available neighboring statements.

Source: [Stacks 01GM](https://stacks.math.columbia.edu/tag/01GM), statement and
proof, and the actual `lemma-one-more-simplex` text in the upstream
`hypercovering.tex` (fetched from stacks/stacks-project since the literature
checkout is absent here). The source works on a site with fibre products; the
node specializes it to the small étale site of an arbitrary scheme. This site
has the required fibre products, with no Noetherian, field, separatedness or
characteristic assumption. Its extra written finiteness condition on `V` follows
from the single-simplex attachment, as already noted by stage 1. No correction
to the node is required or made.

Object, hypothesis and conclusion checklist (all verdicts: exact):

1. Arbitrary scheme `X`: `{X : Scheme.{u}}`. The category `SR(X)` is precisely the
   dependency's `FormalCoproduct.{w} X.Etale`, not schemes over `X` or sheaves.
2. Simplicial hypercover `K`: `K : SimplicialObject (...)` and
   `hK : IsSemiRepresentableHypercover K`. The opened definition requires the
   covering condition for every matching map, including degree zero; its covering
   predicate requires a covering family over each target index in the small
   étale topology.
3. Simplicial sets and inclusion: `V : SSet.{t}`, `U : V.Subcomplex` and
   `U.toSSet`. Mathlib defines this subcomplex as a subfunctor, so its operators
   really are restrictions of those of `V`.
4. Every degree finite and nonempty for both sets: the two conjunctions in `hV`
   and `hU`, quantified over all `i : ℕ`. Finiteness of all nondegenerate simplices:
   `[V.Finite] [U.toSSet.Finite]`, whose opened definition is finiteness of `S.N`,
   the type of nondegenerate simplices in all dimensions. These conditions are
   retained exactly as the node states them, including its redundant finiteness.
5. Nonnegative attachment dimension and new simplex: `n : ℕ`,
   `x : V.obj (op ⦋n⦌)` and `hx : x ∉ U.obj (op ⦋n⦌)`.
6. Clause (1), equality below `n`: `hlower` says the subset `U_i` equals the full
   ambient set `Set.univ` for every `i < n`. This is exactly `U_i = V_i`.
7. Clause (2), one extra simplex in degree `n`: `hdegree` says the full ambient
   set equals `U_n ∪ {x}`; together with `hx` this adds exactly one element.
8. Clause (3), only degenerate new simplices above `n`: `hhigher` quantifies all
   `j`, all `z : V_j`, then `n < j` and `z ∉ U_j`, concluding
   `z ∈ V.degenerate j`. The opened degeneracy definition is precisely the image
   under an operator from a lower dimension, as in the dependency node.
9. Fixed Hom objects: `{HV HU}` with families `v` and `u`, certified by `hv` and
   `hu`. In the opened representing predicate these certificates assert that
   composition with the given family bijects maps from every object with all
   compatible simplex-indexed families. These are the dependency node's chosen
   representing pairs, not extra constraints on the mathematical input. The
   existence theorem supplies such pairs under the node's finiteness hypotheses.
10. Conclusion: `IsSemiRepresentableCovering (simplicialHomRestriction U v hu)`.
    The opened restriction definition applies the inverse of precisely that
    representing bijection to the restricted universal family `v.restrict U`.
    Its domain is `HV`, its codomain is `HU`; hence this is exactly the node's
    restriction morphism, with the dependency's covering predicate.

Edge cases: `n = 0` is included, `hlower` then imposes nothing, and the hypercover
condition still supplies the degree-zero covering. The proof docstring handles
this by the product over the terminal family. For `n > 0`, all faces of `x` lie
in `U`, giving the boundary attachment. Empty simplicial sets are excluded by
the node itself, exactly by the nonempty-degree hypotheses. Empty schemes and
empty formal index families are not excluded by any binder; covering empty
target families is treated by the dependency's universal quantifier. There is
no additive zero object involved. Scheme universe `u`, formal index universe
`w` and simplex universe `t` are independent and explicitly declared; the
family functor takes values in `Type (max u w t)` and its universal property
tests every formal family in the chosen category. No small test universe,
characteristic constraint or additional instance is imposed.

Independent searches, with different queries from the worker:

- LeanFinder: "A hypercover induces covering morphisms between representing
  objects for simplicial families when a subcomplex gains exactly one simplex".
  Eight hits concerned zero/one hypercovers (`ZeroHypercover.add`,
  `Cover.oneHypercover`, etc.); none is the full simplicial covering statement.
- Loogle: `SSet.Subcomplex, SSet.Finite`. Three hits, `instFiniteToSSet`,
  `finite_iSup_iff` and `finite_subcomplex_top_iff`; these describe finiteness,
  not coverings of Hom objects.
- LeanSearch: "Adding a simplex to a simplicial subset induces a covering on
  Hom into a hypercover". Service returned Internal Server Error; no negative
  mathematical verdict inferred.
- `rg` over upstream `WeilConjectures`, the project's `lean/Sheaf`, and Mathlib's
  simplicial-set and sites sources with `one.?simplex`, `one.?more.?simplex`,
  `simplicialHom`, `IsSemiRepresentableHypercover` and
  `nondegenerate.*covering`. Found the existing Hom and hypercover dependencies,
  `glue_simplex` (a pushout statement) and `add_simplices` (a filtration statement),
  neither of which states this item's covering assertion. A further check of
  upstream names and `coord/upstream-overlaps.md` found no matching declaration.

No new definition nodes, dependency modules, statement changes, private copies,
hollow definitions or proofs were introduced. The module has only its named
theorem with `sorry`. Both source docstrings and the seven-step proof docstring
are present, including the isomorphism invariance and separate degree-zero
argument. Imports are used, lines respect the 100-character limit, and the
node's `lean.statement` is verbatim the theorem signature. No unbound variable
or universe was found.

Mismatches and repairs: none. Left the correct Lean and node unchanged; appended
this independent reading. Local `lcompile.py` compiled the item successfully in
1.8 seconds with no errors or warnings. Server compilation and preflight are
checked again by the prescribed delivery script.

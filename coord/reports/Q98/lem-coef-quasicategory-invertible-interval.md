## Worker report

`lean/Sheaf/CategoryTheory/QuasicategoryInvertibleInterval.lean` states the complete
node as `SSet.Enhanced.quasicategory_invertible_interval`, with one `sorry` and
no new definitions. The node copy changes only `lean`. This reconstructs the
three absent delivery artifacts identified by the previous worker: the module,
node record and report. No mathematical statement correction is needed.

Clause-by-clause correspondence:

- The fixed input universe is `universe u`. Each assertion quantifies its own
  arbitrary `D : SSet.{u}` or `C : SSet.{u}` with `[Quasicategory D]` or
  `[Quasicategory C]`; there is no `Nonempty` hypothesis on either input.
- The two-object groupoid nerve J is Mathlib's `SSet.coherentIso.{u}`, defined
  as `nerve WalkingIso`, where `WalkingIso` is `Codiscrete (ULift Bool)`.
  Its vertices `coherentIso.x₀` and `x₁` select false and true, respectively.
  The universe-lifted Bool has exactly the two required objects and exactly
  one arrow between any ordered pair.
- The category hD is `SSet.hoFunctor.obj D`. `HomotopyCat.lean` constructs it
  from the free category on the reflexive edge quiver, quotienting by the
  triangle relations; degenerate edges are already identities. In particular,
  this uses the node's path presentation rather than silently replacing it by
  the distinct `HomotopyCategory₂` construction. The inverse equivalence
  `(SSet.hoFunctor.obj.equiv D).symm` assigns the corresponding object to
  each vertex, without a new definition or unproved choice.
- The first conjunct quantifies every `d₀ d₁ : D _⦋0⦌`. Its left side is
  `Nonempty ((SSet.hoFunctor.obj.equiv D).symm d₀ ≅
  (SSet.hoFunctor.obj.equiv D).symm d₁)`, precisely existence of an
  isomorphism of the specified objects. Its right side is
  `∃ g : SSet.coherentIso.{u} ⟶ D, g.app _ coherentIso.x₀ = d₀ ∧
  g.app _ coherentIso.x₁ = d₁`, so both endpoints are fixed by equalities.
  The connective is `↔`, preserving both implications.
- The second conjunct independently quantifies every quasicategory C. Its
  two clauses apply `modelCategoryQuillen.I.rlp` to the recorded dependency
  declaration `evaluation SSet.coherentIso C coherentIso.x₀` and the analogous
  x₁ evaluation. These are the two endpoint restrictions on Fun(J,C).
  The Mathlib match of `def-weil-pbc-trivial-kan-fibration` explicitly uses
  `I.rlp`: `I` is the family of all boundary inclusions, including n = 0.
  Boundary zero is empty, so its lifting condition is vertex surjectivity;
  every positive-dimensional boundary supplies exactly the other fillers.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, `SSet.Enhanced.evaluation`:
  its full definition restricts the internal hom at the selected vertex and
  identifies the internal hom from the unit with C. Its imported Mathlib
  `SSet.Quasicategory` and internal hom supply the dependency's primitives.
- `Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations`,
  `SSet.modelCategoryQuillen.I`, and
  `Mathlib.CategoryTheory.MorphismProperty.LiftingProperty`,
  `CategoryTheory.MorphismProperty.rlp`: the recorded Mathlib match for the
  trivial Kan fibration node. No dependency record repair is needed.
- `Mathlib.AlgebraicTopology.SimplicialSet.CoherentIso`, `SSet.coherentIso`,
  `SSet.coherentIso.x₀`, `SSet.coherentIso.x₁`;
  `Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat`, `SSet.hoFunctor`,
  `SSet.hoFunctor.obj.equiv`: exact existing constructions for the notions
  introduced by this node itself; no duplicate notions are defined.
- The already recorded proof dependency
  `Sheaf.CategoryTheory.IsofibrationExponentiation` is imported without
  `public`. Its theorem and helper signatures/docstrings were read. The
  other proof-only nodes `lem-coef-homotopy-category-triangle-calculus` and
  `lem-coef-infinity-core-kan-fibration` have no recorded declarations in the
  supplied DAG, so there is no module to import for them. Neither is needed
  to type this statement. All seven DAG proof steps are in its docstring.

Edge cases: empty D makes the first conjunct's vertex quantification vacuous
without affecting the independently quantified second conjunct. For empty C,
Fun(J,C) is empty in every degree because J times a simplex has vertices;
empty-to-empty evaluation satisfies all boundary lifting tests. Equal vertices
allow the constant J-map, so degenerate edges are included. For ordinary nerves,
the first assertion is precisely existence of an ordinary isomorphism. For n = 0
in the second assertion, the boundary lifting test enforces vertex surjectivity;
it is not omitted. The parameter u is arbitrary, including its lowest value.

Searches (actual wrapper responses are preserved in `searches.jsonl`):

- `msearch.py leanfinder`: “For a quasicategory C endpoint evaluation from Fun
  of the nerve of the walking isomorphism into C is a trivial Kan fibration
  and isomorphic homotopy category objects extend over coherentIso”. Eight
  hits, including nerve and homotopy-category adjunction declarations, none
  stating extension into an arbitrary quasicategory or endpoint lifting.
- `msearch.py loogle`: `"coherentIso"`. Twelve hits define the interval,
  endpoints, inverse edges/triangles and `invStructOfEqMapHom`. The last
  extracts inverse data from an already given J-map; it supplies neither
  the converse extension nor the endpoint-fibration assertion.
- `msearch.py grep`: `coherentIso|endpoint.*(trivial|fibration)|isIso.*homMk`
  in Mathlib `AlgebraicTopology`. Seven hits, principally `CoherentIso.lean`;
  no exact statement. Its definitions and full docstrings were read.
- `msearch.py leansearch`: “An endpoint evaluation from coherent isomorphisms
  in a quasicategory is a trivial Kan fibration”. Eight general model-category
  trivial-fibration facts, none about this evaluation.
- `rg` for the item id, `quasicategory_invertible_interval`, `coherentIso`,
  and `hoFunctor` in the upstream `WeilConjectures/`, project `lean/Sheaf`,
  and `dag/lean_names_upstream.json`: upstream has no matching lemma/name;
  project Joyal modules cite this missing lemma in proof plans and use the
  same `hoFunctor`. No existing declaration proves the full node.

The cited [Cisinski source](https://cisinski.app.uni-regensburg.de/CatLR.pdf)
was opened online. Theorem 1.6.6 gives the homotopy-category description;
Corollary 3.5.13 gives the anodyne restriction result used by the node's
endpoint argument. The word nerve and horn filtration are those specified
in the DAG's agent-written proof; the Lean docstring retains that proof.
No statement dispute, new node, dependency repair, or omitted hypothesis.

Validation: the module compiled cleanly through the required `scompile.py`,
including its library module-path compile. The initial dry run detected a
signature-record mismatch; the record is now extracted verbatim from the
file, excluding `:= by`. An independent second reading is left to the next
worker, as required.

## Second reading by Q98

I independently opened the sandbox node and Lean module, both statement-dependency
nodes and their actual declarations, and the recorded proof-dependency module.
Verdict: the signature says exactly what the node says. No mathematical mismatch
was found; the Lean module and node record are retained unchanged. This reading
adds only this review section. There are no new nodes or dependency modules, no
statement correction, and no repair note for this item.

Object/hypothesis/conclusion inventory and correspondence:

1. An arbitrary input universe: `universe u`, with `D : SSet.{u}` and
   `C : SSet.{u}` in two independent universal quantifiers. Verdict: exact;
   no extra size equality or nonemptiness assumption.
2. The ordinary groupoid with two objects and a unique arrow for each ordered
   pair, and its nerve J: `SSet.coherentIso.{u}`. I read `WalkingIso` as
   `Codiscrete (ULift Bool)`, its `zero`/`one`, and the actual nerve abbreviation
   in Mathlib `CoherentIso.lean`. Verdict: the specified groupoid, in every u.
3. Endpoint inclusions selecting 0 and 1: `coherentIso.x₀` and
   `coherentIso.x₁` are `ComposableArrows.mk₀` of those two objects.
   `SSet.Enhanced.evaluation` constructs restriction along the vertex's
   `unitHomEquiv` map and the canonical internal-hom unit isomorphism.
   Verdict: the named dependency's actual canonical endpoint restrictions.
4. The category hD generated by vertices and edges with identity and triangle
   relations: `SSet.hoFunctor.obj D`. I read the reflexive quiver, `HoRel₂`
   composition relation, `HomotopyCategory` quotient, `hoFunctor`, and
   `hoFunctor.obj.equiv` in Mathlib `HomotopyCat.lean`. The last equivalence's
   inverse identifies each vertex with its corresponding object. Verdict:
   exactly the node's path presentation, with no new definition or assumed
   equivalence to a different homotopy-category implementation.
5. Every quasicategory D and every ordered pair of vertices:
   `∀ (D : SSet.{u}) [Quasicategory D] (d₀ d₁ : D _⦋0⦌)`.
   Mathlib `Quasicategory` requires precisely inner-horn fillers; I read its
   class signature. Verdict: exactly the sole structural hypothesis.
6. Isomorphism of these specified objects iff an endpoint-preserving map J to D:
   `Nonempty ((SSet.hoFunctor.obj.equiv D).symm d₀ ≅
   (SSet.hoFunctor.obj.equiv D).symm d₁) ↔ ∃ g : coherentIso ⟶ D, ...`.
   Both endpoint equations are exact equalities `g.app _ x₀ = d₀` and
   `g.app _ x₁ = d₁`. Verdict: both directions and both endpoint conditions,
   with the existential map after the prescribed vertices; no chosen inverse
   or chosen edge is additionally demanded.
7. Every quasicategory C, independently of D, and each of the two endpoints:
   the second outer conjunct is `∀ (C : SSet.{u}) [Quasicategory C], ... ∧ ...`.
   Its two properties are `modelCategoryQuillen.I.rlp` applied to the x₀ and
   x₁ evaluations. I read `I := .ofHoms (fun n ↦ ∂Δ[n].ι)`, the definition
   of `MorphismProperty.rlp`, and `boundary`/`boundary_zero`.
   Verdict: all boundary lifting conditions, including vertex surjectivity,
   exactly as in the dependency's Mathlib match and Stacks Definition 08NL
   (`simplicial.tex`, lines 5520--5545).

Source check: I opened the cited
[Cisinski PDF](https://cisinski.app.uni-regensburg.de/CatLR.pdf), Theorem 1.6.6
and Corollary 1.6.8 (printed pp. 24--25), Corollary 3.5.3 (p. 107), the
construction in 3.5.7 (p. 108), Theorem 3.5.11 and Corollary 3.5.13
(pp. 110--112). Their relevant assumptions are quasicategories and, for the
relative assertions, an isofibration. The terminal map supplies that condition
here. The groupoid nerve forces every edge image invertible, so its edge-inverting
functor object is the full internal hom. The explicit alternating-word horn
filtration in the node applies to this nerve. I checked its two newly attached
nondegenerate simplices at each stage, including stages 1 and 2. No hidden
nonempty-input assumption is required. This item has no Stacks source of its own;
the Stacks definition was checked for its trivial-fibration dependency.

Edge cases checked: empty D leaves no pair of vertices; empty C makes both the
internal hom from this nonempty J and its codomain empty. Every boundary lifting
problem into the empty codomain is absent, including dimension zero. If d₀ = d₁,
a constant map realizes the identity isomorphism. Dimension zero is retained by
`I`, since the zero boundary is empty; positive dimensions supply the remaining
fillers. An ordinary category nerve specializes to ordinary isomorphisms. The
lowest universe u = 0 is allowed by the lifted finite groupoid. There is no
indexed family, scheme, zero-object, ring or characteristic parameter to restrict.

Independent searches, using different wording from the worker:

- `msearch.py leanfinder`: "A simplicial map from the walking isomorphism nerve
  exists between vertices precisely when they are isomorphic in the homotopy
  category; endpoint restriction has right lifting against boundaries".
  Eight hits, including `HomotopyCategory.homToNerveMk` and
  `Nerve.quasicategory`; these describe nerves/adjunctions, not this theorem.
- `msearch.py loogle`: `"coherentIso", "rlp"`: zero hits.
- `msearch.py leansearch`: "Endpoint restriction on functors from the nerve of a
  contractible groupoid to a quasicategory lifts every simplicial boundary".
  Eight hits for nerve constructions and homotopy-category universal properties;
  none gives either endpoint evaluation lifting or the full conjunction.
- `msearch.py grep` in AlgebraicTopology:
  `isomorph.*vert|vert.*isomorph|coherentIso.*(fibr|lift)|evaluation.*boundary`:
  zero hits. Direct `rg` additionally searched `coherentIso`, `walking.?iso`,
  `invertible.?interval`, endpoint lifting/fibration language and the full
  declaration name throughout Mathlib AlgebraicTopology, upstream
  `WeilConjectures/`, project `lean/Sheaf`, and `dag/lean_names_upstream.json`.
  The Mathlib interval constructions were opened; the project references are
  downstream proof plans, not an existing statement of this result.

H4--H9: both statement dependencies have usable interfaces and are used directly.
The only recorded proof-only module is `IsofibrationExponentiation`; I read its
`IsIsofibration`, `exponentialCorner` and theorem signatures and confirmed its
non-public import. The triangle-calculus and core-fibration nodes have no recorded
Lean modules, so no imports for them can be supplied yet. All seven proof steps
are present in the theorem docstring, with dependency names and the empty and
universe cases. There is one named theorem, its entire proof is `sorry`, and
there are no definitions or local notation/instance declarations. Source and
blueprint tags, namespace, public imports and line widths meet the conventions.
All variables and universes are explicitly bound with autoImplicit disabled.
The node differs from the repository only in `lean`, and its `lean.statement`
is verbatim equal to the signature before `:= by`.

Second-reader validation: the prescribed `scompile.py` compiled the delivered
file both as sandbox and by its library module path, exit 0, without errors or
warnings. No Lean or node edit was necessary.

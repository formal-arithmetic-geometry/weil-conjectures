## Worker report

The module `Sheaf.AlgebraicGeometry.PerfectThickClosure` states
`AlgebraicGeometry.Scheme.perfect_thick_closure`, with a single `sorry` proof and
no definitions. The statement is a conjunction of four independently quantified
closure assertions; it does not put any one closure assertion under the hypotheses
of another.

Hypotheses and clauses matched to Lean:

- The scheme is `(X : Scheme.{u})`, without quasi-compactness, separatedness,
  Noetherianity, or other geometric restrictions.
- `D(O_X)` is `schemeDerivedCategory X`. The global
  `HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))`
  binder and the matching per-open binders are precisely the shared carriers
  needed by the recorded `Scheme.IsPerfect` definition. They specify the
  localization structures, not additional geometric hypotheses.
- Clause (1): `T : CategoryTheory.Pretriangulated.Triangle (schemeDerivedCategory X)`
  contains the three objects, three arrows, and shift-by-one target of the final
  arrow. `T ∈ distTriang (schemeDerivedCategory X)` is distinguishedness.
  The three implications with pairs `(obj₁,obj₂)`, `(obj₂,obj₃)`, and
  `(obj₁,obj₃)` conclude perfectness of `obj₃`, `obj₁`, and `obj₂`, respectively.
  This explicitly covers every meaning of two out of three.
- Clause (2): for independently quantified `K L`, `IsPerfect X (K ⊞ L)` implies
  `IsPerfect X K ∧ IsPerfect X L`. The binary biproduct is the direct sum in
  this additive derived category.
- Clause (3), shifts: for all objects `K` and all `n : ℤ`, perfectness of `K`
  implies `IsPerfect X (K⟦n⟧)`.
- Clause (3), finite sums: `I : Type v` with `[Finite I]` is an arbitrary finite
  indexing set, and `K : I → schemeDerivedCategory X` is its family.
  `(∀ i : I, IsPerfect X (K i))` implies `IsPerfect X (⨁ K)`, using Mathlib's
  finite categorical biproduct. Its existence is inferred, with no extra
  `HasBiproduct` assumption. The independent universe `v` excludes no finite set.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom` (full signatures and docstrings inspected).
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`,
  the shared `DerivedCategory (SheafOfModules (moduleRings X.toRingedSpace))`.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `AlgebraicGeometry.Scheme.IsPerfect`;
  its complete signature and its local strictly-perfect representative definition
  were read together with `Scheme.IsStrictlyPerfect` and `perfectSubcategory`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`: `distTriang` and the
  `CategoryTheory.Pretriangulated.Triangle` carrier.

The theorem docstring reproduces all three proof steps of the node: 08CR via
`lem-pc-perfect-two-out-of-three`, 08CS via `lem-pc-perfect-summand`, and the
common refinement/reindexing/termwise finite-free-summand argument from 08CM.
These are proof dependencies, not additional statement hypotheses.

Source checked online because `literature/stacks-project/cohomology.tex` is
absent in this clone: [08CR](https://stacks.math.columbia.edu/tag/08CR),
[08CS](https://stacks.math.columbia.edu/tag/08CS), and
[08CM](https://stacks.math.columbia.edu/tag/08CM). The node's scheme specialization
matches the ringed-space statements of 08CR and 08CS. The source assumes no
further geometric condition.

Edge cases checked: the empty scheme is allowed (the pointwise definition of
perfectness is vacuous there); zero objects are allowed; `I` may be empty,
in which case `⨁ K` is the zero object and the premise is vacuous; singleton
and binary families are covered; shifts include zero, positive, and negative
integers. No global cohomological boundedness is asserted, so non-quasi-compact
schemes remain included. No characteristic restriction occurs.

Searches for an existing statement:

- `msearch.py leanfinder`: "Perfect complexes of sheaves on schemes form a thick
  subcategory: two out of three, direct summands, shifts, finite sums" returned
  eight generic derived-category boundedness/T-structure declarations
  (`DerivedCategory.IsGE`, `IsLE`, `TStructure.t`, and localizations of bounded
  complexes); none states this scheme-perfect closure assertion.
- `msearch.py loogle`: "IsPerfect, distTriang" returned zero hits with an
  unexpected-end-of-input diagnostic; no matching declaration obtained.
- `msearch.py leansearch`: "perfect complexes on schemes closed under shifts and
  finite direct sums" was unavailable (Internal Server Error).
- `msearch.py grep`: `IsPerfect.*distTriang|perfect.*thick|IsPerfect.*biproduct`
  returned zero hits in Mathlib.
- `rg` in `WeilConjectures` for `IsPerfect` found coefficient/module-derived
  perfectness and perfect pairings, not `Scheme.IsPerfect` thick closure.
- `rg` in `WeilConjectures` and `dag/lean_names_upstream.json` for the item id
  and `perfect_thick_closure` returned no matches.
- `rg`/text search in `lean/Sheaf` found only the dependency's perfect-complex
  definitions, plus the unrelated perfect-closed-immersion notion. No existing
  statement supplies the four clauses. DAG searches found the two split proof
  input nodes 08CR and 08CS, neither with a recorded Lean declaration and neither
  a duplicate of the full conjunction.

No new nodes, dependency modules, statement correction, or disputed statement.
Server compilation of the final file was clean (exit 0), with no non-sorry warnings.

## Second reading by F1

I independently read the node statement, its Stacks source places (08CR, 08CS, and
Definition 08CM), the dependency node signatures, and
`Sheaf/AlgebraicGeometry/PerfectThickClosure.lean`.

The objects and hypotheses match item by item. `X : Scheme.{u}` is the scheme of the
node. The two instance binders are exactly the `HasDerivedCategory` structures required
by `schemeDerivedCategory` and `Scheme.IsPerfect` (global sheaves and every open's
module category); they impose no quasi-compactness, separatedness, Noetherianity, or
characteristic assumption. `T : Triangle (schemeDerivedCategory X)` supplies the three
objects and maps, and `T ∈ distTriang (schemeDerivedCategory X)` is distinguishedness.
The three implications render the three possible choices of two perfect terms and
conclude the remaining term. Independently quantified `K L` and `IsPerfect X (K ⊞ L)`
render the binary direct-summand clause and conclude both summands. Independently
quantified `K` and `n : ℤ` render closure under every integer shift. Finally,
`I : Type v`, `[Finite I]`, and `K : I → schemeDerivedCategory X` render an arbitrary
finite family, with pointwise perfectness implying perfectness of `⨁ K`.
Quantifier order and conjunction structure agree with the node, and no clause is
weakened or strengthened.

Edge cases were checked: the empty scheme and zero object remain allowed; an empty
finite index type makes the premise vacuous and the biproduct the zero object; singleton
and binary families are included; all integer shifts, including zero and negative
shifts, are included; no characteristic or cohomological boundedness restriction is
introduced. The independent finite-index universe does not exclude any finite family
accepted by the statement.

I searched Mathlib and the project with `msearch.py` (LeanFinder, Loogle, and
LeanSearch queries for scheme perfect complexes, `IsPerfect` with distinguished
triangles, summands, shifts, and finite biproducts), `rg` over Mathlib,
`WeilConjectures/`, `lean/Sheaf/`, and `dag/lean_names_upstream.json`. Results were
only generic derived-category/T-structure infrastructure and unrelated perfect
notions; no declaration states this scheme-level conjunction. The two Stacks input
nodes 08CR and 08CS are proof dependencies, not duplicate statements.

No mismatch was found. The existing worker module and node `lean` record already use
`AlgebraicGeometry.Scheme.perfect_thick_closure` with a verbatim signature and a
single `sorry` proof. I made no source or statement changes. Compilation with
`scompile.py` succeeded without errors or warnings other than the permitted `sorry`.

## Worker report

The module `Sheaf.AlgebraicGeometry.AffineGroupoidIntegralInvariants` states
`AlgebraicGeometry.isIntegral_affineGroupoid_invariants`, with proof `sorry`.
It renders Stacks Project, `groupoids.tex`, Tag 03BJ, exactly as the item's
statement. No statement correction or disputed mathematical assertion is needed.
The new definition module `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws` supplies
the missing scheme-groupoid predicate with real, explicit laws and no `sorry`.

Hypotheses and conclusion, read against the original node:

| Node text | Lean rendering |
| --- | --- |
| Affine schemes `U = Spec A`, `R = Spec B` | `A B : CommRingCat.{u}` and the literal schemes `Spec A`, `Spec B` |
| Source and target morphisms `s,t : R → U` | `s t : Spec B ⟶ Spec A` |
| Identity `e : U → R` | `e : Spec A ⟶ Spec B` |
| Inverse `i : R → R` | `i : Spec B ⟶ Spec B` |
| Composition `c : R ×_{s,U,t} R → R` | `c : pullback s t ⟶ Spec B` |
| These maps give a groupoid on points, functorially in every test scheme | `hG : Scheme.IsGroupoid s t e i c`; all laws are expanded below; functoriality is precomposition of scheme morphisms |
| `σ = s♯`, `τ = t♯` | `(Spec.preimage s).hom`, `(Spec.preimage t).hom`; `Spec.homEquiv` identifies these with the induced coordinate-ring maps |
| `C = {a : σ(a) = τ(a)}` | Mathlib's `RingHom.eqLocus` of those two ring maps; its carrier is definitionally precisely that set |
| `s,t` finite locally free | `[s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree]`, using the recorded upstream class |
| Every `a ∈ A` has a monic polynomial in `C[T]` | `∀ a : A, ∃ P : Polynomial ((Spec.preimage s).hom.eqLocus (Spec.preimage t).hom), P.Monic ∧ ...` |
| The polynomial annihilates `a` | `P.eval₂ ((Spec.preimage s).hom.eqLocus (Spec.preimage t).hom).subtype a = 0`, evaluation along the actual subring inclusion |

No common base scheme is added: as in the node, the groupoid is in schemes,
equivalently over the terminal scheme. All variables and the sole universe `u`
are explicitly bound. Both rings lie in a common arbitrary universe; no
finite-dimensional, domain, reducedness, nonzero, constant-rank, global-freeness,
field, characteristic, or Noetherian hypothesis is imposed.

Dependency interfaces opened and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-weil-affine-spectrum`: the same module's `AlgebraicGeometry.Spec` and
  `Spec.map`; `Mathlib.AlgebraicGeometry.GammaSpecAdjunction` supplies the
  recorded `Spec.homEquiv` and its forward map `Spec.preimage`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`,
  `pullback.snd` in
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`; existence for
  schemes comes from `Mathlib.AlgebraicGeometry.Pullbacks`.
- `def-pc-finite-locally-free`:
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`, declaration
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`. Its full class extends
  `IsFinite`, `Flat`, and `LocallyOfFinitePresentation`, exactly as the node.
  Also checked the current published source with `scompile.py --source`.
- `def-weil-polynomial-ring`: `Mathlib.Algebra.Polynomial.Basic`, declaration
  `Polynomial`, reached through the polynomial evaluation and monicity imports.
- New `def-a1-scheme-groupoid-laws`:
  `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws`, declaration
  `AlgebraicGeometry.Scheme.IsGroupoid`.

Mathlib's `RingHom.eqLocus` in `Mathlib.Algebra.Ring.Subring.Basic` supplies the
invariant subring; there is no new definition of invariants. The annihilator
conclusion is also the expansion of `RingHom.IsIntegral` for the subtype map,
as checked in `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`.

Of the original proof dependencies, only
`lem-weil-pbc-sheaf-disjoint-union-product` currently has an available interface:
`TopCat.Sheaf.isProductOfDisjoint` in
`Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections` and
`TopCat.Sheaf.objSupIsoProdEqLocus` in `Mathlib.Topology.Sheaves.CommRingCat`.
Both modules are ordinary, non-public proof imports, and their signatures and
docstrings were read. The rank-strata, norm-characteristic-polynomial, and
polynomial-norm-invariance proof nodes currently have neither a Lean declaration
nor a Mathlib match; they are named in the complete proof docstring. No missing
proof-only dependency prevents stating this theorem, and no import cycle is added.

Edge cases checked mathematically before writing:

- Empty `Spec A`: `A` is the zero ring; the invariant subring is also the zero
  ring. The polynomial `X` is monic, including over the zero ring, and vanishes
  at its unique element. No `Nontrivial` assumption excludes this case.
- The identity groupoid has `s = t = id`; the equalizer is the whole ring, and
  `X - C a` is an annihilator.
- Nonreduced rings and variable finite locally free ranks remain allowed. The
  docstring explains local norm construction and finite clopen recombination;
  it never substitutes global freeness or constant rank as hypotheses.
- A nonempty object scheme with empty arrow scheme cannot satisfy the groupoid
  premise because `e` is a common section of `s` and `t`.
- The groupoid definition does not require joint monicity of `(s,t)`; it allows
  groupoids with nontrivial stabilizers, not only equivalence relations.

Searches for existing statements and notions were run through `msearch.py`:

- LeanFinder: “For an affine groupoid scheme whose source and target are finite
  locally free the coordinate ring is integral over the invariant subring”.
  Eight hits, including `IsIntegralHom.hasAffineProperty`,
  `Algebra.IsInvariant.isIntegral`, and `isIntegral_of_profinite`; none is this
  groupoid-scheme theorem. A finite discrete group action does not represent
  an arbitrary finite locally free scheme groupoid.
- LeanSearch: “Groupoid object in a category with pullbacks and invariant
  subring integral finite locally free”. Eight ordinary categorical groupoid
  hits; no internal scheme-groupoid interface.
- Loogle: `Groupoid, IsIntegral, eqLocus` gave no hits (the unqualified
  identifier was unknown); the refined `CategoryTheory.Groupoid, RingHom.eqLocus`
  also gave no hits.
- Mathlib grep: `groupoid.*integral|integral.*invariant|invariant.*integral`
  gave 25 hits, mostly measure-theoretic integrals and finite group invariants;
  no affine-groupoid integrality theorem.
- The new definition's LeanSearch, LeanFinder, and Mathlib grep queries and
  complete results are recorded in its `mathlib_searches`, with the additional
  direct DAG/project searches. The exact search log is retained in the sandbox.
- Direct `rg` searches of `WeilConjectures` and `lean/Sheaf` found no
  scheme-groupoid declaration or matching theorem. Searching the original item
  id upstream gave no hits. The only `IsGroupoidObject` match in `lean/Sheaf`
  concerns simplicial spaces in `SpaceGeometricDescent`, not schemes.
- Direct searches of `dag/nodes`, `dag/lean_names_upstream.json`, and
  `tools/blueprint_refs.py search groupoid` found uses of groupoid schemes but
  no node defining their structure. `blueprint_refs.py ancestor` returned
  `lem-a1-affine-hc0`, used in the new node's ancestry record.

Validation: both delivered modules passed `scompile.py` separately, in dependency
order, including the published-library confirmation, with no errors or warnings.
The theorem proof is exactly `sorry`; the definition has no postponed theorem or
unconstructed data. Delivery preflight and dry run are run before pushing.

## New nodes

`def-a1-scheme-groupoid-laws` defines `AlgebraicGeometry.Scheme.IsGroupoid` for
schemes `U,R` and the five specified maps. Its source is Stacks Tag 0231, the
explicit axioms immediately preceding `definition-groupoid`, and the following
paragraph explaining the equivalent septuple. Its only notion dependencies are
schemes and their chosen fibre product. Mathlib has ordinary categories and
groupoids, but no internal groupoid interface in schemes; the search results
are recorded in the new node. The item gains this node in `stmt_deps` and changes
no other original mathematical field.

Reading the new definition clause by clause: `source_id`, `target_id` give the
two common-section identities. `source_inv`, `target_inv` swap endpoints.
`source_comp`, `target_comp` give the endpoints of a composite. `id_comp` and
`comp_id` give the two unit laws. `inv_comp` and `comp_inv` give the two inverse
laws. `assoc` gives the equality of the two composites of three arrows.
All the latter laws quantify over arbitrary `H : Scheme.{u}` and points of the
chosen pullback. Such points are exactly composable pairs by its universal
property; hence this is an encoding of every law, not a restriction to certain
pairs. In `assoc`, `p=(a,b)`, `q=(b,d)`, `r=(c(a,b),d)` and
`z=(a,c(b,d))`; the five premises identify exactly those pairs. Endpoint laws
ensure the outer pairs exist, so the premise is not vacuous. All operations
commute with precomposition automatically since they arise from scheme maps.
There is no choice of arbitrary category structure, no assumed equivalence
relation, and no strengthening such as a fixed base field.

## Second reading by Q70

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

The module states `isN2_of_finite_domain_extension`: for commutative integral domains `A` and
`B`, with an injective algebra map `A → B`, `B` finite as an `A`-module, `A` Noetherian, and
`A` N-2, the domain `B` is N-2. `IsNoetherianRing A` renders the Noetherian hypothesis;
`IsDomain A` and `IsDomain B` render the integral-domain hypotheses; `[Algebra A B]` plus
`hAB : Function.Injective (algebraMap A B)` renders `A ⊆ B`; `[Module.Finite A B]` renders
finite generation; `hA : IsN2 A (FractionRing A)` renders N-2; and the conclusion is
`IsN2 B (FractionRing B)`. `FractionRing` supplies the fraction fields, while `IsN2` quantifies
over every finite field extension and asserts `Module.Finite` of the integral closure.

The dependency declarations used are `IsN2` from `Sheaf.RingTheory.JapaneseDomain` and
Mathlib's `Module.Finite`, `IsNoetherianRing`, `FractionRing`, `Algebra`, `IsDomain`, and
`integralClosure` (the latter through `IsN2`).

Edge cases checked: the universes `u` and `v` allow different carrier sizes; `IsN2` permits
all finite extensions, including the trivial extension; `Module.Finite` permits the zero module,
and no nonzero or separability hypothesis is added. The explicit injectivity hypothesis is
required to express the stated inclusion of domains.

Searches for an existing declaration: `msearch.py leanfinder` for “N-2 ascends along a finite
extension of Noetherian domains” returned no match; `msearch.py loogle` for
`IsN2, Japanese, finite domain extension` returned no match; grep of Mathlib for
`Japanese|IsN2|N-2` found no predicate; grep of `WeilConjectures/` for `IsN2` found no declaration;
rg of `lean/Sheaf` found only the dependency `IsN2` and no theorem with this statement.

## Earlier second reading (a previous round; superseded)

The statement was read against the node clause by clause. `A` and `B` are commutative integral
domains, finite generation is `Module.Finite A B`, inclusion is the algebra map with explicit
injectivity, and the assumptions are Noetherian plus N-2 for `A`. The conclusion is exactly N-2
for `B`, with no extra hypotheses or weakened clauses. No mismatch was found.

## Second reading by M1

I opened the node and source place (Stacks Algebra, Tag 032I, lines 45202--45232)
independently and matched each part against the declaration.

- Objects: `A : Type u`, `B : Type v`, both commutative rings and integral domains; these are
  `[CommRing A]`, `[IsDomain A]`, `[CommRing B]`, and `[IsDomain B]`.
- Inclusion `A ⊆ B`: `[Algebra A B]` together with
  `hAB : Function.Injective (algebraMap A B)`.
- Finite generation: `[Module.Finite A B]`.
- Noetherian hypothesis: `[IsNoetherianRing A]`.
- N-2 hypothesis: `hA : IsN2 A (FractionRing A)`, using the project's definition (all finite
  field extensions and finite integral closures).
- Conclusion: exactly `IsN2 B (FractionRing B)`, with its fraction field and all finite
  extensions quantified by that definition. Quantifier order and strength match the node.

Edge cases remain covered: `u` and `v` may differ; the trivial finite extension is included;
finite modules may be zero; and no separability, nonzero, characteristic, or dimension
restriction was added. The domain assumptions rule out the zero-ring case as in the node.
The test-extension universe in `IsN2` is the fraction-field universe, so no independent
smaller universe is introduced.

I repeated the required searches: LeanFinder for preservation of Japanese/N-2 under finite
extensions (no match), Loogle for an `IsN2` finite-domain-extension theorem (no match), and
grep over Mathlib, `WeilConjectures/`, and `lean/Sheaf` (only the dependency definition
`IsN2` was found). Thus no existing declaration duplicates this statement.

I found one documentation mismatch: the worker theorem docstring summarized the proof but did
not give the node's six proof steps or dependencies. I replaced it with a six-step docstring
covering fraction-field embedding and finiteness, the tower law, N-2 integral closure,
integrality transitivity, and transfer of generators. The Lean signature matched the node and
required no change.

Independent search details: LeanFinder query "Japanese property preserved by module-finite
injective homomorphism of domains" returned eight unrelated results, including
`fg_of_fg_of_fg` (subalgebra/submodule finiteness) and
`RingHom.QuasiFinite.of_isIntegral_of_finiteType`; none asserts the N-2 conclusion. Loogle
query `IsN2` returned zero hits (unknown identifier in its Mathlib index). Direct `rg` for
`IsN2|N-2` in Mathlib and `WeilConjectures/` returned no hits; the repository search found
`JapaneseDomain.lean` and its uses, but no duplicate of this theorem.

I opened all five dependency nodes and their recorded declaration sources. `Module.Finite`
has `fg_top`, `IsNoetherianRing` is `IsNoetherian R R` (equivalently all ideals FG), `Algebra`
provides the ring homomorphism, and `integralClosure` has carrier `{x | IsIntegral R x}`.
`IsN2` in `JapaneseDomain.lean` quantifies over finite-dimensional field extensions with
`IsScalarTower R K L`, so the ring action is the source's composite action. Each is the
node's notion, not a special case. A finite extension admits a representative in the base
field's universe, so the test-extension universe is not a loss of mathematical generality.
There are no new definition nodes, dependency modules, or statement corrections in this
packet. The only theorem proof remains `sorry`, and no definition data is postponed.

Validation: the final module compiled on the server without errors or warnings. The node's
`lean.statement` is verbatim equal to the unchanged theorem signature. All universes and
variables are bound, and all Lean lines are at most 100 characters.

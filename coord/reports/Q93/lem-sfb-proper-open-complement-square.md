## Worker report

The module `Sheaf.AlgebraicGeometry.ProperOpenComplementSquare` states
`AlgebraicGeometry.ProEtale.CondensedRing.proper_open_complement_square`, with one
`sorry` and no new definitions. It combines precisely the geometric conclusions and
the unbounded mixed-restriction vanishing of the assigned node. The node changes only
in `lean`; there are no new nodes, dependency repairs, or statement corrections.

Source read: main-20261015 blueprint,
`sec-six-functors-basics/sk-thm-sf-comp-composition/det-sf-comp-composition-interchange.proof.md`,
proof (3). Its complement argument is exactly the source of the vanishing. The
statement retains the assigned node's arbitrary commutative condensed coefficients,
unbounded derived category, and arbitrary scheme structure on the closed complement.
The declaration docstring includes all five DAG proof steps and their dependencies.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Prime ell | `(ℓ : ℕ) [Fact ℓ.Prime]` |
| Field k of positive characteristic p different from ell | `{k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`; prime characteristic implies positivity, using the recorded setting's exact convention |
| W, Y, Ybar are k-schemes; Z has a k-structure | `{W Y Ybar Z : Over (Spec (.of k))}` |
| W, Y, Ybar are separated and finite type | Three instances per structure morphism: `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` |
| All maps are over k | `r : W ⟶ Ybar`, `i : Y ⟶ Ybar`, `c : Z ⟶ Ybar` are morphisms in `Over` |
| r proper | `[IsProper r.left]` |
| i quasi-compact open immersion | `[IsOpenImmersion i.left] [QuasiCompact i.left]` |
| c closed immersion with complementary point image | `[IsClosedImmersion c.left]` and `hcomp : Set.range c.left.base = (Set.range i.left.base)ᶜ` |
| U and T are scheme fibre products | `pullback r.left i.left` and `pullback r.left c.left`, not pullbacks of topological spaces |
| j, a, r_Z are the specified projections | `pullback.fst r.left i.left`, `pullback.fst r.left c.left`, `pullback.snd r.left c.left` respectively |
| U separated finite type over k | First conjunction, on `pullback.fst r.left i.left ≫ W.hom` |
| Z separated finite type over k | Second conjunction, on `Z.hom`, with no such input assumptions |
| T separated finite type over k | Third conjunction, on `pullback.fst r.left c.left ≫ W.hom` |
| j quasi-compact open immersion | `IsOpenImmersion (pullback.fst r.left i.left)` and `QuasiCompact` of that map |
| a closed immersion | `IsClosedImmersion (pullback.fst r.left c.left)` |
| r_Z proper | `IsProper (pullback.snd r.left c.left)` |
| Complementarity on W | Equality of the range of the closed projection with the complement of the range of the open projection |
| Every commutative condensed ring | `∀ (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]`; its `MonObj` is the bundled ring object's existing structure |
| Every B in the ordinary unbounded module-object derived category of U | `B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (pullback r.left i.left)) Ab.{u + 1}) (condensedRingObj Λ.X (pullback r.left i.left)))` |
| Exact termwise j_! | `(openImmersionLowerShriek Λ.X (pullback.fst r.left i.left)).mapDerivedCategory` |
| Actual coefficient-compatible total derived a^* | `moduleObjectDerivedPullback Λ.X (pullback.fst r.left c.left)` |
| a^* j_! B is isomorphic to zero in D(T) | `IsZero` of that composite's value on B; in a category with zero object this is equivalent to a nonempty isomorphism to zero |
| No reducedness of Z or T | No reducedness instances or hypotheses occur |

Dependency interfaces read and used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  the recorded setting of `compactificationOverField` uses objects of `Over (Spec k)`
  and `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on their structure morphisms.
  The statement follows these binders; no constructibility or coefficient-finiteness
  restriction is imported as an assumption.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
  Universally closed implies quasi-compact, so the recorded locally-finite-type
  class has exactly the finite-type meaning of the node.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback`, whose body
  is precisely the existing total `leftDerivedFunctor (upperStar Λ f)`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek`:
  the recorded construction uses exact `openImmersionLowerShriek` followed by
  `mapDerivedCategory`, the same j_! factor used here. No compactification-based
  replacement of open extension by zero is made.

All stated proof dependencies' recorded modules are imported without `public` unless
already statement dependencies. These include the Mathlib scheme permanence modules,
`Restrict`, `ResidueField`,
`WeilConjectures.AlgebraicGeometry.FieldPointFactorsThroughClosedImmersion`,
`Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`,
`Sheaf.CategoryTheory.DerivedCategory.LeftDerivedExactComparison`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed`. In particular the
last module's `isZero_upperStar_obj_openImmersionLowerShriek_of_disjoint` is the
actual coefficient-module vanishing needed by step 5.

Edge cases checked mathematically before drafting:
empty W, empty Y (so the complement fills Ybar), empty Z (so Y covers Ybar),
the zero coefficient ring, the zero derived object, arbitrary unbounded B, and
nonreduced complements. Neither base-change space is replaced by a reduced
subscheme. Complementarity concerns point sets only, while both pullbacks remain
scheme fibre products. No algebraic closure, smoothness, boundedness, torsion, or
constructibility assumption is imposed. No disputed statement was found.

Searches for an existing statement (all via the prescribed msearch wrapper):

- LeanFinder: "Base change of a proper map by complementary open and closed
  immersions gives complementary immersions and derived pullback of open extension
  by zero vanishes". Eight hits: immersion coborder and open-immersion pullback
  range results; none gives the combined statement or internal derived assertion.
- Loogle: `AlgebraicGeometry.IsProper, AlgebraicGeometry.IsClosedImmersion`.
  Two hits, the equivalence with proper monomorphisms and its property equality;
  neither matches this node.
- Mathlib grep: `proper_open_complement|complement.*lowerShriek|closed.*extensionByZero`.
  Zero hits.
- LeanSearch: "Derived pullback of extension by zero vanishes on a closed complement
  of an open immersion in a proper base change square". Eight hits on ideal sheaves,
  pullback cones, and base-change permanence; no combined statement.
- Local `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `proper_open_complement`, and derived disjoint vanishing found no exact combined
  statement. Existing
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed` has
  `isZero_leftDerivedUpperStar_obj_openImmersionLowerShriek_of_disjoint`, which is
  the vanishing part under a disjointness hypothesis, not the scheme geometry
  assertions here. It therefore does not justify marking this whole item existing.
- Exact declaration-name search in both source roots and `dag/lean_names_upstream.json`
  found no collision for `proper_open_complement_square`.

Validation: prescribed `scompile.py` passed both sandbox and final module-path
compilations, each in 2.3 seconds, with no errors or warnings. Every variable and
universe is explicitly bound and `autoImplicit` is disabled.

## Second reading by Q93

This is the dispatched worker's own final clause audit; the independent maintainer
review is still required. No subagent was started, as the dispatch explicitly forbids it.
Rereading the node against the file confirms the three geometry conjunctions refer
to the induced k-structure maps, Z's finite-type properties are conclusions, and
all seven remaining geometric properties precede the universal vanishing clause.
The latter quantifies over every bundled condensed ring with commutative
multiplication and every object of the full unbounded derived category. It uses
the recorded total derived pullback rather than only underived pullback. No
mismatch or correction was needed. The sole theorem proof remains `sorry`.

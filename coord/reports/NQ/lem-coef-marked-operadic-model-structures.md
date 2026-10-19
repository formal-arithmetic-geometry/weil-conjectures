## Worker report

The module `Sheaf.CategoryTheory.MarkedOperadicModelStructures` states
`SSet.Enhanced.MarkedOperadic.marked_operadic_model_structures`. This is the sole
postponed theorem in the item module. All auxiliary definitions contain real data, and the structure
types describe the data whose existence the theorem asserts. No selection from an
unproved existence theorem occurs in a definition.

The source was opened online: [Gepner--Haugseng, Section 3.2](https://arxiv.org/html/1312.3178),
Theorem 3.2.5, Corollary 3.2.6, Definition 3.2.9, Remark 3.2.12 and Proposition 3.2.13.
Remark 3.2.12 identifies the full algebra infinity category with the marked enriched
Hom; Proposition 3.2.13 gives the generalized-to-ordinary left Quillen direction.
The theorem docstring gives all seven steps of the DAG proof, naming the inputs.

Clause-by-clause rendering (names below are in `SSet.Enhanced.MarkedOperadic`):

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Fixed nested small/ambient universes | Explicit `universe u`; total simplicial sets are `SSet.{u}`, the category of all such marked objects is in `Type (u+1)`, and coherent operad nerves are `SSet.{u+1}`. No dimension, nonemptiness, finite-object or Kan-zero-fiber assumption is added. |
| Ordinary nonsymmetric infinity operads | `IsFibrant true X` is exactly `NonsymmetricOperad.IsObject (expand X)`, the recorded dependency's ordinary operad predicate, including its marking. |
| Generalized inner fibration | `IsFibrant false X` uses `InertOperad.IsGeneralizedOperad X.hom.val`, whose first conjunct is `InnerFibration`. |
| Cocartesian lifts of every inert arrow | The second conjunct of that same predicate quantifies over every inert base arrow and source vertex, with the prescribed image and cocartesian lift. |
| Incidence Segal equivalence | The predicate uses `InertOperad.Incidence n`, the full category of inert maps out of `[n]` to `[0]` or `[1]`, and actual restriction of coherent cocartesian cone sections to incidence sections. Its restriction equation fixes the comparison and its equivalence is `IsFunctorEquivalence`. Cone evaluation is equivalent to the apex fiber because all cone edges are inert and admit cocartesian lifts. Thus this is the stated fiber-limit comparison. |
| Relative mapping-space incidence equivalence, for every source, base arrow and chosen projections | The last conjunct of `InertOperad.IsGeneralizedOperad` is the relative-limit homotopy-pullback square on incoming mapping spaces, for every cocartesian incidence cone and every test diagram. The base nerve has discrete mapping spaces, so the square is equivalently the comparison on each specified base-arrow fiber. This reuses the landed interface rather than replacing it by an arbitrary comparison map. |
| No generalized zero fiber space condition | `InertOperad.IsGeneralizedOperad` has no `KanComplex` conjunct. The additional Kan-zero-fiber hypothesis belongs only to that dependency's reconstruction theorem, which is not used as the object predicate. |
| Marked sets and the inert base | `base` has the dependency's `SSet.Marked` structure, with the predicate `IsMonoidalInert` applied to the base arrow. Degeneracies are included explicitly; they already are inert identity arrows. `Objects` is the actual `CategoryTheory.Over base`, not the slice over the sharply marked base. |
| Both model structures | Existential witnesses `G : Model E false` and `O : Model E true`. Each record contains a Mathlib `ModelCategory Objects`, completeness, cocompleteness and both functorial weak factorization systems. Mathlib's model axioms include retract closure, two-out-of-three and both characterized lifting classes. |
| Cofibrations are monomorphisms | `Model.cofibrations` identifies the model cofibrations with `SSet.Marked.cof i.left`, namely injectivity in every simplicial degree, in both directions. |
| Every object is cofibrant | `Model.cofibrant` quantifies over every initial object, its initial proof and every target. |
| Exact fibrant objects and markings | `Model.fibrant` is a biconditional for terminal maps. `IsFibrant` uses precisely the ordinary or unrestricted generalized predicate and exact equality with `NonsymmetricOperad.inertMarking`; the explicit degenerate summand is redundant for inert cocartesian markings. |
| Associated infinity categories | `Enrichment.operads` is the actual `SimplicialNerve` of the full ordinary category on `IsFibrant ordinary`, with the normalized sharp enrichment. `Model.localization` asserts coherent `FiniteReedy.IsLocalization` into this nerve; that predicate is universal on entire functor infinity categories. Its objects are precisely operads; its sharp relative mapping complexes consist of inert-preserving functors and coherent equivalences, with actual composition by `sharp_composition`. |
| Identity adjunction is left Quillen from generalized to ordinary | The theorem's first two conjuncts are preservation of cofibrations and trivial cofibrations by the identity. These are exactly the recorded Quillen criterion; the underlying ordinary adjunction is the identity adjunction of the identical slice category. |
| Marked enrichment | One shared `E : Enrichment` supplies the fixed relative marked `hom`, normalized composition, and normalized currying in all simplicial degrees. Identity and the enriched unit are obtained by currying the product projection of the identity morphism. The displayed degreewise formulas imply the ordinary unit, associativity and naturality equations, so this is the actual marked enrichment, not arbitrary Hom objects. |
| Tensors | `tensor K` is explicitly the external marked product `A × K`, with the base map through `A`. `Enrichment.curry` and `curry_formula` give the marked tensor-Hom adjunction and its complete simplex formula. |
| Cotensors | `Enrichment.cotensor` and `tensor_cotensor` give right adjoints to these fixed external tensors; `enriched_cotensor` gives the marked Hom identity with the existing marked internal Hom. Cotensors are specified by their universal property, not chosen arbitrarily as extra hypotheses. |
| Compatibility of the identity adjunction with enrichment | Both `G` and `O` have the very same witness `E`, hence the same Hom, composition, tensor and cotensor. The identity acts as the identity on all these objects and maps. |
| Enriched model compatibility | `EnrichedModelAxiom K G` and `EnrichedModelAxiom K O` assert full marked SM7. For any cofibration and fibration, the canonical two-projection corner map into a pullback is a categorical fibration, trivial when either input is trivial. The pullback's universal square and both comparison equations exclude an arbitrary map. |
| Fibrant-target restriction fibration and triviality | `RestrictionAxiom K G` and `RestrictionAxiom K O` use the explicitly defined enriched `restriction`. It is a fibration in the point categorical model `K`, and is `SSet.Marked.weak` when the cofibration is also a model weak equivalence. `K.weak_equivalences` identifies this class with its model weak equivalences. |
| Categorical weak equivalence terminology | `SSet.Marked.weak` is the recorded marked point model's mapping-test class. The imported saturation theorem equates this class with categorical equivalences after categorical fibrant replacement, as required for arbitrary marked inputs. |
| Full algebra Hom for generalized fibrant source and target | The last conjunct gives `FullAlgebraHom A B`. It asserts natural categorical fibrancy of the actual marked Hom and a simplicial isomorphism to `InertOperad.algebras A.hom.val B.hom.val`, normalized on every source simplex and parameter simplex. That existing definition is the full subcategory of fixed-base coherent functors on inert-preserving vertices, with unrestricted transformations. It is not the core. |
| Ordinary target also allowed | The penultimate conjunct says `IsFibrant true P → IsFibrant false P`; the last conjunct therefore applies with ordinary target as well. |

Dependency declarations read and used:

- `Sheaf.CategoryTheory.CompleteAlgebroid`: the small/ambient universe convention;
  `Algebroid.overFunctors`, reused by the algebra definition, fixes the entire base
  diagram rather than only its vertices. The recorded `completeCategory` signature
  and docstring were read; that unrelated complete-algebroid object is not needed here.
- `Sheaf.CategoryTheory.NonsymmetricOperadsPresentability`:
  `NonsymmetricOperad.IsObject`, `inertMarking`, and its coherent nerve construction.
  Its predicate uses `IsChainTwoInfinityOperad`, `HasMonoidalSegalFibers` and
  `HasMonoidalRelativeLimits`; despite the historical name it is the general ordinary notion.
- `Sheaf.CategoryTheory.ModelInfinityDerivedAdjunction`:
  Mathlib `HomotopicalAlgebra.ModelCategory`, its functorial-factorization convention,
  the left Quillen preservation criterion, and `FiniteReedy.largeNerve` / `IsLocalization`.
- `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`:
  `SSet.Marked`, marked maps, products, `cof`, `weak`, `internalHom`,
  `IsNaturallyFibrant` and `CartesianModelStatement`.
- Added landed dependency `lem-coef-inert-operad-color-reconstruction`, module
  `Sheaf.CategoryTheory.InertOperadColorReconstruction`:
  `InertOperad.IsGeneralizedOperad`, `Incidence`, `algebras`, `algebraInclusion`.
  The node statement introduces the unrestricted generalized notion before imposing
  Kan zero-fiber only on its reconstruction theorem. Only its unrestricted definitions
  are used here; no hypothesis of that theorem enters this item's statement.
- Proof-only imports: `MarkedSaturationPerfectEquivalences` and
  `SimplicialModelNerveLocalization`; their full theorem signatures and proof docstrings
  were read. The two remaining generic categorical-pattern proof nodes have no `lean`
  record at the time of writing, so there is no module for them to import. Their names
  and roles remain in the theorem's proof docstring.

Edge cases checked before drafting:

- At arity zero the generalized incidence category has exactly the identity object;
  restriction from cocartesian cones to its one-object boundary imposes no condition
  that the fiber be terminal or Kan. The ordinary empty product does impose terminality
  and contractibility of the relevant incoming mapping fibers.
- At arity one the incidence category is one edge and its two endpoints; its nerve
  is contractible. All inert maps to zero, including endpoints, are retained.
- The constant generalized operad `N([1]) × N(Delta opposite)` is permitted. Its
  zero fiber is `N([1])`, which is not Kan. Consequently the stronger predicate
  `OperadicPresentability.IsGeneralizedOperad` was not used.
- The empty marked simplicial set is an allowed object of the slice. All its initial
  maps are degreewise injective. There is no hidden nonempty-object restriction.
- A generalized target and an ordinary target are both covered, but no generalized
  operad is silently assumed to have ordinary terminal zero fiber.
- Flat Hom parameters permit noninvertible transformations; only marked parameter
  edges, and hence sharp mapping spaces after fibrancy, restrict to equivalences.

Searches for an existing statement:

- `msearch.py leanfinder`, query: “Marked simplicial sets over Delta opposite have
  generalized and ordinary operadic model structures and the identity is an enriched
  left Quillen functor”. Result: ordinary simplicial category structures on simplicial
  objects, `SimplicialNerve`, `QCat.catEnrichedOrdinaryCategory`; no marked operadic model.
- `msearch.py loogle`, query `HomotopicalAlgebra.ModelCategory`: twelve matches,
  including the usable general model-category structure and its axiom projections;
  no ordinary/generalized operadic specialization.
- `msearch.py grep`, query `categorical.pattern|marked.*simplicial|[Oo]perad`:
  only bibliographical references to operads in Mathlib; no matching theorem.
- `rg` on the upstream `WeilConjectures` source for the item ID and for
  `Generalized.*Operad|generalized.*[Oo]perad|Incidence|incidence|HasMonoidalRelativeLimits|IsChainTwoInfinityOperad`:
  no upstream operadic declaration matching the node.
- The same `rg` on the project found the ordinary operad predicate and the two
  generalized incidence interfaces. `OperadicAlgebraPresentability` adds a Kan zero
  fiber and is unsuitable; `InertOperadColorReconstruction` provides the unrestricted
  definition and the full algebra functor category, so those are reused and its node
  is added to `stmt_deps`. No new definition node is needed. The previously supplied transitive
  dependency compile repair is now landed and is omitted from this packet.
- Names were also checked in `dag/lean_names_upstream.json` and under `lean/Sheaf`;
  no declaration duplicates the new `SSet.Enhanced.MarkedOperadic` namespace.

Validation: the prescribed `scompile.py` wrapper compiled the sandbox file and its
library-path copy cleanly, each in approximately three seconds, including the final
full enriched model axiom. All variables and the universe are explicit. In the item module the only
`sorry` is the named main theorem with the full proof plan in its docstring. No
statement correction or `STATEMENT-DISPUTED` issue remains.

## Repair of returned delivery

The return for immutable head `9cd71a77259e` concerns the maintainer's
`--apply-fixes` filename: that interface accepts
`lem-coef-marked-operadic-model-structures.report.md`, not `report.md`.
The worker packet uses `report.md` as required by `deliver2.py`; the wrapper places
it at `coord/reports/NQ/lem-coef-marked-operadic-model-structures.md` in the delivery.
This repair retains the saved module and node record and submits the complete packet
through that wrapper, without a maintainer-side `--apply-fixes` directory.

On 2026-10-17 the saved packet first passed `deliver2.py --no-push`, including both
file-only compilations and server preflight. Comparison with the current shared node
initially found only the authorized `lean` record and the added landed statement dependency
`lem-coef-inert-operad-color-reconstruction`. The final self-check read the entire
module against the node's statement and seven proof steps, and rechecked the ordinary
operad predicate, unrestricted generalized incidence predicate, full algebra category,
and point marked model interfaces in their current source modules. In particular the
generalized predicate adds no Kan zero-fiber condition, both model witnesses share
the same normalized enrichment, and the full algebra Hom retains transformations.
The recorded theorem signature matches the file, `autoImplicit` is disabled, every
declaration is documented, and the only postponed proof in the item module is the named main theorem.
No mathematical change or statement correction was required by this return.

## Repair of immutable head 43ffd5963a64

The saved packet was dry-run first as instructed. Both Lean files compiled, but
server preflight rejected the stale dependency repair: the straightening module
was already identical to the current base, so its delivered dependency record
required a module change that the commit did not contain. The current shared
`Sheaf.CategoryTheory.SpaceValuedStraightening` already has the required
`noncomputable abbrev Diagrams`. Its source was compared byte for byte with the
saved repaired file before removing the latter.

Removed the redundant straightening module and dependency node copy from this
packet, and removed the direct statement dependency that existed only to carry
that repair. `CompleteAlgebroid` continues to use the landed straightening
module through its existing imports. This also removes the module implicated
in the returned maintainer `--apply-fixes` path diagnostic: no straightening
module fix is requested by this delivery. The item module and its mathematical
statement are retained unchanged.

Self-check: read the entire item module against every clause of the node;
reopened ordinary fibrancy, unrestricted generalized incidence fibrancy, the
full algebra category, point marked model, and Quillen criterion. In particular,
there is no generalized Kan zero-fiber restriction, full Hom retains coherent
transformations, and both models share the normalized enrichment. The theorem
signature matches `lean.statement` verbatim; auto-implicit binding is disabled;
all lines satisfy the width limit; the sole postponed theorem in the item is
the named main theorem with its seven-step proof docstring. The corrected
packet is compiled and checked again by the prescribed delivery wrapper.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

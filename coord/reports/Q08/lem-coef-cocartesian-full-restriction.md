## Worker report

Delivery for `lem-coef-cocartesian-full-restriction`, stage 2, Q08, 2026-10-17.
The shared base already contains the Q148-reviewed module and its earlier statement.
I read that module and both recorded statement dependencies. No repair-note file exists
for this item. The earlier interface gives the fibration and mapping assertions, but its
precomposition clause only says that an ambient precomposed simplex is in the image.
It does not state the commuting square on strict fibers. Its factorization predicate
also leaves the object-value condition implicit. Therefore this is not an existing-only
binding: the delivery retains every old declaration verbatim and appends
`SSet.Enhanced.cocartesian_full_restriction_explicit` in the same owning module.
This declaration states all clauses of the existing natural-language node explicitly;
the node's statement and proof have not changed.

### Hypotheses and clauses

* Fixed universes and quasicategories: `universe u`, `{E B : SSet.{u}}`, and
  `[Quasicategory E] [Quasicategory B]`. Every simplicial set and indexing diagram
  lies in the same fixed universe; there is no cardinality or nonemptiness restriction.
* The map and cocartesian fibration: `(p : E ⟶ B)` and
  `(hp : cocartesianFibrationOver p)`. The recorded dependency includes both inner
  horn lifting and cocartesian lifts at each prescribed source.
* The full subcategory: `(R : E.Subcomplex)` and
  `hfull : R = fullSubcomplex E (fun x ↦ x ∈ R.obj (op ⦋0⦌))`.
  The existing full-subcomplex definition tests every vertex of a simplex.
* Repleteness: `hreplete` takes an equivalence edge whose source `E.δ 1 e` is in
  `R` and requires its target `E.δ 0 e` to be in `R`. In a quasicategory every
  equivalence of objects is represented by such an edge. The assumption is retained
  even though the proof of this lemma does not need it.
* Transport stability: `htransport` quantifies over every vertex `x`, base target
  `b`, and edge `α` with the stated source and target. For `x` in `R` it supplies
  an actual edge `e` with source exactly `x`, target in `R`, image exactly `α`,
  and `IsCocartesianEdge p (SSet.yonedaEquiv.symm e)`. No arbitrary transport map
  or chosen isomorphism substitutes for these equalities.
* Restricted fibration: `Quasicategory (R : SSet)` and
  `cocartesianFibrationOver (R.ι ≫ p)`.
* Preservation and reflection: for every edge `e : Δ[1] ⟶ (R : SSet)`, the
  displayed `IsCocartesianEdge (R.ι ≫ p) e ↔ IsCocartesianEdge p (e ≫ R.ι)`.
* For every small `K` and fixed `a : K ⟶ B`, `relativeFunctorFiber p a` is
  `fiber ((ihom K).map p) (diagramVertex a)`, a strict simplicial pullback over
  the constant diagram point. This is the degreewise fiber, with its entire base
  simplex fixed, not a homotopy fiber or a category of loosely commuting triangles.
  The conclusion asserts `Quasicategory` for both this fiber and its `R` analogue.
* Inclusion: `relativeFunctorInclusion R p a` is the existing canonical pullback
  map induced by postcomposition with `R.ι`. `Function.Injective` of every
  component makes the word inclusion explicit.
* Full subcategory on the stated object values: in every degree `n`, a simplex
  `z` is in the inclusion's image iff, for every parameter vertex
  `i : Fin (n.len + 1)` and every `k : K _⦋0⦌`, its underlying internal-hom
  simplex restricted to `i` and evaluated by `evaluation K E k` belongs to `R`.
  Thus the condition really concerns all vertices `(k,i)` of `K × Δ[n]`.
* Same right-pinched mapping simplices: for every two diagrams `b,c` in the
  restricted fiber and every degree `n`, the canonical `mappingSpaceMap` is
  bijective. This map is already a simplicial map, so the degreewise bijections
  identify the operators as well. Different subtype presentations are compared
  canonically through their inclusion, rather than asserting ill-typed literal
  equality of types.
* Naturality under precomposition: for arbitrary `t : L ⟶ K`, the penultimate
  conjunct is the equality of simplicial maps obtained by inclusion then restriction
  versus restriction then inclusion, with the new base exactly `t ≫ a`. It uses
  the existing `relativeFunctorRestriction`, whose definition has no fibration
  hypothesis. The final conjunct writes the induced mapping-space square in every
  degree and at every simplex. `HEq` only handles the two syntactically different
  endpoint expressions; their equality follows from the preceding strict square.
  No arbitrary endpoint identification is supplied as a hypothesis.
* Empty `K`: it is included in the unrestricted `∀ K`. Then all `K × Δ[n]` are
  empty, both fibers have one simplex per degree, the object-value criterion is
  vacuous, and the inclusion and its pinched mapping maps are bijections. Restriction
  to or from an empty indexing simplicial set uses the same canonical map.

### Dependency declarations and source reading

* `Sheaf.CategoryTheory.EnhancedDiagramsCones`: read the full signatures and
  docstrings of `SSet.Enhanced.IsEquivalenceEdge`, `fullSubcomplex`, `diagramVertex`,
  `evaluation`, `mappingSpace`, and `mappingSpaceMap`. The latter uses the entire
  initial face constant at the source and a last vertex at the target.
* `Sheaf.CategoryTheory.InfinityFibrationsOverSimplicialBases`: read the full
  `SSet.Enhanced.cocartesianFibrationOver` definition. Its public import
  `InfinityFibrations` supplies the exact horn predicate `IsCocartesianEdge` and
  the degreewise strict `fiber`, also read with their docstrings.
* Added the already landed node
  `lem-coef-unstraightening-homotopy-descent-gluing` to `stmt_deps`, following
  brief-stage2 section 5's authorization to add landed notions. Its module is
  `Sheaf.CategoryTheory.UnstraighteningHomotopyDescentGluing`, and the used
  declaration is `SSet.Enhanced.relativeFunctorRestriction`. I read its complete
  definition: it is precisely the canonical pullback map with internal-hom
  precomposition, without any right-fibration assumption. The large descent
  theorem is not assumed or used by this statement. A direct dependency traversal
  found no path from this added node back to the item; its imports also do not
  reach this module.
* The proof-only imports remain the existing
  `InfinityCocartesianCompositionInitiality` and
  `InnerFibrationEquivalenceOuterHornLift`; their recorded statements and source
  declarations were read. The former supplies composition and initiality of lifts;
  the latter supplies the required relative initial outer-horn filler.
* `lem-coef-inner-anodyne-pushout-product` has no recorded Lean module on the
  base. The existing proof-only Mathlib import is retained:
  `Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct`.
  Its `SSet.innerAnodyneExtensions_pushoutObjObjι'` and exponentiation instance
  have the indicated content. No new proof dependency is fabricated.

Source opened online: [Lurie, Higher Topos Theory](https://www.math.ias.edu/~lurie/papers/HTT.pdf),
Corollary 2.3.2.4 and Proposition 3.1.2.1, with opposite cocartesian variance
for the latter. Proposition 2.4.4.3 supplies the dual mapping-space criterion.
The full-subcomplex and strict mapping-square computations follow the node's
agent-written six-step proof. WANTED: an archival HTT copy in `literature/`, as
already requested by the node. The module carries the full six-step proof plan;
no theorem is proved at this stage.

### Edge cases and searches

Checked `R = ∅`, `R = E`, empty `E`, empty `B`, a point base, degenerate base
edges, `K = ∅`, `K = Δ[0]`, and arbitrary non-quasicategorical `K`.
For `R = ∅` and nonempty `K` the restricted fiber is empty; for empty `K` it is
instead a point, which is exactly why no nonempty binder was added. Higher-degree
operator compatibility is supplied by the actual simplicial maps. No extra
quasicategory or monomorphism assumption is imposed on `K`, `L`, or `t`.

Searches made through the prescribed Q08/item wrapper:

* LeanFinder, `Restriction of a cocartesian fibration to a transport stable full
  simplicial subcategory with strict relative functor categories`: eight ordinary
  fibered-category hits (`Functor.IsCocartesian`, `IsStronglyCocartesian` and map
  lemmas), no quasicategorical match.
* Loogle, `"Cocartesian", "Full"`: zero hits.
* Mathlib grep, `cocartesian.*[Ff]ull|[Ff]ull.*cocartesian`, subdirectory
  `CategoryTheory`: zero hits.
* `rg` for `cocartesian_full_restriction|relativeFunctorFiber|relativeFunctorInclusion|
  relativeDiagramInFull` in upstream `WeilConjectures` and side `lean/Sheaf`: only
  the already landed owning module; no upstream duplicate.
* `grep -rn lem-coef-cocartesian-full-restriction` upstream: no result.
* `rg cocartesian_full_restriction dag/lean_names_upstream.json`: no result.
* Side `rg` for `relativeFunctorPre|relativeFunctorRestriction|relativeFunctorFiber.*pre`:
  found the canonical general `relativeFunctorRestriction`; reused it instead of
  writing a second definition. Its owning node is now cited explicitly.

All definitions retain real constructions. The postponed declarations are
`relativeFunctorInclusion_squares`, `cocartesian_full_restriction`, and the appended
`cocartesian_full_restriction_explicit`, all belonging to this DAG node and all
with source/proof docstrings. The older signatures and definitions remain byte-for-byte
unchanged. No statement dispute or natural-language correction is needed.

Validation: the delivered module compiled cleanly using the prescribed
`scompile.py Q08 lem-coef-cocartesian-full-restriction <file>` wrapper: both the
sandbox and final library-path passes completed in 1.9 seconds, with no warnings.
The node signature is extracted verbatim from the new declaration up to `:=`.
Every Lean line has at most 100 characters and `autoImplicit` is explicitly false.

## Second reading by Q08

This is the author's separate verification pass; independent review belongs to the
maintainer's delivery process, as the dispatcher brief prohibits starting agents.
I reopened the node and final module and checked the source/target face indices,
the exact edge image equality, the full-subcomplex equality, and repleteness.
The first conclusion gives the restricted fibration and the edge biconditional.
The diagram conclusion uses strict pullbacks for both categories, injectivity in
each degree, and evaluates every diagram vertex at every vertex of `K`.
Its mapping clause uses the existing right-pinched definition in all degrees.
The final two clauses compare the actual restriction maps on the strict fibers
and on their mapping simplices, with base `t ≫ a` and no nonemptiness premise.
The mismatch found in the older record was the missing commuting square (its
existential statement only expressed image stability); this delivery adds the
explicit declaration while preserving consumers of the older one. The object
criterion and injectivity are now stated without relying on the factorization
predicate's explanatory docstring. All old declarations and their docstrings
are retained; no dependency module or new definition node is introduced.


### Independent maintainer reading of d314b69793e1

The independent reviewer read the immutable item, all three statement dependencies,
the delivered module and its six declarations, and the exact dependency definitions.
The main signature is verbatim equal to `lean.statement`. No mathematical change is needed.
The report's corrupted source numbers above have been repaired.

Every hypothesis agrees: `E,B` are quasicategories, `hp` contains inner horn lifting
and prescribed-source cocartesian lifts, `hfull` is fullness on exactly the vertices
of `R`, `hreplete` is closure under equivalence edges, and `htransport` supplies a
lift with the exact source and base edge and a target in `R`. Face 1 is source,
face 0 is target. The binder `b` does not impose an extra condition: it ranges over
all targets of the quantified base edge. Repleteness is retained, though unused.

Every conclusion agrees: the restriction is a cocartesian fibration; the edge
biconditional gives preservation and reflection; both strict relative diagram
fibers are quasicategories for arbitrary `K`; the actual inclusion is injective
in every degree and its image is exactly the simplices with every `(k,i)` vertex
in `R`; its canonical right-pinched mapping maps are degreewise bijections.
These are actual simplicial maps, so the operators agree under this identification.
The final equality is the strict restriction/inclusion square, with base `t ≫ a`;
the final `HEq` is its induced mapping-space square, with no arbitrary transport.

The definitions contain real data: a strict pullback, its canonical pullback map,
and an explicit factorization predicate. The named square theorem supplies only
compatibility proofs. The restriction helper in the added landed dependency is
the existing pullback map induced by internal-hom precomposition, without any
right-fibration or monomorphism assumption. Its 117-node statement/proof dependency
closure does not reach this item. No helper or universe repair is required.

The six proof steps check as follows. Fullness retains inner-horn fillers and
initial-outer-horn fillers because all vertices occur for dimension at least two.
Transport stability then supplies all restricted lifts. Initiality compares two
lifts over the identical base edge; their comparison is a fiber equivalence, hence
an ambient equivalence. Relative outer-horn filling makes it ambient cocartesian,
and composition proves reflection. The inner-anodyne pushout-product makes
postcomposition an inner fibration; strict base fibers are therefore quasicategories.
Fullness tests precisely the vertices `(k,i)` of `K × Δ[n]`. Pinched mapping
simplices have only the two endpoint diagrams as vertices. Precomposition along
`t × id` preserves all these equations, giving the stated naturality.

Sources read online in Lurie's HTT: Corollaries 2.3.2.4–5 (printed pp.100–101),
Propositions 2.4.1.5 and 2.4.1.7 (pp.116–117), Remark 2.4.1.9 (p.119),
Proposition 2.4.4.3 (p.131), and Proposition 3.1.2.1 (pp.151–152).
The lemma is the node's agent-formulated consequence, not a quotation of one
proposition. The Mathlib pushout-product declarations and dependency outer-horn
and composition/initiality signatures were also read directly.

Checked empty `R,E,B`, full `R`, point base, degenerate edges, degree zero,
empty and point `K`, and arbitrary non-quasicategorical `K,L` and arbitrary `t`.
For empty `R` and nonempty `K` the restricted fiber is empty; for empty `K` it is
a point. There is no nonemptiness premise or finite-dimensional restriction.
All universes and variables are bound; `u` is arbitrary, in the fixed simplicial
universe used by the dependency interface.

Independent searches: Loogle `"cocartesian", "full"` returned no hits;
LeanFinder for full simplicial subsets stable under cocartesian lifts returned
ordinary nerve/full-functor and skeleton/coskeleton declarations, not this result.
Ripgrep in pinned Mathlib's algebraic topology tree and upstream WeilConjectures
found no cocartesian/full duplicate; side-project searches found the existing
owning module and the canonical restriction helper, both reused. The previous
owning declarations are unchanged (only the new public import precedes them).

Reproduced compile using `scompile.py Q08 lem-coef-cocartesian-full-restriction`
on the immutable module: exit 0, sandbox pass 1.8 s, library-path pass 2.0 s,
no errors or warnings. The currently installed wrapper runs the side overlay on
the server; it was invoked only through the prescribed wrapper. All three delivered
theorems have only `sorry` proofs; definitions have no holes; all declarations have
source/blueprint docstrings; the main theorem has all six proof steps; maximum
line width is 96. No live file write, global build, Git mutation, or substitute
coefficient/site construction was performed.

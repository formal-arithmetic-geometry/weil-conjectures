## Worker report

The module `Sheaf.CategoryTheory.QuillenBCommaHomotopyFiber` states
`SSet.Enhanced.quillenB_comma_homotopyFiber`. Its sole postponed theorem has proof
`sorry`; all four helpers have complete defining data/formulae. No new node or
dependency module is needed. The natural-language statement and all eight proof
steps are retained verbatim. `stmt_deps` additionally names the already landed
fiber-detection and realization-cylinder nodes, whose canonical coordinate maps
are used to express the specified comparison. Both were already proof dependencies.

### Exact correspondence of hypotheses and clauses

- Small categories and a functor: `{E B : Type u} [SmallCategory E]
  [SmallCategory B] (U : E ⥤ B)`. Universe `u` is explicit. Arbitrary small categories
  can be placed in a common such universe; no finiteness, nonemptiness, fibrancy,
  localization, or model-category structure on these categories is imposed.
- The comma category with objects `(e,α : Ue → b)` and equation
  `U(h) ≫ α' = α` is the existing `CategoryTheory.CostructuredArrow U b`.
  The projection is `CostructuredArrow.proj U b`. Postcomposition by `β` is
  `CostructuredArrow.map (S := U) β`.
- The hypothesis on EVERY base arrow is precisely `hU`, quantifying `b₀ b₁ β`
  and asserting the dependency's `IsWeakHomotopyEquivalence` of that nerve map.
- The replacement `R = Sing|-|` is the literal functor
  `SSet.toTop ⋙ TopCat.toSSet`. Nerves are Mathlib `nerve` and `nerveMap`.
  Nothing is replaced by an arbitrary fibrant replacement.
- The specified vertex is `quillenBCommaVertex b`, the characteristic-map unit
  on `nerveEquiv.symm b`. In degree zero this is the constant singular simplex at
  the original nerve vertex, not an arbitrary singular point.
- The target is `quillenBCommaFiber U b`, an abbreviation for the recorded
  `homotopyFiber (R.map (nerveMap U)) (quillenBCommaVertex b)`.
  It has paths oriented from `RNU(a)` to `b`.
- The comparison's first coordinate in `IsQuillenBCommaComparison U b c` is
  exactly `R.map (nerveMap (CostructuredArrow.proj U b))`.
- Its second coordinate is fixed on ALL singular simplices by the last equation
  of `IsQuillenBCommaComparison`. The continuous map `H` satisfies
  `H.comp (realizationCylinderComparison _) = (SSet.toTop.map P).hom`.
  On a prism simplex `(x,θ)`, `P` has objects `U(xᵢ)` when `θ(i)=0`, and `b`
  otherwise. Its arrows are `U(hᵢⱼ)` before the switch, `αᵢ` across the switch,
  and `id_b` after it. These are exactly the nerve of the specified natural
  transformation, including its higher compatibility. `HEq` avoids arbitrary
  transports of the object equations; it does not forget any arrow equation.
- The interval parameter in the singular formula is the image of `θ` under
  `SSet.stdSimplexToTop.app ⦋1⦌`, then the standard coordinate homeomorphism to
  `unitInterval`. Thus the formula is `H(σ(t), |θ|(t))`, precisely singularization
  followed by restriction along `Δ¹ → Sing([0,1])`.
- Existence of the canonical comparisons is expressed by `∃ c : ∀ b, ...`, and
  each `c b` has BOTH its specified-coordinate predicate and the required
  `IsWeakHomotopyEquivalence`. The existential is not an unspecified fiber
  equivalence: object and arrow equations determine `P`; the cylinder
  homeomorphism determines `H`; the equation on every singular simplex determines
  the entire uncurried path; both projections determine `c` into the subcomplex.
  No definition chooses `P`, `H`, or `c` from a mere existence theorem.
- Strict-square naturality quantifies `E' B' U' F G comm b`, with
  `comm : U ⋙ G = F ⋙ U'` and `b'` written literally `G.obj b`.
  `quillenBCommaSquare` is Mathlib `CostructuredArrow.map₂`, using that equality
  and the identity of `G.obj b`, so it sends `(e,α)` to `(F(e),G(α))`.
- Both functors satisfy the comma-transition hypothesis: `hU` for `U`, and the
  displayed arrow-quantified premise for `U'`. The target comparison `c'` can be
  any map satisfying the same exact canonical-coordinate characterization.
- The naturality map `t` is specified by BOTH equations: its object coordinate
  applies `RNF`, and its path coordinate applies `(ihom Δ[1]).map RNG`.
  The final equality `RN(commaSquare) ≫ c' = c b ≫ t` is the requested naturality.
- No clause assumes contractibility or even nonemptiness of a comma category.

### Declarations read and used

The full source and docstrings of the recorded statement dependency were read:
`Sheaf.CategoryTheory.EnhancedDiagramsCones`, particularly
`SSet.Enhanced.IsWeakHomotopyEquivalence`, `commaSubcomplex`, `comma`,
`homotopyFiber`, `evaluation`, `constantDiagrams`, and the nerve/realization
imports. The dependency's other definitions retain their existing meanings;
none is privately copied here.

Additional statement-expression interfaces are the already landed
`Sheaf.CategoryTheory.SpacesHomotopyFiberDetection`:
`SSet.Enhanced.homotopyFiberProjection`, `homotopyFiberPath`; and
`Sheaf.AlgebraicTopology.RealizationCylinder`:
`SSet.realizationCylinderComparison`. Their definitions and docstrings were read.
These are public imports, and their nodes were added to `stmt_deps` under the
standing authorization to cite already landed notions.

Mathlib declarations read: `CategoryTheory.nerve`, `nerveMap`, `nerveEquiv` in
`Mathlib.AlgebraicTopology.SimplicialSet.Nerve`; `CostructuredArrow.proj`, `map`,
`map₂` in `Mathlib.CategoryTheory.Comma.StructuredArrow.Basic`;
`SSet.toTop`, `TopCat.toSSet`, `TopCat.toSSetObjEquiv`, `sSetTopAdj`,
`SSet.stdSimplexToTop` in `Mathlib.AlgebraicTopology.SingularSet`;
`SimplexCategory.toTop` and `SimplexCategory.toTopHomeo` and the standard interval
homeomorphism. The categorical/internal-hom currying is the existing
`MonoidalClosed.uncurry`; no second definition of singularization is introduced.

All eight proof dependencies are retained as imports, with public status only
where needed to express the statement. The module docstring carries the full
8-step proof: two-sided bisimplicial resolution; row replacement; equifibered
fiber theorem; transfer by fiber detection; column contraction; prism comparison;
endpoint-preserving reparametrization; naturality. In particular the substantive
`Sheaf.AlgebraicTopology.EquifiberedBisimplicialDiagonal` import remains.

### Edge cases

- Empty `E`: every comma nerve and the source of the fiber arrow are empty, so
  the comparison, its point coordinate, and the singular-prism formula are the
  unique empty maps; the claimed weak equivalence has the correct empty fibers.
- Empty `B`: `U` can exist only from an empty `E`; the family over `b` and its
  naturality clauses have no instances. No `Nonempty` binder was introduced.
- `B` terminal: the comma category is `E`. The transformation has constant target,
  and the comparison is the expected singular-nerve identification with the
  fiber over a point.
- `U = id_B`: each comma `B/b` is contractible, matching the contractible homotopy
  fiber of the identity. This is a check, not an extra hypothesis.
- A point mapping to `BG`: the comma category is the discrete set `G`; its nerve
  is not assumed contractible, agreeing with the loop fiber of `BG`.
- `U : E → [1]`: the one nonidentity transition must be weak; the hypothesis is
  substantive and excludes the point over `1`: the comma at `0` is empty,
  while the comma at `1` is a point.
- The prism at degree zero has the two endpoints and the arrow `α`; at degree
  one it includes the mixed arrow `αᵢ = U(hᵢⱼ) ≫ αⱼ`, correctly oriented.
  Constant-zero and constant-one `θ` give the two endpoint maps in every degree.

### Searches and source check

Fresh searches via the prescribed `msearch.py Q30 <item>` wrapper:

- `leanfinder`: “Quillen theorem B comma category nerve is homotopy fiber when
  postcomposition comma transition functors are weak equivalences” returned
  8 nerve-adjunction hits, including `homToNerveMk`, `nerveAdjunction`,
  `nerveFunctorCompHoFunctorIso`, and `nerveMap`. Read their relevant source
  signatures/docstrings in `NerveAdjunction.lean` and `Nerve.lean`; they construct
  the ordinary nerve/adjunction, not Theorem B.
- `loogle`: `"Comma", "nerve"` returned zero hits.
- `grep`: `QuillenB|quillen_b|comma.*homotopy|homotopy.*comma` in
  `AlgebraicTopology` returned zero hits.
- `rg` of the source project for the item id returned no hits. Searches for
  `quillen`, `Quillen`, and comma/homotopy-fiber combinations found no source
  implementation of the theorem.
- `rg` of `lean/Sheaf` found the parent
  `QuillenBDiscreteFibrationBaseChange.lean`, whose theorem is base change along
  a discrete fibration, with this item in its proof. Read that module in full.
  It is downstream, not a duplicate of the point-fiber theorem. Its
  `quillenBNerveFunctor` abbreviates `RN` on `Cat`, and its path pullback is a
  different construction; this module uses literal functor composition rather
  than importing a downstream theorem or duplicating that abbreviation.
- Searches for `QuillenBComma|quillenBComma|IsQuillenBComparison|quillenB_comma`
  in the project and source gave no existing declaration under these names.

Read Cisinski's online `CatLR.pdf`, Corollary 4.6.12, printed p. 183 / PDF index
198, and the preceding Proposition 4.6.11. The source is the overcategory form:
its square is homotopy Cartesian; applying it to opposite categories gives the
postcomposition comma convention here. Contracting the base slice gives the
point fiber and its induced natural comparison. The archival-copy WANTED note
in the existing node is retained. Source URL:
https://cisinski.app.uni-regensburg.de/CatLR.pdf

### Maintenance handoff and validation

The route note records the durable prerequisite-cycle repair at live `82ea37a3`
and side `279aa08c`, preserved in the subsequent sync. I inspected the two
shared nodes: `lem-coef-sharp-simplex-criterion` and
`lem-coef-ex-infinity-finite-products` still cite
`lem-coef-kan-quillen-model-right-proper-core`. This delivery does not touch
those nodes, the item's substantive proof, search records, or source citations.
The stage-2 sandbox initially contained only dispatcher marker files, so the
Lean candidate and this report were written in this run.

The required `scompile.py` file-only check compiled both its sandbox probe and
module cleanly (2.6 seconds each). One initial elaboration error confused the
realized simplex with the topological simplex used by singular simplices; the
final formula uses the latter's `ULift.down`, with no change of universes.
All variables and the universe are explicitly bound; `autoImplicit` is false.
There are no `#check` lines or local notation/instances. The remaining theorem
proof is deliberately `sorry`, as required in stage 2. No statement dispute,
statement correction, new node, or dependency-record repair is needed.

The prescribed `deliver2.py ... --no-push` dry run passed at `ef20d0fd91`,
with only the independent second-reading section reserved for the second reader.
The edge-case example for a point mapping into `[1]` was corrected in this report
after that run; the Lean and node were unchanged. A final dry run was requested.

## Second reading by Q30

I independently read the sandbox node and Lean module together, then opened the
three statement dependencies and their recorded modules. There is no
`coord/repair-notes/lem-coef-quillen-b-comma-homotopy-fiber.json` in the shared
checkout. The node has no `statement_change`; its mathematical statement and
all eight proof steps agree with the shared node. The delivery adds only its
Lean record and the two already recorded proof dependencies needed to name
coordinates and the cylinder comparison in the statement.

Source check: I opened Cisinski's `CatLR.pdf` online and read Corollary 4.6.12
and Proposition 4.6.11 on printed pp. 182–183 (PDF indices 197–198).
The corollary concerns arbitrary small ordinary categories, assumes weak
equivalences of the contravariant undercategory transitions, and concludes that
the nerve square over the base undercategory is homotopy Cartesian. Passing to
opposites gives this node's covariant costructured-arrow convention. Contracting
the base slice gives the point fiber. There are no ambient finiteness,
nonemptiness, contractibility, or fibrancy assumptions on the ordinary categories.
The specific prism comparison is the natural map of that square. No Stacks tag
is claimed for this item; its source is the cited Cisinski corollary.

The node's objects, hypotheses, and conclusions, matched individually:

1. **Small ordinary categories and a functor.** The binders
   `{E B : Type u} [SmallCategory E] [SmallCategory B] (U : E ⥤ B)`
   introduce exactly these data. The universe is explicitly quantified, and all
   other objects, variables, categories, and instances are bound. Verdict: exact.
2. **The comma category.** `CostructuredArrow U b` has an object with
   `.left : E` and `.hom : U.obj .left ⟶ b`. In Mathlib's source,
   `CostructuredArrow.w` reads `U.map h.left ≫ Y.hom = X.hom`.
   Thus its arrows satisfy precisely the node's relation. The existing
   `CostructuredArrow.proj U b` forgets the structure arrow. Verdict: exact,
   with no private definition of comma categories.
3. **Every comma transition is weak.** `hU` quantifies all `b₀ b₁ β` and applies
   `IsWeakHomotopyEquivalence` to
   `nerveMap (CostructuredArrow.map (S := U) β)`. I read `map` and `map_mk`:
   the structure arrow becomes `α ≫ β`, in the required direction.
   There is no hypothesis on unrelated arrows or on contractibility. Verdict: exact.
4. **Nerve, replacement, and characteristic unit.** `nerve` and `nerveMap`
   are Mathlib's ordinary nerve and induced map. The literal composite
   `SSet.toTop ⋙ TopCat.toSSet` is exactly `R = Sing|-|`.
   I read `TopCat.toSSetObjEquiv`, `sSetTopAdj_unit_app_app_down`, and
   `SSet.stdSimplexToTop` in `SingularSet.lean`; they identify singular simplices
   with continuous maps on the standard simplex and the unit with the
   characteristic map. Verdict: exact; no arbitrary Kan replacement.
5. **The specified base vertex and target fiber.** `quillenBCommaVertex b`
   applies this unit to `nerveEquiv.symm b`; its degree-zero continuous map is
   the constant simplex at the original object vertex. `quillenBCommaFiber U b`
   unfolds to the dependency's `homotopyFiber (R.map (nerveMap U))` at that
   vertex. I read `homotopyFiber`, `comma`, and `commaSubcomplex`: the `true`
   convention imposes the image at endpoint zero and the fixed point at endpoint
   one in every degree. Verdict: the correct fiber and path direction.
6. **The forgetful coordinate of the canonical map.** The first equality in
   `IsQuillenBCommaComparison` requires `c ≫ homotopyFiberProjection _ _` to be
   `R.map (nerveMap (CostructuredArrow.proj U b))`.
   The imported projection is the first projection of that very subcomplex.
   Verdict: exact, rather than an arbitrary equivalence to the fiber.
7. **The entire natural-transformation path coordinate.** The predicate's `P`
   has domain `nerve (CostructuredArrow U b) ⊗ Δ[1]`. For each `(x,θ)`, its
   object equations choose `U(xᵢ)` or `b`, and its arrow equations choose
   `U(hᵢⱼ)`, `αᵢ`, or `id_b` according to the switch. These specify every
   arrow, including identities and nonadjacent arrows. `HEq` permits the
   corresponding endpoint equalities without choosing transports and retains
   the arrow requirement. The equation
   `H.comp (SSet.realizationCylinderComparison _) = (SSet.toTop.map P).hom`
   fixes the realized homotopy. I read that comparison's actual data and its
   homeomorphism theorem: its interval coordinate is the sum of barycentric
   coordinates where `θ(i)=1`.
   The final equation of the predicate quantifies every `n`, singular `σ`,
   interval simplex `θ`, and topological-simplex point `t`. Its left side
   uncurries `c ≫ homotopyFiberPath`; its right side is
   `H(σ(t), |θ|(t))`, using the characteristic singular interval followed by
   `stdSimplexHomeomorphUnitInterval`. The `.down` removes the standard
   topological simplex's existing `ULift`, with no size restriction.
   Verdict: exactly realization, singularization, and restriction along the
   specified `Δ¹ → Sing([0,1])`, with all higher simplices retained.
8. **Existence and weak equivalence for each object.** The conclusion supplies
   `∃ c : ∀ b, ...`, with
   `∀ b, IsQuillenBCommaComparison U b (c b) ∧ IsWeakHomotopyEquivalence (c b)`.
   The existential is appropriate here: the object and arrow formulas determine
   `P`, the cylinder comparison determines `H`, and the equation on all singular
   simplices determines the path coordinate. Together with the first coordinate
   this determines the map into the existing subcomplex. No definition obtains
   data by choosing from this postponed existence theorem. Verdict: exact.
9. **Strict-square data and comma functor.** The naturality clause introduces
   `E' B' U'`, then the same transition hypothesis for `U'`, and `F G comm b`,
   with `comm : U ⋙ G = F ⋙ U'`. The second base object is literally `G.obj b`.
   `quillenBCommaSquare` is `CostructuredArrow.map₂ (eqToHom comm.symm) (𝟙 _)`.
   I read `map₂`: the transformation has precisely the direction
   `F ⋙ U' ⟶ U ⋙ G`, so the image is `(F(e),G(α))` with the transports forced
   by strict commutativity. Verdict: exact.
10. **Induced fiber map and naturality equation.** The quantified `c'` satisfies
    the same canonical-coordinate predicate. The resulting `t` is specified by
    both `t ≫ homotopyFiberProjection = homotopyFiberProjection ≫ RNF` and
    `t ≫ homotopyFiberPath = homotopyFiberPath ≫ (ihom Δ[1]).map RNG`.
    The last equality is `RN(commaSquare) ≫ c' = c b ≫ t`.
    Since the fiber is a subcomplex of the product, the two equations determine
    the induced fiber map. Allowing every canonical `c'` expresses the required
    naturality independently of its witness. Both functors carry the required
    transition hypothesis. Verdict: exact.

Edge cases were checked against the actual binders and coordinate formulas.
Empty `E` gives empty comma nerves, empty singular realizations, and empty
fibers; empty `B` leaves no base vertex to check. Neither case is excluded by an
instance. A terminal base gives the fiber of `RN(E) → *`; `U = id` gives the
contractible slice and identity fiber. A point mapping into a group category
has comma category the discrete group, illustrating why contractibility must
not be imposed. For `[1]`, a point over `1` fails the transition hypothesis
(empty comma at `0`, singleton comma at `1`); thus the premise is substantive.
At `n=0`, constant `θ` selects exactly the two endpoints. At `n=1`, the switch
arrow is `αᵢ`, with compatibility `U(hᵢⱼ) ≫ αⱼ = αᵢ`. General `n` and degenerate
simplices are quantified in the predicate. There are no field, characteristic,
scheme, or zero-object parameters. All small categories can be considered in a
common universe; no independent smaller test universe or equality between
unrelated site universes is imposed.

Independent searches, with different phrases from the worker's searches:

- `msearch.py ... leanfinder "overcategory nerve realizes the homotopy fiber of
  a functor under base change weak equivalences"` returned eight ordinary
  nerve/adjunction hits (`homToNerveMk`, `nerveMap`, `nerveFunctor`,
  `nerve.functorOfNerveMap`, among others). I opened the nerve and nerve-adjunction
  source; none states Quillen B or specifies this comparison.
- `msearch.py ... loogle '"CostructuredArrow", "IsWeakHomotopyEquivalence"'`
  returned zero hits.
- `msearch.py ... grep 'Theorem B|theorem B|homotopy.*fibre|homotopy.*fiber'
  CategoryTheory` returned ordinary categorical references, no comma theorem.
- Direct `rg` on Mathlib's category theory and algebraic topology directories,
  the upstream `WeilConjectures/`, and this project's `lean/Sheaf`, using Quillen,
  Theorem B, and comma/homotopy-fiber phrases found no exact theorem. Upstream's
  Serre Theorem B is unrelated. I opened the project's
  `QuillenBDiscreteFibrationBaseChange.lean`: it states a different base-change
  comparison and explicitly uses this item in proof step 4, so it cannot replace
  this theorem. The other comma-fiber hits concern mapping spaces or coherent
  cones, not ordinary comma nerves under the transition hypothesis.
- The new helper names and theorem name have no upstream-name-index match.
  Existing notions are reused: costructured arrows, nerve, singularization,
  homotopy fiber, its coordinates, and realization-cylinder comparison.

There are no new definition nodes or dependency modules to review. All three
statement dependency records provide the exact definitions used above; none
needs a repair. All recorded proof-dependency modules are imported. The four
helpers contain real defining expressions, the sole theorem remains `sorry`,
and every declaration has its source and blueprint docstring. The theorem's
docstring follows all eight node proof steps, including diagonal replacement,
fiber transfer, column contraction, the prism, relative reparametrization, and
naturality. No private notation, local instances, unbound universe variables,
`let` binders in the signature, or overlong Lean lines occur. The node's
`lean.statement` is byte-for-byte the signature before `:= by`.

**Mismatches and changes:** no mathematical mismatch was found, and no Lean or
node repair was needed. I appended this independent reading, its source check,
clause correspondence, edge cases, and fresh searches. The required wrapper
compiled the exact delivered module cleanly: sandbox probe 2.1 seconds, module
2.6 seconds, no errors or warnings. Compilation used the absolute sandbox path.

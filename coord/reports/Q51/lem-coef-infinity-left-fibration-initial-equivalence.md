## Worker report

The delivery writes `SSet.Enhanced.initial_left_fibration_equivalence` in
`lean/Sheaf/CategoryTheory/InitialLeftFibrationEquivalence.lean`. Its proof is the
required `sorry`. The module also defines the auxiliary predicate
`SSet.Enhanced.IsNaturallyEquivalentOver`; this belongs to the item's own notion
of a coherent natural equivalence over a common base and has real data. No new
independent DAG node, dependency repair, statement correction, or disputed clause
was needed.

Source checked: Kerodon Corollary the project server, tag 03J6 (the online statement and
proof, including the reference to Proposition the project server). The source diagram has
left fibrations over one common infinity-category and says that a functor carrying
an initial object to an initial object is an equivalence. The item's explicit
strict-over-base inverse and coherent inverse witnesses are rendered below.

The Lean statement renders every hypothesis and conclusion clause as follows.

- The one sufficiently large fixed universe is the single explicit universe `u`
  in `E F B : SSet.{u}`. The three objects are quasicategories through
  `[Quasicategory E] [Quasicategory F] [Quasicategory B]`; no extra size equality,
  nonemptiness, or Kan hypothesis is added.
- The maps of the diagram are `p : E ⟶ B`, `q : F ⟶ B`, and `u : E ⟶ F`.
  The hypotheses `hp : leftFibration p` and `hq : leftFibration q` use exactly
  the recorded left-fibration definition (all horns with `n ≥ 1`, `i < n`).
  Commutativity over the base is `hu : u ≫ q = p`, i.e. `q ∘ u = p`.
- The chosen object is `e : E.obj (op ⦋0⦌)`, with initiality
  `he : IsInitial E e`. Its image is the actual degree-zero map
  `u.app (op ⦋0⦌) e`, and the second initiality premise is
  `hue : IsInitial F (u.app (op ⦋0⦌) e)`.
- The conclusion supplies an actual simplicial map `v : F ⟶ E`. The equation
  `v ≫ p = q` is the required strict equality `p ∘ v = q`.
- `IsNaturallyEquivalentOver p (u ≫ v) (𝟙 E)` is the coherent equivalence
  `vu ≃ id_E` over `B`; `IsNaturallyEquivalentOver q (v ≫ u) (𝟙 F)` is
  `uv ≃ id_F` over `B`. Composition order is categorical (`u ≫ v` means
  `v ∘ u`).

The auxiliary `IsNaturallyEquivalentOver r F G` is an explicit expansion of the
node's final convention. It supplies an edge `e`, its inverse edge `g`, and the
two triangle simplices `t` and `s` in the internal functor simplicial set. Its
first eight equations are respectively the endpoints of the natural edge and
the two inverse triangles, exactly the equations in
`SSet.Enhanced.IsEquivalenceEdge`. It then requires, separately for **all four**
simplices `e`, `g`, `t`, and `s`, that their Yoneda maps postcomposed with
`(ihom C).map r` equal the corresponding constant simplex at `diagramVertex r`.
Thus every degree of the transformation and both inverse-equivalence witnesses
compose to `r` followed by the projection, as required for a coherent
transformation in the functor simplicial set over the base. No witness is merely
an unconnected equivalence in the ambient functor category.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: recorded dependency
  `SSet.Enhanced.coneCategory`; the source file was read in full. The item uses
  its declarations `SSet.Enhanced.IsInitial`, `diagramVertex`,
  `IsEquivalenceEdge`'s explicit four-simplex equations, and the simplicial
  internal-hom operations. The recorded `coneCategory` declaration is the
  aggregate owner of these helpers.
- `Sheaf.CategoryTheory.InfinityFibrations`: recorded dependency
  `SSet.Enhanced.cocartesianFibration`; the source file was read in full. The
  item uses its exact `SSet.Enhanced.leftFibration` predicate. No cocartesian or
  cartesian lift property is silently substituted.

Edge cases checked before writing:

- If `E` is empty there is no `e`, so the implication is vacuous; no hidden
  inhabitedness assumption was introduced. If `F` or a fiber of `q` is empty,
  the explicit initiality premise and the strict map equations retain their
  intended meaning.
- For `B = Δ[0]`, the statement reduces to the usual initial-object criterion
  for a map between left-fibration quasicategories. For `E = F = B = Δ[0]`,
  the identity map and identity inverse satisfy all four over-base simplex
  equations.
- For `B` empty, any map over `B` has the required strict equation only when
  its source is correspondingly empty; the theorem adds no nonemptiness or
  point-selection condition.
- The `n = 1` left-fibration horns are retained by the imported definition;
  no positive-dimensional or nondegeneracy case is omitted.

Searches for an existing declaration (2026-10-17):

- `msearch.py ... leanfinder "initial object criterion for a map between left
  fibrations of quasicategories"`: returned eight hits, all unrelated
  bicategorical initial objects, simplex-category initial inclusions, or ordinary
  Kan/model fibrations; no matching theorem.
- `msearch.py ... loogle "SSet.Enhanced.IsInitial, SSet.Enhanced.leftFibration,
  SSet.Enhanced.AreNaturallyEquivalent"`: zero hits (the project declarations
  are not identifiers known to Loogle).
- `msearch.py ... grep "left.?fibration|IsInitial|NaturallyEquivalentOver"
  Mathlib/AlgebraicTopology`: zero hits.
- `rg` over `WeilConjectures/`, `lean/Sheaf`, and all `dag/nodes` for the item
  name and the theorem wording found no existing declaration. The only DAG hits
  are the item's own record and its legitimate citer
  `lem-coef-twisted-arrow-left-fibration`.

The module compiles cleanly with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q51
lem-coef-infinity-left-fibration-initial-equivalence
/home/ubuntu/weil-newtargets-stage2-sandbox/Q51/lem-coef-infinity-left-fibration-
initial-equivalence/lean/Sheaf/CategoryTheory/InitialLeftFibrationEquivalence.lean`.

## Second reading by Q51

I reread the node, its Kerodon source (Corollary the project server, tag 03J6), both
statement dependencies, and the complete module independently. The item introduces
one fixed universe `u`, quasicategories `E`, `F`, and `B`, structure maps `p : E ⟶ B`
and `q : F ⟶ B`, and a map `u : E ⟶ F`. These render as the corresponding
binders and typeclass assumptions in `initial_left_fibration_equivalence`; no universe,
category, or size assumption is added. The hypotheses `hp` and `hq` are exactly
`leftFibration p` and `leftFibration q` from `InfinityFibrations`, and `hu : u ≫ q = p`
is precisely the source's commutative triangle. The chosen vertex is
`e : E.obj (op ⦋0⦌)` with `he : IsInitial E e`, and its image is the actual
`u.app (op ⦋0⦌) e` with `hue : IsInitial F ...`; neither initiality premise is
weakened or strengthened.

The existential conclusion has `v : F ⟶ E` and `v ≫ p = q`, giving the strict
map over `B`. Its two remaining conjuncts are
`IsNaturallyEquivalentOver p (u ≫ v) (𝟙 E)` and
`IsNaturallyEquivalentOver q (v ≫ u) (𝟙 F)`, in the same order as the source's
two inverse equivalences. `IsNaturallyEquivalentOver` supplies the edge, inverse
edge, and both triangle 2-simplices in the internal functor simplicial set, with
the endpoint and triangle equations of `IsEquivalenceEdge`; it additionally forces
the postcomposition of each of all four simplices with the base map to be the
corresponding constant simplex. Thus the inverse witnesses themselves remain over
`B`, exactly as the node's final convention requires. The existing
`AreNaturallyEquivalent` declaration was checked; it does not encode this
all-witness strict-over-base condition, so the helper is part of this item's notion,
not a duplicate of that weaker declaration.

No mismatch was found and no file or node field was changed. In particular, no
extra preservation, cartesian/cocartesian, Kan, inhabitedness, or finiteness
hypothesis appears, and no conclusion clause is omitted. Composition directions
were checked against categorical notation (`u ≫ v` is `v ∘ u`).

Edge cases reviewed: an empty `E` makes the quantified vertex premise unavailable
and hence the implication vacuous; empty `F` or fibers impose no hidden
inhabitedness beyond the stated initiality; `B = Δ[0]` specializes to the ordinary
initial-object criterion; `E = F = B = Δ[0]` admits the identity data; an empty
base introduces no extra point; and the `n = 1` left-fibration horns are retained
by the imported predicate. The shared universe permits all these cases.

Searches were independently checked on 2026-10-17: LeanFinder for the initial-object
criterion, Loogle for `LeftFibration` and `IsInitial`, and grep over Mathlib's
algebraic-topology sources; all returned only unrelated ordinary-category or
Kan/model-fibration declarations. Grep over `WeilConjectures/`, the repository's
`lean/Sheaf`, and all DAG nodes found no existing theorem or duplicate helper.
The dependency files were opened directly: `SSet.Enhanced.IsInitial`,
`diagramVertex`, and the internal-hom conventions come from
`EnhancedDiagramsCones`, while `leftFibration` comes from `InfinityFibrations`.
The required `scompile.py` check passed for the module with only the expected
`sorry` warning.

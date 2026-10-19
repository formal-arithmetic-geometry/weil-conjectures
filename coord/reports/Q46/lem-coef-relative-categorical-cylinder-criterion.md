## Worker report

The module `Sheaf.CategoryTheory.RelativeCategoricalCylinderCriterion` states
`SSet.Enhanced.relative_categorical_cylinder_criterion`, with one `sorry` and no
other postponed proof. It also constructs the endpoint pushout map, the cylinder
structure and the strict relative functor subcomplex explicitly. These helpers
are notions introduced in this node's own statement and are listed in
`lean.declarations`; no new node or dependency repair is needed. The item's only
changed field is `lean`.

Source checked directly: Kerodon Definition the project server
<https://kerodon.net/tag/01K5> and Corollary the project server
<https://kerodon.net/tag/01KD>. The source and node agree. No statement correction
or STATEMENT-DISPUTED issue is needed.

The following matches every hypothesis and clause of the node:

- Small simplicial sets are `A B Q : SSet.{u}`. The degreewise subset inclusion is
  `i : A ⟶ B` with `hi : ∀ n, Function.Injective (i.app n)`. This allows every
  simplicial subset, represented by a monomorphism, without choosing its image.
- `B ⨿_A B` is Mathlib's `pushout i i`, the presheaf pushout, computed degreewise.
  `endpointPushoutMap i s₀ s₁ h` is exactly `pushout.desc s₀ s₁ h`.
- The arbitrary relative cylinder is `c : RelativeCategoricalMappingCylinder i`.
  Its fields `carrier`, `s₀`, `s₁`, `π` introduce the small simplicial set and all
  three prescribed maps. `section₀` and `section₁` say `s₀ ≫ π = 𝟙 B` and
  `s₁ ≫ π = 𝟙 B`. `relative` says `i ≫ s₀ = i ≫ s₁`.
  `endpoint_injective` requires the canonical pushout map to be injective in every
  degree, not just on vertices.
- `categoricalEquivalence` is the test from the recorded Joyal dependency:
  restriction induces an equivalence of the ordinary homotopy categories of
  internal functor objects for every quasicategory `T : SSet.{max u v}`, after
  the canonical `uliftFunctor.{v,u}` on the small inputs. Both universes are
  explicitly bound; the cylinder carrier and the original diagrams remain small
  in `u`. The testing universe is arbitrary. No separate cores-based predicate
  or alternative categorical-equivalence definition is introduced.
- `[Quasicategory Q]` is precisely the target quasicategory hypothesis.
  The maps are `f_A : A ⟶ Q`, `f₀ f₁ : B ⟶ Q`; `h₀ : i ≫ f₀ = f_A` and
  `h₁ : i ≫ f₁ = f_A` give their common restriction.
- `relativeFunctorSubcomplex i f_A` is a subcomplex of `(ihom B).obj Q`.
  In each degree `n`, its simplices `z` satisfy
  `((MonoidalClosed.pre i).app Q).app n z =
  (SSet.const (X := (ihom B).obj Q) (diagramVertex f_A)).app n z`.
  Under the existing internal-hom convention, this says exactly that the entire
  map `B × Δⁿ → Q` restricts to `f_A` composed with projection on `A × Δⁿ`.
  Naturality of these two maps supplies closure under all operators, with real
  proof data and no `sorry`.
- The equivalence assertion quantifies over an edge of that subcomplex's
  `toSSet`. `RelativeEquivalenceEdge` gives source and target by the underlying
  values of `δ 1 e` and `δ 0 e`, equal to `diagramVertex f₀` and
  `diagramVertex f₁`. It invokes the dependency's `IsEquivalenceEdge` on the
  relative simplicial set itself. Thus the inverse edge and both triangular
  witnesses belong to the strict relative fiber as the node requires.
- The other side of the `↔` is `∃ f : c.carrier ⟶ Q,
  c.s₀ ≫ f = f₀ ∧ c.s₁ ≫ f = f₁`. Both extension equations are literal
  equalities, for the given cylinder. No choice of another cylinder occurs.
- The case `A = ∅` is included by the same formula: the internal functor object
  out of the empty simplicial set is terminal degreewise, so the restriction
  equality is vacuous and the subcomplex is all of `Fun(B,Q)`.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsEquivalenceEdge` (the inverse and two triangular witnesses),
  `SSet.Enhanced.diagramVertex` (the vertex associated to a simplicial map),
  and Mathlib's internal hom, simplicial sets, subcomplexes and quasicategories
  imported by this dependency. The recorded main `coneCategory` signature and
  its helper construction/docstring were read too; cones are not needed here.
- `Sheaf.AlgebraicTopology.JoyalModelStructure`:
  `SSet.exists_joyal_model_structure`; its full signature and proof docstring
  fix the precise homotopy-category testing condition used in the cylinder.
  The theorem is imported publicly because this is a statement dependency.
- `Sheaf.CategoryTheory.IsofibrationExponentiation`:
  `SSet.Enhanced.isofibration_exponentiation` and `IsIsofibration`; this is an
  ordinary proof import. The complete restriction and equivalence-edge lifting
  signatures and docstrings were read. The other proof dependency,
  `lem-coef-quasicategory-invertible-interval`, has no recorded Lean module in
  the base, so its future import is left for the maintainer. The proof docstring
  names it explicitly and includes all five steps of the node's proof.

Edge cases checked: `A = ∅` as above; `A = B` forces the cylinder sections to
coincide and the relative functor object to have only constant simplices, so both
conditions reduce to equal endpoints; `B = ∅` forces its retracting cylinder
empty degreewise; `Q = ∅` admits maps only from empty domains. Equal endpoints
are witnessed by degeneracy and extend by composition with `π`. For `B = Δ⁰`,
`A = ∅`, `Q = Δ¹`, the two distinct vertices have no equivalence and cannot
extend over a categorical cylinder, as required. No nonemptiness or finiteness
assumption was imposed.

Fresh duplication searches were performed with the prescribed wrapper (raw
records are in sandbox `searches.jsonl`):

- LeanFinder: "relative categorical mapping cylinder equivalence of diagrams in
  strict restriction fiber if and only if extension over cylinder" returned eight
  abstract precylinder/cylinder hits. They concern abstract model-category
  cylinders rather than the relative diagram-fiber criterion.
- Loogle: `SSet.Homotopy, CategoryTheory.Limits.pullback` returned zero hits.
- LeanSearch: "relative categorical mapping cylinder extension equivalence
  diagrams" returned eight hits on ordinary Kan extensions, abstract cylinders,
  equivalence extensionality, chain-complex homotopies and categorical pullbacks;
  none states this result.
- Mathlib grep via msearch: `RelativeCategoricalMappingCylinder|relative.*[Cc]ylinder|
  Fun.*relative` under `AlgebraicTopology` returned fourteen hits, chiefly abstract
  left homotopies and unrelated homological constructions. Direct `rg` for
  `Categorical.*[Cc]ylinder|[Rr]elative.*[Ff]unctor|[Ff]unctor.*[Ff]iber` found only
  unrelated Eilenberg-Steenrod relative homology.
- `rg` in `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `relativeFunctorSubcomplex`, `RelativeCategoricalMappingCylinder`,
  `RelativeEquivalenceEdge`, and `relative_categorical_cylinder_criterion` found no
  declaration. Exact item-id search in the source tree found no match. A broader
  search for relative functors, strict fibers and mapping cylinders also found
  no existing version of these notions.

Repairs to the earlier sandbox attempt: added the omitted degreewise-injective
hypothesis on `i`; replaced ambient equivalence plus a constant-edge restriction
by an actual equivalence in the explicitly constructed relative fiber; replaced
its cores-based categorical-equivalence field by the recorded Joyal test;
removed the unnecessary added coherent-nerve dependency; added the available
proof import; expanded the five-step proof docstring and corrected the node
signature/date. The earlier second-reading text described an obsolete file and
has been removed so the independent second reader can review the current file.

Validation: `scompile.py Q46 lem-coef-relative-categorical-cylinder-criterion`
compiled this module cleanly with no errors or warnings. The required `deliver2.py ... --no-push` returned exit code 0:
`OK (dry run): commit a8ed52f692 compiles and passes the preflight except for the
second reading, which the second reader writes; nothing pushed.`
This is the wrapper's authorized worker completion result. The independent
second reading remains for the second reader, who alone delivers.

## Second reading by Q46

I independently read the node, its Kerodon source places, the dependency declarations, and the
current module. The node's statement decomposes as follows, with the corresponding Lean rendering
and verdict:

- The objects are small simplicial sets `A B Q : SSet.{u}`, a simplicial map
  `i : A ⟶ B`, and a degreewise simplicial-subset hypothesis. Lean renders these as
  `{A B Q : SSet.{u}}`, `(i : A ⟶ B)`, and
  `hi : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (i.app n)`. This is exactly the
  monomorphism/subset condition and introduces no stronger finiteness or nonemptiness assumption.
- The target `Q` is a quasicategory. Lean has `[Quasicategory Q]`, exactly the recorded
  dependency convention.
- The maps `f_A : A ⟶ Q` and `f₀ f₁ : B ⟶ Q` have equal restriction to `A`. Lean has
  `h₀ : i ≫ f₀ = f_A` and `h₁ : i ≫ f₁ = f_A`; both equalities are present and have the
  node's direction.
- A relative categorical mapping cylinder consists of a small carrier, sections `s₀ s₁`,
  retraction `π`, categorical equivalence of `π`, section identities, agreement on `A`, and
  a degreewise-injective endpoint pushout map. Lean packages these as
  `c : RelativeCategoricalMappingCylinder.{u, v} i`. Its fields are `carrier`, `s₀`, `s₁`,
  `π`, `categoricalEquivalence`, `section₀`, `section₁`, `relative`, and
  `endpoint_injective`. The equivalence field tests every quasicategory
  `T : SSet.{max u v}` using the exact `hoFunctor` criterion from
  `SSet.exists_joyal_model_structure`; since `v` is universe-polymorphic this covers the
  sufficiently-large testing universes in the node. The endpoint map is
  `endpointPushoutMap i s₀ s₁ relative := pushout.desc s₀ s₁ relative`, so it is the
  canonical map from `B ⨿_A B`, not an arbitrary map.
- The relative functor simplicial set is rendered by
  `relativeFunctorSubcomplex i f_A`. Its degree-`n` predicate is equality of the restriction
  `(MonoidalClosed.pre i).app Q` with the constant simplex at `diagramVertex f_A`, so it is
  precisely the strict fiber `Fun_{f_A}(B,Q)` described by the node. The closure proof is
  supplied for all simplicial operators.
- The left side of the conclusion is an edge
  `e : (relativeFunctorSubcomplex i f_A).toSSet _⦋1⦌` satisfying
  `RelativeEquivalenceEdge i f_A f₀ f₁ e`. This requires source `δ 1 e = diagramVertex f₀`,
  target `δ 0 e = diagramVertex f₁`, and `IsEquivalenceEdge` in the relative subcomplex;
  the latter includes the inverse edge and both triangular witnesses in that same strict fiber.
  This exactly expresses isomorphism in the infinity-category of relative functors under the
  node's inverse-and-two-triangle convention.
- The right side is
  `∃ f : c.carrier ⟶ Q, c.s₀ ≫ f = f₀ ∧ c.s₁ ≫ f = f₁`, with both endpoint equations
  and the prescribed cylinder. Quantifier order and conjunctions match the node exactly.

The source check was against Kerodon Definition the project server (tag 01K5), which defines the cylinder
by a categorical equivalence retraction, agreeing sections on `A`, and a monomorphism from the
pushout, and Corollary the project server (tag 01KD), whose two equivalent conditions are isomorphism of
`f₀,f₁` in `Fun_{A/}(B, C)` and extension over the cylinder. The Lean statement is the explicit
simplicial edge formulation of that isomorphism, as required by the node's dependency.

I found no mismatch requiring repair. In particular, `hi` is the needed explicit rendering of
"simplicial subset"; `endpoint_injective` is the source monomorphism condition; the categorical
equivalence test has no extra quasicategory hypothesis on the cylinder; and no hypothesis about
`A`, `B`, `Q`, characteristic, finiteness, or universes is added. The module's helper definitions
are exactly the notions introduced by this node and are recorded in its `lean.declarations`.
The node's `lean.statement` is verbatim the theorem signature in the module.

Edge cases were checked independently: `A = ∅` makes the strict restriction condition vacuous
and gives the ordinary `Fun(B,Q)` case; `A = B` forces the two sections and endpoint diagrams to
agree on all of `B`; `B = ∅` and `Q = ∅` are allowed by the same typed quantifiers; equal endpoints
are represented by a degenerate equivalence edge; and no `n > 0`, nonempty-index, or finiteness
condition occurs. The universe variables are fully bound, and the cylinder's testing universe is
polymorphic rather than identified with `u`.

For one-definition-per-notion checks I reran searches in the project and source trees with `rg`
for `relativeFunctorSubcomplex`, `RelativeCategoricalMappingCylinder`,
`RelativeEquivalenceEdge`, `relative_categorical_cylinder_criterion`, and broader relative
mapping-cylinder/functor-fiber terms. I also reviewed the recorded LeanFinder, Loogle, LeanSearch,
and Mathlib grep searches in `searches.jsonl`. They found only abstract model-category cylinders,
relative homotopies, or unrelated homological constructions. No Mathlib, source, or existing
`lean/Sheaf` declaration states this criterion or defines these helpers. The dependency modules
`Sheaf.CategoryTheory.EnhancedDiagramsCones`, `Sheaf.AlgebraicTopology.JoyalModelStructure`,
and `Sheaf.CategoryTheory.IsofibrationExponentiation` were opened and their exact declarations
were used; no dependency repair or new node is needed.

Compilation with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q46 lem-coef-relative-categorical-cylinder-criterion lean/Sheaf/CategoryTheory/RelativeCategoricalCylinderCriterion.lean`
passed with only the intentional `sorry` proof. No file or node changes were necessary in this
second reading; I am delivering the reviewed worker module and node.

Additional independent search: LeanFinder query "An invertible natural transformation between two
diagrams fixed on a subcomplex exists precisely when their pair extends to a relative Joyal
cylinder" returned eight hits on `PreOneHypercover.cylinderHomotopy`, abstract
`HomotopicalAlgebra.Cylinder`/`Precylinder`, and abstract left-homotopy cylinder replacement.
I opened Mathlib's `Cylinder.lean` and `LeftHomotopy.lean`: these do not state the strict-fiber
quasicategory criterion. I also opened `RelativeMorphism.lean`: its `Homotopy` uses `Delta[1]`
and has no invertibility condition. Broader `rg` hits in the project for relative functors were
checked in `ModelWeakEquivalenceNerve`, `FiberCoconeSimplexExtension`, and
`MarkedRelativeCartesianModel`; these concern unrelated relative functors or marked over-category
mapping objects. There is no existing match. No repair note exists for this item.

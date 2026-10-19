## Worker report

Item: `lem-trf-hom-dual-preserves-homotopies`.
Module: `Sheaf.Algebra.Homology.ModuleHomPrecompHomotopy`.
The seven declarations recorded in `lean.declarations` jointly render every clause.
There are two actual definitions and five theorem statements with `sorry` proofs.
No new nodes, dependency repairs, or statement corrections are needed. The node copy
changes only `lean`.

The earlier Q25 failure confused the Q28 stage-1 split with completion of stage 2.
The current node is split and reviewed, but has no Lean record. Q28's retained report
is explicitly a stage-1 report, containing no Lean module. This delivery supplies
the missing stage-2 interface and does not repeat that split.

Hypotheses and clauses, read against the node:

| Node text | Lean rendering |
| --- | --- |
| A is a commutative ring | Explicitly declared `{A : Type u} [CommRing A]`. |
| P, R, T are cochain complexes of A-modules | Explicit section variables `P R L : CochainComplex (ModuleCat.{u} A) ℤ` and theorem binder `T` of that same type. |
| H_P and H_R are the module-valued total Hom complexes, with the given D | The existing `CochainComplex.moduleHomComplex P T` and `moduleHomComplex R T`, whose terms are `HomComplex.Cochain` and differential is `ModuleCat.ofHom (HomComplex.δ_hom A _ _ _ _)`. The coefficient action is retained. |
| f is a degree-zero chain map P → R | Binder `f : P ⟶ R`, using Mathlib's morphism of cochain complexes, including its differential commutation. |
| f*(φ) = φf, and f* is a chain map | `moduleHomPrecompComponent T f j` has actual linear-map data `(HomComplex.Cochain.ofHom f).comp φ (zero_add j)`. `moduleHomPrecomp_comm` states commutation with D; `moduleHomPrecomp` uses those components and that named verification theorem. |
| Identity is preserved | First conjunct of `moduleHomPrecomp_id_comp`, quantified over every complex Q, is `moduleHomPrecomp T (𝟙 Q) = 𝟙 (moduleHomComplex Q T)`. |
| (gf)* = f*g*, for any further L and g | Second conjunct is `moduleHomPrecomp T (f ≫ g) = moduleHomPrecomp T g ≫ moduleHomPrecomp T f`. Lean's diagrammatic composition reverses the notation order relative to function composition, exactly as needed. All three Hom targets are the same T. |
| f, f' and h satisfy f-f' = d_R h + h d_P | `{f f' : P ⟶ R} (h : Homotopy f f')`. Mathlib's `Homotopy` contains degree-minus-one maps, zero outside that degree, and `f = h d_P + d_R h + f'`, the equivalent additive identity. |
| S_h has degree minus one and S_h(φ) = (-1)^j φh | `moduleHomPrecomp_preserves_homotopies` concludes `∃ H : Homotopy ...`, with `H.hom j (j - 1) φ = j.negOnePow • (HomComplex.Cochain.ofHomotopy h).comp φ (by omega)` for every integer j and every homogeneous φ. The scalar is the integer sign as a unit, so negative j are included. |
| f* - f'* = D S_h + S_h D | The same H is a Mathlib `Homotopy` between the specified precomposition maps. Its `comm` field is exactly this identity after subtracting f'*. Its `zero` field supplies all off-degree zero components. The formula specifies every allowed component, rather than merely asserting an arbitrary homotopy exists. |
| T = A[0], P dual = Hom(P,A[0]), homotopic maps have homotopic duals | `moduleHomDual_preserves_homotopies` specializes the same actual `moduleHomPrecomp` to `(HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0).obj (ModuleCat.of A A)`. No alternative dual complex is defined. |
| Given homotopy inverses f and g, their specific dual maps are homotopy inverses | `moduleHomDual_preserves_homotopy_inverses` takes the two homotopies `hP : Homotopy (f ≫ g) (𝟙 P)` and `hR : Homotopy (g ≫ f) (𝟙 R)`. It returns a `HomotopyEquiv` from the dual of R to the dual of P, with equalities pinning `e.hom` to precomposition by f and `e.inv` to precomposition by g. Both inverse homotopies are fields of that same equivalence. |

Dependency declarations used:

- `def-sc-module-total-hom-complex`: imported recorded module
  `Sheaf.Algebra.Homology.ModuleHomComplex`, declaration
  `CochainComplex.moduleHomComplex`. I read the full module locally and through
  `scompile.py --source`; the server source agrees with the local source.
  Its actual terms and `δ_hom` differential are reused without a private copy.
- `def-weil-abstract-derived-category`: imported recorded module
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, with `DerivedCategory` and
  `HasDerivedCategory` as recorded. I read their signatures and docstrings.
  This item uses the underlying `CochainComplex` and chain-map notions supplied
  by that dependency; it does not need an extra derived-localization hypothesis.
- Mathlib's `Homotopy`, `HomotopyEquiv`, `HomComplex.Cochain.ofHom`,
  `HomComplex.Cochain.comp`, `HomComplex.Cochain.ofHomotopy`, and
  `HomologicalComplex.single` supply the remaining existing notions.
  Their complete signatures and definitions were read in the source. The linear
  data use existing `Cochain.comp_add` and `Cochain.comp_smul` verification proofs.

Every new postponed theorem is a clause of this same node: differential
commutation, identity/composition, the signed homotopy identity, its dual
specialization, and preservation of the specified inverse pair. Their docstrings
contain the natural-language proof. The main homotopy docstring also records
all five DAG proof steps and the two definition dependencies.

Searches made before writing, all through the required `msearch.py` wrapper:

- LeanFinder: `Precomposition by homotopic cochain maps induces a signed homotopy
  on the module valued total Hom complex`. Eight hits, including
  `Cochain.ofHomotopy`, `δ_ofHomotopy`, generic `mapBifunctorMapHomotopy`
  constructions, and `mappingCone.mapOfHomotopy`; no exact module-valued
  total-Hom precomposition statement.
- Loogle: `CochainComplex.HomComplex.Cochain.comp, Homotopy`. Two hits:
  `CochainComplex.mappingCone.descHomotopy` and `.liftHomotopy`; neither states
  this node.
- Mathlib grep: `moduleHomComplex|internalHomMap` in `Algebra/Homology`.
  No hits. Mathlib's generic HomComplex is additive-group-valued, while the
  recorded project definition retains A-modules.
- LeanSearch: `Precomposition on total Hom complexes preserves cochain homotopies
  and induces homotopy equivalences on dual complexes`. Eight hits, including
  `HomComplex`, `Cochain.toSingleMk_precomp`, `Cocycle.precomp`,
  `Cochain.ofHomotopy`, and model-category/right-homotopy precomposition.
  None is the stated total-Hom chain homotopy with its signed components.
- Direct `rg` in `lean/Sheaf` and upstream `WeilConjectures` for
  `moduleHomComplex`, precomposition/homotopy variants, and proposed names;
  direct item-id grep upstream; proposed-name grep in
  `dag/lean_names_upstream.json` and Mathlib. No existing full statement and
  no name collision. The private `koszulCechPrecomp` in
  `KoszulCechComparisonConstruction` has the same degree-zero component
  construction for that diagram, but is unavailable outside its owning module
  and contains none of this node's homotopy conclusions. It was not copied as
  a second public notion. The signed dual for natural-indexed chain complexes
  and the perfect ring dual on a ringed point use different categories and
  do not replace the unbounded ModuleCat Hom complex here.

Edge cases checked before writing and again against the signatures:

- Zero complexes, zero ring, zero maps, and the zero homotopy are allowed;
  no nontriviality, nonzero, boundedness or finite-generation hypothesis occurs.
- In degree j = 0 the sign is +1; in j = 1 and j = -1 it is -1.
  Expanding D S_h and S_h D cancels their d_T terms and leaves
  `φ(h d_P + d_R h)` in all three cases and in general.
- In characteristic two both opposite signs agree, and cancellation still
  holds additively; no characteristic restriction was introduced.
- The identity and composable-map clauses quantify over arbitrary complexes;
  no restriction on L or the fixed target T is hidden.
- For A[0], the existing single complex is genuinely supported in integer
  degree zero, with all differentials zero. No natural-indexed truncation or
  finite-product replacement of the unbounded total Hom was introduced.
- Universes follow the recorded moduleHomComplex interface with explicit u;
  there are no undeclared variables, independent index universes, or equalities
  imposed between unrelated site universes.

No `STATEMENT-DISPUTED` issue was found. In particular the sign in the node is
correct: the source differential gives the cancellation displayed in the DAG.

Validation: `scompile.py Q25 lem-trf-hom-dual-preserves-homotopies` compiled
the delivered module against the published library in 18.4 seconds, with no
errors or warnings. The delivery dry run repeats compilation and preflight.

## Second reading by Q25

No independent second reading by a worker: the dispatcher's current instructions
require direct delivery and the maintainer's independent review. I performed
the clause-by-clause author check above, with the node, source proof and module
open. This section does not claim an independent review.

## Worker report

The module `Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange` states
`AlgebraicGeometry.Etale.boundedBelow_derived_smooth_baseChange`, with one `sorry`
and no new definitions. It includes the allowable-torsion typing of both images,
which the upstream ambient-isomorphism theorem does not state.

Hypotheses and clauses, in the order of the node:

- The four schemes are `{X Y S T : Scheme.{u}}`, with the arrows
  `{h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}`.
- The chosen Cartesian square is `sq : ChosenCartesianSquare h e f g`.
  Its projection equations give the Cartesian square and commutativity, with
  exactly the orientation used by the abelian exchange declaration.
- Smoothness is `[Smooth f]`; quasi-compactness and quasi-separatedness are
  `[QuasiCompact g] [QuasiSeparated g]`. No properness, finite type, or
  cohomological dimension assumption is imposed.
- The fixed prime set is `S.invertiblePrimes`, namely
  `{p | p.Prime ∧ IsUnit (p : Γ(S, ⊤))}`. It is used for both source and target
  torsion conditions; no replacement by the primes invertible on X occurs.
- `K : AbelianDerivedCategoryPlusTorsionOfPrimes T S.invertiblePrimes` says
  that K is bounded below and every geometric stalk of every cohomology sheaf
  has positive annihilators with only those prime factors. There is no upper bound.
- `Lf^*Rg_*K` is `D(upperStar AddCommGrpCat.{u + 1} f).obj
  (R(lowerStar AddCommGrpCat.{u + 1} g).obj K.obj)`.
- `Rh_*Le^*K` is `R(lowerStar AddCommGrpCat.{u + 1} h).obj
  (D(upperStar AddCommGrpCat.{u + 1} e).obj K.obj)`.
- The first two conjuncts apply `allowableTorsionPlusProperty X S.invertiblePrimes`
  to these two objects. They assert precisely that both images belong to the
  specified full subcategory of the derived category of X, including boundedness below.
- The last conjunct is `IsIso (abelianDerivedBaseChangeArrow sq K.obj)`.
  This is the canonical unit/composition/counit exchange of the recorded dependency,
  not an unspecified isomorphism. In a full subcategory containing both endpoints,
  the ambient arrow and its inverse are morphisms of that subcategory, so the
  conjunction says exactly that this arrow is an isomorphism there.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`:
  `AlgebraicGeometry.Etale.abelianDerivedBaseChangeArrow`, the unbounded abelian
  unit-e/composition/counit-f arrow, with `D` exact inverse image and `R` total
  right derived image.
- `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso`:
  `AlgebraicGeometry.ChosenCartesianSquare.baseChangeInverseImageIso`, available
  through the map import; its square datum comes from
  `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`.
- `Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories`:
  `AlgebraicGeometry.Etale.allowableTorsionPlusProperty` and
  `AlgebraicGeometry.Etale.AbelianDerivedCategoryPlusTorsionOfPrimes`.
  These use abelian groups of universe u+1 and the unbounded ambient category.
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem`:
  `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth`, publicly
  imported via `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived`;
  the latter also supplies `AlgebraicGeometry.Scheme.invertiblePrimes`.
  The smooth sheaf theorem is a proof ingredient, not an extra hypothesis.

All already recorded proof-dependency modules are imported without `public` unless
already needed publicly by the statement. `sbc-thm-bounded-allowable-torsion` has no
recorded declaration in this snapshot, so there is no module to import for it;
it is a proof prerequisite, not an object missing from this statement. The
seven-step proof is in the theorem docstring, including the filtered-kernel torsion
argument and the finite hypercohomology filtration omitted in the short blueprint.

Edge cases checked: K=0 satisfies the full statement; a negative lower bound is
allowed, and no uniform bound or positive truncation index is assumed. The empty
scheme is not excluded (its prime-set definition still makes sense). There is no
restriction on characteristic or cardinality of the prime set. An empty allowable
prime set forces stalk elements to be killed by 1 and is compatible with zero.
Schemes use arbitrary universe u, while abelian sheaves use u+1, exactly as the
dependency interfaces. No extra equality of site universes is imposed.

Searches for an existing exact statement (2026-10-15):

- `msearch.py leansearch`: "Smooth base change bounded below derived etale sheaves
  torsion"; service unavailable (Internal Server Error).
- `msearch.py leanfinder`: "Smooth base change for bounded below etale abelian
  complexes with allowable prime torsion and torsion output"; eight algebraic
  etale/base-change results, none about this derived sheaf statement.
- `msearch.py loogle`: "AlgebraicGeometry.Etale.baseChange, IsIso"; zero hits,
  unknown identifier in the service index.
- `msearch.py grep`: "smooth.*baseChange|baseChange.*smooth", Mathlib
  AlgebraicGeometry; five hits about smooth morphisms being stable under base
  change, not this sheaf-cohomology theorem.
- `rg` in upstream WeilConjectures for smooth/base-change and this node id found
  `Etale.isIso_baseChange_app_of_smooth` in SmoothBaseChange/Derived.lean and
  the generic PlusDevissage result. The former only gives an ambient module-sheaf
  isomorphism, with no target allowable-torsion membership. The latter is a generic
  categorical devissage tool, not this geometric theorem. Neither is an exact match.
- `rg` in `lean/Sheaf` for the proposed declaration and allowable-torsion images
  found no existing theorem with this complete conclusion. Existing allowable-torsion
  definitions and the canonical abelian exchange are reused, not duplicated.

No statement correction, dependency repair, or new node is needed. The node already
corrected the blueprint's output-site typo from S to X; this delivery retains its text.
No STATEMENT-DISPUTED issue remains.

Validation: `scompile.py NE sbc-thm-bounded-below-derived-smooth-base-change`
compiled this file cleanly in its sandbox and at its intended library module path.

## Second reading by NE

I read the node statement, its source place in the blueprint, the Lean theorem, and each
recorded statement dependency. The objects and hypotheses match item by item:

- The four schemes `X Y S T : Scheme.{u}` and arrows `h : Y ⟶ X`, `e : Y ⟶ T`,
  `f : X ⟶ S`, `g : T ⟶ S` are the square in the node; `sq : ChosenCartesianSquare h e f g`
  supplies the chosen Cartesian identification and commutativity.
- `[Smooth f]`, `[QuasiCompact g]`, and `[QuasiSeparated g]` are exactly the source
  hypotheses, with no properness, finite-type, Noetherian, or characteristic assumption.
- `K : AbelianDerivedCategoryPlusTorsionOfPrimes T S.invertiblePrimes` renders
  `K ∈ D⁺_{P-tor}(T_Et)`, using the primes invertible on `S` and no upper bound.
- The first allowable-torsion conjunct renders `Lf^*Rg_*K` on `X`; the second renders
  `Rh_*Le^*K` on `X`. Their explicit `D(upperStar f)`, `R(lowerStar g)`,
  `R(lowerStar h)`, and `D(upperStar e)` terms use the recorded abelian derived functors.
- `IsIso (abelianDerivedBaseChangeArrow sq K.obj)` is the specified canonical exchange
  arrow from the base-change-map dependency. Since the allowable predicates describe a
  full subcategory, these endpoint memberships together with ambient invertibility render
  exactly the node's isomorphism in `D⁺_{P-tor}(X_Et)`.

The source blueprint contains an earlier `S_Et` typo; the node itself records the corrected
target `X_Et`, and the Lean uses `X` consistently. Quantifier order and conjunction order
are unchanged. Edge cases checked include `K = 0`, negative lower bounds, `n = 0`, empty
schemes, empty allowable-prime sets, arbitrary characteristic, and the stated universe
shift from schemes `u` to abelian sheaves `u + 1`; none is excluded. The dependency
declarations were opened and agree with the uses above. Searches recorded in the worker
report were repeated against Mathlib, the project, and upstream; no exact existing theorem
was found. No mismatch was found, so no source-based correction or code change was needed.

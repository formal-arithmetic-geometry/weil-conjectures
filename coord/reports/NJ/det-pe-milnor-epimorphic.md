## Worker report

`Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic` states
`AlgebraicGeometry.ProEtale.milnor_epimorphic`, all three conclusions of
`det-pe-milnor-epimorphic`. It also constructs its canonical comparison map.
The blueprint source is main-20261015, sec-proetale-coefficients,
sk-prop-pe-milnor, det-pe-milnor-epimorphic; that detail and its whole unit were read.
The statement and proof in the delivery node are the current server versions,
obtained from the refreshed delivery snapshot after the initial dry run exposed
that the shared checkout's copy was stale. No mathematical statement is corrected.

Each hypothesis and clause is rendered as follows:

- A scheme X is `(X : Scheme.{t})`. Its unchanged small pro-etale site is
  `Scheme.ProEt.topology X`, with objects in universe t+1 and morphisms in t.
- The arbitrary ring sheaf is
  `(R : Sheaf (Scheme.ProEt.topology X) RingCat.{max u (t + 1)})`.
  There is no commutativity, constant-coefficient, finiteness or Noetherian assumption.
- A tower of R-module sheaves is
  `(M : ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R)`.
  Its nth object is `M.obj (op n)` and its transition t_n is
  `M.map (homOfLE (Nat.le_succ n)).op`. This describes the same data as a family
  indexed by natural numbers and consecutive backward maps: arbitrary backward
  maps in the functor are their composites.
- Epimorphic transitions are exactly
  `(ht : ∀ n : ℕ, Epi (M.map (homOfLE (Nat.le_succ n)).op))`.
  Surjectivity on arbitrary sections is not added as a hypothesis.
- `[HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R)]`
  chooses the ordinary localization and its morphism universe, following the
  recorded abstract-derived-category interface. It adds no acyclicity assumption.
- The product P and the map 1-T are the existing
  `towerTransitionEndomorphism (K := fun n : ℕ ↦ M.obj (op n))
    (fun n : ℕ ↦ M.map (homOfLE (Nat.le_succ n)).op)`.
  Its definition is identity minus the product map with nth component
  `pr_(n+1) ≫ t_n`. The first conclusion is `Epi` of this exact map.
- The derived inverse limit is exactly the recorded Milnor-sequence model
  `WeilConjectures.integralOperationsRoos (Scheme.ProEt.milnorSingleTower M)`.
  `milnorSingleTower` applies the existing single-complex functor in degree zero;
  `integralOperationsRoos` takes `mappingCocone` of 1-T on the product of these
  complexes. This is definitionally Cone(1-T)[-1], including its sign convention.
- The second conclusion is `IsZero` of `.homology 1` of that same Roos complex,
  exactly R¹ lim M = 0 under the node's stated convention.
- The third conclusion is
  `IsIso (DerivedCategory.Q.{w}.map (milnorLimitComparison M))`.
  The comparison's source is the single complex of `limit M`; its target is the
  identical recorded Roos complex used in the second conclusion. Thus this states
  that the canonical ordinary-limit comparison is an isomorphism in the derived
  category, rather than asserting an unrelated existential isomorphism.

The helpers supply real data for that canonical map. `milnorLimitProjection M`
is `Pi.lift` of the single-complex images of the actual `limit.π M (op n)`.
`milnorLimitComparison M` is `CochainComplex.mappingCocone.lift` applied to that
projection tuple and the zero cochain. The named theorem
`milnorLimitComparison_condition` supplies only the required equality: the
composite of the tuple with 1-T is zero. Its complete proof is in its docstring:
check each projection, use limit compatibility and additivity, then product
extensionality and δ(0)=0. These helpers belong to this node's canonical map,
not to an independent DAG statement. All four declarations are in
`lean.declarations`. Both the main theorem and the condition theorem have `sorry`
proofs; both definitions have explicit data and contain no `sorry`.

Dependency declarations used; their full source signatures and docstrings were read:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-pbc-proetale-site`: the small-site `Scheme.ProEt` and
  `Scheme.ProEt.topology` publicly imported by the recorded module
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`. Its recorded
  `Scheme.proEtaleDerivedCategory` is for constant commutative coefficients;
  we use its exact underlying site, and use the arbitrary-ring derived category
  required here, through the separate recorded modules below.
- `def-weil-sheaf-of-modules-category`: `CategoryTheory.ringedSiteModules`, in
  `Sheaf.CategoryTheory.RingedSiteModules`, transparently `SheafOfModules`.
- `det-pe-milnor-sequence`: `Scheme.ProEt.milnorSingleTower` and
  `Scheme.ProEt.milnor_sequence`, in `Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence`.
  The current source was obtained with `scompile.py --source` because the shared
  checkout had no usable current record for this dependency. That source imports
  `WeilConjectures.integralOperationsRoos` and `integralOperationsTowerStep` from
  `Sheaf.Paper.IntegralOperationsWellDefined`; those exact definitions are reused.
- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.Q`, in `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-pur-sheaf-inverse-limit`: `CategoryTheory.Limits.limit` and `limit.π`, in
  `Mathlib.CategoryTheory.Limits.HasLimits`; module-sheaf limit instances come
  from `Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits`.
- `def-weil-tower-transition-endomorphism`: `towerTransitionEndomorphism`, in
  `WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism`.
- `lem-weil-proetale-surjective-tower-derived-limit`: its module
  `Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit` supplies the real
  existing instances `ProEtale.surjectiveTower_hasSheafify` and
  `ProEtale.surjectiveTower_wEqualsLocallyBijective` for the max u (t+1) coefficient
  universe. These instances have no commutativity assumption. Its stronger main
  theorem for commutative ring sheaves is not substituted for this node.

The last two already recorded nodes were added to `stmt_deps`; all six original
statement dependencies remain. No other node is stated or modified. All already
stated proof dependencies are imported (they are also statement dependencies).
The two remaining proof dependencies, det-pe-sections-limits-colimits and
 det-pe-sections-conservative, have no Lean record in the refreshed DAG; their
uses are described explicitly in the complete main-theorem proof docstring.
No new nodes or dependency modules are required. The instance search excludes
Mathlib's successor-specialized `hasSheafify_of_essentiallySmall`, as does the
recorded Milnor-sequence module, using the imported general-universe instances
instead. No new instance is defined and no site universe equality is imposed.

Edge cases checked: the zero tower, the empty scheme, a constant identity tower,
noncommutative coefficient sheaves, and a tower eventually zero (necessarily all
zero if all transitions are epic). For the zero tower the unique endomorphism
of the zero product is epic and both limits are zero. For the identity tower the
recursive difference equation has arbitrary right-hand sides and kernel the
constant module. In all cases the constructed comparison is the canonical kernel
map. The shifted-cone differential has the required minus sign; negating its
positive-degree term gives the usual two-term model. Every universe and variable
is bound explicitly, with `autoImplicit false`; u and t are independent.

Searches for an existing declaration:

- `msearch.py` LeanFinder: “A tower of epimorphisms of sheaves of modules on the
  pro-etale site has epimorphic one minus shift, zero first derived limit, and its
  ordinary limit equals its derived limit”. Eight hits concerned sheaf epis,
  light condensed modules and coherent-topology limits; no exact match.
- `msearch.py` Loogle: `"mappingCone", "lift"`. Twelve hits supplied general cone
  lifting APIs; the full `mappingCocone.lift` signature was then read.
- `msearch.py` grep: `Milnor|Roos|derivedLimit|homotopyLimit` in Mathlib/CategoryTheory:
  no hits.
- `msearch.py` LeanSearch: “An inverse tower of epimorphisms of sheaves of modules
  on the pro-etale site has zero first derived inverse limit”. Eight hits supplied
  sheaf limits and coherent-topology sequential-limit facts; no exact statement.
- Direct rg in the pinned Mathlib, upstream WeilConjectures, the side framework
  and lean/Sheaf found `GrothendieckTopology.epi_one_sub_of_forall_exists`,
  `ProEtale.epi_one_sub_of_epi` for constant coefficients, the commutative-ring
  surjective-tower theorem above, and abelian-group Roos results. Their signatures
  were read; none states all three clauses for arbitrary sheaves of rings.
- Direct rg for the item id in upstream sources found no match. Searches for
  `milnorLimitProjection`, `milnorLimitComparison`, `milnor_epimorphic` and
  `MilnorEpimorphic` in the libraries and dag/lean_names_upstream.json found no
  existing declaration with the chosen names.
- Inspection of the refreshed Milnor-sequence dependency identified the exact
  shared Roos construction; its source was read and is used rather than duplicated.

No statement dispute or mathematical correction is needed. The initial dry run's
stale-node mismatch was repaired by retaining the current server statement and
proof verbatim and aligning the Lean with the current recorded Roos interface.

Validation uses only the prescribed file-only `scompile.py` wrapper and
`deliver2.py --no-push`; the second reader will perform delivery. No global build,
direct git command in the shared repository, or direct shared-file edit was made.

## Second reading by NJ

I read the item record `dag/nodes/sec-proetale-coefficients/det-pe-milnor-epimorphic.json`, its
source statement `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-pe-milnor/det-pe-milnor-epimorphic.md`,
and its proof source before checking the Lean file.

The statement, item by item, is rendered in
`Sheaf/AlgebraicGeometry/ProEtaleMilnorEpimorphic.lean` by
`AlgebraicGeometry.ProEtale.milnor_epimorphic`:

1. The scheme is `(X : Scheme.{t})`; the site is exactly
   `Scheme.ProEt.topology X`, supplied by `def-weil-pbc-proetale-site`.
2. The arbitrary ring sheaf is
   `R : Sheaf (Scheme.ProEt.topology X) RingCat.{max u (t + 1)}`. No commutativity,
   constantness, finiteness, Noetherianity, or characteristic hypothesis is added.
3. The tower is
   `M : ℕᵒᵖ ⥤ ringedSiteModules.{max u (t + 1)} R`; its consecutive transition at
   `n` is `M.map (homOfLE (Nat.le_succ n)).op`, exactly the backward map
   `t_n : M_{n+1} -> M_n`. The functor supplies arbitrary composites as in the source.
4. The hypothesis is exactly
   `ht : ∀ n : ℕ, Epi (M.map (homOfLE (Nat.le_succ n)).op)`. There is no stronger
   sectionwise-surjectivity assumption. The required derived-category instance is
   `[HasDerivedCategory.{w} (ringedSiteModules.{max u (t + 1)} R)]`; it is the
   ambient choice needed to state the source's derived-category conclusion and is
   not a mathematical finiteness or acyclicity assumption.
5. The first conclusion is `Epi` of
   `towerTransitionEndomorphism (K := fun n => M.obj (op n))
   (fun n => M.map (homOfLE (Nat.le_succ n)).op)`, the existing identity-minus-shift
   map on `P = ∏ₙ Mₙ`. This is exactly `1-T` from the node.
6. The second conclusion is
   `IsZero ((WeilConjectures.integralOperationsRoos
   (Scheme.ProEt.milnorSingleTower M)).homology 1)`. The recorded
   `milnorSingleTower` and `integralOperationsRoos` are the node's
   `Cone(1-T)[-1]` convention, so this is exactly `R¹ lim M = 0`.
7. The third conclusion is
   `IsIso (DerivedCategory.Q.{w}.map (milnorLimitComparison M))`. The helper's
   source is the degree-zero single complex on `limit M`, and its target is the
   same Roos complex as in clause 6. The helper is built from the actual limit
   projections and the named condition theorem, so this is the canonical map
   `lim M[0] -> R lim M`, not an existential or unrelated isomorphism.

The source proof's five steps are represented in the theorem docstring: sectionwise
surjectivity from preservation of cokernels and products; the recursive right-inverse
construction for `(1-T)(W)`; conservative detection of the epimorphism; the Milnor
cohomology calculation; and the kernel inclusion/quasi-isomorphism with the cone sign.
The two helper definitions contain real data; only their condition proof and the main
statement proof are postponed as named `sorry` theorems.

Edge cases checked: the zero tower, a constant identity tower, an eventually-zero tower,
the empty scheme, and noncommutative coefficient sheaves. The empty index issue does not
arise because the source index is the fixed nonempty `ℕ`; the product and inverse limit
are nevertheless the categorical ones. `n = 0` is included by `Nat.le_succ n`, and no
characteristic restriction is present. The universes `u`, `t`, and derived-category `w`
are independent, with the site/coefficient universe `max u (t + 1)` exactly as required.

I searched with `msearch.py` (LeanFinder, LeanSearch, Loogle, and grep) and direct `rg`
in pinned Mathlib, the upstream WeilConjectures sources, the read-only pro-etale
framework, and `lean/Sheaf`. Searches covered `Milnor`, `Roos`, `derivedLimit`,
`homotopyLimit`, `one_sub_shift`, `milnorLimitComparison`, and
`milnor_epimorphic`; no existing declaration states this item. The recorded
`det-pe-milnor-sequence` interface was read and reused, as were the recorded site,
ringed-module, inverse-limit, transition-endomorphism, and derived-category interfaces.
The refreshed `lem-weil-proetale-surjective-tower-derived-limit` module was checked for
its universe instances; its stronger commutative theorem is not substituted.

No mismatch was found. I made no mathematical or statement correction, added no
hypothesis, and dropped no clause. The node copy remains verbatim aligned with the
Lean signature. File-only compilation passed with the prescribed command:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py NJ det-pe-milnor-epimorphic
lean/Sheaf/AlgebraicGeometry/ProEtaleMilnorEpimorphic.lean`.

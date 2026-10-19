## Worker report

The module `Sheaf.Algebra.Homology.SurjectiveModuleComplexTowerLimit` states
`ModuleCat.surjective_moduleComplexTower_limit`, with `sorry`, and supplies the canonical
helper `ModuleCat.restrictedComplexTower`. No theorem is proved. The helper is part of the
canonical scalar restriction required by this statement, as authorized by the stage-2
missing-helpers rule; it has real data, using existing restriction and comparison functors.
No independent mathematical notion or new DAG node is introduced.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The inverse system of commutative rings is `A : ℕᵒᵖ ⥤ CommRingCat.{u}`. Natural index
  `n` denotes the paper's positive index `n+1`, so the first stage is included.
- Its limit ring is `c.pt` for `c : Cone A`, with limiting hypothesis `hc : IsLimit c`.
  This allows any chosen limit cone, not only a particular chosen limit construction.
- `P n : CochainComplex (ModuleCat.{v} (A.obj (Opposite.op n))) ℤ` is the given
  unbounded cochain complex over the nth ring.
- `t n` is a morphism from `P (n+1)` to the complex `P n` restricted along the successor
  ring map. Thus it is exactly an A_(n+1)-linear chain map, including differential
  compatibility, with no invertibility or exactness assumption.
- `ht : ∀ n i, Function.Surjective ((t n).f i)` is surjectivity in every integer degree.
- `restrictedComplexTower A c P t` has nth object the complex restricted along
  `c.π.app (op n)`. Its successor map is the restriction of `t n`, followed by the
  canonical composition comparison. The comparison is induced by the equation `c.w`
  of the ring cone. `restrictScalarsComp'` has identity underlying additive maps, so no
  arbitrary comparison map, scalar action, or choice is assumed.
- `HomologicalComplex.coneOfHasLimitEval (restrictedComplexTower A c P t)` constructs
  the specified P: its object in degree i is the module limit of the evaluated tower;
  its differential is the map induced by the component differentials. Its cone legs
  are the degreewise inverse-limit projections. This is the node's termwise construction,
  not a replacement by an arbitrarily chosen derived object.
- `HasDerivedCategory.{w} (ModuleCat.{v} c.pt)` is the size/localization infrastructure
  required by the recorded derived-category dependency; u, v, w are independent.
- The first conclusion, `HasProduct (fun n ↦ DerivedCategory.Q.obj ...)`, asserts that
  the countable product used by the triangle exists. The following universal instance
  binder says the assertion works for every choice of this product. This avoids assuming
  product existence and avoids a statement-level `let` or chosen product instance.
- `∃ δ`, with source this product and target `Q(P)⟦1⟧`, supplies the connecting arrow.
- `IsDerivedLimitTriangle` is applied to `Q.map` of the original restricted successor
  maps, `Q.obj` of the constructed termwise limit, and `Pi.lift` of `Q.map` of its cone
  projections. Its definition is precisely the distinguished triangle with middle map
  `1-s`. Consequently the first arrow is the specified product map and each projection
  is the image of the original projection, not merely some isomorphic derived limit.

Dependencies used and inspected:

- `def-weil-inverse-system`: `Mathlib.CategoryTheory.Functor.OfSequence`,
  `CategoryTheory.Functor.ofOpSequence` (and the natural-transformation interface
  `NatTrans.ofOpSequence`). The helper uses `ofOpSequence` to assemble the restricted
  successor maps; the input ring tower is already the equivalent functor encoding.
- `def-weil-derived-limit`:
  `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`,
  `CategoryTheory.IsDerivedLimitTriangle`, also reading `IsDerivedLimit`. The exact
  recorded upstream module was read with `scompile.py --source` because its local file
  is absent. It gives the specified Roos triangle, with the transition endomorphism 1-s.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`.
- Proof dependency `lem-pc-cone-short-exact-quasi-iso`:
  `Mathlib.Algebra.Homology.HomotopyCategory.ShortExact`,
  `CochainComplex.mappingCone.quasiIso_descShortComplex` (read with its canonical
  `descShortComplex` and inclusion formulas).
- Proof dependency `def-weil-triangulated-category`:
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `CategoryTheory.Pretriangulated`
  and its distinguished triangles, provided by the public derived-category imports.
- Proof dependency `lem-weil-derived-limit-products-core`:
  `Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts`,
  `CategoryTheory.derivedCategory_countableProducts_core`; its complete signature and
  proof docstring were read. The proof-only import is included.

The theorem docstring records all five proof steps: scalar restriction, the kernel and
recursive surjectivity of 1-s, the short-exact cone quasi-isomorphism and sign of the
connecting arrow, preservation of exact module products in the derived category, and
checking both the transition endomorphism and the first arrow on projections.
Source passages were read directly in `literature/stacks-project/more-algebra.tex`,
`lemma-compute-Rlim-modules` (091D) and `lemma-distinguished-triangle-Rlim-modules` (0CQD).

Edge cases checked: zero complexes, the zero ring, constant/identity towers, the first
index n=0 (paper n=1), negative and arbitrarily high cochain degrees, and non-surjective
ring transitions. No boundedness, finite generation, freeness, or surjectivity of the
ring maps is imposed. In the zero case both products and the limit are zero and the
triangle is the zero triangle. Constant identity towers give the diagonal first map.
The recursive surjectivity argument uses surjectivity only of the module transitions,
not of differentials or ring maps. A countable tower is nonempty by definition; there
is no empty-index exception hidden in the encoding.

Searches for existing declarations:

- `msearch.py ... leanfinder` query: "The derived inverse limit of a degreewise surjective
  tower of module cochain complexes is the ordinary limit". Eight hits, including
  `HomologicalComplex.isLimitOfEval`, `coneOfHasLimitEval`, and
  `Types.surjective_π_app_zero_of_surjective_map`; none states the derived-limit triangle.
  The ordinary termwise-limit construction is reused.
- `msearch.py ... loogle` query: `"IsDerivedLimit"`. Zero hits.
- `msearch.py ... grep` query: `Rlim|homotopyLimit|derived.*inverse.*limit`, directory
  `Algebra/Homology`. One hit, `CochainComplexPlus.lean:60`, unrelated to this triangle.
- `rg` of project `lean/Sheaf` and the read-only slopmaster2 `WeilConjectures` for
  `surjective.*(tower|[Ll]imit)|IsDerivedLimitTriangle|surjective-module-complex-tower-limit`.
  Inspected `DerivedLimitTowerTriangle.lean`: its theorem requires a K-injective complex
  of towers and does not state this degreewise-surjective varying-ring assertion.
  SurjectiveTowerLimitAcyclic concerns higher right derived functors on abelian-group
  towers, not the asserted unbounded module-complex triangle. No exact existing match.
- Searches for restriction/scalar-composition APIs located Mathlib
  `ModuleCat.restrictScalars`, `restrictScalarsComp'`,
  `Functor.mapHomologicalComplex`, and `Functor.mapHomologicalComplexCompIso`.
  Their full signatures and composition-comparison formulas were read and reused.

No statement correction, dependency repair, or STATEMENT-DISPUTED issue.
The delivered file compiled cleanly using the authorized server-only `scompile.py`:
1.3 seconds, nice 19, two threads, 60-second per-file limit. No local compiler was run.

## Second reading by NC

I independently read the sandbox node and Lean module against the setup of Stacks
more-algebra.tex, section Rlim of modules, Tag 091D (3), (5), and Tag 0CQD.
The source assumes an inverse sequence of rings, modules with linear transitions,
and no finiteness, boundedness, or surjectivity assumption on the ring maps.
The node specializes to commutative rings and degreewise surjective transitions;
the Lean has exactly that specialization.

Object, hypothesis, and conclusion inventory, with correspondence and verdict:

1. The positive-index inverse ring system is `A : ℕᵒᵖ ⥤ CommRingCat.{u}`;
   Lean index `n` is source index `n+1`. PASS: all stages and transition composites
   are retained. I read `Functor.ofOpSequence` and `NatTrans.ofOpSequence` in Mathlib.
2. The ring A with its inverse-limit projections is `c : Cone A`, `hc : IsLimit c`,
   with ring `c.pt` and maps `c.π.app (Opposite.op n)`. PASS: an arbitrary limiting
   cone is permitted; no particular limit presentation is assumed.
3. The complexes of A_n-modules are the family `P`, with degree set `ℤ` and
   coefficients `ModuleCat.{v} (A.obj (Opposite.op n))`. PASS: unbounded complexes,
   arbitrary commutative rings, and independent ring/module universes.
4. The A_(n+1)-linear chain maps are `t n`, whose target is `P n` restricted along
   `A.map (homOfLE (Nat.le_succ n)).op`. PASS: the direction is A_(n+1) → A_n,
   and a complex morphism includes precisely differential compatibility.
5. Surjectivity in every degree is `ht : ∀ n i, Function.Surjective ((t n).f i)`.
   PASS: no splitting, free-module, cohomology-surjectivity, or ring-surjectivity
   assumption is added.
6. Restriction to A is the helper `restrictedComplexTower A c P t`. PASS: I read
   `restrictScalars`, `restrictScalarsComp'App`, `restrictScalarsComp'`, and
   `Functor.mapHomologicalComplexCompIso`. Its comparison uses the reverse of the
   cone equation to identify the composite ring map; the inverse comparison takes
   the doubly restricted target to the directly restricted one. Underlying maps
   are identities, so the transition remains the original t, now A-linear.
7. The complex P with P^i = lim P_n^i and induced differentials is the apex of
   `HomologicalComplex.coneOfHasLimitEval (restrictedComplexTower A c P t)`.
   PASS: I read its definition: `X` is the evaluated limit, `d` is `limMap` of
   component differentials, and its cone legs have `f := limit.π`. This reuses
   the existing termwise construction rather than introducing a private copy.
8. The localization to D(A) is `DerivedCategory.Q` under
   `[HasDerivedCategory.{w} (ModuleCat.{v} c.pt)]`. PASS: I read the Mathlib
   definitions of `HasDerivedCategory`, `DerivedCategory`, and `Q`; this is the
   recorded size infrastructure, not an extra mathematical condition. The
   standard localization is available in a sufficiently large universe, and
   no equality among u, v, w is imposed.
9. The countable derived product exists: the first conjunct is `HasProduct` of
   the localized restricted complexes. PASS: existence is concluded, not assumed.
   The following universal instance binder allows every choice of this product,
   an equivalent choice-independent rendering of the node's product assertion.
10. The connecting arrow is the existential `δ` to `Q(P)⟦(1 : ℤ)⟧`.
    PASS: its source is that same product, and no arbitrary replacement for P
    or its projections is quantified over.
11. The distinguished Roos triangle is `IsDerivedLimitTriangle` applied to
    `Q.map` of the restricted transitions, `Q(P)`, the `Pi.lift` of the localized
    termwise-limit cone legs, and δ. PASS: I read the current server source of
    `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit` and its transition
    endomorphism module using `scompile.py --source`. The predicate is exactly
    membership of `Triangle.mk p (towerTransitionEndomorphism f) δ` in the
    distinguished triangles; that endomorphism is `𝟙 _ - towerProductShift f`.
12. Respect for projections is built into that first arrow, `Pi.lift` of the
    images of the original limit projections. PASS: product projection equations
    are its defining universal property, rather than an unspecified isomorphism.

I also opened the proof-dependency module `DerivedLimitProducts` and the Mathlib
short-exact cone comparison, including `descShortComplex` and
`quasiIso_descShortComplex`. Their actual signatures match the cited proof uses.
The five proof steps and the cone sign are present in the theorem docstring;
the helper and theorem have source/blueprint docstrings. There is no new node,
dependency repair, statement correction, hollow definition, private notation,
unbound variable/universe, or proved theorem in this delivery. The helper has
real functor data and is included in `lean.declarations`. The node's
`lean.statement` was compared programmatically with the file signature and is
verbatim equal. No mathematical or record mismatch was found; I left all correct
Lean and node text unchanged.

Edge cases: ℕ is nonempty and has the first stage 0 (source 1); an empty tower
is outside the node's specified indexing, not an excluded case. Zero modules,
zero complexes, the zero ring, constant identity towers, all negative degrees,
and all characteristics remain allowed. No scheme is involved. Ring and module
universes are independent, and arbitrarily large input data can be placed in a
common universe; no finite-size restriction is hidden in the indexing.

Independent H4 searches (2026-10-15):

- `msearch.py ... leanfinder`: "A Mittag Leffler tower of cochain complexes has
  ordinary inverse limit as derived limit". Eight hits: ordinary complex-limit
  construction/recognition and a cochain-induction lemma, no matching theorem.
- `msearch.py ... loogle`: `"IsDerivedLimitTriangle"`. Zero hits.
- `msearch.py ... grep`: `homotopy.*limit|surjective.*[Tt]ower`. Eighteen hits,
  scalar-tower and homotopy/limit utilities, no matching derived Roos assertion.
- Direct `rg` of Mathlib APIs, repository `lean/Sheaf`, and slopmaster2
  `WeilConjectures` with `restrictedComplexTower`, `surjective_moduleComplexTower`,
  `surjective.*[Ll]imit`, and `IsDerivedLimitTriangle`. I opened
  `DerivedLimitTowerTriangle` (requires K-injective tower complexes) and
  `SurjectiveTowerLimitAcyclic` (higher derived functors of abelian-group towers).
  Neither is the node's varying-ring, arbitrary degreewise-surjective-complex
  statement. Existing scalar restriction and ordinary termwise limits are reused.

Validation: the sole delivered Lean file compiled cleanly with the prescribed
server-only `scompile.py`, 1.3 seconds, nice 19, two threads, 60 seconds per file.
No local compiler or library build was run. Second reading changed only this
independent review report.

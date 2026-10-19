## Worker report

This delivery states `AlgebraicGeometry.curve_trace_cup_naturality` in
`Sheaf.AlgebraicGeometry.Curve.TraceCupNaturality`. The original mathematical statement,
proof and proof dependencies are unchanged. Its statement dependencies gain two definition
nodes supplying the previously unnamed finite cup and degree-normalized trace.
All theorems have `sorry` proofs; all definitions contain real data. The inverses of the
cohomology comparisons are determined by bijectivity, and the trace is determined by a
unique-existence theorem. No arbitrary cup, trace, reduction or pullback is a hypothesis.

Hypotheses and objects, clause by clause:

- An algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- `C` and `D` are `Scheme.{u}`, with structure maps `fC`, `fD`; each has exactly
  `[IsConnectedCurve ...] [Smooth ...] [IsProper ...]`. The recorded connected-curve
  definition includes nonemptiness, connectedness, finite type, separatedness and dimension
  exactly one. The explicit structure maps are required by that recorded interface.
- The prime is `(ell c : ℕ) [Fact ell.Prime] [CharP k c] (hell : ell ≠ c)`.
  Here `c` names the actual characteristic and also includes characteristic zero.
- `A_n` is the existing `C.constantZMod (ell ^ n)`; roots are the existing
  `C.rootsOfUnitySheaf (ell ^ n)`. Ordinary cohomology is `Sheaf.H`, the Ext model
  expressly allowed by the cohomology dependency's record. No compact support or
  pro-etale coefficient replacement is used.
- `degreeNormalizedCurveTrace` is the unique additive trace taking the Kummer class
  of each `tracePointPic ... P` to one. `tracePointPic` uses the existing
  `Scheme.Pic.ofClosedPoint`, the dual point ideal, which is O(P). Its required
  relative-dimension-one instance is derived from connectedness, smoothness and dimension;
  no extra hypothesis is imposed. `Divisor.toPic_single` identifies the point-ideal
  Picard class with the divisor class. The existing
  `Divisor.nonempty_toPic_iso_module` also identifies its representative with the
  valuation-defined `Divisor.moduleOfSmoothConnectedCurve` of the recorded divisor node.
- `finiteCoefficientCup` uses the existing exponent module structure of roots and
  canonical module/abelian cohomology comparison. Yoneda composition on module-sheaf Ext,
  with the Koszul sign for the unsigned Cech convention, gives the constant/roots
  cup followed by exponent evaluation. There are no free cup operations in the statement.
- `curveTraceCupPairing` defines exactly P by applying this cup and then this trace.
  `i : Fin 3` gives exactly i=0,1,2, and the second degree is `2 - i`.
  `Nat.add_sub_cancel' (Nat.le_of_lt_succ i.isLt)` supplies i+(2-i)=2.
- In the first conjunct `hm : 1 ≤ m` and `hmn : m ≤ n` express precisely
  n≥m≥1; `hm.trans hmn` supplies the trace's n≥1 requirement.
  `traceCupConstantReduction` is the constant-sheaf image of the actual
  `ZMod.castHom (pow_dvd_pow ell hmn)`. `traceCupRootsReduction` is the kernel lift
  of the inclusion followed by multiplication by ell^(n-m) on the additive Gm
  sheaf, hence z↦z^(ell^(n-m)). Applying `Sheaf.H.map` gives exactly r and s.
  The right-hand side uses the same `ZMod.castHom` on the trace value.
- In the second conjunct n≥1 is explicit. `f : D ≅ C` is an actual scheme
  isomorphism, `σ : Spec (.of k) ≅ Spec (.of k)` an arbitrary base automorphism,
  and `hσ : f.hom ≫ fC = fD ≫ σ.hom` expresses the covering condition.
  This admits the identity and all semilinear isomorphisms; σ is not required to
  be the identity. Constant pullback is `Etale.cohomologyMap` followed by the
  existing `upperStarConstantSheafIso`. Roots pullback is the same cohomology map
  followed by the kernel lift of the existing `upperStarGmSheafToGmSheaf`.
  The equality is exactly P_D(f*x,f*y)=P_C(x,y), with the same residue coefficient ring.
- There is no finite-field, finite-order, Frobenius, Galois generator, chosen
  roots-of-unity basis or extra orientation hypothesis.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve`,
  `IsConnectedCurve`, its connected-space and dimension clauses.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`: `Scheme.kummerSequence`,
  `rootsOfUnitySheaf`, `constantZMod`, `kummerδ₁` and exactness.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.cohomology`, `Etale.rightDerivedGlobalSections`; the dependency's note permits
  `CategoryTheory.Sheaf.H` and records its ordinary-derived-cohomology bridge.
- `Sheaf.AlgebraicGeometry.DivisorModule`:
  `Scheme.Divisor.moduleOfSmoothConnectedCurve`, and the existing divisor group.
- `WeilConjectures.AlgebraicGeometry.Curve.Picard`: `Scheme.Pic.ofClosedPoint` and
  `Scheme.Divisor.toPic_single`; `Sites.GmPicard`:
  `Scheme.Pic.toCohomologicalPicardGroupAddEquiv`.
- `Sheaf.AlgebraicGeometry.KummerModuleCoefficients`:
  `Scheme.kummerRootModulePresheaf`, reusing `finiteEtaleMuModulePresheaf` from
  `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist` without a second exponent action.
- Mathlib: `constantSheaf`, `constantCommuteCompose`, `Abelian.Ext.mapExactFunctor`,
  `Ext.comp`, `Ext.mk₀`, `Equiv.ofBijective`, `kernel.lift`, and `ZMod.castHom`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`:
  `Etale.cohomologyMap`; `Sites.Gm`: `upperStarGmSheafToGmSheaf`.
- Stated proof dependencies are imported for stage 3: `SecondKummerDivisors`,
  `DivisorClassCurve`, `RightDerivedUniversalDeltaFunctor`,
  `RightDerivedTriangleConnecting`, `PullbackCohomologyLongExactLadder`,
  `GmPicardPullback`, Kummer exactness, the divisor module, and ordinary cohomology.
  The still-unstated proof dependency `lem-wf-etale-cup-functoriality` has no module
  to import. The Mathlib Grothendieck/enough-injectives leaves need no new module.

Edge cases checked before the final statement:

- n=m: reduction is the identity on residues and the roots power is ell^0=1;
  the formula includes this case without a strict inequality.
- m=1, n=1 and ell=2 are included; no division by two or odd-prime assumption occurs.
- n=0 and m=0 are excluded exactly where the node excludes them. The generic cup
  construction also makes sense for N=0 and N=1; these do not add a target hypothesis.
- All of i=0,1,2 have nonnegative complementary degree and sum two.
- The empty scheme and dimension-zero schemes are excluded by the node's connected-curve
  hypothesis, not by extra assumptions. The generic cup accepts an empty scheme and zero
  coefficients: all relevant cohomology classes and products are zero.
- Characteristic zero is included; in positive characteristic only ell=char(k) is excluded.
- f=id and σ=id are included, as are nontrivial semilinear isomorphisms.
- No site/coefficient universe equality is imposed: the small-etale site uses Scheme.{u}
  and the established AddCommGrpCat.{u+1} / lifted ModuleCat coefficient convention.

Searches performed:

- `msearch.py ... leanfinder` queried “Etale cohomology cup products and degree normalized
  curve trace commute with reduction and semilinear isomorphisms”: only cotangent,
  field-trace and group-cohomology hits, no matching statement.
- `msearch.py ... loogle` queried `"trace", "cohomology"`: zero hits.
- `msearch.py ... grep` queried `cupProduct|cohomologyCup|etale.*trace` in
  Mathlib/AlgebraicGeometry: zero hits.
- LeanSearch queried “Cup product in etale cohomology of constant ZMod and roots of unity
  computed by Yoneda Ext composition in sheaves of ZMod modules”: generic `Sheaf.H`
  and Ext composition hits, which are reused, no finite cup construction.
- LeanFinder queried “Canonical coefficient forgetful comparison Ext from constant ring
  sheaf to sheaf cohomology and Yoneda cup products”: generic cohomology/Ext equivalences,
  no matching comparison. Mathlib Sites grep for
  `cupProduct|moduleCohomology|mapExactFunctor` returned zero hits.
- LeanSearch queried “Canonical degree normalized trace from second etale cohomology of
  roots of unity on a smooth proper connected curve to ZMod, sending each Kummer point
  class to one”: field normalized-trace and cyclotomic-character hits, no curve trace.
  Loogle `"trace", "kummer"` and Mathlib AlgebraicGeometry grep
  `degreeNormalized.*Trace|curveTrace|trace.*kummer` returned zero hits.
- Direct rg searches in Mathlib, upstream `WeilConjectures`, `lean/Sheaf` and the
  upstream name index found no declarations with the new names. Direct source searches
  for the item id found no existing exact statement. Node searches and
  `blueprint_refs.py search` for ordinary cup, Yoneda and degree-normalized trace found
  no duplicate finite constant/roots cup or finite ordinary curve trace. The existing
  scalar cups concern O-module/field coefficients; the rational finite-field
  `def-weil-poincare-trace-cup` is not this finite ordinary trace.

Sources read: Milne LEC Section 14, especially the Kummer quotient, trace and its point
normalization, and Section 22's Cech cup; Stacks `sites-cohomology.tex`, Tags 03FD,
0FPJ and 0H9A; the current main-20261015 blueprint proof of
`lem-wf-curve-h1-dual-tate-module`, first paragraph and equations (4.2)-(4.3).
No statement dispute or source correction is needed.

## Second reading by Q136

Independent maintainer second reading, 2026-10-18, of immutable delivery
`d70209affb70f365884f341ca146fc1e63a3f0fa`. I read the item, all six statement
dependencies, both added definition records, all three delivered modules and their
docstrings, and the actual dependency declarations. The previous placeholder in this
section was H11; this complete replacement report repairs it. The worker report above
is retained. No mathematical statement or Lean file is changed.

Clause checks:

- `k : Type u`, `Field k`, and `IsAlgClosed k` render the algebraically closed field.
  `C,D : Scheme.{u}` and the explicit structure maps with `IsConnectedCurve`, `Smooth`,
  and `IsProper` give exactly smooth proper connected curves. I read `IsCurve` and
  `IsConnectedCurve`: finite type, separatedness, nonemptiness, connectedness and
  dimension one are included. The regular, integral, Noetherian and relative-dimension
  instances inside `tracePointPic` follow from these assumptions; none is added.
- `Fact ell.Prime`, `CharP k c`, and `hell : ell ≠ c` express precisely the prime and
  characteristic condition, including characteristic zero. `hm` and `hmn` impose
  exactly n >= m >= 1; `hn` imposes n >= 1 in the second clause.
- `constantZMod` is the existing lifted constant residue sheaf; `rootsOfUnitySheaf`
  is the existing kernel of the power map on `gmSheaf`. `Sheaf.H` is ordinary Ext
  cohomology, expressly permitted by the recorded cohomology dependency; its existing
  derived-global-sections bridge is deferred to stage 3. No pro-etale replacement is used.
- `finiteCupForget` is the actual module-forgetting functor. The comparison forgets
  an extension and precomposes with the integer unit, as in Stacks 03FD. Its inverse
  is fixed by bijectivity, rather than an arbitrary equivalence. `finiteCupRoots`
  uses the existing exponent module presheaf, with a named descent obligation.
  `finiteCoefficientCup` composes the unit extension followed by the roots extension.
  I checked `Ext.comp`, `comp_hom` and `ShiftedHom.comp`: this is the left-then-right
  shifted convention. The displayed (-1)^(p*q) corrects the interchange of shifts
  to the unsigned front/back Cech convention in Milne Section 22. It is a concrete
  construction of the required evaluated cup, not a free bilinear map.
- `tracePointPic` is `Pic.ofClosedPoint`, the dual point ideal. I read
  `Divisor.toPic_single` and `Divisor.nonempty_toPic_iso_module`, which identify this
  class with the actual valuation-defined O(P). `existsUnique_degreeNormalizedCurveTrace`
  normalizes the existing Kummer boundary after the actual Pic/H1 equivalence at
  every closed point and for every proof of invertibility. The trace definition
  selects this uniquely specified additive map. Degree modulo ell^n descends along
  Pic/ell^n, and point classes generate; its existence and uniqueness are valid.
- `curveTraceCupPairing` is precisely trace of that cup. `i : Fin 3` covers degrees
  0, 1, 2 and the explicit degree equality makes the result lie in H2.
- Constant reduction is induced by `ZMod.castHom (pow_dvd_pow ell hmn)`.
  Roots reduction is the kernel lift of inclusion followed by ell^(n-m) times
  the identity on additive Gm, hence precisely the stated power on units. The first
  conjunct applies `Sheaf.H.map` to these two maps and reduces the trace value by
  the same residue homomorphism. Every input and both sides match the node.
- `f : D ≅ C`, arbitrary `σ : Spec k ≅ Spec k` and `hσ` give the semilinear
  isomorphism. The constant pullback uses `Etale.cohomologyMap` followed by
  `upperStarConstantSheafIso`; roots pullback uses the kernel lift of the actual
  units comparison `upperStarGmSheafToGmSheaf`. I read those declarations. Thus the
  second conjunct is exactly P_D(f*x,f*y)=P_C(x,y), without k-linearity, finite-field,
  Frobenius, orientation, basis or additional coefficient assumptions. The reduction
  conjunct can be specialized with D=C and both isomorphisms identities.

Source checks: Milne LEC, Section 14, Propositions 14.2 and 14.5, Remark 14.6,
Theorem 14.7 and Example 14.8 (printed pp.90-93), and Section 22 (printed p.135);
Stacks `sites-cohomology.tex`, lemma-cohomology-modules-abelian-agree (03FD,
line 1862), section-cup-product (0FPJ, line 8205), and
lemma-base-change-cup-product (0H9A, line 8529). On a proper curve compact support
agrees with ordinary cohomology. The Kummer ladder has power ell^(n-m) on the first
two terms and identity on the final Gm, so no factor appears on the Picard input.
Scheme isomorphisms carry O(P) to O(f^-1(P)) and preserve normalization. The proof
docstring contains the generation, both ladders, trace comparison, evaluation
compatibility, cup naturality and assembly steps, including the boundary bridge.

Edge cases: n=m, n=m=1, m=1, ell=2, characteristic zero, every allowed positive
characteristic, all three degrees, zero classes, identity isomorphisms and nontrivial
base automorphisms are covered. Empty and zero-dimensional schemes are excluded
exactly by connected curve. The generic cup also handles empty schemes, N=0 and N=1.
The small-etale site and lifted coefficients retain their established universes;
there is no extra site-object/morphism universe equality or silent size restriction.

Independent searches used `rg` with finite cup, Yoneda cup, normalized trace and
point-class terms across Mathlib, upstream WeilConjectures and the group clone's
lean/Sheaf tree, and exact new declaration names. I inspected the related general
Tate-orientation trace in `EtaleCohomology/PoincareDuality/TraceIsomorphism.lean`:
it does not define this ordinary Kummer-normalized trace. Existing scalar cups
use other coefficient categories; they are not duplicates of this finite cup.
The worker's three-kind searches remain recorded above and in both new nodes.
The new definitions reuse existing coefficients, point ideals and Ext operations.
Their fields, ancestor/via records and new statement-dependency edges are correct.
No independent missing statement prerequisite is required to type this delivery;
the unstated cup-functoriality theorem is a proof dependency for stage 3.

All three `lean.statement` fields are verbatim signature substrings of their files.
Every delivered theorem has only `sorry`; every definition supplies actual data,
with proof obligations named separately. All declarations have source/blueprint
docstrings, all lines are within 100 characters, variables/universes are bound,
and no private notation, global build or live Lean edit was used. The original
item statement and proof are unchanged by the delivery. None of its direct
statement/proof dependencies occurs on the current route-pivot dropped list;
no route-pivot repair note exists for this item, and the delivery introduces
none of the dropped enhancement/model/infinity machinery.

Compiler reproduction on 2026-10-18 passed; details and timings are recorded in Validation below.

## New nodes

`def-wf-finite-coefficient-cup` supplies the finite constant/roots cup that the item uses
but no recorded dependency names. It uses the existing roots module action and canonical
coefficient-forgetting comparison, states the well-definedness obligations with full proof
docstrings, and constructs the cup by transport of Yoneda composition. Sources are
Stacks 03FD and 0FPJ and Milne Section 22. The LeanSearch, LeanFinder, Mathlib/source/side
and DAG searches above found generic ingredients but no duplicate of this construction.

`def-wf-degree-normalized-curve-trace` supplies the ordinary finite trace, defined by
unique point normalization. It constructs O(P)'s Picard class using the existing dual
point ideal and takes the unique normalized additive map, whose existence and uniqueness
are stated with the Milne/Kummer/degree proof. Sources are Milne Propositions 14.2, 14.5
and Remark 14.6. LeanSearch/Loogle/grep and DAG searches above found only unrelated field
traces and a different rational finite-field trace. Both new nodes are in the item's
chapter, inherit its blueprint ancestor and via chain, and are cited by its stmt_deps.

## Validation

Reproduced with:

```text
python3 /home/ubuntu/weil-launcher-nt/scompile.py Q136 lem-wf-curve-trace-cup-naturality snapshot/lean/Sheaf/AlgebraicGeometry/Curve/FiniteCoefficientCup.lean snapshot/lean/Sheaf/AlgebraicGeometry/Curve/DegreeNormalizedTrace.lean snapshot/lean/Sheaf/AlgebraicGeometry/Curve/TraceCupNaturality.lean
```

The wrapper exited 0, with no errors or warnings. Per-file library checks:
DegreeNormalizedTrace.lean 20.2 s, FiniteCoefficientCup.lean 54.7 s,
TraceCupNaturality.lean 26.4 s. Separate sandbox checks also passed (17.1 s,
33.7 s, 32.2 s respectively); preliminary checks passed for both definition
modules (18.2 s and 31.7 s). Private-overlay checks for the cup and trace
passed in 34.1 s and 20.6 s. Every invocation retained the 60-second limit,
nice 19 and two threads; library outputs were private temporary artifacts.
This supplies concrete reproduction of the immutable report's otherwise
non-specific validation assertion. No Lean changes or further compilation
are needed for the report-only fix.

The independent review changes only this report (H11). No source correction or
citer audit is required. No deliver2.py or global build was run by the reviewer.

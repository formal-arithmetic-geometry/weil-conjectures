## Worker report

Restated `CategoryTheory.filteredHomology_tower_differential` in
`Sheaf.CategoryTheory.FilteredHomologyTowerDifferential`, with its sole theorem proof `by sorry`.
The natural statement, statement dependencies, proof plan and proof dependencies are unchanged.
The module uses the current upstream convergence/derived-couple modules and the existing
filtered-complex and concrete-homology-couple interfaces. No new notion or helper is introduced.

This is the restatement requested by the node's `lead_note`: the former declaration was
withdrawn after upstream sync e47efb5a5, with an unknown `comparisonLift` error. Its signature
survives in `lean_before_upsync_e47` and in the shared historical module. That withdrawn module
is not a usable published binding to record as `existing: true`. The delivery retains its
signature and updates the direct imports and proof docstring. There is no
`coord/repair-notes/lem-sp-filtered-homology-tower-differential.json` in the shared repository.

Clause-by-clause correspondence:

| Natural hypothesis or clause | Lean rendering |
| --- | --- |
| An abelian category C | `(C : Type u) [Category.{v} C] [Abelian C]`; both universes are explicit and independent. |
| Each finite filtered integer cochain complex V | The universal `U` binders in `hBZ`, `eH`, `hH` have type `ObjectProperty.FullSubcategory (fun W : FilteredObject (CochainComplex C ℤ) ↦ W.filtration.IsFinite)`. The fixed complex has the same type in the later `U` binder. |
| For all p,q,r with r ≥ 1, boundaries lie in cycles | `hBZ` quantifies `(p q r : ℤ) (hr : 1 ≤ r)` and asserts `complexBoundaries p (p + q) r ≤ complexCycles p (p + q) r`. |
| First quotient identified with graded homology | `eH` is the isomorphism from `cokernel (Subobject.ofLE _ _ (hBZ U p q 1 ...))` to `(U.obj.filtration.gradedPiece p).homology (p + q)`. |
| First representative maps z and g | `hH` existentially supplies the two arrows from `complexCycleRepresentatives p (p + q) 1`, into `complexCycles ... 1` and graded-complex `cycles (p + q)`. |
| Both maps induce the graded quotient of representative inclusion | The first two conjuncts of `hH` compose `z` with the cycle-subobject arrow and `g` with `iCycles`; each equals the representative-subobject arrow followed by `(complexQuotientπ p (p+1) ...).f (p+q)`. |
| z is epic | Third conjunct `Epi z` of `hH`. |
| z π eH = g π_H | Last conjunct of `hH`, using `cokernel.π`, `(eH U p q).hom`, and `homologyπ`. |
| Concrete homology exact couple X, canonical tower T and initial e0 | All occurrences use the definitions `filteredHomologyExactCouple U.obj.obj U.obj.filtration`, its `cycleBoundaryTower`, and `(filteredHomologyEIso U.obj.obj U.obj.filtration p q).hom`. No arbitrary couple or tower is supplied. |
| Families j_s and t_s for all natural s and integer p,q | Binders `j` and `tQ`; their domains are `complexCycles p (p+q) (s+1)` and their targets are graded cycles and `cycleBoundaryTower.Z s (2*p+q) (-p)`. |
| j_s iCycles is the cycle-subobject inclusion | `hj`, an equality with `(complexCycles p (p+q) (s+1)).arrow`. |
| t_s T.Z.arrow e0 = j_s π_H | `ht` is precisely this composite equality using `filteredHomologyEIso` and `homologyπ`. |
| Any s,p,q; r=s+1, p'=p+r, q'=q-r+1 | `(s : ℕ) (p q : ℤ)`; all r,p',q' expressions are expanded to avoid non-unfoldable statement lets. Natural s is coerced to ℤ at integer arguments. |
| Any test object and four morphisms | `(A : C)`, `a`, `a'`, `x`, `y` have exactly the filtration-step/cycle-subobject source and target degrees stated by the node. |
| Ambient differential of a equals ambient inclusion of a' | `ha`, composing `a` with the filtration inclusion and the ambient `U.obj.obj.d`, and `a'` with its filtration inclusion. |
| Graded projection of a is inclusion of x | `hx`, using the cycle-subobject `.arrow` and degreewise `complexQuotientπ`. |
| Graded projection of a' is inclusion of y | `hy`, the same equation at expanded p',q'. |
| Equality of page differential class and differentiated representative class | The conclusion's left side is `x ≫ tQ ≫ cycleBoundaryTower.projection ≫ (pageCouple s).d ≫ eqToHom ...`; its right side is `y ≫ tQ ≫ cycleBoundaryTower.projection` at p',q'. |
| Integer endpoint transport | `congrArg₂ (pageCouple s).E` uses `2*p+q+2+s = 2*(p+(s+1))+(q-(s+1)+1)` and `-p-1-s = -(p+(s+1))`, both proved by `omega`. |
| No epic x or quotient comparison isomorphism | No such binders occur. The only explicit epicity hypothesis is the source's first-representative normalization `Epi z`; the only input comparison is the source's `eH`. |

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian` (the `def-sp-abelian`
  Mathlib match), including its preadditivity, finite products, kernels and cokernels.
- `WeilConjectures.CategoryTheory.Abelian.Filtration`: `CategoryTheory.DecreasingFiltration`
  and its graded quotient `gr` (the recorded `def-sp-filtration`). Its source was read with
  `scompile.py --source` because that newer module is absent from the older source checkout.
- `WeilConjectures.CategoryTheory.Filtration`: `CategoryTheory.FilteredObject` and
  `CategoryTheory.DecreasingFiltration.IsFinite`; existing compatibility accessors `step` and
  `gradedPiece` are provided by the imported subquotient module through
  `Sheaf.CategoryTheory.Filtration`.
- `Sheaf.Algebra.Homology.FilteredComplexSubquotients`:
  `CategoryTheory.DecreasingFiltration.complexCycleRepresentatives`, `complexCycles`,
  `complexBoundaries`, `complexQuotientπ`. Their definitions use actual subobjects,
  intersections, images, pullbacks and cokernels.
- `Sheaf.CategoryTheory.FilteredHomologyExactCouple`:
  `CategoryTheory.filteredHomologyExactCouple`, `CategoryTheory.filteredHomologyEIso`.
  The exact couple uses the specified concrete homology data and exactness proofs;
  its initial E comparison is an equality isomorphism.
- `WeilConjectures.CategoryTheory.ExactCoupleConvergence`:
  `CategoryTheory.BigradedExactCouple.CycleBoundaryTower`, `cycleBoundaryTower`,
  and fields `Z`, `projection`. The tower fixes successor projections and initial projection;
  its natural index s corresponds to s derivations, as required here.
- Proof-only imports follow the currently recorded plan:
  `WeilConjectures.CategoryTheory.ExactCouple` (`BigradedExactCouple` and its derived maps),
  `WeilConjectures.CategoryTheory.DerivedCoupleExact` (`pageCouple_image_prefix`),
  `WeilConjectures.CategoryTheory.FiniteCycleDerivedComparison`
  (`finiteCycle_derived_comparison`), `Sheaf.CategoryTheory.FiniteCycleFormula`
  (`finiteCycle_formula`), and `Sheaf.CategoryTheory.FilteredHomologyCoupleData`
  (`filteredHomologyG` and the other explicit maps).
  `lem-sp-filtered-homology-tower-forward-representatives` has an empty current `lean`
  record and was also withdrawn; its historical module is not imported. Its role remains
  explicit in the proof docstring. It is only a proof dependency, so no missing notion is
  needed to type this statement.

Source and edge-case checks:

Read `literature/stacks-project/homology.tex`, Section `section-filtered-complex` (Tag 012K),
its displayed Z/B formulas and representative differential, and
`lemma-derived-exact-couple` (Tag 011R) and the subsequent test-object representative rule.
The filtered differential sends `(p,q)` to `(p+r,q-r+1)`. With r=s+1, total degree increases
from p+q to p+q+1; after `(p,q) ↦ (2p+q,-p)`, the shift is `(s+2,-s-1)`, exactly `.d`.
At s=0 (r=1), the target is `(p+1,q)` and the tower projection is the initial projection,
so the formula is the usual first connecting-map/graded-projection calculation. No negative
p or q is excluded. Zero complexes, zero filtration steps, and A=0 are admitted. A constant
nonzero filtration is excluded precisely by the node's finiteness requirement. There is no
lower or upper bound on s and no extra countable-coproduct assumption. No disputed statement
or natural-statement correction was needed.

Searches for an existing match (2026-10-17):

- `msearch.py ... leanfinder "filtered cochain complex exact couple differential on cycle
  representatives equals differential of representative"`: 8 hits, on mapping-cone
  differentials and factorizations, none the tower representative identity.
- `msearch.py ... loogle "CategoryTheory.BigradedExactCouple.d, HomologicalComplex.homologyπ"`:
  zero hits; Loogle does not know the project-specific exact-couple differential.
- `msearch.py ... grep "filteredHomology_tower_differential|cycleBoundaryTower" CategoryTheory`:
  zero Mathlib hits.
- `msearch.py ... leansearch "differential of the spectral sequence of a filtered complex
  on cycle representatives"`: 8 hits on `toCycles`, cycle inclusions, opcycles and total
  complexes; no matching spectral-sequence assertion.
- `rg` for `filteredHomology_tower_differential`, `complexCycleRepresentatives`, and
  `filteredHomologyEIso` across the old `WeilConjectures` source and `lean/Sheaf`: the old
  source has no exact theorem; the shared tree has the withdrawn historical module and its
  consumers. The dependency definitions already exist and are reused.
- The blueprint-id search in the old `WeilConjectures` tree and theorem-name search in
  `dag/lean_names_upstream.json` found no match.
- Read current missing/stale dependency sources through `scompile.py --source` for filtration,
  exact couple, convergence, derived-couple prefix and the concrete homology couple.

Validation: `scompile.py NR lem-sp-filtered-homology-tower-differential <module>` passed the
sandbox and library contexts cleanly (1.5 s and 1.6 s respectively before the final explicit
proof-dependency import). The final delivery dry run recompiles the final module and runs
server preflight. Independent second reading is left to the assigned second worker.

## Second reading by NR

I opened the node, its Stacks source place, the theorem file, and every recorded statement
dependency. The node's objects, hypotheses, and conclusion match the Lean as follows.

- The abelian category is `(C : Type u) [Category.{v} C] [Abelian C]`; the two universes are
  explicit and independent, with no extra finiteness, noetherian, characteristic, or field
  hypothesis.
- A finite filtered cochain complex is the `U` binder in the `ObjectProperty.FullSubcategory`
  of `FilteredObject (CochainComplex C ℤ)` satisfying `U.obj.filtration.IsFinite`; `U` is the
  fixed complex used by the later clauses. This is the recorded `FilteredObject` and its
  upstream `DecreasingFiltration`, not a private copy.
- The all-`V` boundary-cycle assumption is `hBZ`, with every integer `p,q,r`, `1 ≤ r`, and
  `complexBoundaries p (p+q) r ≤ complexCycles p (p+q) r`.
- The all-`V,p,q` first-page comparison is `eH`, exactly the isomorphism from
  `cokernel (Subobject.ofLE _ _ (hBZ ... 1 ...))` to graded-piece homology.
- The representative normalization is `hH`: its `z` and `g` have the node's source and
  targets; its first two equations identify both composites with the representative graded
  quotient; `Epi z` is present; and its last equation is precisely `z ≫ π ≫ eH.hom =
  g ≫ homologyπ`.
- The concrete exact couple, canonical cycle-boundary tower, and initial equality isomorphism
  are fixed definitions `filteredHomologyExactCouple`, `.cycleBoundaryTower`, and
  `filteredHomologyEIso`, so no arbitrary couple or tower is introduced.
- The families `j` and `tQ` have exactly the node's domains and codomains. `hj` is the graded
  cycle-subobject equation and `ht` is the tower-arrow/e0 equation.
- The test data are `(s : ℕ) (p q : ℤ)`, `(A : C)`, `a`, `a'`, `x`, and `y` at the displayed
  filtration steps, degrees, and cycle subobjects. `ha`, `hx`, and `hy` render the three node
  hypotheses without an added epicity or comparison-isomorphism assumption.
- The conclusion is the equality of the page differential class of `x` and the tower
  projection of `y`, including the explicit `eqToHom` transport. The two `omega` equalities
  transport the endpoint from `(2*p+q+2+s,-p-1-s)` to
  `(2*(p+(s+1))+(q-(s+1)+1),-(p+(s+1)))`, exactly the node's `(p',q')`.

The source check used Homology Tag 012K's displayed `Z_r`/`B_r` formulas and representative
differential, and Tag 011R's derived-couple representative rule. The Lean uses the recorded
subquotient definitions (actual pullbacks, images, and cokernels), the recorded concrete
homology couple, and the upstream `CycleBoundaryTower`; no source hypothesis is silently
added or omitted. The edge cases are covered: `s = 0` gives `r = 1`; all integer `p,q` are
allowed; zero complexes, zero filtration steps, and `A = 0` are allowed; empty support or
empty index data are not excluded; and the category universes remain independent. The finite
filtration condition is exactly the node's condition, so no extra boundedness convention was
introduced.

For the one-definition check, I searched the old upstream `WeilConjectures` tree, the shared
`lean/Sheaf` tree, `dag/lean_names_upstream.json`, Mathlib, and the three msearch modes recorded
in `searches.jsonl` (LeanFinder, Loogle, and LeanSearch/grep). There is no existing declaration
of this theorem or of a duplicate tower-representative identity. I also read the current source
bindings with `scompile.py --source` for `WeilConjectures.CategoryTheory.Filtration`,
`WeilConjectures.CategoryTheory.Abelian.Filtration`,
`WeilConjectures.CategoryTheory.ExactCoupleConvergence`,
`Sheaf.Algebra.Homology.FilteredComplexSubquotients`, and
`Sheaf.CategoryTheory.FilteredHomologyExactCouple`; each recorded dependency is the notion
used by the theorem. The withdrawn pre-sync declaration is not an existing usable binding.

No mismatch was found, so no Lean or node statement change was necessary. The module compiled
cleanly with `scompile.py` (sandbox and library checks, no warnings beyond the permitted
`sorry` declaration). No `STATEMENT-DISPUTED` flag, new node, dependency repair, or statement
correction is required.

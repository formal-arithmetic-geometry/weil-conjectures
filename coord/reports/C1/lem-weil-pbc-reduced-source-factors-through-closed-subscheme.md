## Worker report

The module `lean/Sheaf/Paper/ReducedSourceFactors.lean` states
`AlgebraicGeometry.reduced_source_factors_through_closed_subscheme`. It uses
`Scheme` and `Scheme.Hom` from Mathlib for schemes and morphisms, `IsReduced Y`
for the reduced-source hypothesis, and `IsClosedImmersion i` for the closed
immersion. The first conjunct is the equivalence: the existence of
`g : Y ⟶ Z` with `g ≫ i = f` is the factorization clause, and
`Set.range f.base ⊆ Set.range i.base` is the set-theoretic image inclusion.
The second conjunct is the stated special case: there exists
`g : Y ⟶ X.nilradical.subscheme` with
`g ≫ X.nilradical.subschemeι = f`, expressing factorization through the
reduction. `Scheme.nilradical`, `IdealSheafData.subscheme`, and
`IdealSheafData.subschemeι` are Mathlib's reduction construction.

Dependencies used are the Mathlib declarations `AlgebraicGeometry.Scheme`,
`AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.IsClosedImmersion`,
`AlgebraicGeometry.IsReduced`, `AlgebraicGeometry.Scheme.nilradical`,
`AlgebraicGeometry.Scheme.IdealSheafData.subscheme`, and
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeι`.

Edge cases checked: the source scheme may be empty; the image inclusion is
formulated with `Set.range` and imposes no nonemptiness assumption. The target
closed subscheme may be empty, and the reduction clause remains quantified by
existence. No finiteness, separation, characteristic, or universe restriction
beyond a common explicit universe for the three schemes is added.

Searches: the node's recorded LeanSearch query found only
`IsClosedImmersion.lift`; LeanFinder found no reduced-source factorization
statement; grep of Mathlib AlgebraicGeometry found no such theorem. `rg` over
`WeilConjectures/` and `lean/Sheaf` found no existing declaration for this
statement. The Mathlib declarations above provide all notions used.

No statement correction or disputed statement was needed.

## Earlier second reading (a previous round; superseded)

The statement was reread against the node clause by clause. `X`, `Y`, and `Z`
are schemes; `[IsReduced Y]` is the reduced-source hypothesis; `i : Z ⟶ X`
with `[IsClosedImmersion i]` is the closed immersion; and `f : Y ⟶ X` is the
map under consideration. The first conjunct matches both directions of the
factorization/image equivalence, with composition orientation `g ≫ i = f`.
The second conjunct exactly records factorization through the canonical
reduction immersion. No clause or hypothesis was added or omitted.

## Second reading by C1

Read the sandbox node and module, all four statement-dependency nodes, and
the actual Mathlib declarations they record. Read the source TeX on the server,
`literature/stacks-project/schemes.tex`, lines 2240–2295, including
`lemma-map-into-reduction` (Tag 0356). The local literature checkout lacks this
file; the server copy and https://stacks.math.columbia.edu/tag/0356 agree.
The source imposes no base-field, Noetherian, separation, or finiteness assumption.

Clause-by-clause list and verdicts:

- Object `X`, an arbitrary scheme: `{X Y Z : Scheme.{u}}`. PASS.
  `Scheme` in Mathlib/AlgebraicGeometry/Scheme.lean:42 is a locally ringed
  space with affine neighbourhoods; `Scheme.Hom` at line 74 gives morphisms
  of locally ringed spaces, exactly the recorded `def-pc-scheme` notions.
- Object `Z` and morphism `i : Z → X`, a closed immersion:
  `(i : Z ⟶ X) [IsClosedImmersion i]`. PASS. The recorded
  `def-weil-closed-immersion` match at Morphisms/ClosedImmersion.lean:45
  is a closed embedding with surjective stalk maps, equivalent to the
  node's surjective sheaf map. No reducedness of `Z` is assumed.
- Object `Y`, reduced: `[IsReduced Y]`. PASS. The recorded
  `def-pc-reduced-scheme` declaration in Properties.lean:69 requires every
  ring of sections to be reduced; lines 74 and 84 give its equivalence with
  reduced stalks, precisely the node's definition and equivalent clause.
- Object `f`, an arbitrary scheme morphism `Y → X`: `(f : Y ⟶ X)`. PASS.
  No condition on `f` is present beyond having the given source and target.
- Conclusion, factorization iff set-theoretic containment:
  `((∃ g : Y ⟶ Z, g ≫ i = f) ↔ Set.range f.base ⊆ Set.range i.base)`.
  PASS. `g ≫ i` is `i ∘ g`; `base` is the underlying continuous map, so
  these ranges are exactly `f(Y)` and `i(Z)`. Both directions and the
  existential factorization are present, without an added uniqueness clause.
- Conclusion, every such `f` factors through `X_red → X`:
  `(∃ g : Y ⟶ X.nilradical.subscheme, g ≫ X.nilradical.subschemeι = f)`.
  PASS. Read `Scheme.nilradical` at IdealSheaf/Basic.lean:529 (radical of
  the zero ideal sheaf), and `subscheme` and `subschemeι` at
  IdealSheaf/Subscheme.lean:454 and 472. They are exactly the recorded
  `def-weil-pbc-scheme-reduction` construction. `support_nilradical` and
  `range_subschemeι` identify its underlying image with all of `X`.
  The conjunction under the same universally quantified `f` gives both
  source clauses in their stated order.

Edge cases: `Y` can be empty, in which case its range is empty and the
factorization exists; no `Nonempty` instance excludes it. `Z` can be empty:
image containment then forces `Y` empty. An empty `X` is also allowed.
The zero ring and its empty spectrum are allowed by `Scheme`, with no
`Nontrivial` binder. There is no index set or numeric parameter, so empty
indices and `n = 0` impose no additional cases. Every characteristic is
covered, with no field binder. `u` is arbitrary, and all morphisms live in
Mathlib's category `Scheme.{u}`; any finite collection of schemes may be
placed in a common universe. No independent testing universe is used.

Independent searches (different wording from the worker):

- `msearch.py ... leansearch "map from reduced scheme into closed subscheme iff
  containment of image"`: service returned Internal Server Error; recorded
  as unavailable, not as evidence of absence.
- `msearch.py ... leanfinder "nilradical subscheme universal property maps from
  reduced schemes"`: eight hits, including `Scheme.nilradical`,
  `nilradical_eq_bot`, and `support_nilradical`; no exact full statement.
- `msearch.py ... loogle "AlgebraicGeometry.IsClosedImmersion.lift"`: four
  hits, all requiring kernel containment, without the image/reducedness premise.
- `msearch.py ... grep "reduction|reduced.*factor|factor.*reduced|nilradical.*lift|
  lift.*nilradical" AlgebraicGeometry`: reduction of elliptic curves,
  not the scheme statement.
- Direct `rg` on Mathlib, `WeilConjectures/`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, using `reduced...factor`, `factor...reduced`,
  `nilradical...lift`, `0356`, and `map.into.reduction`: opened the relevant
  source and project hits. The project's `field_point_factors_through_closed_immersion`
  is restricted to `Spec K`, so is not this statement. The source's
  `IsClosedImmersion.existsUnique_fac_of_range_subset_range` in
  WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean:186
  gives only the containment-to-unique-factorization direction.
  `Scheme.Hom.liftNilradical` and `liftNilradical_subschemeι` in the source's
  IdealSheaf/Subscheme.lean:419–424 provide only the reduction clause.
  `Compactification.ValuativeCriterion.ker_imageι_le_ker` additionally
  fixes a quasi-compact dominant map and is not the node's statement.
  None is a declaration of the complete equivalence together with its
  reduction clause. All notions already exist in Mathlib; no new definition
  node, dependency module, or private copy is needed.

Mismatches and repairs: no H3 signature mismatch or node correction was found.
The original proof docstring named six topics but did not supply the complete
proof or its cited nodes (H8). Expanded it to all six DAG steps: the image
direction; pointwise vanishing using local stalk maps; intersection of primes,
nilpotence and reducedness; vanishing on an affine cover by the sheaf property;
closed-immersion lifting; and the reduction application. Added the conventional
copyright/license header and placed the module docstring immediately after
imports (H9). Removed the redundant Basic import (transitively imported by
ClosedImmersion), the unused Limits opening, and the unused universe `v`.
The theorem signature and the node's `lean.statement` are unchanged and agree
verbatim. Every variable and the sole universe `u` are explicitly bound.
There are no definitions or auxiliary proofs; the only proof remains `sorry`.

Validation: compiled the delivery module with `scompile.py` against the server's
green library; no errors or warnings except the permitted declaration-uses-sorry
warning. The delivery dry run passed preflight and compilation with `OK` before pushing.

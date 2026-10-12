## What changed

Repair of reviewer X-9d08a's return on head 9d08aa082. The theorem
`AlgebraicGeometry.IsCurve.algebraicallyClosedCohomologyInvariant` keeps its original signature
and existing public imports. Its proof still obtains `IsCurve.Assertions` from
`primeCoefficientCurveAssertions` and applies the C7 projection. Its declaration docstring and
its delivered node now describe exactly those two steps.

The existing split theorem `AlgebraicGeometry.IsCurve.primeCoefficientCurveAssertions` keeps
its signature and sole named `sorry`. Its module now has the required title, source labels,
and its own blueprint tag. Its declaration docstring gives all nine reduction steps, with
explicit dependency ids. Its node records those same steps and the union of their dependencies,
rather than an uncited instruction to carry out the whole argument. The coefficient step
establishes the full assertion package; C7 extraction belongs to the item, not the split.
The new node's self-contained statement spells out C1--C8 with their conditional hypotheses.

The repair also corrects the search record: LeanSearch returned a server error, not a proof
of absence. The blueprint provenance points through the item to its imported ancestor
`prop-weil-pbc-algebraically-closed-extension`. No definition or existing statement changed.

## Proved and sorry left

- `AlgebraicGeometry.IsCurve.algebraicallyClosedCohomologyInvariant`: its one original
  `sorry` is replaced by the compiled assertion-package/C7 proof.
- `AlgebraicGeometry.IsCurve.primeCoefficientCurveAssertions`: the only `sorry` in this
  delivery; node `e1-prime-coefficient-curve-assertions`, now with a complete reduction plan.

This is a reduction, not an axiom-free closure: the item still depends on the split theorem's
`sorry`. No additional theorem, anonymous hole, private hole, hollow definition or axiom is
introduced by this repair. The assertion package has seven additional clauses besides the
item's C7 conclusion, and the item performs the actual structure projection with the supplied
field-extension square and degree.

Both delivered Lean modules compiled with `lcompile.py --all`, exit code zero. The final
dry-run additionally checks them locally and on the server and runs the stage-3 preflight.

## No longer needed

No import was removed. The sole added import in the item is the proof-only import of
`Sheaf.AlgebraicGeometry.Curve.PrimeCoefficientCurveAssertions`; the split module publicly
imports `WeilConjectures.AlgebraicGeometry.Curve.Assertions`, needed by its statement.

The item's old direct proof dependencies now belong under the split node. This is a change of
where the argument is recorded, not pruning those dependencies from the target's closure.
In particular the zero-dimensional, smooth, normalization, dense-open, trace, filtration,
finite-pushforward, finite-open-comparison and Zariski-main arguments are still required by the
split plan. No lower node or module is claimed globally unnecessary. The repaired item has
exactly three direct proof dependencies: `e1-prime-coefficient-curve-assertions`,
`def-weil-pbc-eight-curve-assertions`, and `def-weil-pbc-C7`.

## Where the brief, the DAG or earlier work was wrong

The previous delivery moved the geometric proof into one uncited step (`uses: []`), while
leaving the old proof in the item node. Its docstring said only that the proof follows the
reductions. Its report incorrectly claimed those lower dependencies had been pruned and that
the metadata agreed with the Lean proof. The actual declarations for the lower reductions do
exist; the unfinished work is combining them and handling the coefficient-category glue,
not their absence. Those claims are corrected here.

The earlier three search records overstated LeanSearch's failed request and Loogle's unknown
project identifier as successful absence searches. The records now state the actual results.
No mathematical statement was weakened to repair the proof.

## New nodes

`e1-prime-coefficient-curve-assertions` is the already-delivered new node, repaired here.
It states the full `IsCurve.Assertions (ULift (ZMod r)) f F` package on reduced proper curves,
with the item hypotheses before choosing an extension or degree. Its module is
`lean/Sheaf/AlgebraicGeometry/Curve/PrimeCoefficientCurveAssertions.lean`. Its nine steps
retain the source route, and its proof dependencies are precisely the union of their `uses`.
There are no further new nodes and no change records.

## Review by F1

This is the dispatcher-started repairing worker's substantive review of the returned delivery.
No independent lead or second worker was started in this repair session; the next reader
must still make the independent delivery decision. The review below records the checks made
with the sources, Lean modules and node records open, rather than certifying another person's
work as reviewed.

Source reading: the local clone has no downloaded Stacks source, so the current upstream
`etale-cohomology.tex` was obtained in the item's sandbox scratchpad. Read lines 15377--15745:
0A5B (`lemma-constant-smooth-statements`), 0A5C (`lemma-ses-statements`), 0A5D
(`lemma-finite-pushforward-statements`), 03SG (`lemma-even-easier`), 0A3Q
(`lemma-somewhat-easier`), 03SD (`lemma-vanishing-easier`), and 03SC
(`theorem-vanishing-affine-curves`). Also read the public Stacks pages for 03SC, 03SD, 0A3Q
and 03SG and checked the finite-open comparison declaration for 0GJ1
(`lemma-compatible-shriek-push-finite`). Read `dag/units/sk-thm-p1.json`, particularly
step (i) and its `realized` list: the Kummer/Artin--Schreier, normalization, trace and
devissage route is retained. No chapter, unit or target statement is changed.

Hypothesis and conclusion checks against Lean:

- The item and new node both use `k : Type u`, `[Field k]`, `[IsAlgClosed k]`.
  The item additionally quantifies the independent `k' : Type u` with the same field and
  algebraic-closure instances. The split does not fix `k'`: its assertion package quantifies
  every extension. No separability or prime-to-characteristic assumption is added.
- `f : C ⟶ Spec (.of k)` with `[IsCurve f]` means separated, locally of finite type,
  quasi-compact, and `topologicalKrullDim C ≤ 1`, as read in `Curve.lean`. `[IsProper f]`
  and `[IsReduced C]` are present in both signatures. Connectedness, irreducibility,
  smoothness and nonemptiness are not hypotheses of either statement. They occur only in
  auxiliary reductions, where they are supplied by covers, normalization or components.
- `r : ℕ` with `[Fact r.Prime]` permits every prime. The coefficient category is exactly
  `ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))`, with
  `[Scheme.IsConstructibleSheaf F]`; the universe lifts are retained. Every stalk and
  section is killed by r. Since this coefficient ring is finite and Noetherian, the
  finiteness and devissage statements' coefficient hypotheses are satisfied.
- The item has `{C'}`, `{ι}`, `{f'}`, `{ι'}` and `h : IsPullback ι' f' f ι` with exactly
  the same orientations as `Assertions.bijective_cohomologyMap_of_isProper`. There is no
  restriction to a chosen pullback object. `q : ℕ` includes q = 0, and the projection uses
  the same `sheafCompose`/`forget₂` underlying abelian sheaf and `Etale.cohomologyMap`.
- Read all eight structure fields in `Assertions.lean`, not just its module prose.
  C1: q > 2; C2: `[IsAffine C]`, q > 1; C3: prime p, `[CharP k p]`, p-primary F,
  q > 1; C4: constructible and invertible-order F, arbitrary q; C5: proper and
  constructible F, arbitrary q; C6: invertible-order F and arbitrary algebraically closed
  extension/square/q; C7: proper f and arbitrary such extension/square/q; C8: every open
  immersion and surjectivity in degree 2. These are exactly the repaired new-node clauses.
  In particular C4/C6 remain conditional even though constructibility and properness are
  already global hypotheses of the split. The item concludes only C7.

Step checks (the numbers are the split's node/docstring numbers):

1. `lem-weil-pbc-zero-dimensional-cohomology` states finite-product H0 and vanishing in
   positive degrees for separated finite-type dimension-zero schemes; finite stalks follow
   from constructibility. `lem-weil-pbc-zero-dimensional-field-extension` states bijectivity
   for every degree and pullback square. These give all eight clauses, including the H2
   restriction to opens. The step is non-elementary because these cohomology statements
   are cited; deductions from zero groups and finite products are elementary.
2. Read `assertions_constantModSheaf_of_ne_zero` and
   `assertions_constantModSheaf_of_charP` in `SmoothCalculations.lean`: they permit
   disconnected smooth curves and use a finite coefficient quotient. The nodes
   `lemma-weil-pbc-smooth-curve-kummer-localization` and
   `lemma-weil-pbc-smooth-curve-artin-schreier` say exactly this. `thm-sc-main` supplies the
   unit's underlying connected smooth calculations. `lem-sc-smooth-normal` supplies
   normal local rings, and the Noetherian/component leaves supply finiteness. A domain
   has one minimal prime, hence components cannot meet; the finite union of the other
   components is closed, hence each component is open. Empty component-opens give zero;
   the others are dense in an irreducible component. The dense-open node applies because
   constant prime-field sheaves are constructible and killed by a prime. Finite inclusions
   and finite-pushforward assertions transfer the result to X, and short-exact devissage
   assembles it. These are cited non-elementary results, not an elementary smooth-case proof.
3. The normalization node supplies smooth finite-type dimension-at-most-one source,
   finite map and isomorphism over a dense open for reduced X. The finite-pushforward node
   transfers assertions. Over that open, the direct-image definition and extension-by-zero
   stalk formula give identical sheaves; finite pushforward preserves constructibility
   by the Noetherian constructibility node. Both sheaves are killed by r, so both directions
   of the corrected dense-open node apply. It does not assert that normalization pushforward
   equals the original sheaf globally. This step is non-elementary.
4. Read `exists_finite_etale_reduction` in `LocallyConstantReduction.lean`: its hypothesis
   is irreducible U and finite locally constant prime-field coefficients. It gives finite
   etale connected V, degree not divisible by r, constant-quotient filtration and a unit
   retraction. The retract assertion node requires preservation of constructibility,
   prime-to-characteristic and primary type. Constructibility uses the finite-pushforward
   node; the latter types follow since both sheaves are killed by the same prime r.
   Extension by zero carries the unit/retraction relation to X. Non-elementary.
5. Zariski main's node states finite factorization of a separated finite-type quasi-finite
   map over a qcqs target. Here finite etale followed by a quasi-compact open immersion
   has these properties, and X is Noetherian. The reduced closed closure stays finite
   by the closed-immersion and finite-composition leaves, and separated/finite-type by
   the finite-over-separated-finite-type leaf. Etale over reduced gives reduced V.
   Integral incomparability gives the dimension bound by contracting prime chains.
   `IsFinite.of_comp` gives finiteness of V into the inverse image of U, since that target
   is separated over U. Its open image is therefore also closed, and is dense, hence all
   of the inverse image. A surjective open immersion is an isomorphism. This proves the
   square is cartesian, not merely an equality of underlying sets. Non-elementary,
   with the small open/closed/dense argument written out rather than hidden in a tag.
6. Read `Etale.isIso_finiteOpenComparison`: it uses open immersions, finite map and the
   cartesian square of step 5, and identifies exactly the two sheaves in the step.
   `lem-weil-pbc-curve-assertions-finite-pushforward` then reduces to Y, whose curve
   hypotheses were checked in step 5. Non-elementary.
7. The filtration is the one in the locally constant reduction's statement, not a
   construction taken from its proof. Extension by zero is exact as specified in its
   definition node. Successive short exact sequences have constant extension-by-zero
   quotients. Step 3 handles these quotients on reduced Y; short-exact devissage gives
   the induction, starting from the zero sheaf. Steps 6 and 4 then give the locally
   constant case. Non-elementary; the finite induction is elementary bookkeeping.
8. Read `exists_dense_assertions_iff_forall_lowerShriek` in `Reductions.lean`: it requires
   a reduced curve, finite coefficient ring, prime r, constructibility and r annihilation;
   all hold. It supplies finitely many disjoint irreducible opens, dense union, dimension-zero
   complement, locally constant restrictions and the exact assertion equivalence used.
   Steps 4--7 prove each right-hand clause. The equivalence gives the full assertion
   package; C7 is not used as an unproved input. Non-elementary.
9. The constructible-torsion/modules-agree node identifies the prime-torsion abelian and
   module structures and their finite-stalk stratifications. Underlying abelian sheaves
   and their maps are those in the eight-assertion definition. The scalar r kills every
   section, so torsion and Noetherian coefficient hypotheses are available. Sheaf functors
   commute with forgetting this prime-field structure via inverse-image colimits,
   direct-image products and extension-by-zero stalks. The conversion is still work for
   the split's next prover; it is not claimed to have been formalized in this delivery.
   The step is marked non-elementary and cites the conversion node.

For the item itself, step 1 cites the new assertion-package node. Step 2 is elementary:
`Assertions.bijective_cohomologyMap_of_isProper hA k' h q` is a structure projection,
with precisely the properness instance, square and degree already supplied. The item's
`proof_deps` is the union of those two steps' citations. The overlay dependency check found
no dependency returning to either delivered node; no new cycle was introduced.

New-node B1--B7 and search checks:

- B1: status `split`, with nine explicit proof steps and their dependency union; it is
  not an unsplit node carrying an undocumented proof or an empty dependency list.
- B2: k, f, C, r, R, F and every conditional assertion are introduced in its statement.
- B3: statement dependencies name algebraic closure, reducedness, properness, curve
  setting, constructible module sheaves and the definition of the eight assertions;
  the latter defines their pullbacks and primary/invertible-order hypotheses.
- B4: the repaired new statement uses ordinary single-escaped TeX in the parsed JSON.
  The inherited proof steps' doubled mathematical escapes were normalized as well.
- B5: sources name the actual tags and TeX labels, not moving theorem numbers.
- B6: the new node is not a Mathlib leaf; its Lean record names its module and exact
  declaration. Existing geometric Mathlib leaves are cited with their recorded matches.
- B7: reran all searches through `msearch.py` so each query is logged. LeanSearch:
  `constructible prime coefficient curve cohomology assertions`, HTTP/server failure,
  recorded unavailable. Loogle: `IsCurve.Assertions`, unknown indexed identifier,
  not a global absence proof. LeanFinder: `all eight etale cohomology assertions for
  constructible prime field sheaves on reduced curves`, eight ring-theoretic etale
  results, none a match. Mathlib grep: `primeCoefficientCurveAssertions`, zero hits.
  Library rg found the smooth packages, dense-open reduction and filtration declarations
  read above; none directly supplies the full constructible package on a reduced curve.
  `blueprint_refs.py search 'eight assertions'` found the assertion definition,
  dense-open localization, devissage and `thm-sc-main`; all relevant statements are used,
  and none is a duplicate of this constructible reduced-proper assertion package.
  Grep by 03SC/03SD/0A3Q/03SG found the same source reductions and the ancestor extension
  theorem. The new node records that ancestor and the precise intermediate place.

Edge-case tests, by reading the claims on these cases (not extra Lean theorems):

- Empty C and F = 0: zero cohomology in every degree; a zero-to-zero map is bijective;
  the assertion package is valid. For an empty dense-open family, the universal assertion
  over `Fin 0` is true and the localization equivalence covers it.
- C = Spec k or a finite disjoint union of such points: only H0 survives, with a finite
  product of finite stalks; extension preserves it. `IsCurve` does not exclude these cases.
- U empty, filtration of length zero, or zero locally constant G: extension by zero is
  zero, and the induction starts from zero; no nonzero-rank assumption is introduced.
- Characteristic zero and r different from characteristic: use the Kummer branch. For
  r = characteristic p, C3 applies; C4/C6 require prime-to-p coefficients and are not
  claimed unconditionally. Nonproper auxiliary covers/opens are allowed: C5/C7 stay
  implications with properness as hypothesis.
- q = 0 and the identity field extension: C7's projection includes them, with the original
  pullback map. No restriction to positive degrees or nontrivial extensions is made.
- Reducible singular reduced curves: normalization is used only over its dense isomorphism
  locus, with dense-open localization restoring the entire curve.

Return-by-return changes: D2/C1/C2/B1 was sent back as an uncited all-in-one reduction and is
replaced with the nine steps above and their complete `proof_deps`; H8 was sent back for
missing titled source docstring and proof prose and is repaired in the split module;
point 6 was sent back for the stale item node and is repaired with its two actual Lean
steps, dependency union and proof origin; A2/F1--F4/H11 was sent back for the absent review
and generic second reading and is replaced by this file-specific review and the reading
below. The repairing worker applied these changes directly; no fictitious additional lead
request or independent second-reader approval is recorded.

## Earlier second reading (a previous round; superseded)

The previous round's second reading was returned by X-9d08a and is superseded by this repair
reading. Independent second-reader approval remains the next dispatcher's step.

Opened both Lean files and both node records after the repair. Checked each binder listed
in the review above: the item has exactly the original fields, schemes, morphisms, pullback
square, prime, constructibility instance, degree and coefficient universes. Its conclusion
is the same cohomologyMap on the same underlying abelian sheaf. The split retains exactly
its former signature and spells out all eight structure fields in the node statement.
The new node's module/declaration and blueprint tag now agree, and its nine numbered prose
steps in Lean are generated from the same nine node steps with the dependency ids retained.
The item has two prose steps and its code has `have hA` followed by the C7 projection.

The one outstanding mathematical obligation is the full assertion package, with its actual
geometric and coefficient reductions visible. The remaining `sorry` is exactly the public
split theorem, not a private helper or a changed definition. The actual Lean combination
extracts a proper-base-change clause from a larger package; it does not use an axiom or
state the item's bijectivity under a second name. The unit's smooth-curve route, dense-open,
trace, normalization and devissage remain in the split plan. No global pruning is claimed.
The source cases and hypotheses are checked step by step above rather than inferred from a
successful compile. Both modules compile; the independent next reader can inspect the
same finite set of files and rerun the prescribed dry-run before delivering.

## Second reading by F1

1. **Visible changes:** Compared the delivered item with the repository version. Its theorem
   binders and conclusion are byte-for-byte unchanged; the only item change is a proof-only
   import and proof. The added split module and node are new files, as declared in this report.
   Verdict: pass.
2. **Proof checks:** Compiled both modules with `lcompile.py --all`; there are no errors,
   warnings, forbidden declarations, or `sorry` in the item. The one remaining `sorry` is the
   named public split theorem `primeCoefficientCurveAssertions`, with its node and source
   docstring. The item proof is exactly the C7 projection from that theorem. Verdict: pass.
3. **Truth and strength:** Checked the item and split signatures, all instances, universes,
   pullback orientation, coefficient category, arbitrary degree, and conditional C7
   hypotheses. The item conclusion is exactly the original bijectivity statement. The split
   statement is the full assertion package needed by the projection and introduces no extra
   hypothesis. Edge cases and the source reductions are recorded above. Verdict: pass.
4. **Pruning and route:** The item uses only the split theorem and the two C7 declarations;
   the old geometric dependencies are retained in the split node's nine-step plan. No unit
   route is bypassed, and no import can be removed without losing the proof. Verdict: pass.
5. **DAG agreement:** The item node records the two Lean proof steps and their exact direct
   dependencies. The split node records its declaration, nine reduction steps, dependency
   union, source, and blueprint. Verdict: pass.

Changed during this reading: appended this file-specific review section only. No Lean code,
statement, definition, node, or import was changed.

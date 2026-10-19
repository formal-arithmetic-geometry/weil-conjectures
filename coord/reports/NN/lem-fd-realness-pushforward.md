# lem-fd-realness-pushforward — NN stage-1 delivery

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-fd-realness-pushforward.json`: statement, split; no Mathlib match. Nine proof steps, no new nodes and no Mathlib leaves.
- `citations.json`: 25 step/node pairs, with quotes copied verbatim from the current cited statements.
- `report.md`: this report. Search command results remain in `searches.jsonl`; local preparation scripts are sandbox-only support files.

## Attachments

No attachment for the item. Searching the whole available `WeilConjectures/` tree for the blueprint id, the audited declaration names, and reality/pushforward notions found no declaration stating this item. The audited `DeligneLaumon/AffineLine/RealPushforward.lean` file is absent. `isReal_higherLowerShriek_of_isAffine_fiber` in `Reduction/RelativeAffineLine.lean:213` assumes lissity and weight-zero purity, and has `sorry`; it is not an attachment.

Audit-frontier reconciliation (existing-node ownership only, not claims of closed proofs):

- `AlgebraicGeometry.ProEtale.finiteLowerStar_singleFunctor_of_isAffine` belongs to `lem-sf-adic-affine-direct-image-finiteness`. I read the declaration at `SixFunctors/ProEtale/Adic/LowerStar.lean:411` and the existing node's full concrete adic statement and recorded Lean declaration. Its proof in this read-only checkout is `sorry`. This concrete adic result is not substituted for a theorem in the completed coefficient categories.
- `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriek_toComplex_iso_of_isOpenImmersion` belongs to `prop-functor-package`; its existing audit already records that exact declaration. The old module is absent here. The split uses the current package statement rather than importing a missing declaration's undocumented content.
- `AlgebraicGeometry.WeilSheaf.isZero_higherLowerStar_of_isFinite` belongs to `lemma-weil-pbc-finite-direct-image-exact`; the existing audit already records that exact declaration. The old `QuasiFiniteVanishing.lean` is absent here. No duplicate finite exactness lemma is created.
- The audited `WeilSheaf.sum_trace_compactlySupportedCohomology` source module `WeilSheaf/GrothendieckLefschetz.lean` is absent here. Its name does not justify an attachment or a guessed new statement. The coefficient trace identity actually used is the current `thm-trf-grothendieck-lefschetz-qbar`, with its hypotheses checked in Steps 3–4.
- The two other audited open entries already list `prop-functor-package` and `lem-zl-morphism-open-closed-reduction`; no new frontier item is required for them. These stale audit records are maintainer-owned and retained unchanged.

## WANTED

None for the delivered proof. The unavailable audited Lean modules are a source-checkout/audit discrepancy, not a missing mathematical source used in this split.

## What was wrong and what changed

The item statement is unchanged and is true. Both the archived master statement and the current main-20261015 statement have the same hypotheses and conclusion. No STATEMENT-DISPUTED correction is needed. The current proof is the same argument with the same three stages: trace on a fibre, reality of local traces, recovery of the real characteristic factor. This is the trace/Newton route of the unit; the item is not its key theorem, so no unit realization fields are changed.

The imported proof had two C4 failures. `prop-weil-pbc-strict-henselization-stalk-formula` concerns ordinary `Rf_*` of torsion etale sheaves on a strict local base, not `Rf_!` on a geometric fibre with completed rational coefficients. `cor-trf-point-counting` concerns the constant coefficient unit, not an arbitrary constructible Weil sheaf. Neither node is cited in the repaired proof. The package's actual compact-support base-change clause and the general coefficient trace theorem give the needed statements.

The displayed local exponent was also wrong: an F_(q^(dm))-point above a closed point of X_0 of degree e contributes the dm/e power of its one-circuit Frobenius, rather than its m-th power. Step 6 makes this distinction explicit, using the rational orbit formula, which allows a Weil map that is not invertible on an integral lattice.

The general trace theorem has finite-level hypotheses that the old proof did not discharge. Steps 3–4 supply finite coefficient representatives, lattices, finite-Tor reductions, etale-origin witnesses and the constructible compactification adjunction. They never assert an adjoint on all unbounded pro-etale objects and never use a ring map from a finite quotient to a characteristic-zero field.

Newton identities were cited without a node. I use the existing, Lean-closed `lem-weil-exp-trace-determinant` and the displayed finite coefficient formula of `def-weil-power-series-exponential` to write out both directions by induction. This is the same recovery of characteristic factors from power traces. It introduces no lemma that restates a clause of the item, and no new algebra node: each induction is a few lines from those two existing statements.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for reality, real factors, and realness found no alternative node that states this same concentrated pushforward theorem. The broader relative-envelope reality result has lissity and purity hypotheses absent here; it is not used. The existing algebra lemma is reused, as are all coefficient and base-change inputs.

## Review by NN

I read `coord/brief-stage1.md`, the stage-1 contract, the three levels in SETUP, the chapter and unit records, GOAL, dag-sync, and delivery-errors B–E. I compared the item's complete statement and proof in the archived master and current main-20261015 files. I read the statement of every node cited below. For the algebra source I also read Milne, Lectures on Etale Cohomology, Lemma 27.5 and its proof, printed pages 155–156, and the available `ZetaLinearAlgebra/DetTrace.lean` declaration at line 208. Milne gives precisely the trace-power/log-determinant identity, with the characteristic-zero restriction made explicit in our existing node. There are no new nodes requiring additional sources or new Stacks tags.

1. Step 1 uses the compact-support definition for the completed integral, rationalized and common-stage coefficients, and the functor package for the bounded constructible output and equivariant comparisons. The Weil-complex definition says a constructible Weil sheaf is a Weil object whose underlying object is in the heart. The projection is separated finite type, and the fibre is an affine line over the residue field. Iterating the original degree-one Weil map d times gives the correct residue-field datum; this is not a new descent assertion.
2. Step 2 uses the package's actual arbitrary compact-support base-change clause, including its closing coherence/equivariance assertion. The local-Frobenius definition explicitly interprets cohomology-sheaf stalks as cohomology of the point-fibre complex. These give the stated fibre cohomology and its operator, and the vanishing hypothesis eliminates all degrees other than one. This repairs the incorrect ordinary-direct-image citation.
3. Step 3 uses the common-stage definition's explicit finite-field-of-definition sentence and the raw rationalization definition's same-object property to choose a lattice. The integral-residue-Tor node actually states finite Tor amplitude of all reductions, not just constructibility. The constructible-origin node (ii) actually supplies equivalence on bounded complexes, not only lisse sheaves. Hence its essential surjectivity supplies the chosen etale objects and isomorphisms. The choices do not need an invertible lattice Weil map; the trace theorem expressly does not assume one.
4. Step 4 uses the ambient-adjoint-class node for the class-restricted constructible adjunction and refinement comparisons, ctf-stability for both functor restrictions, preservation-class for uniform signed bounds, and the package for the composition and exchange coherence. I checked that their schemes are finite type over the fixed algebraic closure, that all the compactification maps are separated, that the proper compactification has dimension one, and that the target is a separated point. The trace admissibility definition is cited only to specify the datum, with the theorems supplying its existence. This is not an application of a definition as though it proved the adjunction.
5. Step 5 uses the full coefficient trace theorem, whose hypotheses were supplied above; its statement gives finite-dimensionality and boundedness, and the sign is exactly (-1)^1. Point-count finiteness is applied over the residue field, a finite field, with a finite-type affine line as source. The local cohomology degree is zero because the input is a sheaf.
6. Step 6 uses the local-operator definition to compare iterated residue-field and original Weil maps, and the rational Frobenius-powers node for the actual conjugacy result. That node assumes only invertibility at the field stage, exactly what is available. Trace-formal-laws gives conjugacy invariance and the field supertrace. No finite-ring degree formula is silently extended to rational coefficients.
7. Step 7 uses the iota-real definition for reality of P_x, the existing exponential determinant identity for the power-trace series, and the explicit coefficient formula for its exponential. I checked both inductions: inverse coefficients depend only on earlier inverse coefficients; the r>=2 exponential terms in degree n involve only s_j for j<n. The n=1 base case is b_1=s_1. Every operation is a finite rational polynomial operation, so applying iota and complex conjugation is legitimate.
8. Step 8 is the elementary finite sum, using Steps 5–7 and no additional theorem. The negative sign preserves reality.
9. Step 9 reverses the coefficient calculation: real power traces give real exponential coefficients, and the inverse recurrence gives real determinant coefficients. The iota-real definition says precisely that these are the required local factors at every closed point. This argument does not assume Frobenius is semisimple.

For B1–B10 there are no new nodes, invented source tags, or unrun search records. I ran the prescribed search command with LeanFinder, Loogle, LeanSearch and grep, including a second phrasing; all seven returned successfully. I read the returned hits: ordinary sheaf pushforward and matrix characteristic polynomials do not state this Weil compact-support assertion. The exact queries and result names are copied from searches.jsonl, with no match claimed. The existing exponential identity is already a closed project declaration and is not recreated as a Mathlib leaf.

For C1–C8 I checked every cited statement as explained step by step above and copied verbatim quotes to citations.json. Generic statements outside the unit are declared in split_report.tool_uses with their purposes; they support the unit's trace argument, and replace no Fourier or purity result. For D1–D5 the item itself carries the argument, with zero new nodes; the two coefficient inductions are written out. For E1–E7 the statement is unchanged, the invalid citations and degree exponent are repaired, and the coefficient categories are kept distinct. None of the nine steps exceeds 2000 characters or contains an omitted comparison lemma. The operator comparison is the stated equivariance of the existing package, not a new comparison proved inline.

Small cases checked: zero sheaf and zero stalk give determinant 1 and all traces zero; an empty rational-point set gives an empty sum; a unipotent Jordan block causes no problem because the trace-determinant identity has no semisimplicity hypothesis. A point of total degree e=2d contributes exponent m/2 when 2 divides m (and contributes no rational point for odd m), verifying the repaired exponent. For a single scalar lambda the coefficient recursion reads exp(sum lambda^n T^n/n)=(1-lambda T)^(-1), fixing the sign. No new claim excludes rank zero, repeated eigenvalues, or a non-invertible integral presentation of the Weil map.

## Unfinished work

No mathematical split remains unfinished. Stage 1 records dependencies; it does not prove the downstream nodes in Lean. Required dry run and push results will be recorded after the tools finish.

## What changed

Repair of the landing refusal: removed both duplicate private declarations and
replaced their arguments with public Mathlib results. Updated the existing node
proof and proof_origin to match. The earlier independent second reading below
records the pre-repair delivery; the repaired proof needs a fresh second reading.

Filled `AlgebraicGeometry.IsCurve.dense_open_restriction_comparison` without changing
its signature or its public imports. Added proof imports of
`Sheaf.AlgebraicGeometry.Curve.DenseOpenHighCohomology` and
`Sheaf.AlgebraicGeometry.Curve.LowerShriekCoefficientCounit`.

The new coefficient lemma provides a counit-compatible isomorphism between extension
by zero before and after conversion to ULift Z modules. The proof forgets scalars on
that isomorphism, cancels its bijective cohomology map from the existing module counit
comparisons, and uses `Etale.cohomologyMap_map` to form the restriction square. Mathlib's
`Function.Surjective.of_comp_iff'` and `Function.Surjective.of_comp_iff` transfer
surjectivity across the commuting square in both directions.
The existing constructibility hypothesis is preserved, although this argument does
not need it. No definitions or target statements changed.

## Proved and sorry left

Proved `AlgebraicGeometry.IsCurve.dense_open_restriction_comparison`, the sole original
sorry in the item. The returned version's two duplicate private helper declarations
are removed. Their uses are replaced by existing Mathlib declarations, with no new
helper theorem or additional import.

One new sorry remains:
`AlgebraicGeometry.Etale.exists_lowerShriek_coefficient_counit`, node
`lem-pbc-n2-lower-shriek-coefficient-counit`, in the new module
`Sheaf.AlgebraicGeometry.Curve.LowerShriekCoefficientCounit`.
It is precisely the coefficient/adjunction bridge, with no cohomology or surjectivity
in its conclusion; it does not restate the item. The existing
`dense_open_high_cohomology` package supplies both geometric comparison facts and
continues to depend on its already stated higher-degree and open-pullback theorems.

This delivery is a decomposition: one original hole closed and one new hole added,
so its direct net hole reduction is zero. The main theorem still has `sorryAx`
through the coefficient bridge and existing geometric dependencies; no axiom-free
completion of the target is claimed.

Both sandbox modules compile cleanly through lcompile.py. The delivery dry run checks
their axioms and compiles the new independent module on the server.

## No longer needed

The returned delivery's private `AlgebraicGeometry.bijective_H_map_iso` and
`AlgebraicGeometry.surjective_iff_of_bijective_square` are removed. Neither
`Sheaf.AlgebraicGeometry.Curve.FinitePushforwardPullbackComparison` nor
`Sheaf.AlgebraicGeometry.Curve.DenseOpenPrimeAssertions` is needed as an import.
The existing DAG's elementary square step now uses Mathlib cancellation directly.

The six original public imports are preserved; each supplies the unchanged statement
or its coefficient instances. Removed the following eleven original proof imports:

- `Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`.
- `Sheaf.AlgebraicGeometry.CurveCoefficientPair`.
- `Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder`.
- `Sheaf.Paper.ZeroDimensionalCohomology`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`.
- `WeilConjectures.SixFunctors.Finite.Exact`.
- `WeilConjectures.SixFunctors.Finite.Stalk`.
- `WeilConjectures.SixFunctors.OpenClosed.Exact`.

In the new coefficient module, replaced the broad public import of
`WeilConjectures.AlgebraicGeometry.Curve.Assertions` with
`WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients`, which supplies
the abelian and small-site sheafification instances needed by its statement. The following old direct proof dependencies are replaced by the existing
higher-cohomology package and the coefficient bridge:

- `def-weil-geometric-point` (`Mathlib.FieldTheory.IsAlgClosed.Basic`).
- `def-weil-pbc-constructible-torsion` (`Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf`).
- `def-weil-pbc-curve-setting` (`Sheaf.AlgebraicGeometry.CurveCoefficientPair`).
- `def-weil-pbc-direct-image` (`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`).
- `def-weil-pbc-etale-cohomology` (`WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`).
- `def-weil-pbc-extension-pullback` (`WeilConjectures.AlgebraicGeometry.Curve.Assertions`).
- `def-weil-pbc-geometric-stalks` (`Mathlib.CategoryTheory.Sites.Point.Basic`).
- `def-weil-pbc-inverse-image` (`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`).
- `def-weil-pbc-primary-torsion` (`WeilConjectures.AlgebraicGeometry.Curve.Assertions`).
- `def-weil-scheme-morphism-properties` (convention node).
- `lem-weil-pbc-cohomology-pullback-derived-unit` (`Sheaf.AlgebraicGeometry.CohomologyPullbackDerivedUnit`).
- `lem-weil-pbc-extension-by-zero-adjunction` (`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`).
- `lem-weil-pbc-open-closed-short-exact` (`WeilConjectures.SixFunctors.OpenClosed.Exact`).
- `lem-weil-pbc-pullback-cohomology-long-exact-ladder` (`Sheaf.AlgebraicGeometry.PullbackCohomologyLongExactLadder`).
- `lem-weil-pbc-zero-dimensional-cohomology` (`Sheaf.Paper.ZeroDimensionalCohomology`).
- `lemma-weil-pbc-finite-direct-image-exact` (`WeilConjectures.SixFunctors.Finite.Exact`).
- `lemma-weil-pbc-finite-stalk-formula` (`WeilConjectures.SixFunctors.Finite.Stalk`).
- `lemma-weil-pbc-geometric-stalk-conservative` (`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`).

This is a change in direct dependencies, not a claim that every listed node is
unreachable from all targets. In particular, open-closed exactness, finite direct
image, zero-dimensional vanishing and the derived cohomology comparison remain
beneath `DenseOpenHighCohomology`; its existing route is kept. The separate finite
stalk-formula, geometric-stalk-conservativity, primary-torsion and field-extension
steps are not used in this restriction proof. No unit statement or realized unit
step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The current repository item imports the geometric proof dependencies named by its
node; the sandbox replaces these direct proof imports with the two smaller interfaces. The existing higher-cohomology package is the shorter usable interface.
Its module counit is not definitionally the counit in this item: the item applies
abelian extension by zero first, then coefficient conversion. Simply applying that
package would compare the wrong domain sheaf. The new bridge records both the
isomorphism and its counit equality, and the Lean proof uses that equality on X and
after each open pullback.

Mathlib searches were run for both surjectivity transport and the coefficient
bridge. LeanSearch returned an Internal Server Error, recorded as unavailable.
LeanFinder returned site-equivalence and constant-sheaf counit facts, not this bridge;
grep and direct source inspection found adjoint uniqueness and its counit law as
tools. The original delivery copied two private helpers that the landing checker correctly
rejected as duplicate statements. The repair removes both entirely. The first is
replaced by `Sheaf.functorH`, `Functor.mapIso`, and
`Iso.addCommGroupIsoToAddEquiv.bijective`; the second is replaced by the two public
`Function.Surjective` composition cancellation lemmas. The duplicate declarations
in FinitePushforwardPullbackComparison and DenseOpenPrimeAssertions are private,
and the latter module depends on this item, so importing those modules would not
provide a usable replacement. Reusing public Mathlib results avoids that cycle and
the duplicate proofs.

Read Stacks Lemma 0GJA, `lemma-restrict-to-open`, proof and remark (d), from the locally
available Stacks source. The expected literature path is absent in this clone.
Empty opens, the whole open, the empty scheme, and arbitrary (not necessarily
constructible or torsion) abelian sheaves satisfy the coefficient bridge because it
is an adjunction comparison under equivalences. The use of the high-cohomology
package keeps the dense-open geometry of the original proof.

## New nodes

`lem-pbc-n2-lower-shriek-coefficient-counit` states the coefficient conversion of
extension by zero together with the counit identity required in the item. Its
source is the counit arrow in Stacks 095L used in the dense-open proof of 0GJA;
its proof explains objectwise coefficient equivalences, commutation of restriction,
transport of the adjunction, and the counit law for left-adjoint uniqueness.
It is one general categorical part of the argument, with no curve, constructibility,
density, cohomology, or restriction-surjectivity assertion. Searches of the existing
DAG, blueprint and Lean modules found no declaration with this counit-compatible
statement. No change records are needed.


## Earlier second reading (a previous round; superseded)

1. Compared both delivered modules with the repository. The sole existing public
   theorem signature and its docstring are byte for byte unchanged. Its six public
   imports are unchanged. There are no definition changes and no change records.
   Only the existing node's proof, proof_deps and proof_origin differ. Verdict: pass.
2. Both modules compile through lcompile.py. Scratch copies with explicit #print axioms
   show propext, Classical.choice and Quot.sound for bijective_H_map_iso, no axioms for
   surjective_iff_of_bijective_square, and only those three plus sorryAx for the main
   theorem and coefficient lemma. The latter is the sole new sorry, a whole named public
   theorem with its docstring and node. No forbidden declarations or hollow definitions
   occur. The main theorem is a checked reduction, with open dependencies; it is not yet
   free of sorryAx. Verdict: pass.
3. Read the coefficient lemma's statement and complete categorical proof. E is an
   equivalence, including the ULift ring-isomorphism restriction; objectwise equivalences
   preserve sheaves, restriction commutes with coefficient composition, and transported
   adjunctions compare by left-adjoint uniqueness with its counit law. Empty opens,
   whole opens, empty schemes and arbitrary abelian sheaves cause no exceptions.
   The lemma contains no geometric or cohomological assertion and is strictly a part of
   the argument. Independent LeanFinder, Loogle and grep searches used different wording;
   Loogle found leftAdjointUniq_hom_app_counit as a tool, not an exact replacement.
   Inspected the existing inverse-image/forgetful natural isomorphism and open-immersion
   restriction definitions. Completing the transport would require new categorical
   constructions rather than a short application, so the named lemma remains open.
   Verdict: pass.
4. Checked cancellation of the coefficient isomorphism on cohomology, its pullback,
   and the direction of both surjectivity implications in the commuting square.
   DenseOpenHighCohomology is the existing shorter interface. The report now explicitly
   lists all eleven removed proof imports and every one of the eighteen old proof_deps
   absent from the new node. The reduced new-module imports compile with the needed
   coefficient instances. Read dag/units/sk-thm-p1.json: its realized statement and
   steps are preserved, including dense-open reduction by the open-closed sequence;
   this delivery changes only a route below that unit. Verdict: pass.
5. Checked the existing node against each step of the Lean proof, and the new node's
   declaration, verbatim signature, source, proof, proof_origin, searches, creation,
   blueprint, chapter, unit and Lean fields. Its proof_deps are exactly the union of
   the proof-step uses; all dependency nodes exist. Verdict: pass.

Changes by the second reader: corrected the inaccurate claim that no imports were
removed, corrected the description of the current repository's imports, listed the
removed imports, and replaced the new coefficient module's broad Curve.Assertions
import with ConcreteCoefficients. The checked proof bodies were retained.


## Second reading by N2

Fresh independent reading of the repaired delivery, superseding the earlier round.

1. Compared the item with the repository using `diff -u`. The existing theorem's
   signature and docstring are byte for byte unchanged, and its six public imports
   are unchanged. There are no definition changes, target changes, or change records.
   The new coefficient theorem is in its own module. Verdict: pass.
2. Compiled both modules in import order through `lcompile.py --all`, without errors
   or warnings. Compiled scratch copies with explicit `#print axioms` for both public
   declarations: only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` occur.
   The coefficient theorem is the only delivered whole named theorem left with
   `sorry`; there are no forbidden declarations or hollow definitions. The checked
   main proof is a reduction with open dependencies, not an axiom-free proof.
   Verdict: pass as a decomposition.
3. Read the bridge's complete categorical proof and checked the empty scheme,
   empty open, whole open, zero sheaf, and arbitrary abelian sheaf cases. Equivalence
   of coefficients induces equivalences on sheaves; restriction commutes with
   coefficient composition. Transporting the adjunction and choosing the canonical
   left-adjoint comparison gives exactly the required counit identity. This statement
   has no curve, density, cohomology, or surjectivity conclusion and is strictly one
   part of the argument. Fresh LeanFinder, Loogle, and grep searches used equivalence
   and intertwining terminology. They found adjunction-uniqueness tools, including
   `leftAdjointUniq_hom_app_counit`, but no exact replacement. Inspected upstream
   open-immersion restriction and the proved module inverse-image/forgetful comparison.
   Closing the bridge requires the coefficient equivalences and their coherent
   adjunction transport, rather than a short existing theorem application; retained
   the valid named hole. Verdict: pass.
4. Read the proof downward: the counit equality transports the existing geometric
   package through an isomorphism; `Sheaf.functorH.mapIso` gives bijectivity; the two
   composition-cancellation lemmas transport surjectivity across the natural square
   in the correct directions. The duplicate private helpers are gone. The existing
   `DenseOpenHighCohomology` is the shorter available geometric interface. All eleven
   removed imports and all eighteen removed direct proof dependencies are listed
   under No longer needed. Public imports supply statement data or required instances;
   the two newly added imports are proof-only. Read the Stacks dense-open proof and
   remark (d), and `dag/units/sk-thm-p1.json`: no realized unit statement or step is
   bypassed; the dense-open/open-closed route remains beneath the geometric package.
   Verdict: pass.
5. Compared the existing node JSON: only `proof`, `proof_deps`, and `proof_origin`
   changed. They describe the repaired proof, including the Mathlib replacements.
   Checked the new node's signature against Lean, source, natural-language proof,
   searches, creation record, blueprint ancestry, chapter, unit, and Lean record.
   Both nodes' proof dependencies equal the union of their proof-step uses; all
   referenced nodes exist. Verdict: pass.

Changes in this fresh second reading: explicitly classified one hole closed plus
one hole added as a decomposition with zero direct net hole reduction, and recorded
fresh compilation, axiom inspection, searches, and metadata review. No Lean proof,
statement, definition, or node repair was needed.

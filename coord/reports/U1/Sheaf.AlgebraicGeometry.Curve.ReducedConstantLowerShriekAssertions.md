## What changed

Merge-lock return repair (reviewer X-a0009, returned head a0009b451): the
review passed, but landing could not acquire the maintainer merge lock.
The repair uses deliver3.py --no-push to fetch current sheaf-dag and rebuild
the delivery commit on that base, with fresh local and server compilation,
axiom probes and preflight. No mathematical correction was requested in this
return; the reviewed Lean proofs and node statements are preserved. The
second reader must deliver the newly based commit rather than re-push the
returned head.

Repaired both delivered modules. The parent signature is unchanged. Its proof maps
`constantModSheaf_iso_constantSheaf` through `openImmersionLowerShriek`, transfers all
eight assertions along the resulting isomorphism, and applies the reduction-data
transfer to the existence witnesses. Proved the transfer declaration by unpacking its
witnesses and applying `Assertions.lowerShriek_constantModSheaf_of_finite`. Added
proof-only imports of `ConstructibleSheaf.Pullback` and `SmoothBaseChange.Derived` for
constructibility and invertible-order torsion transport. Updated the parent node,
corrected all four new node records, and expanded sourced docstrings.

## Proved and sorry left

`reducedConstantLowerShriekAssertions` and
`reducedConstantLowerShriekAssertions_of_reduction_data` are proved. The private
cohomology equivalence, comparison surjectivity, comparison bijectivity, and assertion
transport helpers are all proved. Both modules compile without warnings.

Exactly one declaration remains `sorry`:

- `exists_reducedConstantLowerShriekReductionData`, node
  `k1-exists-reduced-constant-lower-shriek-reduction-data`.
`constantModSheaf_iso_constantSheaf` is now proved in the second reading, using
`Submodule.quotEquivOfEqBot` and `LinearEquiv.toModuleIso`.

The reduction-data definition contains no `sorry`.

## No longer needed

The new reduction module now publicly imports `SmoothBaseChange.Defs` for its
coefficient statements and imports `Curve.Reductions` only for its transfer proof;
this replaces its unnecessary public `Curve.Reductions` import. No import of the
parent module was removed. The false literal-equality declaration
`constantModSheaf_eq_constantSheaf` is replaced by a sheaf isomorphism. The duplicate
finite-transfer sorry is eliminated: its dependency is the existing
`lemma-weil-pbc-curve-normalization-constant` declaration.

The parent no longer directly depends on
`lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-noetherian-finitely-many-components`, `lem-sc-smooth-normal`,
`lemma-weil-pbc-smooth-curve-kummer-localization`,
`lemma-weil-pbc-smooth-curve-artin-schreier`,
`lem-weil-pbc-zero-dimensional-cohomology`,
`lem-weil-pbc-zero-dimensional-field-extension`,
`lem-weil-pbc-curve-assertions-dense-open`,
`lem-weil-pbc-curve-assertions-finite-pushforward`,
`lemma-weil-pbc-eight-curve-devissage`, `thm-sc-main`, `def-sc-constant-sheaves`,
`lem-weil-pbc-reduced-curve-normalization`,
`lem-weil-pbc-finite-pushforward-constructible-noetherian`,
`def-weil-pbc-extension-by-zero`, `def-weil-pbc-direct-image`, or
`lem-weil-pbc-constructible-torsion-modules-agree` as proof dependencies.
These are not globally pruned: the smooth existence argument and the existing
transfer theorem still need their relevant geometric and cohomological dependencies.
No node or module is claimed unnecessary throughout the target closure.

## Where the brief, the DAG or earlier work was wrong

The previous delivery overlooked the existing transfer theorem
`AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite`,
recorded by `lemma-weil-pbc-curve-normalization-constant`; normalization transfer glue
is therefore not missing as a single declaration. The genuinely unfinished part is
choosing the modification and proving its smooth lower-shriek assertions, together
with the coefficient isomorphism construction. The previous coefficient equality was
unjustified: `Etale.constantModSheaf` uses R/(r), while the parent uses R. Canonical
module equivalence gives an isomorphism. The old transfer dependency on the parent
also formed a cycle; it is replaced by the existing theorem node. The definition node
was misclassified, and its statement failed to describe the existential data.

## New nodes

`k1-reduced-constant-lower-shriek-reduction-data` defines the existential witnesses:
finite surjective modification, smooth composite, dense isomorphism open, cartesian
pullback immersion and eight smooth lower-shriek assertions. Its source is the
normalization paragraph of Stacks 0A3Q; it has no proof dependencies. Blueprint
searches for normalization and 0A3Q found no blueprint definition of this package.
Mathlib searches found normalization machinery, not this assertion-bearing package.

`k1-exists-reduced-constant-lower-shriek-reduction-data` asserts existence of those
witnesses under the reduced-curve and prime hypotheses. Its source is Stacks 0A3Q's
normalization paragraph followed by 03SG's smooth lower-shriek argument. The proof
now cites normalization, finite component decomposition, zero-dimensional cases,
Kummer and Artin--Schreier calculations, `thm-sc-main`, dense-open localization,
finite pushforward and devissage. Blueprint searches for 03SG and 0A3Q found no exact
packaged existence statement. LeanFinder returned normalization and etale-locus
machinery rather than this assertion package.

`k1-reduced-constant-lower-shriek-assertions-of-reduction-data` is now proved by the
existing transfer declaration. Blueprint search for curve-normalization-constant
found `lemma-weil-pbc-curve-normalization-constant`, which is recorded in `same_as`
and is the sole proof dependency. Direct source comparison verified its finite,
surjective, smooth, dense-open-isomorphism, pullback and assertion hypotheses match
exactly the unpacked data. The earlier Mathlib search missed this source-library
result; it is no longer duplicated as an unfinished theorem.

`k1-constant-mod-sheaf-prime-coefficient-identification` now asserts a nonempty
isomorphism from the quotient-coefficient constant sheaf to the R-valued constant
sheaf. Its source is `Etale.constantModSheaf` in `SmoothBaseChange.Defs` and
`Submodule.quotEquivOfEqBot`, followed by `constantSheaf.mapIso`. Blueprint searches
for constant sheaf and quotient by zero found no exact prime-coefficient isomorphism.
LeanSearch was unavailable (Internal Server Error), recorded by the actual search
tool. Loogle returned the constantSheaf functor, and direct Mathlib source inspection
found the quotient-by-zero equivalence. The second reading closes the coefficient-only intermediate theorem, with no curve
assertions in its type, using the existing quotient equivalence machinery.
The correction is recorded in
`coord/changes/constant-mod-sheaf-prime-coefficient-isomorphism.md`.

## Earlier second reading (a previous round; superseded)

1. The parent theorem's signature remains unchanged. Its proof now uses a mapped
   coefficient isomorphism instead of an equality rewrite.
2. Both modules compile without warnings. Exactly the two public named declarations
   listed above remain unfinished; no private helper or definition uses `sorry`.
3. Compared Stacks 03SG's disjoint-component and empty-or-dense argument and 0A3Q's
   normalization paragraph with the new existence statement and its proof plan.
   Compared the recorded existing finite transfer declaration against every unpacked
   reduction-data hypothesis; the duplicate transfer sorry is removed.
4. Compared `Etale.constantModSheaf`'s R/(r) definition with the parent's R object.
   Quotient-by-zero gives a module equivalence and hence a sheaf isomorphism, not
   object equality. Checked all eight transported fields: cohomology equivalences
   preserve C1-C5, geometric stalk isomorphisms transport torsion hypotheses, and
   `cohomologyMap_map` gives the commuting squares for C6-C8.
5. Corrected the cyclic transfer dependency, delivered the parent proof update,
   restored the actual normalization and smooth calculation dependencies, and kept
   `thm-sc-main` and unit `sk-thm-p1`. Checked empty X, empty U, empty component
   intersections, zero-dimensional components, proper and affine branches, and both
   characteristic cases in the natural-language existence argument. Prime r makes
   r zero in R; the coefficient isomorphism needs no nonemptiness hypothesis on U.

## Earlier second reading (a previous round; superseded)

1. Compared the parent module with the repository using diff. Its public imports,
   existing docstring and theorem signature are byte for byte unchanged; only proof
   imports, private transport helpers and the proof body are added. The reduction
   module and four helper nodes are new, absent from the repository. The unlanded
   equality-to-isomorphism correction is explicitly documented by the change record;
   no existing library statement, definition, or target is altered. Verdict: pass.
2. Compiled both modules in import order through lcompile.py, without warnings.
   Inspected every body: no forbidden declarations or attributes, no hollow definition,
   and only exists_reducedConstantLowerShriekReductionData remains sorry. Scratch
   #print axioms checks cover all public declarations and all four private helpers.
   The definition, coefficient theorem and private helpers use only propext,
   Classical.choice and Quot.sound. The parent, reduction transfer and existence
   theorem additionally use expected sorryAx from unfinished dependencies. Verdict:
   valid partial proof, not an axiom-free completion of the parent.
3. Read https://stacks.math.columbia.edu/tag/03SG and
   https://stacks.math.columbia.edu/tag/0A3Q against the witnesses and hypotheses.
   Normalization is finite, smooth over the algebraically closed field, surjective,
   and an isomorphism on a dense open; pulling back j supplies the required square.
   The smooth lower-shriek calculation handles each disjoint component, including
   empty opens and zero-dimensional components, without requiring properness.
   Empty X uses the empty modification and empty dense open; j empty gives the zero
   sheaf. The characteristic branches cover both r invertible and r equal to the
   positive characteristic. The existence split states assertions on the smooth
   source, not the original reduced X; finite transfer is separately applied in Lean.
   Fresh LeanFinder search for smooth-curve lower-shriek cohomology and normalization
   found relative-normalization and algebraic-sheaf machinery, not this package.
   rg of Curve/Reductions and SmoothCalculations found the finite-transfer theorem
   and smooth constant calculations, already used in the route. A fresh Loogle
   quotient-equivalence search found quotEquivOfEqBot; used it to close the second
   split. This coefficient proof also works for empty U and needs no geometric
   hypothesis. Verdict: the sole remaining split is sourced and strictly part of
   the normalization argument.
4. Checked C1-C3 transport by cohomology equivalences, including primary torsion
   transported through the injective stalk isomorphism. C4-C5 transport finite
   cohomology and the constructibility/torsion hypotheses; C6-C8 use naturality
   cohomologyMap_map with the correctly directed isomorphisms. All proof-only
   imports remain plain import. No public import is removed. The No longer needed
   list accounts for every old parent proof dependency: they move below the
   existence/transfer steps rather than becoming globally unnecessary. Read
   dag/units/sk-thm-p1.json realized: the curve-calculation step and thm-sc-main
   remain in the existence plan; no unit step is bypassed. Verdict: pass.
5. Compared all five node records with the Lean declarations. The definition
   records exactly the existential data; the existence node lists normalization
   and the smooth calculation dependencies; the transfer node cites precisely
   lemma-weil-pbc-curve-normalization-constant. The parent lists the three helpers
   it actually applies, and the coefficient node now describes the compiled
   quotient-equivalence proof. Each new node carries its source, searches,
   creation, blueprint, chapter, unit and verbatim Lean signature. Verdict: pass.

Changed in this reading: proved constantModSheaf_iso_constantSheaf by simplifying
its coefficient ideal to bottom, applying quotEquivOfEqBot.toModuleIso and mapping
through constantSheaf. Updated its proof record and this report. A trial explicit
Mathlib quotient import was redundant and removed after compilation. No existing
statement or definition changed. One named split remains; no module is globally
pruned.

## Second reading by U1

1. I compared both delivered Lean modules with the repository versions. The parent
 theorem signature and its docstring are unchanged. The reduction module is new, and
 the coefficient correction is documented by its change record. No target or existing
 public declaration was weakened, strengthened, or given an extra hypothesis. Verdict:
 pass.

2. I compiled both modules in import order with `lcompile.py --all`; both compile
 without errors or warnings. The parent theorem, transfer theorem, coefficient
 isomorphism, and all private transport helpers contain proofs. The sole remaining
 `sorry` is the named existence theorem
 `exists_reducedConstantLowerShriekReductionData`, with its node and sourced
 docstring. No definition is hollow and no forbidden declaration occurs. The proof
 route uses only the permitted ordinary axioms, plus expected `sorryAx` inherited by
 the unfinished existence and geometric calculation dependencies. Verdict: pass.

3. I read Stacks 03SG and 0A3Q. The smooth case is the eight assertion package for
 an open immersion, including the empty-open case; the reduced case uses finite
 normalization, a dense isomorphism locus, smooth pullback, finite pushforward, and
 dense-open comparison. The reduction-data definition and transfer theorem match
 these hypotheses clause by clause. The coefficient statement is an isomorphism from
 the quotient module, as required by `constantModSheaf`, rather than a false object
 equality. Empty schemes, empty opens, zero-dimensional components, and both prime
 characteristic branches remain included. Verdict: pass.

4. I checked every assertion transport in `assertions_of_iso`: cohomology
 equivalences preserve C1--C5, stalk module isomorphisms transport primary and
 invertible-order torsion, and `cohomologyMap_map` gives the commuting maps for
 C6--C8. The coefficient proof uses the existing Mathlib
 `Submodule.quotEquivOfEqBot` and `LinearEquiv.toModuleIso`. Proof-only imports are
 plain imports. The parent node records exactly the three helpers it applies, while
 the existence node retains the normalization and smooth calculation route; no unit
 step is bypassed. Verdict: pass.

5. I compared the node records with the declarations and proof bodies. The transfer
 node cites the existing finite normalization transfer theorem, the coefficient node
 records its quotient-equivalence proof and searches, and the parent node records all
 three actual helper dependencies. The unit `sk-thm-p1` and its curve-calculation
 step remain realized. Verdict: pass.

Changed in this second reading: no mathematical or interface change. I added this
review section, confirmed the repaired merge-lock base, and retained the one sourced
existence split. No additional pruning was found.

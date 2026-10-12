## What changed

Proved `AlgebraicGeometry.epi_etaleCohomology_artinSchreier_one` with its signature
unchanged. Added proof-only imports of the scalar model, SemilinearFrobenius and
RightDerivedFunctor.Triangulated. The proof constructs Frobenius as `wp + id`, proves
its semilinearity by comparing composites with scalar sheaf endomorphisms on sections,
and applies the existing, proved `LinearMap.Frobenius.surjective_sub_id`. The identity
`F x - x = H¹(wp) x` and `AddCommGrpCat.epi_iff_surjective` finish the argument.

Added `AdditiveCohomologyScalarModel.lean`, which constructs scalar sheaf maps, proves
their naturality and zero/unit/addition/composition identities, and constructs all
module axioms on derived cohomology. Added `AdditiveCohomologyFiniteDimensional.lean`
for the remaining comparison/finiteness step. Each new module contains one public
theorem. Updated the item's node and added two matching nodes.

All three modules compile locally without warnings. The required delivery dry run
is the final validation. No target, existing signature, definition or public import changed.

## Proved and sorry left

- Proved `AlgebraicGeometry.epi_etaleCohomology_artinSchreier_one`
  (node `lem-sc-artin-schreier-first-cohomology-epi`); no sorry remains in the item.
- Proved `AlgebraicGeometry.exists_finiteDimensional_etaleCohomology_one_scalar_model`
  (node `lem-sc-additive-cohomology-finite-scalar-model`), from the finiteness theorem.
- The only delivered sorry is
  `AlgebraicGeometry.finiteDimensional_etaleCohomology_one_of_scalar_model`
  (node `lem-sc-additive-cohomology-finite-dimensional`). Its proof is exactly `by sorry`.
  It requires finite-dimensionality for an already specified, section-induced scalar
  action. It has no Frobenius, positive-characteristic or surjectivity conclusion.

Edge cases checked mathematically: in the affine case H¹ is zero, hence finite for
any scalar action. In the proper case the action is the usual action on H¹(O_C),
including positive-genus curves; no vanishing is claimed. Scalars 0 and 1, sums,
products and naturality are proved in Lean, not hypothesized. Lang--Steinberg also
covers a zero cohomology vector space and noninvertible Frobenius.

## No longer needed

Both pre-existing public imports support the item's signature and are unchanged.
Seven proof-only imports were removed from the item: EtaleAffineQcoherentULift,
EtaleZariskiQcohComparison, KInjectiveComputes, RightDerivedUniversalDeltaFunctor,
PQFCohomology, DirectImage.FiniteFreeComplex, and RightDerivedFunctor.PlusSingle.
The affine, comparison, coherent-finiteness and single-object comparison imports
are retained as the proof plan of AdditiveCohomologyFiniteDimensional; that module
also imports IsProperOrIsAffine. Compactification remains beneath that dichotomy.
The following three dependencies are no longer needed by this argument:

- `lem-weil-pbc-right-derived-universal-delta-functor`, module
  `Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor`: ordinary additivity and
  functoriality suffice; no universal delta-functor construction is used.
- `pqf-def-cohomology`, module `Sheaf.Paper.PQFCohomology`: its long exact sequence and
  higher-direct-image package are unnecessary for this epimorphy argument.
- `lem-sp-kinjective-computes`, module `Sheaf.CategoryTheory.KInjectiveComputes`:
  the natural single-object derived comparison already recorded in
  `lem-sp-derived-functor-single-identification` suffices for the remaining model bridge.

This is pruning from this argument; other targets may still reach these modules.
The proper/affine dichotomy, affine acyclicity, etale/Zariski comparison, proper
coherent finiteness and single-object derived comparison remain dependencies of
the new finiteness node. Compactification and affineness of a proper curve's open
complement remain beneath the existing `lem-sc-proper-or-affine`; they are not
claimed pruned. Lang--Steinberg remains directly used by the item.

## Where the brief, the DAG or earlier work was wrong

No false statement or signature correction was found. The original plan described
transport of scalar actions but provided no theorem with the precise section-induced
action and coefficient universe used by the item. The scalar-action construction is
now actual Lean, and only its natural comparison and finite-dimensionality remain.
The existing etale/Zariski statement covers the associated small-coefficient sheaf,
not arbitrary natural section equivalences with AddCommGrpCat coefficients in u+1;
the new finiteness node records that bridge explicitly. No claim that ULift preserves
injectives is made. The unit route is retained: its p-primary part still uses the
Artin--Schreier argument. The unit's `realized` arrays are empty on the base; this
worker has not changed them.

Searches used the required msearch tools and repository rg searches. LeanSearch was
unavailable (HTTP internal error); LeanFinder returned unrelated cotangent/group
cohomology results. No existing statement covered the remaining scalar finiteness
bridge. Stacks 0A3N and 0A3L were read online; the cited blueprint source text is not
present in this read-only clone, but its imported proof is in the item node.

## New nodes

`lem-sc-additive-cohomology-finite-scalar-model` is realized by
`Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyScalarModel`. Its scalar construction
is proved and it obtains finiteness from the next node.

`lem-sc-additive-cohomology-finite-dimensional` is realized by
`Sheaf.AlgebraicGeometry.Curve.AdditiveCohomologyFiniteDimensional`. It isolates the
proper/affine finiteness and the natural comparisons, with the module structure and
scalar sheaf maps supplied as hypotheses. This is strictly part of the original
argument. Neither new statement restates epimorphy or asserts surjectivity.
No change records are needed; existing interfaces are unchanged.


## Second reading by K1

1. Compared the complete item module against the repository with diff. Its sole
   existing declaration, including every binder, universe and epimorphy conclusion,
   has byte-for-byte the same signature and docstring. Only proof-only imports and
   the proof body changed. The two new modules introduce the two recorded theorems;
   there are no new public definitions or changes requiring a change record. Pass.
2. Read all three modules, including the scalar-map naturality, zero, one, sum and
   composition proofs and the complete module structure. All compiled locally
   without warnings. The only sorry is the named finite-dimensionality theorem,
   exactly `by sorry`; there is no hollow definition or prohibited declaration.
   Scratch `#print axioms` checks and the delivery probe check the trust boundary;
   sorryAx is expected from the explicitly open finiteness lemma. Pass, conditional
   on that listed lemma; the target is not claimed axiom-free yet.
3. The finiteness lemma does not restate epimorphy: it has neither wp nor p nor a
   surjectivity conclusion. Its section formula fixes the scalar action uniquely.
   Affine curves have zero H¹, projective lines also have zero H¹, and proper
   positive-genus curves have finite nonzero H¹. Scalar zero and one cause no
   exception, and the scalar construction proves these identities. The docstring
   explains scalar-compatible natural comparisons, including coefficient lifting.
   Read Stacks 0A3N, 03P2 and 02O6 and the existing comparison/affine declarations.
   Fresh LeanFinder search for finite-dimensional first structure-sheaf cohomology
   returned cotangent/group-cohomology results; Loogle for FiniteDimensional and
   cohomology returned no match. Repository searches found proper coherent
   finiteness and scalarCohomologyModule, which use different cohomology models;
   neither supplies this large-coefficient natural comparison. No short existing
   theorem closes the remaining bridge. Pass.
4. The proof opens the target and proves sectionwise semilinearity before applying
   the already proved surjective_sub_id. It uses no unnecessary general delta
   functor construction. Corrected the inaccurate removed-import claim and listed
   all seven removals, distinguishing dependencies moved to the finiteness plan
   from the three discarded nodes. Read sk-prop-cd.json: its realized arrays are
   empty and unchanged; the Artin–Schreier route remains the p-primary route. Pass.
5. Read all three node records. Their declarations, hypotheses and conclusions
   match Lean, and proof_deps is the union of the steps' uses. The new nodes have
   source, searches, creation, blueprint, chapter, unit and Lean records. Added
   the five proof-only imports for the open finiteness node's recorded dependency
   plan so those dependencies remain reachable by the import-based queue. Pass.

Second reading changes: restored dependency-plan imports in the open finiteness
module and corrected/completed the pruning report. No proof or signature repair
was needed. No change records are required.

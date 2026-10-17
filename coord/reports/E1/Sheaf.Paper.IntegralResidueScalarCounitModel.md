## What changed

Repaired return H10 from reviewer C-16ac5 (returned head `16ac5fa73a`).
`IntegralResidueScalarCounitModel` now contains private copies of `mateModel`,
`naturalOrdinaryFac`, `reduction_unit_fac`, and `restrict_pull_fac`, together with
`exactSquareFac`, `exactSquareFacInv`, `liftedSquareFac`, `exactLeftSquareFac`,
`transportedUnitFac`, `mixedDerivedUnitFac`, and `cachedProofInstance1` through
`cachedProofInstance12`. These are the proved calculations from
`968c37bf00:lean/Sheaf/Paper/IntegralResiduePullFlatModel.lean`; none adds a hole.
The local composite exactness instances are scoped to these calculations.

Replaced `import all Sheaf.Paper.IntegralResiduePullFlatModel` with proof imports of
`IntegralResiduePullSquareData` and
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
The ordinary-unit import is retained. The counit node no longer lists the flat-model
node in step 1 or `proof_deps`; step 1 describes the local private calculations.

The retained delivery proves `integralResidue_scalarCounit_model` with its exact
original statement. The two fully proved auxiliary modules
`IntegralResidueOrdinaryTensorSquare` and `IntegralResidueOrdinaryTensorNormalization`
provide the ordinary balanced-tensor comparison and its homotopy normalization.
The original `residueOrdinaryRestrictedRegularPullIso` construction is moved unchanged
to the ordinary square and publicly reexported through the item module. The associated
change record is `coord/changes/e1-ordinary-residue-tensor-square.md`.
No target or existing theorem statement changes.

Validation against the current published build: `lcompile.py --all` compiled the ordinary
square (0.1 s, cached), homotopy normalization (50.6 s), and repaired counit module
(51.0 s), with no errors or warnings. The unchanged importers
`IntegralResidueTensorPullCounitModel` (8.8 s) and `IntegralResidueScalarGeometryBridge`
(20.6 s) also compiled against these sandbox modules without errors or warnings.
Their validation copies and compiled artifacts were removed from the delivery sandbox.
The declaration parser confirms that the item theorem's signature is unchanged from
both the current library and returned head, and the moved coefficient isomorphism's
signature, body and visibility are unchanged. All Lean lines are at most 100 characters.
`deliver3.py E1 Sheaf.Paper.IntegralResidueScalarCounitModel --no-push` printed
`OK (dry run)` for commit `730074ebfb`: compilation and preflight pass, with only
the fresh independent second reading left for the second reader. Nothing was pushed.

## Proved and sorry left

Holes closed relative to the current library: one,
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_scalarCounit_model`
(node `new-integral-residue-scalar-counit-model`). The H10 repair restores its
compilation after the old private helpers were removed upstream.

Also fully proved in the retained delivery:

- `AlgebraicGeometry.ProEtale.CondensedRing.residueOrdinaryTensorPull_module`
  (node `new-integral-residue-ordinary-tensor-square`).
- `AlgebraicGeometry.ProEtale.CondensedRing.residueOrdinaryTensorPull_homotopy`
  (node `new-integral-residue-ordinary-tensor-normalization`).

Holes added: zero. Remaining holes in the item: zero. Remaining holes in all three
delivered modules: zero. All copied private helpers are proved. No split-off obligation
remains. Upstream declarations may still carry `sorryAx`; this delivery adds none.

## No longer needed

Removed the returned delivery's proof import of
`Sheaf.Paper.IntegralResiduePullFlatModel` and its node
`new-integral-residue-pull-flat-model` from this item's proof dependencies.
The proof needs neither the flat-model theorem nor its new comparison module.
Other library users may still need those modules; no global withdrawal is claimed.

Relative to the original library module, the direct proof imports of
`IntegralReductionTensor`, `IntegralResidueOrdinaryMonoidal`, and
`IntegralResiduePullSquare` are replaced by the new ordinary-square and homotopy modules
and the direct square-data import. Their underlying constructions remain used; their
nodes are not pruned. The original public `IntegralResidueTensorModel` import is retained.
The ordinary square is public because it defines the coefficient isomorphism used in
the statement; homotopy normalization is imported only for the proof.
No blueprint unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

H10 is confirmed: the returned proof imported private helpers from
`IntegralResiduePullFlatModel`, and landing `8d7d33e89a` removed them. The repair
makes these calculations private to their actual user and removes the obsolete DAG
edge. The helpers prove identities for arbitrary homotopy complexes; the flat-model
theorem and its flatness hypotheses were never used by this proof.

The earlier delivery's ordinary tensor step needed a comparison of constructed maps;
the two retained auxiliary modules prove it and its homotopy passage explicitly.
No statement was found false, no hypothesis was added, and the proper-base-change
unit route is unchanged. The earlier second reading applies to the returned delivery;
a fresh independent reading must cover this repair.

## New nodes

The retained `new-integral-residue-ordinary-tensor-square` node records the proved
ordinary balanced-tensor equality and unchanged coefficient isomorphism construction.
The retained `new-integral-residue-ordinary-tensor-normalization` node records its proved
passage to homotopy using the generic tensor-single comparison. Both have source,
proof narrative, edge-case discussion and Mathlib search records. Neither has an open
obligation. H10 adds no further node. The change record is
`coord/changes/e1-ordinary-residue-tensor-square.md`.

## Second reading by E1

Independent reading of the H10 repair, with all three delivered Lean modules,
their three nodes, the shared originals, and the dependency declarations open.

1. **Public statements and definitions: pass.** Compared the item with the shared
   module using `diff` and the project's declaration parser. The full source
   signatures of `integralResidue_scalarCounit_model` and
   `residueOrdinaryRestrictedRegularPullIso` are byte-for-byte identical. For the
   moved definition, the body, visibility and attributes are also identical; its
   changed module and public reexport are declared in
   `coord/changes/e1-ordinary-residue-tensor-square.md`. No other existing module
   is delivered or adapted. Read the earlier landed change record
   `integral-residue-ordinary-regular-pull-iso.md`: this move preserves that
   constructed coefficient identification rather than replacing it by a witness.

2. **Proofs and kernel checks: pass.** Independently ran `lcompile.py --all` on
   the three modules without errors or warnings. A temporary scratch module
   importing the delivered modules printed axioms for the item theorem, both
   auxiliary theorems and the coefficient isomorphism. Each has only `propext`,
   `Classical.choice`, `Quot.sound` and inherited `sorryAx`. The delivered source
   contains no `sorry`, forbidden declaration, skipped kernel check, or data
   chosen from an unproved existence theorem. The cached instance definition is
   `inferInstance`; the coefficient isomorphism composes existing isomorphisms.
   Read the private calculations: `mixedDerivedUnitFac` uses the defining
   derived-unit factorization; `mateModel` proves equality by the injective
   adjunction hom-equivalence; `scalar_restriction_counit` inverts the constructed
   scalar comparison, never the extension counit. The scratch module was removed.

3. **New statements and small cases: pass.** There are no split-off holes.
   `residueOrdinaryTensorPull_module` has arbitrary commutative condensed ring
   objects, their monoid morphism, an arbitrary scheme morphism and an ordinary
   module. Its projection argument uses the explicitly constructed epimorphism
   and faithfulness of forgetting actions; it does not assume flatness.
   `residueOrdinaryTensorPull_homotopy` first applies that equality degreewise and
   then the proved tensor-single identity. These are strictly ordinary and
   homotopy parts of the counit argument, with no derived mate in either
   statement. Checked the identity coefficient map, identity scheme morphism,
   zero module/complex and empty scheme cases: the same unit and inverse-unit
   cancellations apply, and cancellation of the projection remains valid for
   the zero object. No nonempty-site or nonzero-coefficient assumption enters.
   Read Bhatt--Scholze's local PDF at Lemma 6.5.9(5), printed p. 51, and Remark
   6.8.15, printed p. 62. The nodes correctly identify these as explicit formal
   comparison calculations, not additional verbatim lemmas of the paper.

4. **Route and pruning: pass.** Independently searched with different wording:
   LeanFinder, "Base change for extension and restriction of scalars respects
   the balanced tensor product under a strong monoidal inverse image functor";
   Loogle, `"map₂HomologicalComplexObjSingleIso"`; and Mathlib grep,
   `mapBifunctorSingle|mapCochainComplexSingle|transport_δ`. The hits give ordinary
   algebraic tensor identities or the monoidal and single-functor ingredients
   already used here. Searched shared `lean/Sheaf` and `lean/WeilConjectures`
   for tensor/pullback comparisons and read
   `mapDerivedCategorySquareIso_hom_app_Qh_obj` and
   `mapDerivedCategoryAdjunction_unit_app_Qh_obj`. The former is the same exact
   square calculation with factors conjugated; the latter requires exactness
   of the left adjoint, unavailable for scalar extension here. Neither closes
   the mixed derived counit comparison directly. The retained short factor
   calculations are appropriate. Public imports supply statement constructions
   or the declared reexport; private proof imports supply only calculations.
   Checked every original `proof_deps`: the ordinary-monoidal node remains used
   through the new ordinary-square and normalization nodes, while the other
   original dependencies remain in the proof. The returned flat-model edge is
   genuinely unused and removed. The `sk-thm-properbasechange` unit and its
   `realized` statement and three steps are untouched; no unit is bypassed.

5. **DAG agreement: pass.** Each stored Lean signature matches its declaration.
   Each `proof_deps` is exactly the union of the proof steps' `uses`. The item's
   four steps match the mate/unit calculation, inverse restriction calculation,
   homotopy normalization and final counit naturality in the proof. The two new
   nodes record their respective projection and degreewise tensor-single proofs,
   with source, searches, creation, blueprint, unit and Lean records. The only
   changed existing-node fields are `lean`, `proof`, `proof_deps` and
   `proof_origin`. No statement or statement dependency changed.

Second-reading change: supplied the missing source and blueprint tag in the new
homotopy-normalization module docstring. No proof repair was necessary. Added
this independent review and fresh search/axiom verification; all hole counts
remain one existing hole closed, zero added and zero split off.

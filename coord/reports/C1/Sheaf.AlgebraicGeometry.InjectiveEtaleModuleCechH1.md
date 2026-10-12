## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.InjectiveEtaleModuleCechH1` by a
complete Lean proof from the existing ringed-site theorem
`CategoryTheory.injective_module_cech_cohomology_isZero` and two strictly smaller
interface statements. The original theorem's signature and public imports are unchanged.

The proof constructs the precoverage of all families generating covering sieves and proves
that it generates exactly `Y.smallEtaleTopology`. Thus arbitrary covering index sets,
including infinite ones, satisfy the coverage hypothesis of the existing theorem without
an extra finiteness or refinement assumption. It obtains the chosen fibre products from
`SiteCechComplex.exists_of_covering`, transports the sheafification instances, and applies
the ringed-site theorem in degree one. It then transports zero cohomology through the
presheaf and complex isomorphisms using the two homology functors. All these combinations
are written and checked in Lean; no sorry remains inside this proof.

Added proof-only imports of `Mathlib.AlgebraicGeometry.Sites.AffineEtale`,
`Sheaf.CategoryTheory.Sites.InjectiveModuleCechAcyclic`, and the two new modules
`Sheaf.AlgebraicGeometry.InjectiveEtaleConstantRingModule` and
`Sheaf.CategoryTheory.SiteCechMathlibComparison`. Updated the parent node's proof,
proof dependencies and proof origin to match the code. No existing definition or statement
changed; no change record is needed. The unit `sk-thm-p1` and its realized steps are
unchanged: this delivery carries out the parent's stated route through 03FC.

All three delivery modules compile cleanly with the prescribed local compiler. The imports
of the new constant-ring interface were reduced to the basic module-sheaf file, the étale
site and the injective-object definitions; abelian-category imports are unnecessary there.

## Proved and sorry left

Proved (from named dependencies):
`AlgebraicGeometry.Scheme.isZero_cech_H_one_of_injective_module_sheaf`.
The item's one original sorry is removed. This is a reduction, not a claim that the
transitive proof is sorry-free: the existing ringed-site acyclicity and chosen-product
existence declarations used by the proof are still open library work.

Two new named sorries remain, exactly as the whole proofs of their public theorems:

- `AlgebraicGeometry.Scheme.exists_injective_etale_ring_module`, in
  `Sheaf.AlgebraicGeometry.InjectiveEtaleConstantRingModule`, node
  `lem-weil-pbc-injective-etale-constant-ring-module`. This realizes the coefficient
  category interface, independently of any cover or any cohomology assertion.
- `CategoryTheory.SiteCechComplex.mathlib_complex_iso_exists`, in
  `Sheaf.CategoryTheory.SiteCechMathlibComparison`, node
  `lem-weil-pbc-site-cech-mathlib-comparison`. This compares the two Čech models for
  every abelian presheaf and arbitrary arrow family, independently of injectivity or
  acyclicity.

Both have complete natural-language proofs in their docstrings and matching nodes. The
first is checked on the zero ring, zero sheaf and empty scheme: the local action and
injectivity transport do not require nonzero scalars or nonempty objects. The second is
checked on an empty index set (both complexes have zero objects in every degree), a
singleton family, and the zero presheaf. Its comparison is contravariant restriction
along the unique projection-compatible isomorphisms and therefore uses the correct
alternating differential. The section and index universes agree as required for the
categorical products; the site universes remain unrestricted.

## No longer needed

No original imports were removed; the statement-facing imports are preserved. No original
mathematical branch is pruned: the coefficient realization, ringed-site acyclicity and
Čech-model comparison remain the three steps of the same argument. The old direct proof
edges to the coefficient and abelian-sheaf definitions are now carried by the interface
nodes rather than used as if those definitions already provided the equivalence.

Old direct `proof_deps` edges no longer used by the parent proof are
`def-weil-pbc-abelian-etale-sheaves`, `def-weil-pbc-etale-sheaves`, and
`def-weil-sheaf-of-modules-category`. Their content remains needed transitively by
the coefficient interface; no module is claimed globally unreachable or pruned.

Neither the abelian-presheaf injectivity theorem in
`WeilConjectures.CategoryTheory.Sites.CechComplex` nor its abelian-sheaf specialization in
`WeilConjectures.CategoryTheory.Sites.CechCriterion` is imported: their injectivity
hypotheses do not apply to the underlying abelian sheaf of J. No such hypothesis is added.
The tentative abelian-category imports in the new constant-ring module were removed.

## Where the brief, the DAG or earlier work was wrong

The parent's proof is mathematically consistent, but its steps 1 and 3 were labelled
`elementary: true` even though the listed definitions supply neither the constant-ring
coefficient equivalence nor the isomorphism to Mathlib's Čech complex. Those are genuine
interfaces. They are now separate statements, rather than an assumed coercion or a
restatement of the original vanishing theorem. The middle acyclicity step is the existing
statement node and is used unchanged.

The local clone contains only the literature lists, not the Stacks source files. Read
Stacks 03FC, 03FD and 03AM online and fetched the canonical `sites-modules.tex` and tag
index into this item's scratchpad. Sections 093I and 03CV and Sites Example 0H7J provide
the constant-sheaf/module definitions; the local-action equivalence and the choice-of-model
comparison are interface arguments written by C1, as recorded in their proof origins.
No assertion is attributed to 03FD that it does not state.

Searches for both interfaces used LeanSearch (unavailable with Internal Server Error),
LeanFinder or Loogle, and direct Mathlib/source/DAG searches. The returned
`SheafOfModules.toSheaf` forgets scalars but supplies no inverse equivalence;
`forgetToSheafModuleCat` uses a terminal object's section ring and does not give the
constant-ring equivalence. `SiteCechComplex.comparison_exists` compares only two choices
within that encoding. These results therefore do not close either missing interface.

## New nodes

`lem-weil-pbc-injective-etale-constant-ring-module`: the injective realization of a
ModuleCat-valued étale sheaf as a ringed-site module with the same abelian presheaf.
This is step 1 of the parent's proof; no cover or vanishing statement is part of its
conclusion. Module: `Sheaf.AlgebraicGeometry.InjectiveEtaleConstantRingModule`.

`lem-weil-pbc-site-cech-mathlib-comparison`: the comparison of a chosen-product Čech
complex with Mathlib's `cechComplexFunctor`, on any category with finite wide pullbacks.
This is step 3 of the parent's proof and applies without the covering or injectivity
hypotheses. Module: `Sheaf.CategoryTheory.SiteCechMathlibComparison`.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered parent module with the repository using diff: its sole existing
   declaration signature and docstring are byte for byte unchanged, and all original public
   imports remain. The only Lean changes are four private imports and the proof body. Both
   additional modules are new; there is no changed definition or hidden hypothesis.
2. Compiled all three files in import order through lcompile.py: no errors or warnings.
   A scratch copy with #print axioms checked the parent and both new declarations: the
   parent and each new theorem use exactly propext, Classical.choice, Quot.sound and
   sorryAx. The parent is a checked reduction, not a transitively sorry-free theorem.
   There are precisely the two reported whole-theorem sorries, no hollow definitions and
   no axiom, unsafe, opaque, implemented_by or extern declarations.
3. Read both interface statements, their docstring arguments and nodes. For the coefficient
   interface, Sections 093I (section-constant) and 03CV (section-sheaves-modules) of the
   fetched sites-modules.tex define the objects used. The action is well defined after local
   refinement, and the inverse restricts along the constant scalar maps; full faithfulness
   transports monomorphisms and the extension property. Zero ring, zero J, and empty Y
   cause no exception. For the comparison, read Mathlib's SheafCohomology/Cech.lean and
   FormalCoproducts/Cech.lean: degree p is indexed by Fin(p+1) → I, and mapPower has exactly
   the omitted-factor projections used by S.indexMap. Product uniqueness and contravariant
   restriction give commuting differentials. Empty I gives zero groups in every degree;
   singleton I and zero F also agree. No cover or injectivity is assumed for this interface.
   These are strictly separate parts of the argument, not renamed vanishing assertions.
   Independent LeanFinder searches used “sheafification of constant ring presheaf preserves
   injective objects” and “alternating coface map ... chosen wide pullback Cech”; direct
   searches included the upstream CechComplex and Mathlib FormalCoproducts. The hits
   PresheafOfModules.sheafify, sheafification and sheafificationAdjunction implement action
   extension and its adjunction, but do not directly supply the ModuleCat-sheaf equivalence
   and injectivity transport. alternatingCofaceMapComplex and cechIsoCechNerveApp do not
   compare the project's chosen-product structure. Neither interface closes in a few lines.
4. Read the proof from its conclusion backward. The two IsZero.of_iso calls use inverse
   isomorphisms in the correct directions. The topology equality lets the given arbitrary
   sieve cover be used by the existing ringed-site theorem, with degree 1 positive and no
   finite-index restriction. AffineEtale supplies the small-etale sheafification instance;
   the other new imports provide the three used theorem interfaces. No new public import
   is proof-only. Read sk-thm-p1.realized: its statement and all four realized step lists
   are unchanged, and the reduction retains the 03FC route. Completed the pruning report
   with every removed old direct edge; these definitions are still required transitively.
5. Matched the parent node's three proof steps and proof_deps union with the actual proof:
   coefficient realization, covering/product existence and ringed-site acyclicity, then
   homology transport. Both new nodes have their sources, full proofs, search records,
   creation metadata, unit/chapter and Lean records. Their hypotheses and conclusions
   match Lean, including universes. Replaced their flattened Lean statement records by
   verbatim signatures, made their blueprint source places name the exact parent steps,
   and explicitly labelled the failed LeanSearch records unavailable.

6. Repaired return C4 (reviewer X-9e2c5): the coefficient node's first proof step now
   explicitly uses `lem-weil-pbc-ring-sheafification-underlying-sets` for the underlying-set
   identification and `lem-weil-pbc-site-sheafification-sections-local` for local constant
   representatives and local equality. Both IDs were added to that step's `uses` and to
   `proof_deps`. The coefficient theorem's docstring now names both facts and Stacks Sites
   00YR and 00WK. [Stacks 00WK](https://stacks.math.columbia.edu/tag/00WK) supplies local
   representatives and agreement after covering refinement; these are substantive facts,
   rather than consequences stated by the sheafification definition alone.

Second reading repaired the sheafification citations in the coefficient node and theorem
docstring and recorded them here, in addition to the earlier metadata corrections.

## Second reading by C1

1. Compared the parent module with the repository using `diff -u`. Its existing
   declaration signature and docstring are byte for byte unchanged; the changes are
   four proof-only imports and the replacement proof. The other two modules are new,
   and neither adds a hypothesis to or alters any existing declaration or definition.
   Verdict: pass; no statement change record is required.
2. Compiled all three delivery modules in import order with lcompile.py, without
   errors or warnings. Compiled scratch copies with `#print axioms` for the parent
   and both interfaces: each lists only propext, Classical.choice, Quot.sound and
   sorryAx. The parent contains no sorry; the two reported interfaces each contain
   exactly one whole named-theorem sorry. No forbidden declarations or hollow
   definitions occur. Verdict: pass as a reduction with open dependencies.
3. Read the two interface signatures, docstring proofs and nodes. Scalar extension
   by locally constant representatives and restriction along the constant scalar map
   are inverse on objects and morphisms, preserving injectivity and the underlying
   presheaf. Checked zero coefficients, zero J and the empty scheme. The earlier
   X-9e2c5/C4 repair is present: the proof explicitly cites underlying-set
   sheafification and local representatives/local equality, and both dependency IDs
   occur in proof[0].uses and proof_deps. For the comparison, checked SiteCechComplex's
   universal property, indexMap_pr and signed succAbove differential against Mathlib's
   FormalCoproduct.power/mapPower and alternating coface construction. Empty I, a
   singleton family and zero F agree; no sheaf or covering assumption is needed.
   Independent LeanFinder queries used "equivalence between sheaves valued in modules
   and modules over sheafified constant rings" and "isomorphism alternating restriction
   cochain complex products sections formal coproduct Cech nerve". The former finds
   module sheafification adjunctions, without the required coefficient equivalence;
   the latter finds unrelated simplicial comparisons. Direct library searches and
   reading the existing comparison_exists confirm no duplicate interface. Neither is
   a restatement of the parent vanishing assertion or closes in a few lines.
   Verdict: pass; retain both smaller statements.
4. Read the reduction backward from both IsZero transports: the inverse isomorphisms
   have the correct directions. The precoverage topology equality uses all covering
   sieves and therefore retains arbitrary, including infinite, covering index sets.
   The degree-one positivity and sheafification instances are supplied without new
   hypotheses. Each new parent import supplies a used interface or instance; the
   new modules' public imports support their signatures. Checked sk-thm-p1.realized:
   the unit statement and route are retained. The pruning report names all three old
   direct proof edges removed (abelian-etale-sheaves, etale-sheaves and
   sheaf-of-modules-category); none is globally pruned, since the coefficient
   interface still needs them. Verdict: pass.
5. Matched the parent node's three proof steps to coefficient realization, chosen
   products/ringed-site vanishing and homology transport. Matched both new nodes'
   statements, universe conditions, verbatim Lean records and dependency unions to
   their files. They have the required creation, source, search, origin and blueprint
   metadata. Verdict: pass.

This reading changed only the report: added this exact required heading and recorded
fresh compilation, axiom, dependency, edge-case and independent-search checks. The
previous citation repair is verified; no further Lean or DAG repair was needed.

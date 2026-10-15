## What changed

Closed the sole remaining hole in Sheaf.Paper.GeometricFieldProEtaleEvaluation,
AlgebraicGeometry.ProEtale.geometric_field_proetale_evaluation, without changing its
signature or any existing definition. Added two fully proved modules:

- Sheaf.Paper.GeometricFieldProfiniteDenseSubsite proves that the specified relative
  profinite test functor is a dense subsite over an algebraically closed field.
- Sheaf.CategoryTheory.DenseSubsiteModuleRestriction transports module structures
  through set and abelian restriction equivalences on a cover-dense subsite.

The original theorem applies dense-subsite comparison in the three coefficient
categories, obtains the prescribed adjunction unit/counit isomorphisms, proves the
singleton structural map is invertible by terminality, and applies the module theorem.
All new imports of the original module are proof-only. No existing public signature,
visibility or target was changed; no other group's module was adapted.

## Proved and sorry left

Closed: AlgebraicGeometry.ProEtale.geometric_field_proetale_evaluation (the only
original sorry; node lem-weil-pbc-geometric-field-proetale-evaluation).

Added and fully proved:
AlgebraicGeometry.ProEtale.geometricFieldProfiniteDenseSubsite (node
lem-weil-pbc-geometric-field-profinite-dense-subsite), and
SheafOfModules.isEquivalence_pushforward_of_dense (node
lem-weil-pbc-dense-subsite-module-restriction).

Sorries left: none. Sorries added: none. This is a proof, not a decomposition.
All three delivered modules compile without warnings. Explicit #print axioms checks
for both new public theorems and all six original public theorems report only
propext, Classical.choice and Quot.sound; there is no sorryAx.
The five previously proved original theorems retain their proofs.

## No longer needed

Removed these original proof-only imports from the item:

- Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
- Sheaf.AlgebraicGeometry.ProEtaleInverseImage
- Sheaf.CategoryTheory.RingedSiteModules
- Sheaf.CategoryTheory.SiteInverseImageTensor
- Sheaf.RingTheory.IndPrincipalZariski
- Sheaf.RingTheory.WeaklyEtaleField
- WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
- WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
- WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
- Mathlib.CategoryTheory.Sites.LocallyInjective
- Mathlib.CategoryTheory.Sites.Limits
- WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
- Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types

The finite-product and finite-subalgebra classifications are replaced by the explicit
LC(Spec B,K) map and local-ring/spectrum bijection criterion. The other removed imports
are either unused or already supplied publicly by retained imports. All original
public imports remain byte for byte unchanged.

The second reader also removed the redundant new proof-only imports
Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv and
Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal from the item. Their declarations
are already available through retained imports. In GeometricFieldProfiniteDenseSubsite,
WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine already publicly supplies
these five redundant proof-only imports, which were also removed:

- WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField
- WeilConjectures.RingTheory.ProEtale.PullbackProfinite
- Mathlib.Topology.Connected.Separation
- Mathlib.AlgebraicGeometry.Pullbacks
- Mathlib.Topology.Homeomorph.Lemmas

The direct public imports of the new modules name notions in their statements;
all other remaining imports supply proofs or constructions used in those proofs.

Removed from the original node's direct proof_deps (the complete difference):

- lem-sc-finite-etale-algebra-criterion: replaced by the local-ring argument.
- lem-weil-pbc-tychonoff-product-quasi-compact: no product of finite spectra or
  finite-intersection-property argument is used.
- lem-weil-pbc-profinite-limit-function-factorization and
  lem-weil-pbc-spec-small-colimit-limit: no explicit inverse limit is needed here.
  They remain transitive dependencies of the existing test-object framework.
- lem-weil-pbc-weak-etale-field: the larger finite-subalgebra theorem is unused.
  The already proved source-library separable-field theorem and absolute-flatness API
  suffice. Sheaf.RingTheory.WeaklyEtaleField is pruned from the targets' import closure.
- lem-weil-pbc-left-exact-site-inverse-image-tensor: the point adjunctions already
  have the specified restriction as right adjoint; tensor reconstruction is unnecessary.
  This node remains reachable through the imported framework.
- def-weil-affine-spectrum, def-weil-pbc-ind-etale-algebra,
  def-weil-pbc-ind-etale-basis, lem-weil-pbc-ind-etale-basis and
  lem-weil-pbc-locally-constant-prime-spectrum: used in the proved dense-subsite node
  or its dependencies, rather than directly in the original node.

A source import-graph comparison from lean/TargetsCheck.lean, overlaying all delivered
modules on this checkout, removes exactly Sheaf.RingTheory.WeaklyEtaleField and adds
exactly the two proved new modules. This is an import-closure check, not a replacement
for the maintainer's pinned sorry ledger. No other module is claimed globally pruned.
The unit's realized proper-base-change route is preserved.

## Where the brief, the DAG or earlier work was wrong

The node's finite-subalgebra inverse-limit route was mathematically valid but longer
than necessary. The existing local-ring API gives a direct algebra classification.
The private pointComponentsEquiv in the proved ProEtalePointComponentsMaps module is
stronger than the public theorem: its correspondence applies to every affine source,
without a weak-contractibility assumption. It is reused by import all only in private
proof helpers; no private declaration occurs in a public signature or definition.

The original docstring's tensor calculation is unnecessary once the specified point
adjunction is available. Its right adjoint is already the exact restriction functor,
so equivalence gives its actual unit and counit isomorphisms directly.

Finite-family universe corrections are explicit: the finite affine refinement has
indices in Type u and is reindexed by Fin n for the coherent-topology API (Type 0);
profinite covering families are lifted with ULift for the test-object theorem.
The zero ring, empty profinite space, empty family and arbitrary ring sheaves are
covered without nonemptiness or nontriviality assumptions. The singleton argument
works for every scheme, independently of the field assumptions.

The literature PDF named by existing nodes is absent in this read-only checkout;
Examples 4.1.10 and 4.2.11 were checked in the primary arXiv paper at
https://arxiv.org/pdf/1309.1198. No repository literature files were changed.

## New nodes

lem-weil-pbc-geometric-field-profinite-dense-subsite: fully proved dense-subsite
criterion for the specified relative test functor. Its proof records the scalar
pushout, local-ring algebra classification, full faithfulness, affine density and
finite-cover topology comparison. It introduces no future proof obligation.

lem-weil-pbc-dense-subsite-module-restriction: fully proved general transport theorem
for module sheaves. The action is constructed as the unique preimage under the set
restriction equivalence and each module law is checked using cover density. It
introduces no future proof obligation. No change records or forced adaptations.

## Second reading by E4

1. **Existing interfaces: pass.** Read all three delivered modules and compared the
   item with its repository version using diff and the project's declaration parser.
   All 22 existing declarations keep byte-identical signatures and visibility; every
   existing definition body is identical. Only the remaining theorem's body and its
   explanatory proof docstring changed. The five previously proved theorems retain
   their proofs. There are no forced adaptations, signature changes or change records.
   Read the change records naming this module; none requires a further adaptation.

2. **Proof and trust: pass.** Recompiled all three files through lcompile.py, including
   after the import cleanup: no errors or warnings. A fresh scratch overlay at
   scratchpad/second-reading/ compiled the same three files and a probe printing the
   axioms of geometricFieldProfiniteDenseSubsite,
   SheafOfModules.isEquivalence_pushforward_of_dense, and all six original public
   theorems. Each prints exactly propext, Classical.choice and Quot.sound, with no
   sorryAx. Scanned all delivered Lean for forbidden declarations/options and sorry:
   none. The explicit algebra map liftPrimeSpectrum is constructed before its
   bijectivity proof. The remaining choices are inverses under proved bijections or
   equivalences, with the uniqueness needed downstream; no arbitrary object is chosen
   from an unproved existence statement.

3. **New statements and sources: pass; zero statements left open.** Read
   Bhatt--Scholze Examples 4.1.10 and 4.2.11 in
   https://arxiv.org/pdf/1309.1198 (printed pp. 28 and 30). The dense-subsite theorem
   uses exactly the specified relative fibre-product functor and coherent topology.
   Checked the pushout projection equations, the characteristic-function localization
   calculation, separable algebraic prime localizations, the explicit LC(Spec B,K)
   map, stalk cancellation and the spectrum bijection. The zero algebra has empty
   spectrum and the localization equalities remain valid vacuously; the empty
   profinite space gives the zero LC algebra. The topology proof allows an empty
   finite refinement and uses Fin n only to reindex the same family, with ULift for
   the converse universe conversion. No nonemptiness or nontriviality is assumed.
   For module transport, the section variables are exactly continuity, set and abelian
   restriction equivalences and cover density; no equivalence of the underlying sites
   or of ring restriction is silently assumed. The lifted action is the full functor's
   preimage of a conjugated map of set sheaves. Cover density and sheaf separatedness
   verify every module axiom and linearity of lifted morphisms, including the zero
   ring and zero module. The identity scalar map agrees with the original restriction.
   Repeated independent msearch.py searches with different wording (generating
   subcategories/module sheaves; Stone spectra/weakly etale algebras), a Loogle query
   for pushforwardPushforwardEquivalence, and rg over lean/ and Mathlib found no
   replacement theorem. Read the matching Mathlib theorem: it requires C ≌ D and
   therefore does not replace dense restriction. No split-off sorry was introduced.

4. **Route and pruning: pass after repair.** Read the retained five proofs, all new
   helpers and the realized record of dag/units/sk-thm-properbasechange.json. This
   item lies below the unit's proper-base-change steps; none is bypassed. Dense-site
   comparison and the already specified adjunctions directly prove the nine conjuncts;
   the terminal argument works for every scheme. The module theorem proves the
   arbitrary ring-sheaf clause, not merely constant coefficients. Independent searches
   found no shorter complete route. Removed eleven redundant proof imports (six in
   the item and five in the dense-subsite module); all files recompiled. Replaced the
   inaccurate claim that no original import was removed with the complete list, and
   corrected the weak-etale-field pruning claim using the actual target import graph.
   The No longer needed section lists all eleven removed original proof dependencies.

5. **DAG agreement: pass after documentation repair.** The original node differs only in proof, proof_deps and
   proof_origin. Every proof_deps list is exactly the union of its steps' uses; all
   referenced nodes exist and their Lean/Mathlib interfaces were read. In particular,
   the dense-subsite proof uses the proved private pointComponentsEquiv (which needs
   only affineness), not the weaker public point-components theorem with its extra
   weak-contractibility hypothesis; the node explicitly records this reuse. Both new
   nodes have source, self-contained statement, searches, complete proof steps,
   provenance, creation/blueprint records, chapter/unit and matching Lean declarations.
   Both are fully proved parts of the argument, not renamed open copies of the item.
   Corrected two inherited stale phrases in the original node: the split-cover
   reference now names the assertion rather than its obsolete step number, and the
   site-equivalence theorem is no longer described as still open.

Changes made by the second reader: removed redundant proof imports; repaired the
complete import-removal and target-closure pruning report; added this independent
reading; corrected two stale proof-description phrases in the original node.
No Lean proof, statement, definition, visibility or public import was changed.

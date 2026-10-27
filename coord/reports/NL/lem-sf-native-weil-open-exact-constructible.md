# Worker report: lem-sf-native-weil-open-exact-constructible

## Files written

- dag/nodes/sec-six-functors/lem-sf-native-weil-open-exact-constructible.json: split, with its original statement unchanged and seven proof steps.
- dag/nodes/sec-six-functors/lem-sf-native-adic-open-restrictions.json: statement; not in Mathlib. Open restriction and disjoint actual module pullback for native adic extension by zero, without Frobenius or constructibility hypotheses.
- dag/nodes/sec-six-functors/lem-sf-native-adic-constructible-pullback.json: statement; not in Mathlib. Stability of native adic constructibility under module pullback.
- dag/nodes/sec-six-functors/lem-sf-native-adic-qcqs-stratification.json: statement; not in Mathlib. A finite global lisse stratification on a quasi-compact quasi-separated scheme.
- citations.json: a verbatim statement quote for every node citation of every item step.
- searches.jsonl and search-results/: the searches actually run and their unmodified printed results. search-queries.json records the queries by proposed node.

The three supporting nodes have empty proofs and proof dependencies. They are not Mathlib leaves. Their project declarations are already present in the live sorry map; the audit records their full names for attachment verification.

## Attachments

AlgebraicGeometry.ProEtale.instIsIsoFunctorAdicSheafUnitAdicOpenImmersionLowerShriekAdjunction and AlgebraicGeometry.ProEtale.isZero_adicUpperStar_adicOpenImmersionLowerShriek belong to lem-sf-native-adic-open-restrictions (WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion, lines 115-120 and 213-228).

AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.upperStar belongs to lem-sf-native-adic-constructible-pullback (WeilConjectures.SixFunctors.ProEtale.Adic.Constructible, lines 218-229).

AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.isAdicStratifiedLisseSheaf belongs to lem-sf-native-adic-qcqs-stratification (WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero, lines 127-198).

I read these exact entries in local/sorry_map_slopmaster2_liveb2378f05.jsonl.gz, then traversed their dependency graphs. All four entries have s=false and ts=false, and no reachable entry has either sorry flag. The respective traversals visited 612, 608, 582 and 590 declarations. This checks the supporting declarations only. I do not renew the rejected ATTACH claim for the whole item.

## WANTED

None. The native constructions and their complete source proofs are available in the read clone; the relevant general ringed-site arguments are in the local Stacks sources.

## Problems corrected or clarified

The earlier attachment refusal involved a non-existent/truncated name for an anonymous preservation instance. This delivery splits the item rather than making another attachment claim. The item previously had no proof or proof dependencies. Its source line descriptions are descriptive; the actual source was read and the new statements name the explicit supporting declarations.

There is no source or statement dispute. I preserved the given locally finite continuous coefficient ring, finite rank allowed to depend on the covering member, and local constructibility. In particular I did not apply the nearby condensed-coefficient constructibility theorem to the native coefficient sheaf. I did not assume schemes globally quasi-compact, globally separated, or that pro-etale geometric stalks alone detect all sheaves.

The created.item chain ends at the maintainer seed, so blueprint_refs.py ancestor reports None. The nodes retain this null ancestor and the full intervening via chain. Whole-blueprint searches for extension by zero, stratifications, disjointness, constructible pullback, stratified lisse, and restriction identities found no node giving the three native supporting assertions. The unit sk-thm-sf-package and chapter sec-six-functors were read: this is below the package's existing open-constructibility/localization route, not a replacement of a unit step. Neither chapter nor unit records were changed.

## Not duplicates

lem-sf-native-adic-open-restrictions vs lem-sfb-open-module-restriction-identities: the existing node has pulled-back condensed-ring coefficients; the new statement concerns modules over locally finite continuous function sheaves and actual coefficient-changing pullback, with arbitrary disjoint morphisms.

lem-sf-native-adic-open-restrictions vs lem-sfb-internal-open-extension-disjoint-vanishing: again the existing node has internal modules over a pulled-back condensed ring, whereas the new node uses the native continuous function sheaf. I do not identify these coefficient categories.

lem-sf-native-adic-open-restrictions vs lem-cbc-proetale-extension-zero: the latter has finite constant rings and a stalk prescription; the new one gives actual module restriction and disjoint pullback for native coefficients.

lem-sf-native-adic-constructible-pullback vs lem-weil-pbc-pullback-preserves-bounded-constructible: the latter is the derived finite-coefficient assertion; the new one is the native sheaf-heart assertion with locally finite continuous coefficients.

lem-sf-native-adic-qcqs-stratification vs lem-weil-pbc-constructible-stratification-assembly: assembly starts with finite stratifications on immersed pieces; the new assertion extracts a global finite stratification from merely local constructibility on a qcqs scheme. I cite assembly for assembling the actual boundary stratification.

lem-sf-native-adic-qcqs-stratification vs lem-weil-pbc-etale-stratification-local-gluing: that node stratifies a specified etale morphism into finite etale morphisms, not an arbitrary native coefficient module into lisse restrictions.

None of the three statements restates exactness or constructibility of extension by zero with Frobenius. The whole target constructibility argument stays in steps 4-7, with a chosen affine neighbourhood, a compact open intersection, and a finite boundary partition.

## Review by NL

I read coord/delivery-errors.md B-E in full and checked this split against those cases. For the item I read WeilSheaf/OpenImmersion.lean, especially the definition using IsoAlgebra.mapOfNatIso, the constructibility theorem, and all three preservation instances. I also read the actual Adic/OpenImmersion.lean proof of the unit and disjoint pullback and the Adic/ExtensionByZero.lean affine-neighbourhood proof. These give the route followed by steps 1-7. The proof is marked agent-written because I expanded the source's categorical assembly and used the generic ringed-slice theorem, rather than claiming a verbatim proof from a human document.

For the new open-restriction node, I checked that the source unit is invertible for every open immersion, and that the vanishing theorem uses the actual adic module pullback along any morphism with disjoint image. It does not assume quasi-compactness. Its proof uses the two module adjunctions and zero restriction of direct image, so I made this a supporting statement rather than pretending disjoint vanishing follows from the definition of a coefficient module.

For the new pullback node, I read Constructible.lean definitions and the proofs of lisse, stratified-lisse and constructible pullback stability. A pulled-back trivializing cover is again a cover, the unit module pulls back to the unit module, and the finite rank can vary with its covering member. The new node states the last, constructibility assertion alone. For the new qcqs node I read exists_isAffineOpen and the global finite stratification proof. It takes a finite affine subcover and uses the pieces V_a minus the earlier V_b; quasi-separatedness is an actual hypothesis, retained in the statement. These two supporting facts are not consequences of finite generation or quasicoherence of structure-sheaf modules. The Mathlib search hits for SheafOfModules.pullback/pullbackIso and IsFinitePresentation do not assert them. The topology hit about locally constructible subsets also does not supply a finite lisse stratification of a module sheaf. The four searches per new node use distinct semantic phrasings in LeanFinder and LeanSearch, as well as Loogle and recorded Mathlib grep; all services answered.

Step 1 uses the framework for the exact coefficient sheaf and extension presheaf, weakly-etale localization for the identification with the ringed slice, the two Mathlib base-change leaves for openness and quasi-compactness, and the ringed-sheaf-slice adjunction statement for exact additive extension. I opened every cited statement. The latter explicitly allows any sheaf R of commutative rings and gives the direct-sum/sheafification formula, so it applies to B, unlike the finite-constant-ring nodes. I read Stacks sites-modules.tex labels lemma-extension-by-zero (03DI) and lemma-extension-by-zero-exact (03DJ); neither assumes finite coefficients. The native coefficient restriction is equality of the functions on the same object, not an unproved finite-coefficient comparison.

Step 2 uses only the framework's displayed lift, the fixed-pair definition (including faithful forgetting), and the native abelian statement's exact conservative forgetful functor. It uses that statement, not the contents of its future proof. Exactness is checked by the homology object: exact forgetting sends it to zero, and conservativity detects its zero map as an isomorphism. Additivity is checked on faithful underlying arrows. Step 3 writes the biproduct equations, kernel/cokernel formulas, and the finite-diagram equalizer/coequalizer construction. Those are the short elementary universal-property arguments left as steps, not new category-theory nodes.

Step 4 uses the affine qcqs and base-change statements exactly as written. Quasi-compactness is applied over the chosen affine V, not inferred from an unjustified global quasi-compactness hypothesis. Quasi-separatedness of the open D follows by the intersection criterion, which the affine node explicitly gives; the argument is written out. Retrocompactness is checked using that same intersection criterion, so D and its complement have the constructibility needed for assembly. Step 5 cites the new pullback and qcqs statements: the former applies to b:D to bar U, and the latter is applied only after both qcqs hypotheses on D were established.

Step 6 uses the new unit/disjoint node for two different restrictions. The unit identifies the restriction on D and hence on its individual strata. The map from Z to bar T misses bar U by the cartesian definition of D. Its actual module pullback therefore vanishes. Rank zero supplies the complement's lisse model, without any nonzero rank requirement. The assembly statement takes a finite immersed partition with constructible images and finite local stratifications, all now supplied. Its predicate can be the native B-module lisse predicate. I wrote the contraction of the coefficient tensor factors so that this passage uses actual module pullbacks. Step 7 uses only the framework's equality of the underlying sheaf of the lifted functor with G and the definition of local constructibility.

I checked the small cases U empty, U=T, F=0, D empty, Z empty, and an empty scheme in the new qcqs node. No claim requires positive rank, a nonempty stratification, a bound on ranks across all members of a covering, or the existence of a boundary point. For the new pullback statement f=id and empty source reduce to the same condition. For the new open restriction statement j=id permits only the empty disjoint source, and j with empty source gives zero extension. For the qcqs statement I retained quasi-separatedness and did not promote local constructibility to a finite global partition on a non-quasi-compact scheme.

B1-B10: the new nodes are statement-only, introduce all objects, cite the defining framework, have actual source places and recorded searches, and were searched in the whole DAG/blueprint before creation. Their project declarations were also searched before writing and checked against the live sorry map. C1-C8: the nontrivial native restriction and stratification facts have nodes; every used node statement was opened; no proof-only data is borrowed. The three foreign-unit generic tools are declared in split_report.tool_uses with their reasons. D1-D5: no whole clause of the item was moved into a replacement node and no child depends on the item; each new node's statement depends only on definitions. E1-E7: coefficients, qcqs hypotheses, actual morphisms and tensor pullbacks were checked above. The unchanged target statement is consistent with the available source. All seven steps are below 2000 characters, and their elementary arguments are explicitly written.

## Unfinished work

No split work remains. The three native supporting statements have project declarations with no reachable sorry in the live map; the maintainer's delivery review verifies their attachment records. This is a stage-1 delivery only: no Lean files were written and no compiler, Lake or global build was run.

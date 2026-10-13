## What changed

Replaced the hole in `CategoryTheory.homComplex_hypercohomology` with a complete Lean
reduction. Constructed the ordinary-to-derived global cohomology map from the right-derived
unit, proved it invertible on K-injectives, and proved it invertible on Hom complexes with
arbitrary source by a naturality square along a K-flat resolution. The private proved helper
`CategoryTheory.bijective_precomp_quotient` proves invariance of homotopy classes into a
K-injective target directly from Mathlib's `Qh_map_bijective`.

Added `Sheaf.Algebra.Homology.HomComplexGlobalHomotopy`, isolating the ordinary global
cohomology comparison (Equation 0A8Z). It has neither derived global sections nor any
K-injectivity hypothesis. No existing signatures, definitions or visibility changed.

## Proved and sorry left

Closed the original hole `CategoryTheory.homComplex_hypercohomology`
(node `lem-pur-hom-complex-hypercohomology`) by reduction, not an unconditional proof.
Added one hole: `CategoryTheory.homComplex_global_homotopy`
(node `lem-pur-hom-complex-global-homotopy`). Its entire proof is `by sorry` in its own
module; its docstring and node describe the complete natural global-cochain argument.
There are no other holes in the delivered files. Net holes closed minus added: zero.
The new hole is strictly the ordinary-global computation, independent of the derived-unit,
K-flat-resolution and quasi-isomorphism arguments now proved in the original module.

## No longer needed

Removed direct proof imports `Sheaf.Algebra.Homology.HomComplexGlobalCochains` and
`Sheaf.Algebra.Homology.HomComplexProjections` from the original module. Their nodes
`lem-pur-hom-complex-global-cochains` and `lem-sc-hom-complex-projections` are now used
only by the new ordinary global comparison. Neither module is claimed globally pruned:
they remain dependencies of that comparison and of other imported lemmas.

The common-roof/fibre-product independence and source-naturality argument in original
Step 4 is unnecessary: the natural transformation is defined before choosing any
resolution, and a resolution is used only to prove its components invertible. Degreewise
epimorphism and flatness-of-terms properties of the K-flat resolution are unused here.
The old proof dependency `def-pur-hom-complex` is also moved to the new ordinary
global-comparison node; its module remains a public statement import here. This lists
all three old `proof_deps` entries absent from the revised list.
No existing dependency module is removed from the transitive import closure.

## Where the brief, the DAG or earlier work was wrong

The old plan is valid but longer than needed: a derived-unit comparison supplies naturality
without common roofs. The existing global-cochain theorem is objectwise and does not
state bifunctor naturality; the projection map formula gives the missing compatibility,
which remains in the new ordinary global-comparison item.

Checked edge cases of the new statement: either complex zero gives zero groups, degree-zero
complexes recover ordinary module-sheaf morphisms, and no boundedness or injectivity is
used in Equation 0A8Z. Read the sources online because the local Stacks TeX was absent.
The unit record has no realized proof steps to bypass, and the six-operations route stays.

## New nodes

`lem-pur-hom-complex-global-homotopy` in
`dag/nodes/sec-smooth-purity/lem-pur-hom-complex-global-homotopy.json`, stated in
`lean/Sheaf/Algebra/Homology/HomComplexGlobalHomotopy.lean`, is the natural ordinary
zeroth global-cohomology computation of Equation 0A8Z. Its proof uses the existing global
cochain and projection nodes and Mathlib's external Hom cohomology API. Searches were
run with LeanFinder, Loogle, grep and LeanSearch (the last returned Internal Server Error).
No change record is needed: existing public interfaces are unchanged.


## Second reading by T3

1. Compared the original module and its node with the repository using `diff`.
   The existing theorem signature and visibility are byte-for-byte unchanged;
   no existing definition or target was altered. The only added declaration in
   that module is the private proved precomposition helper. Verdict: pass.
2. Compiled both modules locally in import order with `lcompile.py`: no errors
   or warnings. The only delivered `sorry` is the named theorem
   `CategoryTheory.homComplex_global_homotopy`, listed above. No forbidden
   declaration forms or hollow definitions were added. The explicit `#print axioms` probe reports only `propext`,
   `Classical.choice`, and `Quot.sound` for the private helper; the two
   public comparison theorems additionally depend on `sorryAx`. Verdict: pass, conditional on the stated remaining hole
   and existing dependencies, rather than an unconditional proof.
3. Read Stacks 0A8Z (label
   `sites-cohomology-equation-global-cohomology-hom-complex`) and 08JA.
   The new lemma is the degree-zero ordinary-global assertion, for arbitrary
   complexes, with neither a derived functor nor a K-injectivity assumption.
   Its projection-based construction gives both variances: precomposition acts
   on the source, postcomposition on the target; the differential compatibility
   and passage to cocycle classes preserve these actions. Zero source or target
   yields zero groups; degree-zero complexes yield ordinary sheaf morphisms;
   unbounded complexes use products, not finite sums. The docstring and new node
   give the required proof. Fresh LeanFinder and Loogle searches with different
   wording found only external Hom cohomology and its representative formula;
   `rg` on Sheaf and both upstream source trees found no exact global natural
   comparison. The local-sections comparison requires a site object and local
   restriction, so it does not replace this statement on an arbitrary site.
   Closing this remaining natural comparison requires a substantial construction,
   not a short application. Verdict: true, strictly simpler, and not a restatement.
4. Read the reduction from the top. The right-derived unit supplies a natural
   transformation before resolutions are chosen. Its component at a K-injective
   Hom complex is invertible. Along the K-flat resolution the right side is
   invertible by `quasiIso_homComplex_map`; the left side is invertible by the
   ordinary comparison and `Qh_map_bijective`. The naturality square then proves
   the desired component invertible. No arbitrary existence witness is used to
   define data. Statement imports expose only signature requirements; new proof
   imports remain plain. The old proof dependencies moved to the new node are
   now all listed under No longer needed. Read `sk-def-sf-operations.json`:
   its `realized.statement` and `realized.steps` are empty, so no realized unit
   step is bypassed. Verdict: pass; net zero holes, a genuine decomposition.
5. Compared each revised proof step with its Lean implementation and checked
   the new node's statement against its verbatim Lean record. The existing
   node changes only `proof`, `proof_deps`, and `proof_origin`; the new node
   carries source, dependencies, searches, creation, blueprint, unit/chapter,
   and Lean fields. The precomposition helper implements the cited Mathlib
   K-injective-to-derived bijection without an additional hole. Verdict: pass.

Changed only this report: completed the list of old proof dependencies moved
below the new lemma, and recorded the independent reading. No Lean repair was
needed. One original hole is closed by reduction and one strictly simpler hole
is added; no modules are globally pruned.

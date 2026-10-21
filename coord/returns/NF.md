

## lem-weil-pbc-ringed-projection-mate-exact (2026-10-15 17:58 UTC, branch head f7a36e1158)

L: independent stage-2 immutable head f7a36e1158c9: the dependency node def-pc-kflat-complex: its `lean` changed on newtargets-dag since the delivery's base ({"module": "Sheaf.Algebra.Homology.KFlat", "declaration": "CochainComplex.IsKFlat", "file": "lean/Sheaf/Algebra/Homology/KFlat.lean", "statement": "def IsKFlat (K : CochainComplex (SheafOfModules.{w} ); the reviewer decides and the group re-pushes

Launcher: Sheaf.Algebra.Homology.KFlat now provides IsKFlat, IsKFlatResolution, and the independent-coefficient predicates; import it instead of changing it.
## lem-weil-compact-support-reduction-tower-functor (2026-10-15 23:34 UTC, branch head af1d5e4680)

L: approved by the reader, but the landing refused it: NOT MERGED lem-weil-compact-support-reduction-tower-functor: coord/.merge.lock held for 120 s by pid 3338206: /usr/bin/python3 tools/merge_delivery.py Q29 lem-kun-global-generated-stalkwise --stage 1 --reviewer NT-Codex-Q29-777e27298 --head 777e27298579165b3bbe3411efbe21cce9cff74f --spot-checked Read all required instructions, the item, cited nodes, blueprint/unit route, and Stacks/Mathlib sources. The module-to-abelian coefficient comparison, cokernel criterion, exact stalk argument, and conservative stalk conclusion are correct with unchanged hypotheses and target. No new nodes, duplicates, Rebase the delivery onto the current DAG, re-read every cited node that changed, adjust the split, and push again.

## lem-sp-filtered-homology-tower-forward-representatives (2026-10-17 06:01 UTC, branch head 62eb000b61)

L: independent stage-2 immutable head 62eb000b614c: incremental DAG validation: blueprint: lem-sp-filtered-homology-tower-forward-representatives: blueprint.from.node lem-sp-filtered-homology-tower-differential is not a blueprint node


## lem-weil-pbc-pseudocoherent-inverse-ring-reconstruction (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 6 (2462 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 6 (2462 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## det-uniform-constructible-ext-torsion (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 1 (2805 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 1 (2805 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are; the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.


## lem-weil-pbc-etale-constant-shriek-rel-dim-1 (dedicated repair handoff)

The previous worker ended with: re-split (decision of the human, 2026-10-17): step 4 (2617 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged

Compiler messages and attribution:
re-split (decision of the human, 2026-10-17): step 4 (2617 characters) is not elementary and hides lemmas; make each hidden argument a node of its own that the step cites; keep the statement unchanged. Start from the existing proof text of this node (it stays in the node file): keep its route and its other steps, and replace each long step by short steps that cite new nodes (or existing nodes/Mathlib leaves) for the arguments it now carries inline. The node's statement and its Lean record stay as they are (its stage-2 Lean statement remains valid, since the statement does not change); the new nodes go through stage 2 as usual. The stage-1 review rejects a non-elementary step longer than 2000 characters.

## lem-zl-bertini-field-extension (2026-10-17 19:35 UTC, branch head 211de05066)

L: independent stage-2 immutable head 211de05066ef: H1: the head 211de05066ef ('Split lem-zl-bertini-field-extension') is the stage-1 split, not a stage-2 statement. It has no Lean module (the snapshot has no lean/ tree), no lean record on the item node, and the report lacks '## Worker report' and '## Second reading by NF'. It adds six non-definition nodes (Tags 037N/0G31/0G32/0G33/037Q statements and a Mathlib leaf), which stage 2 does not allow. H2/H3/H8/H10 cannot be checked and there is nothing to compile. Correction: deliver one module stating Tag 0G4D as the node says (k,K fields, K/k finitely generated, GeometricallyIrreducible of Spec K -> Spec k via the Mathlib class, n>=1, g : Fin n -> K, Omega = FractionRing (MvPolynomial (Fin n) K), exists c with x_i, sum g_i x_i, sum c_i g_i AlgebraicIndependent over k; conclusion geometric irreducibility over the subfield k(x, xi)), with no Infinite k or separability assumption, the shared universe forced by GeometricallyIrreducible recorded, the proof sorry, docstrings giving the source place, blueprint id and the 7 proof steps, a complete lean record, both report sections, and a clean per-file compile.

## lem-sf-comparison-open-tensor-coherence (2026-10-18 07:03 UTC, branch head b0f81aa2c7)

L: independent stage-2 immutable head b0f81aa2c76e: H12/§1 theorem stmt_deps: the delivery adds theorem nodes lem-pur-open-projection-site-transport and lem-pur-support-site-comparison to stmt_deps only to use plain defs openProjectionExtensionComparison (OpenProjectionSiteTransport.lean:46, the derived-category version of openImmersionLowerShriekComparisonUpperStarIso of the already-cited lem-cbc-proetale-extension-zero-comparison) and supportDerivedPullbackIso (SupportSiteComparison.lean:273, the same wrapper around supportSiteComparisonCoefficientPullbackIso of the already-cited lem-weil-pbc-comparison-pullback). Neither is .choose of the theorem. Correction: remove both theorem nodes from stmt_deps and define e_F and a_j as helper declarations in the item module (listed in lean.declarations with source/blueprint docstrings), or move them into a definition node that the item cites; keep the theorems at most in proof_deps. Otherwise correct: all clauses, map orientations, adjunction-normalized gamma maps, h, unbounded binders, universes, edge cases, docstrings with the 5 proof steps, statement verbatim; nt_compile --json clean (6.1 s, rc 0). The second-reading section is a no-review note, recorded but not a fault on its own.

## lem-fix-site-perfect-scalar-hom (2026-10-21 07:39 UTC, branch head 56770ebd5b1)

L: independent stage-2 immutable head 56770ebd5b19: H2/H12 theorem-stmt_dep: the statement uses plain defs RingedTensorModules and RingedDerivedTensorCoherence from theorem node lem-sf-ringed-derived-closed-symmetric-monoidal (not .choose); cite the existing def node def-zl-ringed-derived-closed-symmetric-monoidal-data instead. ringedFiniteFreeScalarSection is a plain def owned by the uncited theorem node lem-sf-ringed-finite-free-tensor-complex, while the cited lem-sf-ringed-finite-free-tensor-data supplies nothing to the statement: drop it and add an existing:true def node on RingedFiniteFreeHomBaseChangeData (or inline the helper). Substance correct: F, H, symmetry and tensor comparison pinned; c is the specified transpose; iso, both naturalities and evaluation clauses match; no extra hypotheses; edge cases OK. nt_compile --json exit 0, 56.3 s (thin margin vs 60 s). A stage-2 FIX cannot change stmt_deps, hence RETURN.

## What changed

Proved `AlgebraicGeometry.etale_section_colimit_finite_zero_cover` in
`Sheaf.AlgebraicGeometry.EtaleSectionColimitEventualZeroAux`, preserving its signature.
Added proof-only imports of `Sheaf.AlgebraicGeometry.EtaleSectionColimitLocalZero`
and `WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit`.
The existing local-zero sieve theorem supplies local vanishing; the already proved
`Scheme.exists_finite_affine_of_mem_smallEtaleTopology` extracts a finite affine family.
Lift its `Fin n` index into `Type w` and verify that it is covering. Prove the separatedness
implication by applying the sheaf condition to maps from `ModuleCat.of Λ (ULift.{w} Λ)`
and evaluating at the lifted unit. This avoids any relation between the scheme and
coefficient universes. Updated the finite-zero-cover node to record these actual steps.
The other theorem and its already complete filteredness proof are unchanged.

Local compilation passed with no warnings. The source-library finite-refinement theorem
has no sorry. Empty objects and empty finite covers are supported by the sheaf condition;
`Fin 0` and its lift are permitted. No nonzero-section or nontrivial-ring assumption is added.
No definitions, existing statements, target signatures, or unit-level routes were changed.

## Proved and sorry left

Closed the one remaining hole:
`AlgebraicGeometry.etale_section_colimit_finite_zero_cover`
(node `lem-weil-pbc-etale-section-colimit-finite-zero-cover`).
The module now has no sorry. Added holes: none. Split-off statements: none.
`AlgebraicGeometry.etale_section_colimit_eventual_zero_of_finite_cover` was already proved
and remains unchanged. The local-zero theorem used here is already proved in the library.

## No longer needed

None. No imports were removed, and the old node had no named proof dependencies to prune.
All four public Mathlib imports remain needed by the existing signatures or first proof.
Both added imports are used by the new proof. No new finite-cover, sheafification,
or separatedness helper modules need to be introduced.

## Where the brief, the DAG or earlier work was wrong

The node's old one-step plan had no proof dependencies, although its first assertion is
already provided by `lem-weil-pbc-etale-section-colimit-local-zero-sieve`. Its module was
reintroduced and proved by S1 (the landed change record
`coord/changes/etale-section-colimit-local-zero-reintroduction.md`). The dependency is now
explicit. The existing source-library finite affine refinement works for every compact
etale object, without quasi-separatedness, and avoids duplicating the compactness argument.
The mathematical plan and the statement are correct.

## Second reading by U1

1. Compared the entire delivered module with the repository using `diff` and checked
   both existing theorem signatures byte for byte. Verdict: unchanged signatures,
   docstrings and existing filteredness proof; only two private proof imports and
   the finite-zero-cover proof changed. No definitions or target statements changed.
2. Compiled the delivered module cleanly with lcompile.py. A scratch copy with
   `#print axioms` for both module theorems, the local-zero-sieve theorem and the
   finite-affine-refinement theorem reports exactly `propext`, `Classical.choice`
   and `Quot.sound` for each, without `sorryAx`. Scanned for forbidden declarations
   and sorry: none. Verdict: complete kernel-checked proofs, no hollow data.
3. There are no new or split-off statements or nodes to validate. Read the two
   imported results and checked the selected arrows really belong to the sieve.
   The lifted finite index works independently of the scheme universe. Empty
   schemes/covers and the zero coefficient ring require no extra assumption:
   covering separatedness and evaluation at the unit still apply. Verdict: no
   disguised restatement or added hole.
4. Searched the library's section-colimit modules and source finite-cover/sheaf
   separatedness results, and used msearch grep with finite-cover and
   hom_ext_ofArrows terminology. The proof already uses the existing finite affine
   refinement and categorical sheaf separatedness; no shorter complete replacement
   was found. Both added imports are proof-only and used; the four public imports
   supply notions in the signatures. The old proof_deps list was empty, so no old
   dependency is omitted from No longer needed. Read sk-thm-p1's realized record:
   this auxiliary node replaces no unit-level statement or step. Verdict: pruned
   as reported and unit route preserved.
5. Compared the node JSON: only proof, proof_deps and proof_origin changed. The
   three steps match the local-zero sieve, finite selection and rank-one-module
   separatedness argument in Lean. The dependency is the existing local-zero
   node; no new-node fields are required. Verdict: DAG agrees with the proof.

Changes by the second reader: appended this review only; no Lean or DAG repair
was needed. This delivery closes one previously open hole, adds none, and keeps
both module theorems proved.

## What changed

Proved `AlgebraicGeometry.Scheme.etale_subsheaf_final_stalk_criterion` in
`Sheaf.AlgebraicGeometry.EtaleSubsheafSupportStalk`, keeping its signature and imports.
Mathlib's jointly-surjective stalk maps supply one section representative, or two
representatives on a common pointed neighbourhood. The factorization/emptiness
hypothesis makes every inhabited section set Unique. The open-immersion lift supplies
the pointed neighbourhood needed for the converse. Updated the existing node's proof
steps to describe these Lean arguments; its proof dependencies and origin stay the same.

The source was read in the locally available Stacks Étale Cohomology text, at
`lemma-support-subsheaf-final` (Tag 04HV). The target node is not a realization of
`sk-thm-iff`'s statement or steps; the unit route is unchanged.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.etale_subsheaf_final_stalk_criterion`
(node `lem-weil-pbc-etale-subsheaf-final-open-parts-stalk`), the only sorry in the item.
No sorry remains in the item, and no new sorry or auxiliary module was added.
The proof uses the definition `etaleSubsheafFactorization`, not the sorry-bearing
existence theorem `exists_open_etale_subsheaf_final_factorization` in its module.

## No longer needed

None: both existing public imports are needed by the unchanged statement.
No node or module from the planned dependencies is removed. The proof derives
uniqueness from the factorization hypothesis rather than separately proving that
monicity of the terminal map gives pointwise subsingletons.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The proof plan's monicity-to-section-subsingleton
step was unnecessary because the Unique and emptiness clauses of hW already give
uniqueness of every inhabited section set. No signature or definition was changed.

Searches used the prescribed leanfinder, loogle and grep wrappers, plus local rg
across Sheaf, WeilConjectures and Mathlib. Semantic search found no exact criterion;
Loogle/grep found Mathlib Point.toPresheafFiber_jointly_surjective and its two-element
version. These and IsOpenImmersion.lift/lift_fac close the complete argument.

## Second reading by K1

1. PASS: compared the sole delivered module against the repository with diff and
   checked the existing theorem signature byte for byte. No hypothesis, conclusion,
   definition, declaration visibility or import changed. The docstring now describes
   the implemented argument rather than the older monicity argument. No change record
   is needed because no statement or definition changed.
2. PASS: local lcompile.py compilation is clean. A scratch copy with #print axioms
   AlgebraicGeometry.Scheme.etale_subsheaf_final_stalk_criterion reports exactly
   propext, Classical.choice and Quot.sound; in particular no sorryAx. Scanned the
   complete module: no sorry, axiom, unsafe, opaque, implemented_by or extern, and
   no new definition. Read the section-uniqueness, common-representative, open-lift
   and point-evaluation arguments individually; each proves the stated goal.
3. PASS: no statement was split off and no new node or module was introduced.
   Checked the boundary cases W empty (no geometric lift or stalk element), W full
   (identity neighbourhood supplies the section), and empty etale objects (the
   factorization hypothesis forces their unique section). Re-searched Sheaf and
   WeilConjectures with subterminal/stalk terms, and Mathlib Point.Basic/Monoidal;
   independent leanfinder search for filtered colimits of sets with at most one
   element and Loogle search for sheafFiber/Subsingleton found no direct replacement
   for the entire criterion. The existing jointly-surjective lemmas give the short
   argument without introducing auxiliary statements.
4. PASS: the proof starts at the target and closes its only hole using Mathlib and
   the stated hW hypothesis. Both public imports are required in the signature:
   EtaleSubsheafSupportOpen provides etaleSubsheafFactorization and EtalePoint
   provides pointSmallEtale. No proof-only public import or obsolete proof dependency
   was found, so No longer needed is complete. Inspected sk-thm-iff.json: this node
   realizes neither its statement nor a step, and its unit route stays intact.
5. PASS: the existing node changes only its proof field. Its two steps describe the
   Lean proof, their uses union equals proof_deps, and proof_origin remains Tag 04HV.
   All three old proof dependencies are used foundational notions with Mathlib
   declarations. The support-existence theorem is a statement dependency supplying
   the meaning of hW, not an existence theorem invoked by this proof.

Second reading changed only this report by recording the independent review;
no repair to the Lean proof or DAG was necessary. Holes closed: one, namely
AlgebraicGeometry.Scheme.etale_subsheaf_final_stalk_criterion. Holes added: none.

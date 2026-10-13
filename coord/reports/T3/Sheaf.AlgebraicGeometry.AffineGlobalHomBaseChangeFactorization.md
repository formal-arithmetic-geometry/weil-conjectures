## What changed

Replaced the sole sorry in AffineGlobalHomBaseChangeFactorization with a complete Lean
reduction, preserving its signature. The proof obtains the actual gamma and normalized
sections comparison from exists_globalHomPullbackComparison, substitutes its fixed
adjunction equalities, proves invertibility of gamma's adjunct using a new perfect-source
lemma, and constructs b by mapping this isomorphism and composing with the sections
isomorphism. It then rewrites the chosen global comparison's defining equation and
specializes a general sections/base-change mate identity. The target map and both fixed
adjunctions are unchanged.

Two new proof-only imports replace four direct imports. Both new lemmas have separate
modules, source citations, complete proof plans, and nodes. The original node's proof,
proof_deps and proof_origin now describe the Lean reduction. No definitions, existing
statements, visibility, or other modules were changed.

## Proved and sorry left

Closed: AlgebraicGeometry.affineGlobalHomBaseChange_factorization
(lem-pc-affine-global-hom-base-change-factorization). No sorry remains in the item.

Added and still sorry:

- AlgebraicGeometry.exists_affineSectionsBaseChangeMate
  (lem-pc-affine-sections-base-change-mate), in AffineSectionsBaseChangeMate.
- AlgebraicGeometry.perfect_internalHom_pullback_isIso
  (lem-pc-perfect-internal-hom-pullback-isIso), in PerfectInternalHomPullbackIsIso.

This is a decomposition: one upper hole closed, two lower holes added (net -1).
It is not a claim that the factorization is free of sorry dependencies. The parent also
uses existing statements and the fixed map's construction, whose open dependencies
remain with their current nodes. All delivered modules compile via lcompile.py.

## No longer needed

Removed direct imports from the item:

- Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
- Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
- Sheaf.AlgebraicGeometry.PerfectRHomTensorComparison
- Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImageComposition

These modules and their four corresponding nodes are still needed below the new
lemmas: the first, second and fourth in AffineSectionsBaseChangeMate, and the third in
PerfectInternalHomPullbackIsIso. Thus no transitive module or mathematical dependency
has been pruned. The other two original proof imports remain in the item because its
proof explicitly uses quasi-coherence of RHom and preservation by derived direct image.

The old proof_deps entries removed from the parent node are:

- lem-pc-ringed-spaces-derived-direct-image-composition
- def-pc-global-derived-rhom
- lem-pc-affine-qcoh-derived-equivalence
- lem-pc-affine-derived-pullback-tensor-tilde
- lem-pc-perfect-rhom-tensor-comparison
- def-pc-derived-base-change-map

The four lemma dependencies now occur in the lower proof plans. The global-Hom
and base-change definitions remain used in signatures and in the lower plans;
they are not obsolete nodes. This list records removal from the parent's direct
proof_deps, not removal from the targets' import closure. Pruned modules: none.

## Where the brief, the DAG or earlier work was wrong

The original plan describes the right argument, but the existing signatures do not
supply its normalized affine source comparison or its sections/base-change mate equation.
The perfect duality theorem supplies duality data but not invertibility of the exact
evaluation-defined arrow for the supplied canonical tensor comparison. These are the
two gaps split off here; unproved existing lemmas were not treated as obstacles.

Mathlib's expComparison results found by semantic search require Cartesian monoidal
categories and do not apply to derived tensor. LeanSearch returned Internal Server Error;
LeanFinder, Loogle, Mathlib/project grep, and blueprint searches were also used. Sources
0AA7, 08I3, 08HY, 0D5T, and 0FPC were read on the Stacks website because the local
literature/stacks-project sources are absent on this machine. Tag 0FPC is an Example,
not a Lemma; the new docstring uses the correct label.

Edge cases checked mathematically: zero M or K gives zero objects and invertible zero
endomorphisms; identity g reduces the sections identity to the adjunction triangle;
zero m makes both sides of the mate equation zero. The general sections lemma requires
only Rf_*E to be quasi-coherent, exactly where the affine equivalence is applied. It
asserts neither Tor independence nor invertibility of BC_E. The perfect lemma allows
arbitrary unbounded K because exact pairing represents the tensor right adjoint on the
whole derived category. No target statement, unit statement, or realized step is bypassed;
the unit's realized arrays for this item contain no additional binding route.

## New nodes

lem-pc-affine-sections-base-change-mate states the affine extension/restriction mate
identity for every object L and every arrow E → R(g_X)_*L. It has no internal Hom or
perfectness assumption and does not assert its final arrow invertible. It packages
steps 2, 3 and 5 of the original plan without restating the perfect-Hom factorization.
Its target sections natural isomorphism is simultaneous in L and m.

lem-pc-perfect-internal-hom-pullback-isIso states invertibility of the precisely
specified evaluation-defined pullback map for a perfect source and arbitrary target K.
It has no affine base rings, global sections, fibre-product square, or sheaf base-change
map. It is step 4 of the original plan. The parent uses its conclusion to build b and
combines it with the independent mate identity, rather than applying a renamed copy
of the original theorem. No change record is needed because no interface changed.

## Second reading by T3

1. **Interface preservation: pass.** Compared the delivered parent module with
   the repository using diff. Its sole existing theorem signature and docstring
   are byte-for-byte unchanged. Only proof-local options, proof imports and the
   proof body changed. The two other modules are new; no existing definition,
   target, visibility or statement changed and no change record is required.
2. **Proof and trust: pass.** Independently compiled all three modules in import
   order through lcompile.py: no errors or warnings. Inspected every declaration:
   precisely the two named split theorems contain sorry; no data definition or
   forbidden trust escape is added. A scratch #print axioms probe checks all three
   declarations; only the standard axioms and sorryAx from the reported open
   dependencies occur. The parent constructs b by mapping asIso(theta) and
   composing with d, rather than defining data from an arbitrary existence hole.
   Existential witnesses a,d are eliminated inside a theorem proof only.
3. **Split statements: pass.** Read both signatures, complete docstring arguments
   and matching nodes. The sections statement concerns arbitrary E,L,m with
   quasi-coherent Rf_*E, while the perfect statement concerns the local
   evaluation-defined arrow for arbitrary K. Neither restates the parent.
   Identity pullback, zero perfect source, zero K, and zero m have the expected
   identities or zero maps; no Tor independence is needed for the asserted
   factorization. Rechecked the source construction in Stacks
   [08I3](https://stacks.math.columbia.edu/tag/08I3), the general base-change map
   [08HY](https://stacks.math.columbia.edu/tag/08HY), and perfect duality
   [0FPC](https://stacks.math.columbia.edu/tag/0FPC).
   Independently searched with LeanFinder for monoidal comparison at a dualizable
   object, Loogle for adjunction/natural-isomorphism comparisons, and msearch grep
   for dualizable, tensorRightHomEquiv and mateEquiv. Project searches included
   pullback/internalHom and sections/baseChange in both roots. The Cartesian
   expComparison lemmas do not apply; the rigid tensor Hom equivalence and mate
   calculus are ingredients, not either normalized derived statement.
   perfect_rhom_evaluation_isomorphisms supplies the all-objects evaluation
   comparison, but transporting it and identifying the supplied canonical t
   still requires the argument left in the perfect split. No split closes by
   an immediate existing theorem application.
4. **Route and pruning: pass after report repair.** Followed the parent proof
   downward: fixed comparison witnesses, normalized adjunction substitution,
   quasi-coherence, invertibility of theta, construction of b, and specialization
   of the sections mate equation. All parent imports are used, and the additional
   lower imports encode their stated proof plans. Inspected
   dag/units/sk-thm-picard-duality.json: its realized statement and step arrays
   contain no binding node bypassed here. The original five mathematical steps
   persist in the two lower arguments and parent reduction. Added the exhaustive
   list of old parent proof_deps removed; no transitive pruning is claimed.
5. **DAG consistency: pass.** The existing node changes only proof, proof_deps
   and proof_origin. Both new nodes have source, chapter/unit, provenance,
   searches, blueprint origin and complete Lean records; their stored signatures
   equal the source signatures verbatim, and proof_deps equals the union of
   proof-step uses. The parent dependencies name precisely its reduction.

Second reading changed only report.md: completed the removed-dependency list and
recorded this review. The Lean reduction and split statements needed no repair.
One original hole closed, two named holes added: a decomposition, net -1.

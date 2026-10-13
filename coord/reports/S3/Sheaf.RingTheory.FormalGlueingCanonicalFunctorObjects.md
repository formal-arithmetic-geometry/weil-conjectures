## What changed

Proved `FormalGlueing.exists_canonical_functor_objects` without changing its statement,
visibility, universes, or imports. Proved private helpers identify each restricted chart
with the canonical localized R-module, construct the comparison and swap equivalences,
and transport their linear maps and compatibility equations along those equalities.
The selected equivalences are uniquely determined by their displayed heterogeneous
linear-map equalities; no arbitrary existence witness supplies module data.

Both compatibility equations follow from localization uniqueness. Multiplication by
all localized denominators is bijective in the target. After restricting to the original
module, the cocycle follows from the swap formulas. After restricting to pure tensors,
the square follows from the comparison, localized-map, and swap formulas. Additivity
and localization uniqueness extend these computations to every element. This also covers
zero denominators, the zero module, repeated charts, and an empty chart family.

The source is Stacks Project Remark 05EL, read at
https://stacks.math.columbia.edu/tag/05EL (the local literature checkout is absent).
The existing node's two-step route and all unit-level steps are retained.

## Proved and sorry left

Closed the sole original hole:
`FormalGlueing.exists_canonical_functor_objects`
(node `lem-weil-pbc-formal-glueing-canonical-functor-objects`).
No holes added or split off. No `sorry` remains in the delivered module.
All private helpers have complete proofs.

## No longer needed

None. Both existing imports remain needed: `FormalGlueingData` supplies the statement
and canonical constructions; `FormalGlueingCanonicalMaps` supplies comparison bijectivity
and inverse swap identities. No planned node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The restricted localized chart and the localized R-module
are not definitionally equal in Lean. Their literal bundled equality must be proved
using `Module.ext'` and `algebraMap_smul`, before transporting the equivalences.
The suggested fraction induction can be replaced by localization uniqueness and
agreement at denominator one, preserving the same canonical construction and source route.

## Second reading by S3

1. **Interface: pass.** Read the complete diff against the repository module.
   The sole existing declaration, `FormalGlueing.exists_canonical_functor_objects`,
   has a byte-identical signature, including universes, arbitrary ring map, arbitrary
   finite chart family, literal bundled-module equalities and both HEq clauses.
   Imports, visibility and existing docstring are unchanged. All added declarations
   are private proved helpers; no definitions or change records were added.
   Read [Stacks Remark 05EL](https://stacks.math.columbia.edu/tag/05EL): its canonical
   object has exactly the scalar-extension module, localized charts and canonical
   comparison/overlap maps asserted here, with no covering, flatness or finiteness
   hypothesis on the rings or module.

2. **Proof: pass.** The delivered file compiled cleanly through `lcompile.py`.
   A scratch copy with `#print axioms FormalGlueing.exists_canonical_functor_objects`
   was compiled separately and showed exactly `propext`, `Classical.choice` and
   `Quot.sound`; the delivery tool also probes all declarations.
   There are no remaining sorries or forbidden declarations in the delivered file.
   `canonical_piece_eq` proves equality of the R-actions rather than assuming a
   definitional identification. `canonical_alpha` uses precisely the bijectivity
   clause of `compare_properties` and `compare_smul`; `canonical_overlap` uses
   both inverse identities of `swap_properties`. The chosen equivalences are
   fixed by their HEq linear maps, and both existential lemmas are proved here;
   the charts and prime module are explicit constructions.

3. **Split statements: pass, none.** No holes or new public statements were added,
   and no new nodes require source/search review. Checked the private helpers:
   scalar bijectivity propagates through localization by map injectivity and
   surjectivity, and through scalar extension by base-changing the actual scalar
   linear equivalence. Thus localization uniqueness applies without assuming a
   domain or nonzero denominators. At denominator zero the localization is zero;
   repeated denominators cause no difficulty. Empty chart families require no
   alpha, square or cocycle instances, and the zero-module case is included.

4. **Route and pruning: pass.** Read both imported modules in addition to the
   construction. The square is reduced twice by `local_ext`, then by tensor
   induction to the denominator-one compare/swap formulas. The cocycle is reduced
   three times by `local_ext`, then its two evaluations agree by
   `swap_one` and `local_map_one`. All bijectivity assumptions concern the common
   codomain and are established explicitly. Searched independently with Loogle
   for `IsLocalizedModule.ext` and with rg for interchange/composition and
   canonical-glueing results in Mathlib, the upstream RingTheory sources and
   lean/Sheaf. Mathlib supplies the uniqueness lemma already used here; nearby
   swap naturality results do not give this square or triple cocycle. The similar
   helpers in `FormalGlueingCanonicalMaps` and `FormalGlueingData` are private,
   so cannot replace the local proofs through their public interfaces.
   Both imports and both original proof-dependency nodes are used; nothing is
   pruned. Read `dag/units/sk-thm-p1.json` and its `realized` statement/steps:
   this construction is below those unit steps and bypasses none of them.

5. **Nodes: pass.** Compared the delivered node with the repository node: only
   `proof` and `proof_origin` differ. Its unchanged two dependencies are exactly
   the data construction and canonical-map properties used in Lean. The revised
   second step accurately describes localization uniqueness, denominator-one
   formulas, scalar bijectivity and tensor induction. Statement, Lean signature,
   chapter, unit and all other fields are unchanged.

Second reading changed only this review report. No mathematical repair was needed.
The original hole is closed, zero lower holes are added: proved 1 of 1, not a
hole-preserving decomposition.

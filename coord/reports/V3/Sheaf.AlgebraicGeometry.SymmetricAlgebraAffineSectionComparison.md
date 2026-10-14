## What changed

Completed `Sheaf.AlgebraicGeometry.SymmetricAlgebraAffineSectionComparison` with the
signature and public imports unchanged. The proof follows all three steps of its
node: affine module and symmetric-algebra base change, transport to tilde sections,
and generator computations for naturality and the sheafification-unit factorization.

All intermediate work is proved in private helpers in this module:
`symmetricCongr`, `symmetricCongr_ι`, `exists_sectionTensorEquiv`,
`exists_tildeTensorEquiv`, `exists_sectionEquiv`, `section_induction`,
`restriction_smul`, and `restriction_comp`. The two unfinished new modules left by
the previous attempt were never in the repository; their files were moved out of
`lean/` into `scratchpad/` and are not delivered. No public definitions or statement
interfaces were changed. The existing node's proof text now describes the Lean argument.
The conservative static checker also requires
`coord/changes/symmetric-algebra-affine-section-proof-elaboration.md`, which
documents the added tensor notation opening and declaration-local heartbeat options.
The repair removes both previously added file-wide transparency options; the complete
proof compiles with the baseline transparency settings in 16.0 seconds. A fresh
`#print axioms` check of the public theorem and all eight private helpers compiled
in 16.4 seconds and lists only `propext`, `Classical.choice`, and `Quot.sound`.

Two local declaration heartbeat settings allow the elaborator to compare the transported
section-module scalar structures; the 60-second file compilation limit is unchanged.

Repair validation: `deliver3.py --no-push` with `WEIL_SERVER_COMPILE=1` passed
local compilation, the axiom probe, server compilation, and preflight on a freshly
fetched `sheaf-dag` base. It printed `OK (dry run)`; nothing was pushed. The previous
second reading below is retained as historical review of the returned version;
the repaired version is ready for its next independent reading.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.SymmetricAlgebraSheaf.exists_affineSectionComparison`
(node `lem-weil-pbc-symmetric-algebra-affine-section-comparison`).

Holes closed: 1. Holes added: 0. No `sorry` remains in any delivered declaration.
Every private helper is proved, including the tensor isomorphisms, their pure-tensor
formulas, and the section induction principle. No arbitrary witness of an unproved
existence theorem is used to supply data. The affine base-change maps are determined
by their pure-tensor formulas, and the pointwise equivalences are proved here.

The proof covers zero modules, the empty affine open, and the zero section ring:
all isomorphisms and tensor inductions are unrestricted and require no finiteness,
separatedness, nonemptiness, or nontriviality hypotheses.

## No longer needed

No repository imports or DAG dependencies were pruned. Both original proof imports
are used: `Sheaf.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange` and
`Sheaf.RingTheory.SymmetricAlgebraBaseChange`. All original direct proof dependencies
remain relevant, including the affine tilde-Gamma global section isomorphism.

The unpublished sandbox modules `SymmetricAlgebraAffineSectionEquiv` and
`SymmetricAlgebraAffineSectionGenerators` are unnecessary as separate items:
their obligations are now proved as private helpers. They had no repository node
files and are not withdrawn library modules.

## Where the brief, the DAG or earlier work was wrong

The returned landing failed while inspecting an absent downstream Picard module,
not while compiling this theorem. The current import-pruning checker skips missing
downstream source paths. This repair also removes the unnecessary file-wide
`backward.isDefEq.respectTransparency` and
`backward.isDefEq.respectTransparency.types` overrides, and revalidates the reduced
file against the current build and freshly fetched delivery base. No Picard module
is imported, reconstructed, or changed by this delivery.

The previous attempt had left two proposed intermediate holes without node records
or an assembled proof of the item. Those proposals are now completely proved inside
the item, so this delivery does not pass the obligation on again.

The prescribed tensor plan works. For the tilde side, Lean requires explicit change
of tensor base from Γ(Spec R,top) to R via `equivOfCompatibleSMul`, using surjectivity
of `ΓSpecIso.inv`; `tilde.isoTop` alone changes the module factor, not the tensor base.
Scalar and restriction computations also require the correct section-module instances.

The repository lacks the downloaded Stacks TeX files named by the node. The relevant
source pages were read online: [01I8](https://stacks.math.columbia.edu/tag/01I8),
[01LN](https://stacks.math.columbia.edu/tag/01LN), and
[0C6F](https://stacks.math.columbia.edu/tag/0C6F). Their roles agree with the plan:
affine tilde tensor constructions, affine quasi-coherent base change, and symmetric
algebra localization. No source or unit-route correction was needed.

## Earlier second reading (a previous round; superseded)

1. **Interfaces: pass.** I diffed the sole delivered Lean module against the
   repository version and compared the existing theorem signature programmatically:
   `exists_affineSectionComparison` is byte-for-byte unchanged, as is its docstring.
   All three imports have their original visibility. The public comparison-map import
   supplies the statement's definitions; both base-change imports are proof-only.
   The only extra declarations are private proved helpers. The change record accurately
   documents the file-local notation opening and elaboration options; no definition,
   existing declaration signature, target, or other module is altered.

2. **Proof and axioms: pass.** The delivered file compiled locally without errors or
   warnings in 18.7 seconds. A scratch copy with `#print axioms` for the public theorem
   and each of `symmetricCongr`, `symmetricCongr_ι`, `exists_sectionTensorEquiv`,
   `exists_tildeTensorEquiv`, `exists_sectionEquiv`, `section_induction`,
   `restriction_smul`, and `restriction_comp` compiled in 18.9 seconds. Every result
   lists exactly `propext`, `Classical.choice`, and `Quot.sound`, without `sorryAx`.
   The delivered source contains none of the forbidden constructs and no `sorry`.
   `symmetricCongr` constructs both algebra maps by the universal property and proves
   they are inverse. The tensor equivalences are obtained from actual linear maps
   with proved bijectivity. The chosen section equivalences are proved here, and their
   scalar/restriction formula determines them on an additive generating family.
   No arbitrary witness of an unproved existence statement supplies data.

3. **Split statements and edge cases: pass.** There are zero split-off holes or new
   public statements, so no new node or postponed docstring proof is needed. I read
   each helper's hypotheses and conclusion. The symmetric-algebra induction covers
   coefficients, degree-one generators, products and sums; tensor induction covers
   zero, pure tensors and sums. This remains valid for the zero module, zero rings,
   empty affine opens (including empty W), and U=W. No step assumes nontriviality,
   nonemptiness, finite generation, finite presentation, or separatedness. Searches
   with the independent phrases “SymmetricAlgebra equivalence induced by linear
   equivalence between modules” and “quasicoherent symmetric algebra sections on an
   arbitrary affine open tensor product global sections” through LeanFinder, plus
   `rg` in Mathlib, upstream modules and `lean/`, found no direct shorter comparison
   or usable public replacement for the private symmetric-algebra congruence.
   `IsSymmetricAlgebra.of_equiv`/`comp_equiv` require an existing algebra equivalence;
   the related `exists_symmetricEquiv` in SymmetricConormalPresentationTransport is
   private and handles a more general semilinear transport. The existing dependency
   theorems are used rather than restated as new holes.

4. **Top-down route and pruning: pass.** I traced the whole proof from the target:
   sectionwise symmetric-algebra base change, tilde section base change and chart
   transport give the components; additive section induction proves naturality and
   the unit factorization. Naturality uses the restriction composition law,
   `tilde.toOpen_res`, and `appIso_hom_naturality`. The final clause uses the actual
   `affineComparison_toOpen` formula, module linearity and sheafification-unit
   naturality. Thus the proof establishes both bijectivity and the stated composite,
   rather than just an abstract section equivalence. Every original direct
   dependency is used and all imports are needed; “No longer needed” is complete.
   I read `dag/units/sk-thm-p1.json`, including all four steps and `realized`:
   this item is a lower tool node and changes none of those realizations or routes.
   The source pages [01LN](https://stacks.math.columbia.edu/tag/01LN),
   [01I8](https://stacks.math.columbia.edu/tag/01I8), and
   [0C6F](https://stacks.math.columbia.edu/tag/0C6F) support the affine base-change,
   tilde tensor-construction and localization ingredients of the retained plan.

5. **DAG agreement: pass.** I compared the delivered node with the repository node:
   only `proof` and `proof_origin` differ. Its recorded Lean statement equals the
   unchanged theorem signature. The three proof steps accurately describe the
   module base-change equivalence, symmetric and tilde tensor transports, and the
   generator computations. The union of their `uses` is precisely the unchanged
   seven-element `proof_deps`; there are no new nodes, undeclared split statements,
   removed dependencies, or changes to the unit's realizations.

Second reading changed only this report by adding the independent review and
verification evidence. No Lean proof, interface, import, node, or change record
needed repair. Holes closed: `AlgebraicGeometry.SymmetricAlgebraSheaf.exists_affineSectionComparison`
(one of one); holes added: none; modules or nodes pruned: none.


## Second reading by V3

Independent reading of the repaired version, 2026-10-14:

1. **Visible interfaces: pass.** Compared the complete delivered module with the
   repository version using `diff`, then extracted and compared the existing
   `exists_affineSectionComparison` signature and docstring byte for byte. Both
   are unchanged. The three imports and their visibility are unchanged: the public
   comparison-map import supplies definitions in the statement; the two base-change
   imports are needed only for proofs and remain plain imports. The additional
   declarations are private. The existing change record accurately documents the
   tensor notation opening and the two declaration-local heartbeat settings. No
   definition used by any target, public signature, or target statement changes.

2. **Proof and axioms: pass.** Read all 326 lines, including every helper and both
   final compatibility arguments. A fresh scratch copy with `#print axioms` for the
   public theorem and all eight private helpers compiled through `lcompile.py` in
   18.6 seconds, without errors or warnings. Every declaration uses only `propext`,
   `Classical.choice`, and `Quot.sound`; none uses `sorryAx`. The delivered source
   has no `sorry` or forbidden declaration/implementation constructs. In
   `symmetricCongr`, both maps are constructed by symmetric-algebra lifts and proved
   inverse on generators. The tensor equivalences use actual linear maps and proved
   bijectivity. In particular the base-change maps are determined on pure tensors,
   and the chosen chart equivalences are determined on their additive generating
   family by the displayed formula. No arbitrary unproved existence witness supplies
   data, and no definition contains a proof hole.

3. **Split statements and small cases: pass.** There are no new public statements,
   split-off holes, or new nodes. Checked the private helpers for the zero module,
   zero rings, empty affine opens, identity inclusions, and arbitrary affine opens
   contained in W. Neither tensor nor symmetric-algebra induction requires
   nontriviality, finite generation, nonemptiness, or separatedness. The scalar-base
   replacement in `exists_tildeTensorEquiv` uses surjectivity of the proved
   `ΓSpecIso` inverse, rather than assuming that changing only the module factor
   changes the tensor base. Independently ran LeanFinder searches for a natural
   additive comparison on affine opens and for the symmetric-algebra equivalence
   induced by a linear equivalence, and a logged grep for symmetric-algebra
   equivalences. Read the returned Mathlib declarations. `IsSymmetricAlgebra.of_equiv`
   and `comp_equiv` require the algebra equivalence already; they do not replace its
   construction. Searched `lean/`, upstream algebraic geometry, and Mathlib's
   symmetric-algebra files with `rg`. The related semilinear transport helper is
   private in another module, and the quasi-coherent symmetric-algebra assembly
   depends downstream on this comparison. No direct shorter independent route was found.

4. **Route and pruning: pass.** Read both base-change dependency statements and the
   comparison-map module. The first helper applies module base change to F and then
   symmetric-algebra base change. The tilde helper applies module base change to
   tilde(A), uses `isoTop`, and transports scalars through the affine chart.
   Section induction then proves naturality using restriction composition,
   `tilde.toOpen_res`, and `appIso_hom_naturality`. The final compatibility uses
   `affineComparison_toOpen`, the actual scalar action on the restricted module,
   and naturality of the sheafification unit. Thus the composite is the specified
   unit on every section. All seven old proof dependencies remain used; no import,
   node, or module can be listed as pruned from this proof. Read all four steps and
   the `realized` mapping of `dag/units/sk-thm-p1.json`; this lower tool node preserves
   that unit's route. Read Stacks
   [01I8](https://stacks.math.columbia.edu/tag/01I8),
   [01LN](https://stacks.math.columbia.edu/tag/01LN), and
   [0C6F](https://stacks.math.columbia.edu/tag/0C6F): their tensor construction,
   affine base-change ingredient, and localization of symmetric algebras support
   the retained argument, with general algebra base change supplied by the proved
   universal-property dependency.

5. **DAG agreement: pass.** Compared the node JSON with the repository version.
   Only `proof` and `proof_origin` change. The recorded Lean statement equals the
   unchanged theorem signature, and the union of the three steps' `uses` equals
   the unchanged seven-element `proof_deps`. Step 1 describes the module tensor
   equivalence; step 2 describes symmetric and tilde transport, including the
   scalar-base adjustment; step 3 describes section induction for both naturality
   and the unit equation. No unit realization, statement dependency, source,
   or new-node record is changed.

Second reading changed only this report, by appending this fresh independent review.
No Lean, DAG, import, or change-record repair was needed. Holes closed:
`AlgebraicGeometry.SymmetricAlgebraSheaf.exists_affineSectionComparison` (one of one).
Holes added: none. Split off: none. Pruned: none.

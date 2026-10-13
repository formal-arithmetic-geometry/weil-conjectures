## What changed

Reduced `AlgebraicGeometry.Etale.strictLocalDerivedExchange_leray` to the exchange
computation before sections and an independent sections-unit/Leray computation.
The latter is proved completely using exact-derived comparison, naturality and
the derived-composition unit factorization. The main proof combines the two
computations using localization naturality and functoriality. Signatures of all
existing declarations stay unchanged. No definitions or other held modules changed.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Etale.strictLocalDerivedExchange_leray`.
Proved the new theorem `AlgebraicGeometry.Etale.strictLocalSections_unit_leray`,
including its three private comparison helpers. All three sandbox modules compile
with lcompile.py --all.

One new hole remains: `AlgebraicGeometry.Etale.injectiveExchange_representative`
(blueprint: lem-weil-pbc-injective-exchange-representative). Its source and complete
proof in words are in its docstring and node. It computes exchange before applying
sections, with no Leray assertion, and is strictly a part of the original argument.
This is a decomposition with one original hole closed and one new hole added,
not an axiom-free proof of the original theorem. Existing imported holes are unchanged.

## No longer needed

No original public import was removed from the item. No transitive module is claimed pruned.
The new sections helper now imports only
`Sheaf.AlgebraicGeometry.StrictHenselizationRestriction`; its unnecessary direct imports
`StrictLocalInjectiveSourceComparison` and `WeilConjectures.SixFunctors.BaseChange.Square`
were removed during second reading.
The original direct proof dependency
`lem-weil-pbc-injective-sections-pullback-comparison` is not used by this calculation:
no cohomology, neighbourhood restriction, or source sections unit inversion occurs.
Its module remains in the pre-existing signature import closure, so this is only
pruning of the proof plan, not removal of an imported module.
The other original direct dependencies
`prop-weil-pbc-derived-inverse-image-adjunction`,
`def-weil-pbc-underived-exchange` and
`def-weil-pbc-strict-local-injective-source-comparison` move to the exchange helper;
none is globally pruned. The sections helper does not use
`lem-weil-pbc-derived-leray-composition` or its declaration `derivedLeray_comp`;
its proof dependencies now record only the strict-local exactness input and
its proof text names the generic source interfaces actually used.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or required interface correction was found. The DAG formerly
combined exchange and Leray into one step; the delivery separates them so the
remaining exchange calculation can be proved independently. Mathlib searches found
no theorem for the full comparison; generic derived composition and unit lemmas in
the source library provide the Leray part.

## New nodes

`lem-weil-pbc-injective-exchange-representative` in
`Sheaf.AlgebraicGeometry.InjectiveExchangeRepresentative` states the exchange
calculation on an injective representative before sections; its proof remains sorry.
The target direct-image unit is retained, so pulled-back injectivity is unnecessary.

`lem-weil-pbc-strict-local-sections-unit-leray` in
`Sheaf.AlgebraicGeometry.StrictLocalSectionsUnitLeray` is proved and applies to any
complex D and any r:Q(D)→T. It never inverts r or the direct-image unit, including
for zero or nonacyclic complexes. Together these are exactly the two independent
computations needed by the original theorem.

## Second reading by K1

1. Interface: diffed the sole existing delivered module against the repository.
   The theorem signature from `theorem strictLocalDerivedExchange_leray` through
   its final `:=` is byte-for-byte unchanged. The only module changes are two
   ordinary proof imports and the proof body. The two other modules are new.
   No definitions, target statements or other held modules were changed.
2. Proof: independently compiled all three modules with lcompile.py --all.
   Also compiled scratch copies with #print axioms for all three public theorems
   and the three private sections helpers. The sections theorem and its helpers
   use only propext, Classical.choice and Quot.sound. The remaining exchange
   theorem and the main theorem use sorryAx, as explicitly reported. The sole
   textual sorry is the entire proof of injectiveExchange_representative; no
   hollow definition, unsafe, opaque, extern, implemented_by or custom axiom.
3. Split statements: read Stacks Tag 03Q9 (theorem-higher-direct-images), its
   final injective-complex paragraph, sourceInjectiveDirectImageIso, the generic
   derivedPlus_mateEquiv_app_fac and pullbackSquareComparison_hom_app_factorsh.
   The exchange statement is the computation before sections, retaining the
   target unit. Bounded-below injectivity makes only the SOURCE unit invertible;
   q lifts through the fully faithful inclusion, as its docstring explains.
   No qcqs assumption is needed for this natural-transformation computation:
   unlike the full stalk theorem of 03Q9, it asserts no exchange isomorphism.
   Zero J and identity f reduce to unit/naturality identities; no pulled-back
   injectivity is presumed. The sections statement allows arbitrary D and r,
   including zero r and nonacyclic D, since neither is inverted. It contains
   no exchange assertion and is kernel-proved. This is a genuine decomposition,
   not a renamed copy of the item. Repeated searches with different words via
   msearch leanfinder, loogle and grep, and rg on Sheaf and slopmaster2, found
   generic derived unit factorization, not an exact public replacement.
   EtaleKInjectiveUnitLeray has a private analogous leray_fac calculation, but
   its public theorem assumes K-injectivity and has a different conclusion;
   it cannot replace this general sections statement. The new nodes carry
   source, docstring proof, complete Lean signature, creation and blueprint data.
4. Route and imports: the main proof applies congrArg of exact sections to
   the exchange computation, moves the localization comparison by naturality,
   applies strictLocalSections_unit_leray at the displayed pullback transport,
   and combines the two termwise maps by Q.map_comp. These are actual independent
   parts of the original argument. Read dag/units/sk-prop-h2.json: its realized
   fields are empty and unchanged; no unit realization or chapter route is
   bypassed. No globally pruned module is claimed. Updated No longer needed to
   account for every old direct proof dependency. Narrowed only the new sections
   helper import to StrictHenselizationRestriction, sufficient for its signature
   and exactness input, and checked compilation again.
5. DAG: compared the item node with the repository: only proof, proof_deps and
   proof_origin changed. Its two dependencies match the two applied theorems.
   The exchange node records the original adjunction, underived exchange and
   canonical source comparison. The sections node incorrectly cited
   derivedLeray_comp, which is an associativity theorem and is never applied.
   Removed that citation from its proof and proof_deps, recording the generic
   rightDerived_ext, rightDerivedNatTrans_fac and comparison-unit interfaces
   actually used. Its statement dependencies now name the sections/derived
   cohomology definition and strict-local restriction. Marked failed LeanSearch
   service results unavailable and made the new source labels precise.

Second reading changed imports, DAG dependency accuracy, source/search metadata,
and this report. The mathematical statements and working proofs were retained.
One original hole closed and one new hole added: net zero, a decomposition.
Source read: https://stacks.math.columbia.edu/tag/03Q9.

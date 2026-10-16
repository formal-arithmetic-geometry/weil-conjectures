## What changed

Proved the derived open-immersion projection formula, the compactification
projection morphism's naturality in its second variable, and both bounded
constructible naturality lemmas. The argument is the
naturality of the proper projection mate, the inverse open-immersion comparison,
and the compactification pullback isomorphism. For the first variable, private
formal lemmas establish naturality of the two adjunction mates and their
composite. The bounded statements follow by the faithful full-subcategory
inclusion and explicit reduction of its lifts.

The open case first proves that the adjunction unit is invertible on module
objects and on their derived categories. The underived tensor-support argument
uses the coequalizer presentation of the relative tensor: both objects of the
parallel pair have invertible abelian extension counits, so the coequalizer does
too. The linearized counit and scalar-change equivalence then put the relative
tensor in the image of module extension by zero. The underived projection maps
assemble into a complex isomorphism. Replacing the ambient complex by a K-flat
representative proves support for the derived tensor. Finally the derived
projection comparison is the image of its invertible unit/tensor comparison
followed by an invertible counit. All these helpers are private and proved.

Added a proof-only import of
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal`
for its K-flat tensor-localization comparison. The complex comparison follows
the already proved finite-coefficient argument, now using the relative tensor
of module objects rather than treating the two coefficient categories as equal.

Added five proved instance shortcuts in the unclaimed module
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor`. They cache the
existing derived monoidal structure and the three graded tensor side conditions;
they do not change the underlying tensor data. The assigned module uses a local
transparency directive to avoid unfolding the derived localization functors.
All existing signatures, definition bodies, and public imports are unchanged.
The change record is
`coord/changes/H1-projection-naturality-tensor-instances.md`.

Other source modules present in the sandbox are byte-identical dependency
copies. The published build initially lacked some new modules and exposed the
older unbundled scheme interface for BoundedConstructible. These copies compile
the current source interfaces; they introduce no delivered source changes.
The modules held by A4 (BoundedConstructible) and D4 (Derived.Monoidal) are
unchanged.

## Proved and sorry left

Closed 4 of the original 5 holes, with no holes added and no decomposition:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_openImmersionProjectionComparison`.
- `AlgebraicGeometry.ProEtale.CondensedRing.exceptionalProjectionMorphismOfCompactification_natural_right`.
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_natural_right`.
- `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleExceptionalProjectionMorphism_natural_left`.

The one original hole remaining is:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_boundedConstructibleExceptionalProjectionMorphism`:
  the proper derived projection formula on the compactification, followed by
  extension by zero and the pullback comparison.

No DAG node has a lean attachment to this module or the remaining declaration
in the shared snapshot; the original file has no blueprint identifiers. No new
sorry is introduced in a definition, private helper, instance, or theorem.
The instance-shortcut module has zero holes.

## No longer needed

None. No original import was removed and no node or module was bypassed.
The proof follows the three constituent maps already described in the module.
The general sheaf-of-modules and ordinary etale projection-formula modules were
examined but are not imported: their coefficient categories do not match these
condensed module objects.

## Where the brief, the DAG or earlier work was wrong

The current source module has no directly attached DAG node, so there is no
node-specific numbered proof or proof-dependency attachment to update. The
module's own naturality plan was sufficient and is followed.

The original documentation says the bounded naturality term proof times out.
The underlying issue was uncontrolled unfolding of the derived functors after
passing to underlying morphisms. Keeping those functors closed and explicitly
reducing the full-subcategory lifts resolves it. Existing docstrings are
preserved; their statements that these three naturalities and the open formula
are sorried are now outdated.

The pre-existing open-immersion projection-formula theorem for abelian pro-etale
sheaves is not a theorem about the relative tensor product on module objects in
the derived category. The delivery supplies the relative-tensor support argument and the
derived comparison needed to bridge that distinction. The proper case still
requires the condensed-module derived projection formula, not the coherent
sheaf or ordinary discrete-coefficient versions.

## Second reading by H1

1. **Signatures and definitions.** Compared the delivered projection-formula module with the shared repository version. All existing declaration signatures and definition bodies are unchanged; the only interface addition is the proof-only import of `DerivedCategory.LeftDerivedFunctor.Monoidal`. The five added instances in the unclaimed derived tensor module are new declarations and do not alter existing signatures. **Verdict: pass.**

2. **Compilation and trust.** Compiled all sandbox modules with `lcompile.py --all`; every module compiled successfully. The only remaining `sorry` is the explicitly reported `isIso_boundedConstructibleExceptionalProjectionMorphism`; no `sorry` occurs in a definition or private helper. Axiom checks on the four closed declarations report only the allowed base axioms plus `sorryAx` inherited from the still-open declaration/import closure. **Verdict: pass with the existing upstream `sorryAx` dependencies explicitly retained; these are closed local holes, not yet unconditional target proofs.**

3. **Statements and split-offs.** The four closed declarations retain their original statements. No new public theorem obligation or split-off statement was added. Read every private helper: the relative tensor argument uses the actual coequalizer construction, and the derived argument uses a K-flat representative inside a proof, without defining data from an arbitrary existential witness. The tensor caches use the existing monoidal structure and inferred proofs; they contain no hollow data. **Verdict: pass.**

4. **Route and pruning.** The proof follows the compactification route: open-immersion projection comparison, proper projection naturality, and compactification pullback. The added import is used for the K-flat tensor localization comparison; no original import or proof dependency is unused. **Verdict: pass; no pruning required.**

5. **DAG and unit agreement.** Searched the DAG for the exact module and declaration names: the source snapshot has no node attached to this module, and no new nodes were created. Existing unit declarations and the target statements are untouched; the proof uses the route described by the module. **Verdict: pass.**

**Changes made during second reading:** no Lean proof changes were necessary. Added this review section only. A separate header comparison checked all 17 original declarations in ProjectionFormula and all four in Derived.Tensor byte for byte, with no mismatches. All eight other sandbox Lean sources match the shared versions byte for byte. Searched the related library projection and module-object files for shorter routes; the existing abelian-sheaf formula does not supply the relative-module-tensor comparison. The delivery remains the compiled sandbox contents described above.

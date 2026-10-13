## What changed

Proved `ModuleCat.baseDerivedExtension_coherent_triangle_distinguished` in
`Sheaf.Algebra.Homology.BaseDerivedExtensionCoherentTriangle`, with its signature,
visibility, and existing public imports unchanged. Added only proof imports:
Mathlib derived-category exact-functor and K-projective APIs, and the existing
LargeFilteredFreeResolution, FilteredFreeKProjective,
QuasiIsoSaturatedTriangulated, ResolvingClassEssentialConstancy, and
LeftDerivedKanSourceTriangles modules. Updated the existing node's proof,
proof_deps, and proof_origin to describe the compiled route.

K-projective resolutions give a resolving class on which ordinary homotopy
extension followed by localization inverts quasi-isomorphisms. Essential
constancy and the existing Kan-extension source-triangle theorem prove
triangulatedness for the supplied shift and counit, directly. Exact restriction
of scalars then preserves the given distinguished derived image of T. The
shift-compatible factorization and triangle-composition isomorphisms identify
that image with the required composite, including its third arrow.

The original unit record `sk-thm-picard-semicon` has empty realization lists;
no unit statement or realized proof step is bypassed. The proof imposes no
boundedness, flatness, or nonzero-ring condition, and preserves the separately
chosen derived-category morphism universes.

## Proved and sorry left

Closed 1 hole:
`ModuleCat.baseDerivedExtension_coherent_triangle_distinguished`
(node `lem-pc-base-derived-extension-coherent-triangle`).

No sorry remains in the delivered module. Added 0 holes and split off 0 new
statements. Existing dependency theorems are used as permitted by stage 3;
this report does not claim that their entire transitive proof closure is closed.

## No longer needed

No original public import was removed: those imports supply the existing public
statement API. Every added proof import is used.

The planned direct dependency `lem-pc-base-derived-extension-resolution`, module
`Sheaf.Algebra.Homology.BaseDerivedExtensionResolution`, is no longer needed by
this proof and has been removed from its proof_deps. Its K-projective resolution
ingredients are used directly. The proof also does not need its assembly/shift
transport route through `lem-pur-left-derived-from-kflat-class`
(`Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`),
`lem-pur-left-derived-exact-chosen-localization`
(`Sheaf.CategoryTheory.DerivedCategory.LeftDerivedExactOfLocalization`),
`lem-pur-left-derived-exact-when-defined`
(`Sheaf.CategoryTheory.LeftDerivedExactWhenDefined`), or
`lem-pur-right-kan-extension-coherent-shift`
(`Sheaf.CategoryTheory.RightKanExtensionCoherentShift`). These are route-local
pruning claims; other target branches may still need those modules.

## Where the brief, the DAG or earlier work was wrong

The original plan says the shift supplied by the resolution existence theorem
can be identified with the given shift by counit compatibility. Its Lean
conclusion supplies triangulatedness for an existential shift but does not
supply counit compatibility for that shift. Also, that existence theorem uses
a common derived morphism universe for D(R) and D(B), whereas this item's
unchanged signature permits independent choices. No statement was changed.
The existing source-triangle Kan theorem applies to the supplied shift and
counit, and the direct K-projective resolving-class construction avoids both
gaps.

Lean compilation succeeded. The delivery dry run is the final verification;
the second reader will add their own section and deliver.

## Second reading by Y3

1. **Interface unchanged.** Compared the delivered Lean module with the
repository version. The theorem statement and all existing declarations are
byte-for-byte unchanged; only proof-only imports and the theorem proof differ.
Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py` and checked
`#print axioms ModuleCat.baseDerivedExtension_coherent_triangle_distinguished`.
Compilation succeeds with no errors or warnings, no `sorry` remains, and the
axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`; no forbidden
declarations or hollow definitions were introduced. Verdict: pass.

3. **Statements and split-offs.** No new theorem or split-off statement was
added. The existing target is proved at its unchanged strength, and the proof
uses the supplied derived functor, counit, and shift structures without adding
hypotheses. Verdict: pass.

4. **Shortest route and pruning.** The proof directly constructs the
K-projective resolving class, applies the existing saturated-localization,
essential-constancy, and Kan-source-triangle results, then uses exact
restriction of scalars and triangle isomorphisms. The node removes the unused
resolution and alternate transport route dependencies listed above; every
remaining proof import is used. Verdict: pass.

5. **DAG and unit agreement.** The node's proof steps, `proof_deps`, and
`proof_origin` describe the compiled proof. The unit record
`sk-thm-picard-semicon` has empty `realized` lists, so no unit route is
bypassed. Verdict: pass.

No code or DAG repair was needed during second reading; only this report section
was added.

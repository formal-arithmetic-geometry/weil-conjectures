## What changed

Proved `CategoryTheory.Functor.leftDerived_inverts` in
`Sheaf.CategoryTheory.DerivedFunctorInverts`, without changing its statement or visibility.
Four private, fully proved helpers construct cofiltered denominator categories, their
postcomposition functor, its initiality, and the limit property of a supplied essentially
constant cone. Definedness follows from the existing
`CategoryTheory.initial_iff_essentiallyConstantProDiagram`. The comparison is the hom of
the canonical isomorphism between the two limit cones over `S/X`; cone naturality gives
all denominator-square equations, and functoriality gives the outer rectangle.

Replaced the public import of `Sheaf.CategoryTheory.LeftDerivedValueMorphism` with the
public import of `Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem`, which
is the interface actually needed by the unchanged statement. Replaced the redundant private
import of the latter with the proof-only import
`Sheaf.CategoryTheory.DerivedCategory.EssentiallyConstantCofinal`. The only direct importer,
`Sheaf.CategoryTheory.LeftDerivedExactWhenDefined`, already imports
`Sheaf.CategoryTheory.LeftDerivedValueMorphism` independently; no adaptation is needed.
Updated the item's DAG proof, proof dependencies and proof origin to this route.
Public-import change record: `coord/changes/derived-functor-inverts-imports.md`.
The unit `sk-def-sf-operations` has no realized statement or proof steps, so no unit route
is bypassed.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.Functor.leftDerived_inverts`
(node `lem-pur-derived-functor-inverts-05sb`). Added zero holes; split off zero statements.
No `sorry` remains in the delivered Lean module. The existing imported theorem
`CategoryTheory.initial_iff_essentiallyConstantProDiagram`
(node `lem-pur-essential-constant-cofinal-0a1s`) remains an upstream proof obligation;
this delivery does not modify it. The four private helpers are fully proved.

The complete file compiles through the prescribed `lcompile.py` without warnings.
The right-calculus proof handles the identity denominator and imposes no extra
nonemptiness or smallness assumptions. It also works for the zero category and when
`s` is an identity. Cone uniqueness makes no assumption that the cone legs or `F(s)`
are isomorphisms.

## No longer needed

Removed import: `Sheaf.CategoryTheory.LeftDerivedValueMorphism`.
Pruned from this item's proof dependencies:
`lem-pur-derived-functor-morphisms-05sa` /
`Sheaf.CategoryTheory.LeftDerivedValueMorphism` /
`CategoryTheory.Functor.leftDerived_value_morphism`.
Its pointwise-Kan bridge and right-localization Hom-colimit route are consequently
not needed for this item's proof. These modules remain independently imported elsewhere,
so this is pruning of this item's route, not a claim of global unreachability.
The redundant private import of
`Sheaf.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem` is replaced by its
necessary public import. No new module is introduced.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement was found. The plan's second step constructs an inverse by
fraction comparisons and 05SA uniqueness; an explicitly proved limit property and
Mathlib's uniqueness of limit cones give the entire isomorphism more directly.
The first step's previously unstated appeal to initial restriction is supplied by the
existing `lem-pur-essential-constant-cofinal-0a1s` declaration. Its initiality hypotheses
are proved here from MS2 and MS3, not assumed. Searches used LeanFinder, Loogle and grep;
LeanFinder found Mathlib's initiality criterion, Loogle returned no exact match, and
repository/Mathlib searches found the existing essential-constancy restriction theorem.

## Second reading by W3

1. Interface preservation: compared the entire delivered module with the repository
   using `diff -u`, and programmatically compared the text from
   `theorem leftDerived_inverts` through its final conclusion before `:= by`.
   The existing signature is byte for byte identical, and its visibility and
   docstring are unchanged. No existing definition is edited. The only public
   interface change is the import replacement declared in
   `coord/changes/derived-functor-inverts-imports.md`. Repository-wide import search
   confirms that the sole direct importer, `LeftDerivedExactWhenDefined`, already
   imports `LeftDerivedValueMorphism` independently. Verdict: pass.
2. Proof and trust: independently compiled the delivered file with `lcompile.py`
   without errors or warnings. A scratch copy printing axioms of all five
   declarations shows only `propext`, `Classical.choice`, and `Quot.sound` for
   the four private helpers. `leftDerived_inverts` additionally uses `sorryAx`
   through the explicitly reported upstream theorem
   `initial_iff_essentiallyConstantProDiagram`. Thus the local hole is closed,
   but this is not yet an axiom-free proof of the target's import closure.
   No new hole, forbidden declaration, or hollow definition occurs. The sole
   new definition constructs postcomposition directly; it selects no object
   from an unproved existence statement. Verdict: pass with that upstream
   obligation recorded.
3. Split statements: none were added. Read all helper proofs: identity gives a
   denominator even for the identity-only system; right MS2 gives common sources;
   right MS3 equalizes maps without requiring them to lie in S. For the cone
   helper, naturality along the two common-stage arrows proves the lift equation,
   and the retraction at the distinguished index proves uniqueness. Its existential
   hypothesis already rules out an empty index category. Identity s, the zero
   category, and noninvertible individual cone legs cause no exceptional case.
   No helper restates the item or conceals an assumption. Verdict: pass.
4. Route and pruning: checked Mathlib's fraction-calculus and morphism-property
   comma files, its `initial_of_exists_of_isCofiltered` criterion, and the library's
   essential-constancy modules using alternate searches for cofiltered over
   categories, postcomposition, and essential-constancy limit properties.
   Found no shorter existing proof of the whole statement. Mathlib's initiality
   criterion is already used. The proof-only essential-constancy import is needed
   for the iff; the public definitions import is needed for the signature.
   Both supplied cones are proved limiting, initial restriction preserves the
   second limit, and limit uniqueness supplies the iso. Naturality for
   `c(a) → b` gives the first comparison equation; functoriality gives the outer
   rectangle. The removed 05SA proof dependency is the complete old dependency
   not used now and is listed under No longer needed. The unit record has empty
   realized statement and steps; no prescribed unit step is bypassed. Verdict: pass.
5. DAG agreement: compared the old and delivered JSON. Only `proof`, `proof_deps`,
   and `proof_origin` differ. Their two steps accurately describe the cofilteredness
   and initiality construction, the fixed-value equivalence, the explicit limit
   construction, and the naturality calculation. Dependencies are exactly the
   definitions node and the existing essential-constancy restriction node.
   There are no new nodes requiring additional fields. Verdict: pass.

Second reading changed only this report: added the independent review and explicit
axiom audit, including the remaining upstream `sorryAx` dependency. No Lean repair
or node correction was needed. Holes closed: `CategoryTheory.Functor.leftDerived_inverts`;
holes added: none. This is one local proof completed, with zero split-off statements.

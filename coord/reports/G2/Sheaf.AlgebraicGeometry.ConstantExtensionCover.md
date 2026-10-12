## What changed

Replaced the sole sorry in Sheaf.AlgebraicGeometry.ConstantExtensionCover by a complete Lean proof. Added proof-only imports of WeilConjectures.ConstructibleSheaf.Pullback, WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver, and Sheaf.AlgebraicGeometry.ConstantExtensionCokernelPresentation. Existing public imports and the original theorem signature are unchanged.

The proved private helper exists_constantCokernel_cover applies the existing constant-morphism local theorem to a map with finitely generated constant source. A point-indexed cover is selected from its covering sieve. Every selected member contains a point, so the empty sieve cannot cover it. Sheaf.isConstant_cokernel_over then gives constant cokernels. The over-site comparison, the cokernel presentation isomorphism, and Etale.upperStarComp transport this result to the middle term. Finally Cover.bind composes the covers.

Both modules compile locally without warnings. The source was read online at Stacks Tag 093U, Lemma 18.43.5, because the literature source files are absent on this machine. The module docstring records the complete finite-presentation argument. No library or target signature changed; no axiom was added.

## Proved and sorry left

AlgebraicGeometry.Scheme.exists_constantExtension_cover: its one original sorry is removed. The cover and local cokernel refinement helpers are fully proved.

The only sorry added is AlgebraicGeometry.Scheme.exists_constantExtension_cokernelPresentation, in Sheaf.AlgebraicGeometry.ConstantExtensionCokernelPresentation, node lem-pc-constant-extension-cokernel-presentation. This is the finite-presentation/pushout part of the source argument. Its conclusion is a cokernel presentation, with an arbitrary sheaf morphism, and does not assert local constancy. The separate refinement from that presentation to local constancy is proved in the item.

Edge cases: an empty scheme admits an empty cover; selected sieve members in the refinement are nonempty because their images contain the selected point. Zero modules and the zero ring cause no problem. Neither the new statement nor the proof requires a splitting of the original extension, commutativity of Λ, or connectedness of X. For noncommutative finite Λ, the finite free left module and its submodule K are finite sets, and hence finitely generated left modules.

## No longer needed

No existing import is removed. No planned node is globally pruned: lem-constructible-constant-exact, lemma-constructible-flc-biproduct, lem-constructible-shortexact-local-lift, def-constructible-finite, and def-constructible-constant move below the new presentation node. The item's direct proof dependencies are now just that presentation node and lemma-constructible-hom-constant-locally.

WeilConjectures.ConstructibleSheaf.KernelCokernel cannot be imported because it imports this item. Its fully proved constant-cokernel argument was adapted using the underlying constant-morphism module directly, avoiding an import cycle. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original parent plan already notes that exists_etale_local_lift_of_shortExact has a CommRing / SheafOfModules specialization, whereas this item uses Ring / fixed-coefficient ModuleCat sheaves. That mismatch remains part of the new presentation item; the present delivery does not incorrectly apply that theorem. The exactness and biproduct statements were read and assigned to the presentation node, where they are needed.

Delivery tool failure: the first deliver3.py --no-push run required a nonempty second-reading section at server preflight. This worker's explicit brief says that section belongs to the second reader and must not be written here. The section is therefore omitted. No tool or validation check has been modified or bypassed. The signature metadata error reported by that same run has been repaired.

## New nodes

lem-pc-constant-extension-cokernel-presentation / Sheaf.AlgebraicGeometry.ConstantExtensionCokernelPresentation: the first three steps of the parent plan, ending at the cokernel description of the extension. Its statement distinguishes an arbitrary morphism between constant sheaves from a morphism induced by a module map. The source is Stacks Tag 093U, extension pushout diagram; the proof is written in full in the Lean docstring and as three DAG steps. LeanSearch was unavailable; LeanFinder and grep returned quasicoherent or algebraic presentations but no theorem of this form. The blueprint search returned no matching cokernel-presentation node. The node inherits the parent's proper-base-change chapter and unit. No change record is needed because no existing statement or definition changes.

## Second reading by G2

1. PASS: compared the entire existing module with the repository using diff. The original
   theorem signature and docstring are byte-for-byte unchanged; its public imports are
   unchanged. Only proof bodies, private proof helpers, and three proof-only imports are
   added. The other Lean module is new. No existing definition or target statement changes,
   so no change record is required.
2. PASS: compiled both delivered modules in import order with lcompile.py, without warnings.
   Searched all delivered Lean text for sorry and forbidden declarations/attributes. Exactly
   one sorry remains, the named presentation theorem listed above; there are no hollow
   definitions or forbidden constructs. Scratch copies with #print axioms confirmed that
   presentationCover and exists_constantCokernel_cover depend only on propext,
   Classical.choice, and Quot.sound. The presentation theorem and the item additionally use
   sorryAx. Thus the item's proof body is complete, but its axiom-free closure still waits
   for the split presentation theorem.
3. PASS: read the new statement and its complete docstring argument against Stacks Tag 093U
   (https://stacks.math.columbia.edu/tag/093U), and checked its DAG node. This is the finite
   presentation/local-lift/pushout portion of the argument, not a renamed local-constancy
   conclusion. Its arbitrary sheaf morphism need not be globally a constant module map;
   the proved refinement is needed. A finite free left module over a finite noncommutative
   ring and its kernel are finite, hence finitely generated. The zero ring, zero outer
   modules, identity quotient, and empty scheme cases introduce no exceptions. Repeated
   LeanFinder and Mathlib grep searches with pushout/epimorphism/presentation terminology,
   and searched the project and upstream FreeLifting declarations. The search hits concern
   a different SheafOfModules encoding or constituent lifting facts, not this presentation
   statement. Closing the remaining theorem requires the substantive local-lift and
   pushout formalization, not a short application of an existing declaration.
4. PASS: checked the cover refinement from the top downward. The point-indexed sieve cover
   selects nonempty members (each selected member has a point over its index), correctly
   enabling the constant-morphism lemma. The cokernel isomorphism, over-site comparison,
   upperStarComp, and Cover.bind give precisely the requested composite cover. All added
   imports supply declarations actually used by the proof. The No longer needed section
   lists all five old direct dependencies displaced by the presentation node; they remain
   below that node, so none is globally pruned. Inspected sk-thm-properbasechange.realized:
   neither this item nor its new helper replaces a unit statement or a realized unit step.
5. PASS: compared the original and delivered parent nodes: statement and statement
   dependencies stay unchanged, while proof, proof_deps and proof_origin now describe the
   actual two-step reduction. The new node has the required source, full proof steps,
   dependency union, search records, creation/blueprint/unit/chapter fields and matching
   Lean module, declaration and signature. The acknowledged CommRing/SheafOfModules
   local-lift mismatch is a remaining obligation inside the presentation argument; the
   delivered Lean proof never applies that incompatible declaration.

Second-reading changes: appended this independent review and clarified that removing the
item's original sorry does not yet remove sorryAx from its transitive proof. No Lean proof,
statement, import, or DAG repair was necessary.

## What changed

The original signature of `AlgebraicGeometry.grothendieckExistence_supported_system`
is unchanged. This repair restores the delivered proof against the dependency interfaces present
after the batch rollback and adds the missing annihilation import. Its proof now obtains a supported formal object, applies proper
Grothendieck existence on the given closed subscheme, algebraizes by closed
pushforward, proves proper support using the existing support characterization,
and recovers the compatible thickening isomorphisms.

Added two modules:
- `Sheaf.AlgebraicGeometry.ClosedSupportedFormalAlgebraization`: proved categorical
  transport of essential surjectivity using `closedImmersion_coherentFormal_equivalence`,
  its natural completion comparison, finite pushforward coherence, and the equivalence
  counit. The explicit composite of these isomorphisms is written in Lean.
- `Sheaf.AlgebraicGeometry.SupportedThickeningDictionary`: the remaining transport
  of sectionwise annihilation and completion isomorphisms through the dictionary.
  It assumes no adic completeness, separatedness, or properness. It provides no
  algebraization: its conclusion about restrictions requires a completion isomorphism.

The main proof directly uses proper existence and the support characterization. All
three modules compile using `lcompile.py --all`, without warnings. The dry run passes
its preflight, with the second reading correctly left to the second reader. No definitions,
existing statement signatures, or other groups' modules were changed.

## Proved and sorry left

Closed the item's sole hole:
`AlgebraicGeometry.grothendieckExistence_supported_system`
(node `lem-weil-pbc-grothendieck-existence-supported-system`).

New theorem proved with no local hole:
`AlgebraicGeometry.closedSupported_formal_algebraization`
(node `lem-weil-pbc-closed-supported-formal-algebraization`). This proof uses the
existing, still-holed closed-immersion equivalence as intended by stage 3.

One new hole remains:
`AlgebraicGeometry.supportedThickening_dictionary`
(node `lem-weil-pbc-supported-thickening-dictionary`). Its exact proof is `by sorry`;
its docstring and node give the complete transport argument. No holes remain in the
item's module. This delivery is a decomposition: one upper hole closed and one lower
hole added, not a claim that Grothendieck existence is axiom-free. Existing dependency
holes are unchanged.

## No longer needed

Removed direct proof imports from the item:
`Sheaf.AlgebraicGeometry.ThickeningSystemsDictionary`,
`Sheaf.AlgebraicGeometry.ClosedImmersionCoherentEquivalence`,
`Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties`, and
`Sheaf.AlgebraicGeometry.CoherentFormalModule`.
The first two are now reached through the two new helper modules. Formal-module
and closed-proper-subset definitions/properties remain available through existing
imports. None is claimed to leave the targets' transitive import closure.

The original explicit support-image calculation using
`closedImmersion_coherent_support` is unnecessary: the proper-support characterization
applies directly to the actual pushforward, using sectionwise annihilation and a
reflexive pushforward isomorphism. Its module remains needed for the formal equivalence.
No whole module is pruned from the closure. The unit route is unchanged.

For completeness, the old node's proof dependencies removed from its direct route are
`def-weil-pbc-coherent-formal-module`,
`lem-weil-pbc-thickening-systems-dictionary`,
`lem-weil-pbc-closed-immersion-coherent-equivalence`, and
`lem-weil-pbc-closed-subset-proper-over-base-properties`.
The formal-module definition and the first two lemmas remain used through the helper
modules. The closed-proper-subset lemma is no longer applied in this proof, although
its module remains transitively imported. The two old dependencies retained directly
are `prop-weil-pbc-grothendieck-existence-proper` and
`lem-weil-pbc-module-support-proper-over-base`.
The repair adds the direct import `Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated`
because the current dependency graph no longer exposes that theorem through the importer path.

## Forced adaptations

The returned build failed at line 122 with `Unknown constant
AlgebraicGeometry.Scheme.Modules.closedImmersion_pushforward_annihilated` after the
batch rollback changed the dependency imports. The proof line using this theorem is
required for the support characterization, so the importer now explicitly imports
`Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated`. The rollback also
removed the two helper modules used by the delivered proof; this repair restores them
in the sandbox and restores the corresponding plain imports. Their declarations and
all existing signatures are unchanged. These are forced lines only; no unrelated
module was edited.

## Where the brief, the DAG or earlier work was wrong

No mathematical error established. The existing dictionary's Lean signature packages
many comparisons in existential data, rather than exposing the particular supported
object and extraction operation used here. The new holed statement isolates that
specialization, including the identification of the kernel-comap ideal and normalization to the comparison
chosen by `hc`; the second reading repairs the original normalization argument.

Edge cases checked: I = 0 gives the ordinary coherent system dictionary; I = top gives
zero thickenings/formal terms. The identity closed immersion imposes no annihilation
restriction; an empty closed subscheme forces the pushed terms to vanish. Nilpotent
closed subschemes retain scheme-theoretic annihilation, not just topological support.
The formal algebraization helper has no properness assertion, and assumes exactly
completion equivalence on Z; properness is used separately in the main theorem.

## New nodes

`lem-weil-pbc-supported-thickening-dictionary` records the remaining annihilation and
isomorphism transport, in `Sheaf.AlgebraicGeometry.SupportedThickeningDictionary`.
It is strictly a dictionary step and never constructs an algebraization.

`lem-weil-pbc-closed-supported-formal-algebraization` records the proved transport
of completion essential surjectivity, in
`Sheaf.AlgebraicGeometry.ClosedSupportedFormalAlgebraization`. It works for any ideal
on any Noetherian scheme and assumes completion equivalence on the closed subscheme.

Updated the original node's proof, proof dependencies, and proof origin to follow the
Lean proof. No change record is required because all existing signatures are unchanged.

## Earlier second reading (a previous round; superseded)

1. **Unchanged interfaces: pass.** Diffed the delivered item against the repository:
   only its proof and plain imports changed. Its entire existing theorem signature,
   public imports, and original declaration docstring are byte-for-byte unchanged.
   The other two modules are new, and no definition or other group's module is edited.
   No change record is required.
2. **Proof and trust: pass with the declared dictionary hole.** Compiled all three
   files in dependency order using lcompile.py; checked explicit #print axioms for
   grothendieckExistence_supported_system, closedSupported_formal_algebraization,
   and supportedThickening_dictionary. Only propext, Classical.choice, Quot.sound,
   and sorryAx occur. The only local sorry is the named dictionary theorem, exactly
   by sorry. No axioms, unsafe/opaque declarations, implementation overrides, or
   definitions with holes occur. G and N are local choices within an existential
   proof; no public data definition selects an arbitrary unproved witness.
3. **New statements: pass after a written-proof repair.** Read Stacks Tags
   [088E](https://stacks.math.columbia.edu/tag/088E) (first proof paragraph),
   [088F](https://stacks.math.columbia.edu/tag/088F), and
   [087T](https://stacks.math.columbia.edu/tag/087T), together with the complete
   existing thickening dictionary and formal closed-immersion equivalence signatures.
   The closed-supported helper assumes completion equivalence, obtains only the
   coherent pushforward and its completion isomorphism, and imposes no unsupported
   properness conclusion. The holed dictionary omits completeness, separatedness,
   and properness legitimately: it only constructs a formal object and extracts
   restrictions conditional on an existing completion isomorphism. It is strictly
   a part of algebraization, not a renamed existence theorem. Checked I=0 (constant
   thickenings), I=top (zero terms), identity and empty closed immersions, and
   nonreduced Z (annihilation by its actual kernel, including nilpotents).
   Independent searches used LeanFinder for equivalence of modules on infinitesimal
   neighborhoods with adic systems, Loogle for CategoryTheory.Functor.EssSurj,
   Mathlib grep for formalModule|CoherentThickening|SupportedOn, and rg across both
   source roots and upstream. No existing theorem closes the transport statement.
   Loogle finds objPreimage and objObjPreimageIso, already used by the proved helper.
   The first written proof incorrectly relied on uniqueness alone to identify
   separately chosen pullback comparisons. Replaced this with transition normalization:
   compare the dictionary's d with c, induce their difference on thickening modules
   using the invertible closed-immersion counit, modify φ by its inverse, and use
   naturality to recover the original compatibility equation. Added the supporting
   fully faithful pushforward import and DAG dependency. Stalkwise annihilation is
   now explained by representatives on a common open and the product stalk formula.
   This categorical transport is not a few-minute Lean closure; its hole is retained.
4. **Route and pruning: pass.** Traced the main proof: dictionary, proper completion
   equivalence on Z (comap_comp), supported algebraization, proper support via the
   annihilating closed pushforward, and recovery of ψ. Traced θ, pushforward of the
   completion isomorphism, β inverse, and the equivalence counit in the proved helper.
   The shorter support characterization correctly replaces the explicit support-image
   calculation. Removed the redundant annihilation import; all proof-only imports
   are plain. Completed the old proof_deps accounting above. Read sk-thm-p1.json:
   no node removed here realizes a unit statement or step; its realized route stays.
   No module is claimed pruned from the target closure.
5. **DAG agreement: pass after repair.** Read all three delivered nodes. The item's
   proof steps follow the actual Lean applications, with their union as proof_deps.
   The new algebraization node records the explicit categorical composite. The new
   dictionary node records exactly the residual formal-object and isomorphism
   transport, now including the closed-pushforward counit used in normalization.
   Both new nodes have source, full signatures, searches, created/blueprint/unit
   records. Marked the recorded failed LeanSearch as unavailable. Added the missing
   blueprint references to the two new module docstrings.

Second reading changed the dictionary's natural-language proof and matching node step
and dependency, added its fully faithful pushforward proof import, removed the item's
redundant annihilation import, completed pruning documentation, and repaired module
blueprint/search metadata. No statement or Lean proof term changed. One original hole
is closed, one new hole is added: this remains a decomposition with net zero holes,
not an axiom-free proof of Grothendieck existence.

## Second reading by H3

1. **Interfaces: pass.** Compared every delivered module with the current repository.
   GrothendieckExistenceSupportedSystem is the sole existing module; its theorem
   signature was compared as raw text through `:= by` and is byte-for-byte identical.
   All original public imports and definitions are unchanged. The other two modules
   are new relative to this checkout. There are no statement changes or change records.
2. **Proof and axioms: pass with the declared residual hole.** Compiled all three
   modules in import order through lcompile.py. A scratch module printed axioms for
   grothendieckExistence_supported_system, closedSupported_formal_algebraization,
   and supportedThickening_dictionary: only propext, Classical.choice, Quot.sound,
   and sorryAx occur. Exactly one local hole remains, the public named theorem
   supportedThickening_dictionary, with proof `by sorry`; no definition has a hole.
   No axiom, unsafe, opaque, implemented_by or extern declaration occurs. Existential
   choices of N and G occur inside theorem proofs, never as arbitrary public data.
3. **New statements: pass after expanding the written argument.** Independently read
   [Stacks 088E](https://stacks.math.columbia.edu/tag/088E), first proof paragraph,
   [088F](https://stacks.math.columbia.edu/tag/088F), and
   [087T](https://stacks.math.columbia.edu/tag/087T). Read the complete existing
   thickeningSystems_dictionary and closedImmersion_coherentFormal_equivalence
   interfaces. The dictionary helper needs no completion or properness hypothesis:
   it constructs the formal system and extracts restrictions only conditional on
   an existing completion isomorphism. The algebraization helper assumes the
   completion equivalence on Z and concludes coherence and a completion isomorphism;
   proper support is established separately in the item. Neither is a restatement
   of the item. Checked I=0 (constant thickenings), I=top (zero thickenings), identity
   and empty closed immersions, zero terms, and nonreduced Z (its actual ideal must
   annihilate the terms). Independently searched LeanFinder for coherent modules on
   infinitesimal neighborhoods versus inverse quotient systems, Loogle for
   Functor.objObjPreimageIso, Mathlib grep for CoherentThickening/IsCoherentFormalModule/
   SupportedOn, and both library roots for formal equivalences and dictionaries.
   LeanFinder returned local-cohomology and Hausdorffification results; Loogle found
   the essential-image isomorphism already used. No existing result closes the hole.
   Read ThickeningCompletionHomDictionary too: its Hom comparison cannot construct
   the arbitrary supported formal object required here. Closing the full residual
   categorical dictionary is not a few-minute proof.
   Expanded normalization explicitly: with t=d.inv followed by c.hom, its component
   on a thickening module H is ε_H.inv followed by t_(j_n,*H) followed by ε_H.hom.
   Naturality against the unit and the triangle identity identify the induced
   component on j_n^*G with t_G. Hence ψ followed by t_H equals t_G followed by ψ.
   For φ'=φ followed by t_H.inv, the d-compatibility equation implies precisely
   the original c-compatibility equation. No arbitrary comparisons are equated.
4. **Route and pruning: pass.** Traced the supported dictionary, comap_comp and proper
   existence on Z, the explicit θ/pushforward/β inverse/counit composite, finite
   pushforward coherence, the proper-support characterization with GZ and Iso.refl,
   and the final dictionary extraction. Proof-only imports are plain. Restored the
   direct annihilation import: the current compiler happens to find the theorem
   transitively, but the returned build and the declared proof dependency require
   the direct import. No other import was added or removed in this reading. The
   old proof_deps omitted from the direct route are all listed under No longer
   needed; formal-module, dictionary and closed-equivalence dependencies survive
   through helpers. ClosedSubsetProperOverBaseProperties is not directly applied.
   Read dag/units/sk-thm-p1.json: none of these omitted nodes is a realized unit
   statement or step, and the realized route is unchanged. No whole module is pruned.
5. **DAG: pass after matching the expanded explanation.** Checked each delivered
   node's signature against its actual Lean statement and its proof_deps against
   the union of step uses. The main node records coherence, annihilation and proper
   support applications explicitly. The algebraization node records the categorical
   composite actually written. The residual dictionary node has source, searches,
   created, blueprint, chapter/unit and complete Lean fields, and now explicitly
   records the counit formula and unit/triangle argument from its docstring.
   Existing node statements and statement dependencies were not changed.

This second reading restored the direct plain annihilation import and expanded the
remaining dictionary's docstring and matching DAG step. No statement or definition
changed. Closed hole: AlgebraicGeometry.grothendieckExistence_supported_system.
Added hole: AlgebraicGeometry.supportedThickening_dictionary. The additional theorem
AlgebraicGeometry.closedSupported_formal_algebraization has no local hole. This is
one upper hole replaced by one strictly smaller lower hole, a decomposition with net
zero holes, with no whole module pruned.

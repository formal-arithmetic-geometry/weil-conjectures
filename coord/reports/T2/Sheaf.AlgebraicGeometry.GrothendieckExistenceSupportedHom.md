## What changed

Proved the existing declaration `AlgebraicGeometry.grothendieckExistence_supported_hom`
without changing its signature, visibility, or definitions. Added two proved private helpers
in `Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedHom`:
`map_bijective_of_isos` and `supported_formalCompletionMap_bijective`.

The support reduction constructs `j^*G` and `j^*F`, proves their coherence, and uses the
annihilation theorem to obtain invertible units. It transfers the existing proper completion
bijection through fully faithful pushforward, termwise pushforward, and the natural completion
comparison. The main proof then composes that bijection with the formal Hom dictionary.
All added imports of the existing module are proof-only imports.

Added `Sheaf.AlgebraicGeometry.ThickeningCompletionHomDictionary` for the remaining dictionary
transport. Its theorem equates formal morphisms with compatible families and specifies the image
of a completed morphism. It neither assumes properness or completeness nor asserts algebraization.
The associated new node and the existing item's proof route are included in the sandbox.

## Proved and sorry left

Closed the one original hole in `AlgebraicGeometry.grothendieckExistence_supported_hom`
(node `lem-weil-pbc-grothendieck-existence-supported-hom`). No direct `sorry` remains in the item.
Both private helpers are proved, with no local holes. These proofs use the existing named
statements for proper completion, annihilation, closed pushforward, and its completion comparison.

Added one hole: `AlgebraicGeometry.thickeningSystems_completion_hom_equiv`, in
`Sheaf.AlgebraicGeometry.ThickeningCompletionHomDictionary`, node
`lem-weil-pbc-thickening-completion-hom-dictionary`. Its proof is exactly `:= by sorry`.
This is a decomposition: one upper hole closed and one strictly smaller formal-dictionary hole
added, net zero direct holes before accounting for newly reached dependencies. The proper-support
transport is complete Lean; only the general formal Hom/family identification remains.

Both files compiled together using `lcompile.py --all`. Existing upstream dependency holes
remain with their original named statements and nodes; none were modified in this delivery.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.ThickeningSystemsDictionary` from the
item and replaced it by `Sheaf.AlgebraicGeometry.ThickeningCompletionHomDictionary`, which still
imports and uses the original dictionary. Thus neither the original dictionary module nor its
node `lem-weil-pbc-thickening-systems-dictionary` is globally pruned.

The original direct proof dependency
`lem-weil-pbc-thickening-systems-dictionary` is no longer applied in the item's proof;
it is replaced there by `lem-weil-pbc-thickening-completion-hom-dictionary`. The old
node remains a dependency of the new node. All three other old `proof_deps` are
still used directly: `def-weil-pbc-coherent-formal-module`,
`lem-weil-pbc-closed-immersion-coherent-equivalence`, and
`lem-weil-pbc-formal-completion-fully-faithful-proper`.
No original dependency node or module is globally pruned. The closed-immersion coherent
module equivalence is not needed separately: its formal-completion comparison remains used
from the same `ClosedImmersionCoherentEquivalence` module. Its coherent support formula and
formal essential-surjectivity assertions are not used by the support reduction. No public import
was removed, and no blueprint unit statement or realized step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing plan is mathematically usable, but its bundled dictionary does not directly expose
an equivalence to the unbundled compatible-family subtype with the particular `c` supplied here.
The new statement isolates that missing transport rather than duplicating the supported Hom
conclusion. It applies without proper support, separatedness or adic completeness.

The support proof uses constructed pullbacks and invertible adjunction units instead of choosing
arbitrary coherent preimages from an unproved existence theorem. All witness extraction occurs
inside theorem proofs; no new definition chooses data from mere unproved existence.

Checked the new statement on I=0, I=top, empty schemes, and zero modules. In the I=top case the
formal systems and thickening modules are zero, while the original module Hom need not be zero:
this illustrates precisely why the new theorem does not assert algebraization. For I=0 both
sides are constant restriction systems. No case requires properness or completeness. The
comparison-independence argument uses fully faithful closed pushforward and adjunction triangles,
so arbitrary choices of natural comparison do not introduce an extra hypothesis.

The local clone lacks the untracked Stacks source and blueprint section files. Read the cited
source at https://stacks.math.columbia.edu/tag/088E,
https://stacks.math.columbia.edu/tag/0883, and https://stacks.math.columbia.edu/tag/088F;
read the unit's statement and every realized step from `dag/units/sk-thm-p1.json`.
Mathlib/source/project searches found no shorter supported-Hom theorem. LeanSearch was
unavailable; LeanFinder and Loogle responded, and the actual searches are recorded in
`searches.jsonl`. A full formalization of the dictionary transport is left as the new item.

## New nodes

`lem-weil-pbc-thickening-completion-hom-dictionary` records the formal Hom identification,
with the source Remark 088F and equation 0880, an expanded four-step proof, actual Mathlib
searches and a verbatim Lean signature. Its only geometric proof dependencies are the existing
thickening dictionary and fully faithful closed pushforward; it also names the completion and
pullback definitions. It is strictly the third step of the supported-Hom argument, before the
algebraization bijection. No statement/definition changes or forced adaptations are included,
so there is no change record.


## Second reading by T2

1. **Interfaces: pass.** Compared the two delivered modules with the repository.
   The only existing module changed is `GrothendieckExistenceSupportedHom`.
   Extracted its existing theorem signature up to `:=` and checked byte-for-byte
   equality, including `IsSeparated f`, both transition projection equations,
   the prescribed `hc`, coherence, properness of `j ≫ f`, and both sectionwise
   annihilation hypotheses. Its docstring and all six public imports are unchanged.
   There are no changed definitions, change records or adaptations. The two added
   helpers are private theorems; all added imports of this module are plain imports.
   The new dictionary module publicly imports only material its signature uses.

2. **Proofs and data: pass as a decomposition.** Compiled both files in import order
   with `lcompile.py --all`, without errors or warnings. The sole new local hole is
   the named public theorem `thickeningSystems_completion_hom_equiv`; its body is
   exactly `by sorry`. There is no definition or forbidden trust feature in either
   delivery. Scratch copies print axioms for the existing theorem, both private
   helpers and the new theorem: only the three standard axioms and `sorryAx` from
   the explicitly open statements occur. The map-conjugation helper uses only
   `propext`, `Classical.choice` and `Quot.sound`. In the geometric helper, FZ and GZ are actual tensor
   pullbacks, and annihilation makes their units invertible. The choice of an
   adjunction for fixed functors is determined up to its canonical adjunction
   isomorphism; no arbitrary coherent preimage is used to define data. The choices
   of a completion comparison and the dictionary equivalence stay inside proofs.
   The full-subcategory inclusion and pushforward are fully faithful; factoring
   their composite map proves both halves of the completion bijection. The final
   equivalence equation gives exactly the original restriction function.

3. **Split statement: pass.** Read the new node, its verbatim Lean signature, and
   its entire docstring proof against the actual interfaces of
   `thickeningSystems_dictionary` and `closedImmersion_pushforward_fullyFaithful`.
   Read [088E](https://stacks.math.columbia.edu/tag/088E), first proof paragraph,
   [0883](https://stacks.math.columbia.edu/tag/0883),
   [088F](https://stacks.math.columbia.edu/tag/088F), and
   [087T](https://stacks.math.columbia.edu/tag/087T).
   This is the morphism part of the dictionary, not another algebraization theorem:
   it removes completeness, separatedness, the proper support and annihilation
   assumptions, and equates formal arrows with families rather than lifting them
   to arrows on X. It is strictly a part of the argument.

   Checked the comparison-independence argument explicitly. For pullback L with
   fully faithful right adjoint R, write eta and epsilon for unit and counit.
   Given a natural automorphism alpha of L, set
   gamma(M) = epsilon(M)^(-1) ; alpha(R(M)) ; epsilon(M).
   This is a natural automorphism of the identity on the target category.
   The triangle identity says L(eta(F)) = epsilon(L(F))^(-1), so naturality of
   alpha along eta(F) gives gamma(L(F)) = alpha(F). Naturality of gamma at any
   v : L(G) -> L(F) gives alpha(G) ; v = v ; alpha(F). Apply this to the
   difference of the dictionary's c and the supplied c. Cancellation identifies
   the two family conditions. The dictionary's r transports compatible components
   in both directions, and its rho naturality identifies the image of completion
   of w with componentwise pullback of w. Thus no equality between arbitrary
   choices of comparison is assumed.

   For I=0, both sides are the Hom of constant systems with identity transitions;
   the centrality argument also covers a nontrivial natural comparison. For I=top,
   both formal systems and all restricted modules are zero, hence both sides are
   singleton, although Hom_X(G,F) need not be. Empty schemes and either zero module
   also give singleton Hom sets. None of these checks needs properness or adic
   completeness. Independent searches used the launcher LeanFinder query
   "Natural transformations between quotient inverse systems of coherent sheaves
   identified with compatible morphisms on closed subschemes", Loogle for
   `Functor.FullyFaithful` with `Iso.homCongr`, and grep for natural-transformation
   equivalences and whiskered Hom equivalences. They returned general limit,
   adjunction and whiskering tools, no matching geometric dictionary theorem.
   Searched both upstream and current WeilConjectures roots for completion and
   thickening declarations, and the existing Sheaf thickening/completion modules.
   The existing bundled dictionary is the needed source; no simpler replacement
   was found. Closing its unbundled transport is substantial formalization, not
   a few-minute application of an existing lemma; the one named hole remains.

4. **Route and pruning: pass.** The proof first finishes the proper-support
   reduction from the existing proper completion bijection, fully faithful closed
   pushforward, coherent finite-type criterion and annihilation theorem. Only the
   formal-family identification is split. All current direct proof imports supply
   declarations used either by these helpers or the final proof. The old direct
   dictionary import is replaced, but is still reached through the new dictionary
   module, so no module is globally pruned. The amended `No longer needed` section
   names the one old proof-dependency node no longer applied directly, and explicitly
   accounts for each of the other three. Read `dag/units/sk-thm-p1.json`, including
   its complete `realized` list: neither item is a realized unit statement or step;
   this reduction leaves the finite-etale lifting and unit route intact.

5. **Nodes: pass after a notation repair.** The original node changes only `proof`,
   `proof_deps` and `proof_origin`. Its steps correspond to constructing coherent
   pullbacks, full-faithfulness transport, endpoint conjugation and composition
   with the formal-family equivalence. Checked their cited Lean statements: each
   supplies precisely the part used, including the natural formal-completion
   comparison (not the unused essential-surjectivity clauses). The new node has
   the same chapter and unit, its source, four proof steps, their dependency union,
   the actual search records, split status, worker creation record, blueprint
   ancestry and verbatim multiline Lean statement. Its natural-language statement
   used plain Unicode instead of the contract's TeX notation; converted it to TeX
   with the same mathematical meaning, making the canonical comparison explicit.

Changes by this reading: repaired the new node's statement notation, completed the
old direct dependency accounting under `No longer needed`, and added this independent
review. No Lean declaration, proof, definition or import needed repair. One original
hole is closed and one strictly smaller hole is added: a decomposition with net zero
local holes, not a claim that the target's import closure is sorry-free.

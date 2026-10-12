## What changed

Proved `CategoryTheory.tor_dimension_shift_natural` with its original signature.
All changes are in `Sheaf.Algebra.TorDimensionShiftNatural` and its DAG node.
Private, fully proved helpers splice Mathlib's projective resolution of the kernel onto
its free presentation, verify the resulting projective resolution, and construct the
natural homology comparison. Mathlib's `isoLeftDerivedObj` and `leftDerived_app_eq`
transport the comparison to Tor. The theorem docstring and DAG now describe this route.

Searches: leanfinder for dimension shifting of left-derived functors found projective
vanishing and derived-category triangles, but no direct shift theorem; loogle for
`CategoryTheory.Functor.leftDerived` found the definition and resolution API; grep for
`leftDerived.*(exact|δ)|dimension.shift.*Tor` found no shift theorem. Reading Mathlib's
projective-resolution and short-complex APIs supplied the complete direct proof.

## Proved and sorry left

Closed the sole original hole: `CategoryTheory.tor_dimension_shift_natural`
(node `lem-sc-p1-tor-dimension-shift-natural`). Holes closed: 1. Holes added: 0.
There are no remaining `sorry`s in the delivered module and no new modules.
The local compile passed without warnings. A temporary `#print axioms` check reported
exactly `propext`, `Classical.choice`, and `Quot.sound`; the command was then removed.

The construction includes the boundary case i = 1 explicitly through n = 0: the
three compared terms are P₃,P₂,P₁ and Q₂,Q₁,Q₀. Exactness at P₁ uses injectivity of
the presentation map; exactness at P₀ uses the surjective resolution augmentation.
No nonzero-module assumption is used, so zero modules and the zero ring remain covered.

## No longer needed

Removed the proof-only import `Sheaf.Algebra.Homology.FreeResolutionSesSplit` and the
proof dependency `lem-weil-pbc-free-resolution-ses-split`. Mathlib supplies a projective
resolution directly, and Tor can be computed with projective resolutions.
All original public imports remain: they provide the theorem's Tor, module category,
monoidal structure, freeness/projectivity and short-exact-sequence interface.
No other planned node or module is pruned by this proof. This reports a dependency
removed from this item, not a claim that no other target branch uses that module.

## Where the brief, the DAG or earlier work was wrong

The original plan's use of a split compatible free-resolution theorem was unnecessary:
only one projective resolution of the kernel is needed. The splicing route and the unit's
route are preserved; the unit's `realized` lists are empty. No statement or definition
was changed. The cited Stacks source is absent from this clone's literature directory;
the same algebra.tex was read in the existing local Stacks checkout, at the proof of
`lemma-exact-sequence-NL` and the Tor section. No additional literature was needed.

## Second reading by V1

1. Compared the only delivered module with the repository version using `diff` and
   checked the existing theorem signature byte for byte: unchanged, including the
   commutative ring, arbitrary short exact sequence, free middle term, every degree
   i ≥ 1, all coefficient modules, and every coefficient morphism. There are no
   existing definitions changed, change records, or extra delivered modules.
   Read Stacks algebra.tex in /home/ubuntu/c1-stacks-review at section-tor,
   lemma-tor-welldefined, lemma-long-exact-sequence-tor, and the dimension-shift
   paragraph of lemma-exact-sequence-NL. The statement agrees with the cited shift
   and the explicit resolution argument supplies all positive degrees and naturality.

2. Compiled the whole module independently with lcompile.py: no errors or warnings.
   A scratch copy with `#print axioms CategoryTheory.tor_dimension_shift_natural`
   reported only propext, Classical.choice, Quot.sound. The source contains no sorry,
   axiom, unsafe, opaque, implemented_by or extern. All private constructions are
   explicit: spliceX, spliceD, the augmentation, and the tensor functor. The chosen
   projective resolution is Mathlib's proved construction, not an arbitrary witness
   extracted from an unproved existence theorem. Exactness at degree zero uses the
   epic resolution augmentation; exactness at degree one uses hS.mono_f. The
   quasi-isomorphism also uses hS.epi_g. Higher exactness is Q.exact_succ.

3. No statements were split off, no holes were added, and no new nodes are needed.
   Inspected all private helpers: they are fully proved parts of the argument.
   At i = 1 (n = 0), spliceScIso compares P₃ → P₂ → P₁ with Q₂ → Q₁ → Q₀;
   it never identifies the exceptional splice differential with Q's differential.
   Zero modules and the zero ring impose no additional hypothesis. The identity,
   zero and arbitrary coefficient maps all fall under the proved functor naturality.

4. Searched again with Loogle `CategoryTheory.Tor'`, read the pinned Mathlib Tor,
   ProjectiveResolution.isoLeftDerivedObj and leftDerived_app_eq APIs, and searched
   the local algebra modules for other dimension-shift statements. Loogle supplies
   projective vanishing but no natural dimension-shift theorem. The existing
   tor_dimension_shift_free is still sorry and supplies only pointwise isomorphisms,
   so it cannot shorten this naturality proof. The direct splice is appropriate.
   Every remaining public import supports the signature: Tor, ModuleCat monoidal
   and additive instances, Module.Free and enough projectives (hence the required
   HasProjectiveResolutions instance), ModuleCat.abelian, and ShortExact.
   No new proof-only import was made public. The removed FreeResolutionSesSplit
   import and its node are exactly the unused old proof dependency. Read
   dag/units/sk-thm-picard-duality.json: its realized statement and step lists are
   empty; no realized unit node or step is bypassed by this lower-level splice.

5. Compared the delivered DAG node with the original: only proof, proof_deps and
   proof_origin changed. The three retained dependencies are the Tor, exact-sequence
   and free-module definitions. The recorded four steps match spliceResolution,
   torResolutionIso, spliceScIso and spliceHomologyIso. In particular the Tor
   comparison is natural by leftDerived_app_eq, and the short-complex comparison
   is natural before applying homology; the final equation is e.hom.naturality.
   The proof_origin records the projective-resolution variant of the source route.

Verdict: passes all five checks. Second reading changed only this report by adding
this independent review; no Lean or DAG repair was needed. Closed one original
hole, added none, and retained the reported pruning of FreeResolutionSesSplit.

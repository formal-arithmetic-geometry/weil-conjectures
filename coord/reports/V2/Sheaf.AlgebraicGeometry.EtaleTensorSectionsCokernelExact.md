## What changed

Proved `AlgebraicGeometry.Scheme.Modules.etaleTensorSections_cokernel_exact` in
`Sheaf.AlgebraicGeometry.EtaleTensorSectionsCokernelExact`, without changing its signature,
visibility, original docstring, definitions, public imports, or file-level options.

The proof implements the stated route. Tensor pullback preserves the cokernel complex because
it is a left adjoint. The existing `RingedSpace.module_exactness_local_lifting` theorem supplies
Zariski local preimages on each etale object. Private, proved helpers construct the comparison
between tensor sections on a covering open and ordinary sections of the pulled-back module.
Naturality of the adjunction comparison and its unit equation show that these comparisons
respect both the module morphism and normalized etale restrictions. The resulting image sieve
contains the covering sieve of open immersions.

A private, proved generic helper converts this local lifting condition into an epimorphism onto
the presheaf kernel after sheafification. Its composite with the invertible kernel comparison
is the kernel lift of the sheafified sequence, proving exactness. A separate generic private
helper shows that ULift preserves the image sieve. Keeping that argument generic avoids the
expensive unfolding of the concrete tensor-section presheaves during elaboration.

Added only proof imports: `Mathlib.Algebra.Category.Grp.EpiMono`, `Mathlib.CategoryTheory.Adjunction.Additive`,
`Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting`, and
`Sheaf.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality`.
Updated the original node's `proof`, `proof_deps`, and `proof_origin` to describe the actual
argument and the existing open-section comparison definition it uses.

Validation: the complete file compiles cleanly through lcompile.py in about 14 seconds.
The declaration comparison reports no changed existing statement and no new sorry.
Both new Sheaf proof imports pass import_direction.py. Every Lean line is at most 100 characters.
The empty scheme/open, zero morphism, and zero modules require no extra assumption: the existing
local lifting theorem and the covering-sieve criterion already include them. No quasi-coherence,
flatness, affine hypothesis, or surjectivity of global sections is used.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.etaleTensorSections_cokernel_exact`
(node `lem-sc-etale-tensor-sections-cokernel-exact`).

No sorry remains in the item's module; no holes were added or split off. All private helpers
are proved. This is one proof, not a decomposition. Existing imported dependencies keep their
own previously recorded proof status; no dependency module was edited.

## No longer needed

No original import or original proof-dependency node was pruned. All three original dependencies
remain used, and `new-etale-tensor-open-section-iso` is added for the explicit comparison
`tensorOpenSectionIso`.

Removed redundant provisional imports before delivery:
`Mathlib.Algebra.Category.Grp.Abelian`, `Mathlib.CategoryTheory.Preadditive.LeftExact`, and
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels`. The final file compiles without them.
The second reader also removed the redundant proof import
`Mathlib.CategoryTheory.Sites.LocallyBijective`, verifying compilation without it.
These were not imports of the original item, so they do not count as pruning original modules.

The proof does not import the separate tensor-section local-surjectivity or right-exactness
modules, or directly import the sheafified sectionwise cokernel local-image module. It uses the
already proved local exactness criterion and Mathlib kernel comparison instead. None of these
was an original direct dependency of this item, and no global unreachability claim is made.

## Where the brief, the DAG or earlier work was wrong

No statement or mathematical error was found. The original node's single step left the
normalized restriction transport and sheafification glue implicit; both are now proved in
Lean. The unit is `sk-prop-h2`, whose realized statement/step lists do not designate this node;
the local-image proof route and all original dependencies are retained.

The advertised local literature text is not populated in this read-only clone. The Stacks
source pages for Tags 070S, 03FH, and 0096 were read directly. The module's source attribution
is kept, and the argument is the local module lifting and adjunction argument described by the
node, using existing library declarations rather than adding sourced holes.


## Second reading by V2

1. Interface preservation: PASS. Read the whole module and its diff against the repository.
   The sole existing theorem's signature and docstring are byte for byte unchanged;
   no existing declaration was removed or changed in visibility. Original public imports,
   options and definitions are unchanged. The declaration-comparison tool reports no
   statement changes, no removed declarations and no new sorry. There is no change record
   because this delivery changes only proofs, private helpers and proof imports.
2. Proof and trust: PASS. Independently compiled the file through lcompile.py with no
   errors or warnings. A scratch copy with `#print axioms
   AlgebraicGeometry.Scheme.Modules.etaleTensorSections_cokernel_exact` reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. No sorry or forbidden
   declaration occurs in the delivered module. The three private definitions explicitly
   construct the open object, its inclusion and the comparison isomorphism; none chooses
   data from an unproved mere-existence theorem. The adjunction comparison is determined
   by its unit, as required by the existing tensor-pullback construction.
3. Split statements: PASS, none. All new private helpers have complete checked proofs;
   no theorem is split off and no hole is added. Read the local exactness criterion and
   the open-section comparison definition used below the target. Empty schemes/opens,
   zero modules, zero morphisms and identity restrictions introduce no hidden hypothesis:
   covering sieves include the empty cover of the empty object, and the unit and inverse
   equations apply uniformly. The argument only lifts sections killed by the cokernel
   map locally; it never assumes surjectivity of global sections.
4. Route and pruning: PASS after import cleanup. Read the proof from the target through
   ULift, the local image sieve and the generic sheafified kernel-lift argument. Checked
   the naturality and unit equations and cancellation of tensorSectionsComp on each
   open immersion. Independent LeanFinder, Loogle and grep searches found the existing
   kernel-lift exactness criterion used here, but no direct theorem replacing this
   local-image argument. A similar coefficient-naturality helper elsewhere is private,
   and the public open-section naturality theorem does not cover an arbitrary etale U
   over X. All original proof dependencies remain used, so none is omitted from
   `No longer needed`. The unit sk-prop-h2 has empty realized lists and is unchanged;
   the delivery keeps the local-image route below that unit. Scratch removal tests
   show Grp.EpiMono and Adjunction.Additive are necessary, while Sites.LocallyBijective
   is redundant and has been removed. Both added Sheaf imports supply declarations
   used explicitly in the proof.
5. DAG agreement: PASS. Compared the node diff and checked its steps against the Lean
   helpers. Only proof, proof_deps and proof_origin changed. The proof-dependency list
   is exactly the union of the steps' node uses: the three original nodes plus
   new-etale-tensor-open-section-iso. Its recorded declaration is tensorOpenSectionIso,
   the explicit construction actually used. No new nodes or statements were added.

Second-reading changes: removed one redundant proof-only Mathlib import and updated this
report. The proof and DAG required no repair. One original hole is closed, zero holes
are added, zero statements are split off, and no original module is pruned.

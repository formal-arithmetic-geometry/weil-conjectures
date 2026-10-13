## What changed

Replaced the sole remaining hole in
`AlgebraicGeometry.principalCechAugmentation_quasiIso` with a cohomological reduction.
The proof instantiates explicit degree-coordinate presentations of the source and
Čech target, proves their differential and augmentation formulas from the existing
construction, and combines monicity and epicity of each homology map using the
abelian-category isomorphism criterion and `quasiIso_iff`.

Added proof-only imports of `Sheaf.AlgebraicGeometry.PrincipalOpenCechHomologyInjective`
and `Sheaf.AlgebraicGeometry.PrincipalOpenCechHomologySurjective`. Each new module
states one half of the finite augmented Čech staircase argument, with complete
coordinate hypotheses. These are separate injectivity and surjectivity assertions,
not another assertion that the augmentation is a quasi-isomorphism. No existing
signature, definition, visibility, or public import was changed.

Updated the construction node's proof route and added two matching statement nodes.
The unit `sk-thm-picard-duality` has empty realized statement/step lists here; no
unit-level statement or step is bypassed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.principalCechAugmentation_quasiIso`
(node `def-sc-principal-open-alternating-total`).

Added exactly two holes, both entire public named theorem proofs in new modules:

- `AlgebraicGeometry.principalOpenCech_homology_injective`
  (`lem-sc-principal-open-cech-homology-injective`): injectivity on cohomology.
- `AlgebraicGeometry.principalOpenCech_homology_surjective`
  (`lem-sc-principal-open-cech-homology-surjective`): surjectivity on cohomology.

No sorry remains in the original module. This delivery is a decomposition, not a
sorry-free proof of Čech acyclicity: one hole closed, two added, net minus one.
The original module checks all presentation hypotheses and genuinely combines the
two strictly weaker assertions. No data is selected from either new theorem.

Edge cases checked mathematically: r=0 gives sections on the empty open and a
product with no coordinates, hence both sides zero; r=1 gives the ordinary section
complex on D(f₀); empty or repeated principal opens are allowed; no boundedness,
quasi-coherence, or injectivity of individual terms of J is assumed. The K-injective
hypothesis is used by the resolution/homotopy argument in both remaining obligations.

## No longer needed

No original-module import was removed. In both new modules the second reader
replaced the broad RingedSpaceDerivedDirectImage and WeilConjectures right-derived
KInjective imports with the directly needed Sheaf.Paper.DerivedHomMayerVietoris
(defines moduleRings) and Mathlib.Algebra.Homology.DerivedCategory.KInjective.
No library module becomes unreachable from the targets. Otherwise none; the original node had no proof dependencies
to prune. The existing definitions and their coordinate specifications remain used.
The increasing-tuple comparison modules were examined for a shorter route but are
not imported by the original module: applying them directly would require a separate
comparison of open restriction, scalar action, total coordinates, and augmentation.
No pruning claim is made for those modules, since other target routes still use them.

## Where the brief, the DAG or earlier work was wrong

The current construction node already records all earlier algebraic steps as proved
and has empty proof_deps; its only remaining obligation is K-injective augmentation
acyclicity. The standing brief's description of many unproved planned dependency
modules therefore does not describe this particular item. Those existing proofs and
all existing statements have been preserved.

The local literature checkout contains the citation lists but not cohomology.tex.
The source actually read was https://stacks.math.columbia.edu/tag/08C1,
Lemma 20.40.1, proof, together with the existing finite-cover augmentation modules.
LeanSearch returned HTTP Internal Server Error; the searches record this as unavailable,
not as a negative mathematical result. LeanFinder and Mathlib grep found no exact
principal-open coordinate theorem. The whole blueprint search found no duplicate
of the two separate principal-open cohomology assertions.

## New nodes

`lem-sc-principal-open-cech-homology-injective` states that a closed section whose
image is a total boundary was a section boundary. Its source is Tag 08C1's finite
augmented-row argument; its complete proof in words includes the descending column
elimination, the last use of injectivity of row augmentation, and transport from an
injective-term resolution along homotopy equivalences. It is stated in
`lean/Sheaf/AlgebraicGeometry/PrincipalOpenCechHomologyInjective.lean`.

`lem-sc-principal-open-cech-homology-surjective` states that every total cohomology
class is represented by the augmentation of a closed section. Its source is the same
finite augmented-row argument; its proof in words kills positive Čech columns,
uses sheaf gluing at column zero, and transports across the K-injective comparison.
It is stated in `lean/Sheaf/AlgebraicGeometry/PrincipalOpenCechHomologySurjective.lean`.

Both statements specify the actual source, target, coefficient differential,
deletions, degree transports, signs, and augmentation through degree isomorphisms.
Neither concludes QuasiIso or repackages that conclusion. No change record is needed:
only proof bodies and proof-only imports of the existing module changed.

## Second reading by U1

1. Compared the original module with the repository using `diff -u`. The only
   changes are two plain, proof-only imports and the body of
   `AlgebraicGeometry.principalCechAugmentation_quasiIso`. Every existing signature,
   definition body, visibility and public import is byte-for-byte unchanged. Pass.
2. Compiled all three delivered modules through `lcompile.py --all`: exit code zero,
   with no errors or unexpected warnings. The only two remaining `sorry`s are the
   complete named proofs listed above. No prohibited declaration or attribute,
   hollow definition, or choice of data from a new unproved theorem occurs. The
   delivery tool also probes the axioms of every declaration. Pass, subject to the
   two explicitly reported open cohomology assertions.
3. Read both new signatures and their complete coordinate formulas. The source
   differential, target differential, and augmentation are all fixed; arbitrary
   degree isomorphisms cannot change the claimed cohomology maps. Checked r=0
   (both section and coordinate modules zero), r=1 (the singleton restriction is
   an isomorphism), zero coefficients, empty basic opens, repeated cover members,
   and arbitrary unbounded coefficient degrees. The finite horizontal staircase
   works for degreewise injectives and transfers along a homotopy equivalence
   from a K-injective resolution. Read Stacks Tag 08C1 directly; it supplies the
   finite-row exactness argument and degreewise-injective resolution route.
   Independent LeanFinder search for finite covers, exact augmented rows, and
   monomorphisms/epimorphisms on homology found generic diagram and Mayer-Vietoris
   lemmas, not these assertions. Independent Mathlib grep for augmentation Mono/Epi
   and Čech homotopies, plus repository searches for augmentation quasi-isomorphisms,
   found no matching coordinate theorem. These are two strictly weaker halves,
   combined by a genuine coordinate verification and the abelian mono/epi criterion;
   this is a decomposition, not net proof progress. Pass.
4. Checked the existing tuple-based alternating total, its homotopy lemma,
   injective row augmentation, and principal-cover resolution quasi-isomorphism.
   They require comparison of models or additional coefficient hypotheses and
   do not immediately prove these coordinate assertions. All original imports
   remain required by unchanged public constructions. In the two new modules,
   a scratch compilation confirmed that direct imports of the moduleRings
   definition and Mathlib KInjective suffice; broad wrapper imports were replaced.
   The two new imports of the original module are
   used only in the proof and correctly remain plain imports. The old node has
   empty proof_deps, so the No longer needed list is complete. The unit
   sk-thm-picard-duality has empty realized statement and step lists; these edits
   bypass no realized unit step. Pass.
5. Compared the old node and read both new nodes. The original node changes only
   permitted proof-route fields. Its proof_deps are exactly the two new assertions;
   both new nodes contain their source, full proof plan, search records, creation
   and blueprint provenance, matching chapter/unit, and Lean declaration record.
   Their mathematical statements match Mono/Epi of the displayed homology maps.
   Pass.

Second reading replaced two broad public imports in each new module with direct
imports, and completed this report; theorem signatures and proof bodies were unchanged. Neither
remaining staircase assertion can be closed in a few minutes using the current
coordinate API. One original hole closed and two new holes added, net minus one;
no module or old proof dependency was pruned.

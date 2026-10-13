## What changed

Proved `AlgebraicGeometry.Scheme.exists_subsingleton_hom_of_isPerfect` in
`Sheaf.AlgebraicGeometry.PerfectHomGap`, preserving its complete signature and public imports.
The proof chooses the actual perfect internal dual, a uniform global Tor interval, and
one global-sections bound. It proves the interval arithmetic and applies the existing tensor
gap theorem, then transports vanishing through the tensor--RHom comparison and the additive
Hom/global-sections equivalence.

Four proved private helpers construct the additive natural identification of Hom from the
unit with top-open sections, prove the qcqs zeroth-hypercohomology gap by a truncation
triangle, and translate K-flat tensor vanishing into actual derived homology vanishing.
The natural isomorphism of sections is constructed explicitly; no data is chosen from a
mere existence theorem. Open-scheme derived localizations are universal localizations,
as in the existing open-derived-localization lemma, and only their existence is used.

Updated the original DAG node's proof, proof_deps, and proof_origin to follow this route.
All added imports are proof-only. No existing definition, statement, visibility, or instance
was changed. No other module was adapted. The unit's realized statement and steps are empty;
the proper-flat support route still uses precisely the original perfect Hom gap statement.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_subsingleton_hom_of_isPerfect`
(node `lem-sc-perfect-ext-bounded-qcoh-vanishing`).

Added zero holes; there is no `sorry` left in the delivered module. This is a complete proof
from the existing named library declarations, including dependencies that remain admitted.
The private helpers `sections_equiv`, `sections_iso`,
`exists_qcoh_zerothHypercohomology_gap`, and `tensor_homology_isZero_of_gap` are all proved.
No new module or public theorem is introduced.

Validation: the complete assigned module compiles without errors or warnings through
lcompile.py, including the uniform global gap argument. The delivery dry run provides the
mechanical signature, axiom, import-cycle, and preflight checks.

## No longer needed

Removed the direct proof imports:
- `Sheaf.AlgebraicGeometry.LerayDegenerateSections`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Projective`

The item's direct proof dependencies `lem-pc-leray-degenerate-sections`,
`lem-pc-affine-vanishing`, and `lem-pc-finite-support-hi` are replaced by the already existing
`lem-pc-uniform-inverse-affine-sections-bound`. Its own dependency route still supplies the
ordinary qcqs sections bound, so these removals are direct-import pruning, not a claim that
all three modules disappear from the targets' transitive import closure.

All other original proof imports remain in use. No unit statement or step was pruned.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and no mathematical dispute was found. The old proof plan says
the perfect tensor--Hom comparison supplies a finite Tor interval, but its Lean conclusion
only supplies a perfect dual. The proof therefore explicitly invokes perfect locally finite
Tor dimension and quasi-compactness to obtain the required uniform interval.

The hypercohomology gap conclusion uses an existential K-flat representative predicate,
not directly the homology of the canonical derived tensor. The proved private tensor helper
provides this missing comparison using the existing K-flat tensor comparison theorem.

The comparison's dual is quantified before its chosen second object, and its invertibility
is asserted for that object. Choosing a comparison for K and applying it to every L would
not supply invertibility. Instead the proof applies the comparison separately to each L and
identifies its dual with the fixed internal dual by the theorem's equality clause.

The global gap needs no new admitted statement: the existing inverse-affine sections bound
already supplies uniform ordinary cohomological dimension, and the truncation glue is proved
locally. The truncation argument includes all endpoints, requires no boundedness of L, and
also applies to the empty scheme. The chosen N is natural and positive, making a<=b automatic
from the Tor interval. No new nodes and no change records are needed.

## Second reading by C2

1. Compared the complete Lean diff with the repository version. The existing public
   theorem signature, docstring, visibility and all public imports are byte-for-byte
   unchanged. Only its proof, proof-only imports and proved private helpers changed.
   There are no adaptations or interface changes requiring change records. PASS.
2. Compiled the assigned file with lcompile.py without errors or warnings. Checked
   all five declarations with #print axioms in a scratch copy. sections_equiv,
   sections_iso and tensor_homology_isZero_of_gap use only propext, Classical.choice
   and Quot.sound. The global-gap helper and main theorem also use sorryAx through
   existing open library dependencies. No forbidden declaration or local sorry occurs.
   The sections identification is explicitly constructed; the perfect dual is fixed
   by equality to actual RHom, and the chosen derived-category localization is a
   universal localization. No arbitrary data witness from a holed existence statement
   is used. PASS.
3. There are no split-off statements, new public declarations, new nodes or new holes.
   Independently checked the private truncation and tensor-comparison arguments.
   Empty X, N=0, lo=hi, negative endpoints and unbounded L cause no missing case:
   a=-hi-N <= -lo=b, A has support <=-N-1, and the upper truncation has support >=1.
   Independent LeanFinder/Loogle and source searches found no shorter scheme-level
   result replacing this argument. PASS.
4. Read the proof downward against every called scheme-level dependency. All added
   imports are proof-only and supply the used comparisons, instances or homology
   infrastructure. The three removed old proof dependencies are exactly those listed
   in No longer needed. The existing uniform inverse-affine bound retains their
   underlying cohomological-dimension route. The unit sk-thm-picard-duality has no
   realized statement or step here; its route and the caller in
   AffinePerfectPlusLocallyFree remain intact. PASS.
5. Checked the node fields and the union of all step uses. Only proof, proof_deps and
   proof_origin differ from the original node. Found and repaired an omitted explicit
   dependency: lem-sc-derived-internal-hom-adjunction, used to choose adj and its
   compatible symmetric form. The corrected proof_deps exactly equals the step-use
   union and all dependency node files exist. PASS after repair.

Second-reading changes: added the internal-Hom adjunction dependency and its explanation
to the existing node; removed an unused local Γ binding and an extra blank line.
No mathematical proof repair or additional pruning was needed. One original hole closed,
zero holes added; the proof still rests on the reported existing admitted dependencies.

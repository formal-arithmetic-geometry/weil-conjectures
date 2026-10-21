## What changed

Replaced the sole unfinished proof of
`AlgebraicGeometry.Scheme.ProEt.affine_component_site_projection` with a complete
construction and evaluation argument. The five existing definitions, theorem
signature, universes, and public imports are unchanged. All auxiliary declarations
are private and proved. No source-library file is changed.

The affine object is the existing, explicitly constructed
`WContractification.PullbackProfinite` algebra, transported through `T.isoSpec`.
Its fibre homeomorphism, ind-Zariski instance and local-ring isomorphisms give the
object clauses. A private generalization of the proved source algebra-map
correspondence removes its unused local-ring hypothesis on the source algebra.
Affine gluing then proves the mapping property for arbitrary schemes. This gives
functoriality, finite limits via topological-slice Hom functors, and the canonical
component factorization for qcqs objects. Finite jointly surjective families give
pro-etale covers, including the empty family.

The remainder constructs the actual Kan-extension/sheafification adjunction.
The canonical factorization makes the pointwise Kan index terminal. Sheaves on
the coherent profinite slice preserve finite products; the Kan presheaf therefore
preserves finite qcqs coproducts. A covering sieve on a qcqs scheme has a finite
affine refinement. The split-cover hypothesis then proves both injectivity and
surjectivity of the sheafification unit, using its equalizer and image sieves.
The canonical adjunction unit normalizes the evaluation isomorphism, and a
pointwise Kan calculation proves its joint naturality in sheaves and objects.
One concrete-category proof handles sets, abelian groups, and rings directly,
so every evaluation is an isomorphism in its stated coefficient category.

Updated the item's DAG proof, proof dependencies and proof origin to follow this
argument. The unit's realization route and all target statements are unchanged.
The copied proof docstring continues to describe the source argument; its steps
are implemented by the existing closed source tools where those suffice.

## Proved and sorry left

Original holes: one, in
`AlgebraicGeometry.Scheme.ProEt.affine_component_site_projection`.
Closed: that declaration. Added: zero. Remaining in the delivered module: zero.
No split-off statements or new nodes.

The required server-side single-file compiler accepted the complete proof in
23.4 seconds (exit code 0). `#print axioms` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx`. Removed the diagnostic
command and two unused-tactic warnings before delivery. A byte-for-byte comparison
checks all five original definitions, the theorem signature, and the public-import
list against the shared source. No consumer adaptation is needed. The delivery
tool performs the final compilation and preflight on the submitted packet.

## No longer needed

The following planned direct dependencies and their top-level `tool_uses` entries
were removed from this node. This is dependency pruning, not a request to delete
any source-library declaration or module:

- `lem-weil-pbc-ind-etale-stability`: the existing graph-restriction algebra is
  already ind-Zariski, hence ind-etale; weak etaleness of its functorial maps follows
  from morphism-property cancellation against the structure maps.
- `lem-weil-pbc-left-exact-site-inverse-image-tensor`, module
  `Sheaf.CategoryTheory.SiteInverseImageTensor`: the general-universe flat
  Kan-extension API and canonical sheaf pullback prove exactly the needed
  geometric-morphism clauses. Tensor and coherence assertions are unnecessary.
- `lem-weil-pbc-localization-spectrum-embedding`,
  `lem-weil-pbc-locally-constant-prime-spectrum`,
  `lem-weil-pbc-profinite-clopen-basis`, and
  `lem-weil-pbc-spec-clopen-idempotent`: the closed source
  `WContractification.PullbackProfinite` construction already supplies the fibre
  homeomorphism and algebraic properties. These are removed as separately planned
  obligations of this node. The underlying mathematical constructions remain
  used inside the adopted source library; no source dependency is withdrawn.
- `lem-weil-pbc-proetale-qcqs-finite-family-geometry`, module
  `Sheaf.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry`: only its independently
  stated `finite_coproduct_evaluation` constituent is needed. Import its module
  `Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation` directly;
  the additional qcqs site-limit and slice-limit package is unnecessary here.
- `lem-weil-pbc-sets-sheaf-iso-on-stalks`: the required stalk maps are isomorphisms
  directly from the construction; no separate sheaf-isomorphism criterion is used.
- `lem-weil-pbc-sheaf-algebraic-structures-objects`, module
  `WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresObjects`: construct
  and evaluate the inverse image directly in each concrete coefficient category.
- `lem-weil-pbc-site-sheafification-sections-local`, module
  `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal`: Mathlib's
  generic concrete-category equalizer/image-sieve results suffice for the unit.

The exploratory direct proof imports for the preceding modules, and
`WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant`, were removed. The last
module's mathematics remains a transitive part of the reused source construction.
No Lean file is withdrawn, and no claim is made that these modules are globally
unreachable: other parents and adopted source proofs may still need them.

The replacement finite-coproduct dependency is an existing node and an existing
proved declaration, previously a constituent of the approved finite-family
package. Its addition to `proof_deps` records the narrower actual use; no new
maintainer approval was inserted into `tool_uses`.

## Where the brief, the DAG or earlier work was wrong

No statement repair is needed. The corrected split-cover condition is essential
and is used only for the sheafification-unit argument. No evaluation formula is
asserted for arbitrary qcqs objects.

The planned generic site theorem has small-category hypotheses that do not apply
directly to these full sites. The already proved general-universe flat
Kan-extension instance applies at colimit size `(u, u+1)` and avoids imposing a
small skeleton or changing the statement. The coefficient-category argument also
avoids any need to transfer ring structures from a set-valued isomorphism.

The source algebra-map correspondence states a local-ring-isomorphism hypothesis
on both algebras. Its inverse construction and injectivity proof only need that
hypothesis on the target algebra. The proved private generalization is used to
establish the required mapping property from arbitrary affine schemes; the source
library's public signature and proof remain untouched.

Edge cases checked in the argument: empty base, empty E, empty qcqs object,
zero-element covering families, arbitrary finite index types reindexed by Fin n,
and the identity component map. No nonemptiness assumption is introduced.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

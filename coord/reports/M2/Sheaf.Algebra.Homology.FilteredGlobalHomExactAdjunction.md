## What changed

Restored `lean/Sheaf/Algebra/Homology/FilteredGlobalHomExactAdjunction.lean`
from the quarantine path in `coord/rework.tsv`, preserving every public declaration,
statement, definition's data, public import and DAG attachment. The archive itself
is untouched. This is a substantive proof delivery, not a restoration-only packet.

Proved the five exact-filtered construction theorems. Antitonicity follows by
mapping the factorization of step inclusions and comparing images. Finite filtration
bounds follow from preservation of invertible whole-step inclusions and zero
bottom-step inclusions; additivity preserves the cochain bounds. Mapped filtered
morphisms induce maps of image subobjects. For grading, the mapped step inclusion
is monic, so its factorization through its image is invertible. The cokernel
comparison and the isomorphism between the inclusion arrows construct the graded
isomorphism, and the mapped quotient projection detects uniqueness. A proved private
helper establishes its naturality by cancelling step inclusions and quotient
projections. This transports exact-functor preservation of quasi-isomorphisms to the
graded maps; the target localization then inverts them.

The graded comparison precedes `exactFiltered_inverts` so the latter uses its
proved naturality. The existing functor-law proofs now use `FilteredObject.Hom.mk`
instead of the removed `HomPreservingSteps.mk`. All existing definition bodies
apart from these proofs are unchanged. A declaration-local linter option preserves
the original exactness-instance parameters of `exactFiltered_antitone`, although
its proof needs only additivity.

Searches: LeanFinder for exact additive functors preserving associated graded
complexes returned ordinary exact-functor APIs, not this filtered construction;
Loogle for `CategoryTheory.imageSubobject` reported an unknown identifier; Mathlib
and library `rg` found `imageSubobject_comp_le`, `imageSubobjectMap_arrow`,
`PreservesCokernel.iso`, `cokernel.mapIso`, and the ordinary quasi-isomorphism
transport lemmas. Those APIs give the shorter direct construction above. The source
Varshavsky §§5.1.1–5.1.5 and the unit's statement/route were read. The original
filtered-injective, Hom-invariance and calculus dependency signatures were also
read; none supplies a normalization theorem for arbitrary calculus parameters.

Also proved `CochainComplex.FiniteFiltered.graded_laws` in the unclaimed module
`Sheaf.Algebra.Homology.FilteredDerivedHomCalculus`. The initial axiom probe showed
that its existing hole still entered the type of `quasiIso` and hence the inversion
theorem. The new proof cancels the monic step arrows to establish the restriction
identity/composition laws, then cancels the epimorphic cokernel projections to
establish the graded laws. This is a proof-only support change; every signature,
public import, definition body and the other nine theorem proofs stay unchanged.
No module held by another group is edited.

Change record: `coord/changes/FilteredGlobalHomExactAdjunction-restore-proofs.md`.

## Proved and sorry left

Closed five of the six archived holes, all under
`CochainComplex.FiniteFiltered`:

- `exactFiltered_antitone`;
- `exactFiltered_bounds`;
- `exactFiltered_preserves`;
- `exactFiltered_graded_iso`;
- `exactFiltered_inverts`.

Also closed the existing supporting hole
`CochainComplex.FiniteFiltered.graded_laws`, node
`lem-trf-filtered-derived-hom-calculus`. Thus the packet closes six existing holes
in total, five in the assigned module and one in its calculus dependency.
Added zero holes and split off zero theorems. The private
`exactFiltered_graded_naturality` is fully proved. In particular,
`exactFilteredGrIso` now selects from a proved unique characterization.

One original hole remains:
`CochainComplex.FiniteFiltered.filteredGlobalHomExactAdjunction`, node
`lem-trf-filtered-global-hom-exact-adjunction`. Its statement is unchanged and is
marked `STATEMENT-DISPUTED` for the interface defect below. This is not a proof or
decomposition of that last theorem.

The complete sandbox compiles through `lcompile.py --all` without errors or warnings:
14.6 s for the supporting calculus and 18.7 s for the assigned module. The same
compile, using the sandbox's newly compiled dependency, printed the axioms of all
six closed theorems and all five construction definitions (`exactFilteredObject`,
`exactFilteredComplex`, `exactFilteredGrIso`, `exactFilteredDerived`, and
`exactFilteredDerivedQ`). Every one uses only `propext`, `Classical.choice`, and
`Quot.sound`. The temporary print commands are removed from the delivery.
The delivery preflight also probes the declarations. The nine untouched supporting
holes are `truncation_bounds`, `restriction_square`, `truncation_maps`,
`cone_antitone`, `shift_antitone`, `cone_shift_bounds`, `cone_maps`,
`shift_preserves`, and `filteredDerivedHomCalculus`, all in the same namespace and
all retaining their original node `lem-trf-filtered-derived-hom-calculus`.
Zero-complex, zero and whole filtration steps, identity functors, negative indices,
and both boundedness flags are covered without additional hypotheses.

## No longer needed

Removed the following redundant private imports; the retained public calculus
import already exposes the APIs needed by the completed construction:

- `Sheaf.Algebra.Homology.FilteredHomComplexInvariance`;
- `Sheaf.Algebra.Homology.FilteredLocalizationInjectiveModel`;
- `Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits`;
- `WeilConjectures.Algebra.Homology.FilteredComplexSubquotients`;
- `WeilConjectures.CategoryTheory.Abelian.Filtration`.

No node or module is claimed pruned. The remaining Hom-comparison proof still has
its original dependency plan, including the filtered-injective and Hom-invariance
results. Those edges and every unit route are preserved. No upstream declaration
or quarantined archive is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The archived functor-law proof used the retired constructor
`FilteredObject.HomPreservingSteps.mk`; the current category uses
`FilteredObject.Hom.mk`. The unmodified archive fails to compile for that reason.

STATEMENT-DISPUTED: the main Lean theorem quantifies over arbitrary
`GlobalHomCalculusIn` structures, whereas the source's comparison uses the canonical
filtered Hom construction with its canonical associated-graded comparison. The
structure has no field normalizing `gradedComparison` to a filtered chain model,
or relating its positive-grade components to the filtered-morphism comparison.
The ordinary-model field is only a `Nonempty` object isomorphism and does not fix
this defect.

A concrete test is to keep every field of a standard calculus G and replace only
`G.gradedComparison 1 P Q` by its negative, for every P,Q. Naturality in both inputs
still holds because negation commutes with composition. The only other structure
law involving this comparison is `graded_projection`, and it uses grade zero,
which is unchanged. The scratch file `scratchpad/SignTwist.lean` was accepted by
`lcompile.py`: an actual structure update, with no sorry, verifies that every field
survives this modification. This checks the alleged freedom directly against the
current Lean structure, rather than assuming a field is absent.

For the counterexample test, use the identity adjunction on abelian groups and the
standard filtered Hom model. Take P and Q to be Z concentrated in cochain degree
zero, with P pure in filtration degree zero and Q pure in filtration degree one.
Their filtered Hom is Z[0] pure in filtration degree one; its F^0, underlying
object and grade one have the same nonzero H^0. Let GA be the standard calculus and
GB its grade-one sign modification. Their filteredHom, homEquiv, cohomology,
ordinaryHom and gradedSum fields are identical. Transport the identity functor's
normalized representative comparisons along the canonical isomorphisms.

The proposed conclusion's `morphism` clause then forces H^0(F^0(c)) to send the
identity filtered map to itself. Thus it acts as +1 on Z. On the other hand,
`gradedTerm_cohomology` at r=1,a=0,n=0 forces the sole nonzero graded-sum component
to be +1. The `graded` equation, with the negated target gradedComparison, therefore
forces H^0(gr^1(c)) to be -1. For an object pure in filtration degree one these are
the same induced map, a contradiction on Z. The sign-structure update is checked
in Lean; the entire concrete derived-category counterexample is a mathematical
edge-case argument, not a claimed fully formalized refutation.

Accordingly I have not filled the last hole from a false auxiliary lemma, added a
normalization hypothesis, changed the public statement, or weakened its conclusion.
A future interface repair should specify the canonical filtered Hom model and
normalize all graded comparisons to its symbol maps, with all consumers checked.
The existing DAG route describes that canonical construction but does not establish
that the arbitrary parameters in this Lean signature are so normalized. Independent
review should resolve this statement defect before the remaining hole is proved.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

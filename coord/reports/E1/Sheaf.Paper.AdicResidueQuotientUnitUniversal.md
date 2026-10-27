## What changed

Replaced the sole hole in
`AlgebraicGeometry.Scheme.adicResidueQuotientUnit_universal` by a complete Lean
assembly, preserving its entire public signature, public imports and existing
docstring. Added proof imports for the existing Cech reflector, completeness and
scalar-extension calculus, plus the two new modules described below. No existing
definition or statement changed; there are no consumer adaptations.

The proof constructs the existing augmented Cech reflector for the actual residue
kernel. Proved private helpers establish completeness of finite scalar restrictions,
closure under products and cones, completeness of the supplied Roos limit point,
exactness of the specified scalar-extension functor, and invertibility of the Cech
unit after every finite reduction. Nilpotent localization is proved directly from
its sequential-colimit definition; the scalar-restriction completeness theorem is
used with its actual representative convention. The product argument constructs
both inverse identities using the reflector Hom bijection, so it assumes no
exactness of sheaf products.

Factor the given map as the Cech unit followed by f. Transposing ha(0) gives
F_0(a) followed by the transpose of the residue leg equal to identity. The first
new lemma makes that transpose invertible; hence F_0(f) is invertible. The cone of
f is complete with zero residue extension. The second new lemma kills this cone,
so f is invertible. Explicit cancellation and composition with its inverse give
the required injectivity and surjectivity for every complete target. Only ha(0)
is used, while all hypotheses of the original theorem are retained.

Compilation uses only the prescribed remote lcompile.py entry point. All three
modules compiled in the initial successful run (main file 31.0 seconds); the final
import-pruned version is compiled again before delivery. The delivery tool runs
the required final compiler, declaration, hole and axiom checks.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.adicResidueQuotientUnit_universal`
(node `lem-sfb-adic-residue-quotient-unit-universal`). The assigned module has zero
remaining holes, including all its private helpers.

Added exactly two holes, each the complete body `:= by sorry` of a named public
theorem in its own new module:

- `AlgebraicGeometry.Scheme.adicResidue_quotient_residue_projection_isIso`, in
  `Sheaf.Paper.AdicResidueQuotientFiniteProjection`, node
  `lem-sfb-adic-residue-quotient-finite-projection`.
- `AlgebraicGeometry.Scheme.adicResidue_isZero_of_complete_residue`, in
  `Sheaf.Paper.AdicResidueKoszulNakayama`, node
  `lem-sfb-adic-residue-koszul-nakayama`.

This is a decomposition: one original hole closed, two smaller holes added,
not a net reduction in the number of holes or a completed proof from standard
axioms alone. The first lemma computes one finite projection and quantifies over
neither a normalized map nor a complete target; the second has no quotient tower,
limit cone or mapping bijection. The complete argument combining them is in the
assigned module. There are no new definitions, axioms or private holes.

## No longer needed

No library module is withdrawn and no globally pruned module is claimed.

Removed the tentative proof import
`import all Sheaf.Paper.CompletionFiniteReduction`: only its proved nilpotent
localization calculation was needed. That calculation is now proved privately
from the sequential-colimit definition, and the actually used scalar-restriction
lemma is imported directly from `Sheaf.Paper.RestrictionSectionCompleteness`.
This avoids making this proof depend on the larger finite-completion comparison.
The original two public imports are preserved.

The original plan's full unit-compatible universal-property identification with
a Koszul quotient limit is unnecessary for the main assembly: only its residue
projection consequence remains in the first new node. The main node no longer
has a direct proof dependency on
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`; that theorem remains needed by
the finite-projection calculation, so it is not globally pruned.
`lem-weil-pbc-constant-completion-equivalence` remains needed for its actual
sectionwise quotient-kernel formula. The adjoint-tower node remains needed for
the normalized adjunction and transposition. No step realizing the unit
`sk-lem-integral-models` has been bypassed or withdrawn.

## Where the brief, the DAG or earlier work was wrong

The constant-completion theorem is stated on a chosen strict quotient
presentation. Its existing conclusion does not directly identify the supplied
slice adjoint tower, its counit-transpose transitions and its residue leg. The
first new node isolates precisely the finite part of this comparison that the
main proof needs. Its docstring specifies the insertion-of-one and successor
normalizations; it does not commute arbitrary tensor products with inverse limits.

The existing `AdicCompleteResidueConservative` theorem cannot supply the second
step here: it imports `AdicCompleteReductionCone`, which uses
`AdicResidueCechQuotientCone`, which imports the assigned module. The import-cycle
check rejects that route. The new residue-zero lemma instead has the independent
Koszul proof of Stacks Tag 0G1U. Its proof uses the retained general theorem
`CategoryTheory.ringedKoszulCompletionReflector`, not the narrower
`wfCompletionReflector` primary attachment of that node.

Both new statements were checked on J=0, J=A, the zero ring, zero complexes and
unbounded complexes. For J=0 the residue extension and zero-generator Koszul
model are identities. For J=A the residue category is zero and completeness
at the section one forces a complete object to vanish. The first statement
requires neither completeness nor boundedness of M, and the second requires
no finite generation of its cohomology. There is no statement dispute.

A local graph traversal found inherited metadata problems unrelated to the new
edges: the cycle between `lem-pc-ring-hom-extension-differential` and its
`-adjacent` node, and the missing identifier
`def-weil-pbc-localization-universal-property`. Neither was edited. Neither new
node has any dependency path back to the assigned node, and all its immediate
dependencies exist. The Lean import graph compiles.

## New nodes

`lem-sfb-adic-residue-quotient-finite-projection` records invertibility of the
scalar transpose of the residue leg of any specified quotient Roos limit.
Source: Stacks Tag 099M, lemma-naive-completion, and Tag 0A0E,
lemma-derived-completion-koszul. Its proof is the Artin--Rees Koszul/quotient
comparison followed by the reflector's finite-reduction consequence and
normalization of the adjoint successors. This is the computational part of the
argument, not a renamed mapping-property assertion.

`lem-sfb-adic-residue-koszul-nakayama` records zero detection by residue extension
on complete complexes. Source: Stacks Tag 0G1U,
lemma-derived-complete-zero-bis, Tag 0G1T, lemma-derived-vanishing-mod-I, and
Tag 0A0E. Its independent proof uses ideal-power torsion of finite Koszul
homology, balanced tensor cancellation, finite ideal-power and Postnikov
filtrations, and the Koszul reflector. In particular it does not use the assigned
universality statement or reconstruction from the quotient tower.

Each node has the complete proof in words in its module, exact Lean signature,
source labels, recorded LeanFinder/Loogle/grep searches, and the original unit
and blueprint ancestry. Blueprint searches for derived-complete-zero and
naive-completion found no matching unrestricted slice statement (the intrinsic
completion definition has additional torsion/perfectness hypotheses).
There are no change records because no existing signature or definition changed.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

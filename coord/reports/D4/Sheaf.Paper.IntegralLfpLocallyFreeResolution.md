## What changed

Proved the unchanged theorem
`AlgebraicGeometry.ProEtale.integral_lfp_locallyFree_resolution` by a concrete pullback
construction. For `a = ℓ^N • id P`, let `Q = cokernel a` and let `B(Q) → Q` be the counit of
the sheafified free-abelian/free-module adjunction. The degree-zero term is
`P ×_Q B(Q)`; the degree-one term is its projection's kernel. This avoids the original
finite-etale torsor and pushforward globalization.

The main module proves the following glue in Lean: preservation of local freeness under
locally split extensions and pullbacks, the kernel's finite presentation, an induction
showing that a finite free integral matrix with free rational cokernel has locally free
image, and the resulting local freeness of the resolution kernel. The image induction
uses the existing pivot-cover theorem and an explicitly constructed epi-mono factorization
of its block matrix.

Four new modules provide the needed interfaces. `ModuleObjectFreeGenerators` constructs
its adjunction, object and counit without existential witness definitions, proves the
counit epimorphic, and proves that finite constant set charts give finite free generators.
`IntegralLfpFiniteQuotientCharts` proves globalization of local torsion bounds by finite
affine refinement, a finite maximum, and inverse-image comparisons.
`IntegralLfpEventualFreeImage` combines that result with the proved generator theorem.
`IntegralLfpLocalTorsionCharts` retains the one open local classification theorem. Its
rationalization comparison is already proved and reused by the main module. Arithmetic
helpers also prove discreteness and finiteness of every nonzero principal coefficient
quotient, continuous lifting through that quotient, division computing its kernel, and
the categorical cokernel comparison. The nonzero rank-one local chart case is proved:
constant-norm neighborhoods, continuous unit comparisons with a fixed coefficient,
finite constant quotient charts, and eventual scalar annihilation. Generic block
elimination, finite diagonal cokernels, and scalar images/cokernels of a free-plus-torsion
biproduct are also proved. Finite free scalar quotients have finite constant set charts.
The proved
`integralDiagonalLocalChart` combines all these ingredients for a finite free module
plus a finite family of nonzero constant-norm cyclic cokernels, with a common eventual
bound. `integralColumnDivides` supplies the column-elimination factor under the pivot
norm bound.

All added imports of the existing module are proof imports. Existing public signatures,
definitions, targets and visibility are unchanged, and no consumer required adaptation.
An explicit `RationalMatrixKernels.{u}` type eliminates expensive inference; the main
module compiles without a heartbeat override. The local module also compiles at the
default compiler limits.

## Proved and sorry left

Original holes closed: one,
`AlgebraicGeometry.ProEtale.integral_lfp_locallyFree_resolution`.
There are zero `sorry`s in the item module.

New holes added: one,
`AlgebraicGeometry.ProEtale.integral_lfp_local_torsion_charts`
(node `lem-weil-pbc-integral-lfp-local-torsion-charts`). Its proof is exactly `by sorry`.
What remains is the local matrix elimination and assembly: refine finite presentations
and rational free charts; diagonalize the continuous integral matrix using dominating
pivots; compare the resulting diagonalized module with the normalized pullback of
`P`; transport `integralDiagonalLocalChart` through coefficient and underlying-set
pullback comparisons. The finite-sum scalar calculation itself is now complete.
The rational free comparison and the arithmetic finite-principal-quotient calculations
are supplied in the same module, together with the rank-one torsion bound and the
finite free scalar quotient comparison. No global exponent, generator construction, global
epimorphism, resolution kernel, or short-exact-sequence argument remains in this hole.

The new declarations `moduleObjectFreeGeneratorsπ_epi`,
`moduleObjectFreeGenerators_locallyFree`, `integral_lfp_finite_quotient_charts`, and
`integral_lfp_eventual_free_image` are proved, as are all private helpers. The intermediate
bound and generator statements were initially split during this session and then proved
in the same sandbox. The final result is a decomposition, with one original hole closed
and one new strictly local hole added (net zero); it is not an axiom-free proof of the
entire imported theory. Existing postponed inputs, including the analytic pivot-cover
input, are used through their existing library declarations.

All five delivered Lean files compile together. Edge cases checked include zero source
rank in the image induction, zero maps, zero quotients (the underlying set has one element),
torsion modules, and empty schemes/covers (the finite supremum is zero). An unchanged
consumer, `IntegralLfpHomContinuity`, also compiles. Axiom checks for the generator
epimorphism and local-freeness theorem show exactly the three permitted axioms; the
resolution still reports `sorryAx`, as expected from the explicitly reported open inputs.
The new complete diagonal scalar-chart calculation and column-division helper also
pass individual axiom checks with only the permitted three axioms. Printing the
resolution with universes enabled confirms its single original universe parameter `u`.
The complete local-chart module compiles in 16 seconds and the item in 11 seconds,
without increasing any compiler limit.

## No longer needed

No original import was removed and no existing named module is newly unreachable.
The original node's sole old proof dependency,
`def-weil-pbc-continuous-integral-coefficients`, is no longer a separate proof step;
it remains a statement dependency and its unchanged module remains publicly imported.
Its definitions and proved coefficient properties are still used. Thus this is not
a pruned node or module.
The original plan's finite-etale splitting torsor, finite-etale pushforward of its
resolution, and finite-etale counit argument are unnecessary for this proof. They were
not separate named dependencies of the original node, so no existing module is claimed
as pruned. The new local proof also avoids the initially considered DVR-factorization
node: continuous division at constant norm supplies the cyclic comparison directly.

During import minimization the new generator module dropped the redundant proof imports
`Mathlib.CategoryTheory.Adjunction.FullyFaithful`,
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`, and
`Mathlib.CategoryTheory.Preadditive.Biproducts`. The local and global quotient-chart
modules use the inverse-image and constant-sheaf imports their statements need, without
importing the generator construction. A final compilation also removed five redundant
proof imports from the local module: `Mathlib.Analysis.Normed.Group.Ultra`,
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products`,
`Mathlib.CategoryTheory.Limits.Types.Products`,
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts`, and
`Mathlib.Algebra.Category.Grp.Adjunctions`. The retained sites-adjunction import is
needed by the proof that the underlying-set functor preserves finite products.

## Where the brief, the DAG or earlier work was wrong

The original node gave an integral globalization in words but supplied no Lean declarations
for its torsor and finite-etale pushforward steps. The replacement constructs the needed
global object from existing adjunctions and a pullback instead. Bhatt--Scholze's
Proposition 6.8.11(3) supplies the local finite projective resolution argument; the global
two-term resolution is an expanded agent argument, not a displayed assertion of that
proposition. The updated node makes this distinction explicit. No statement is disputed
and the unit route is unchanged.

The existing `integralMatrix_pivot_cover` exposes row quotients, monicity and rational
invertibility; it does not expose column divisibility or constant-norm pivot charts.
That interface suffices for the proved image induction in the item. For the remaining
cokernel diagonalization, start from `integralMatrix_analytic_cover` and its entry norm
bounds, retain these bounds when splitting off the selected row and column, and use
the proved `integralColumnDivides` and `integralPivotCokernelIso`. The arithmetic and
finite-sum conclusions after obtaining that diagonal form are already supplied by
`integralDiagonalLocalChart`; they should not be split off again.

## New nodes

`lem-weil-pbc-module-object-free-generators`: the actual composite free functor, its
canonical epimorphism, and its finite-constant-set local-freeness comparison, all proved.

`lem-weil-pbc-integral-lfp-eventual-free-image`: the eventual image and locally finite
free canonical quotient generators, proved from the two more specific interfaces.

`lem-weil-pbc-integral-lfp-finite-quotient-charts`: the common global exponent, proved
by finite refinement and a maximum of the local bounds.

`lem-weil-pbc-integral-lfp-local-torsion-charts`: the remaining local continuous integral
matrix classification step, with a source, complete proof in words, and proved auxiliary
rationalization and principal-quotient calculations. This is the only new postponed theorem.

The original resolution node's proof, proof dependencies and proof origin now follow the
actual categorical construction and image induction. The change record
`coord/changes/D4-integral-resolution-private-proof-context.md` documents the static
checker's conservative classification of added file-local proof commands. Existing
statements and definitions are unchanged; the record lists all downstream users.


## Second reading by D4

1. **Visible interface: pass.** Compared the only existing delivered Lean module with
   the repository version by diff, and compared the full theorem signature as text:
   `integral_lfp_locallyFree_resolution` is byte-identical. Its elaborated declaration
   retains the original single universe parameter `u`. Independently compiled the
   unchanged `IntegralLfpHomContinuity` consumer against the sandbox outputs.
   No existing definition,
   hypothesis, conclusion, visibility, public import or target changed. The added
   generic helpers are private and the preservation attributes are local instances.
   The existing change record accurately explains the conservative interface flag.

2. **Proof and data: pass as a decomposition.** Independently compiled all five
   modules in import order without errors or warnings. The only new `sorry` is the
   entire proof of the public named theorem `integral_lfp_local_torsion_charts`.
   Checked the source for forbidden declarations and compiler-limit overrides;
   none occur. Read every data construction: generator adjunction, free generators
   and counit are actual composites of existing functors and adjunctions; image,
   cokernel, pullback and kernel objects use their universal-property constructions.
   No definition chooses an arbitrary witness of an unproved existence theorem.
   The scratch axiom checks confirm the three permitted axioms for the generator
   API and the completed diagonal and column-division calculations. The resolution
   and chart interfaces additionally use `sorryAx` through their reported open
   inputs. The remaining local classification hole is not an axiom-free proof.

3. **Split-off statement: pass.** Read the local theorem and its complete docstring
   argument against the source text at Definition 6.8.10 and Proposition 6.8.11(3).
   The paper gives the finite projective resolution for an already locally constant
   finite coefficient module; continuous presentation diagonalization is the stated
   agent expansion, not a verbatim paper assertion. Rational free charts fix matrix
   rank; maximal pivots admit continuous integral row and column division. Shrinking
   at nonzero pivots gives constant norms, and the proved principal quotient and
   diagonal calculations then give local bounds and finite constant set charts.
   Checked zero matrices, zero source/target ranks, units, pure torsion, a zero
   quotient (one underlying element), and empty schemes/cover members. The local
   theorem asks for no global exponent, epimorphism or resolution and is strictly
   the local classification part of the argument. The main module contains real
   pullback, kernel and matrix-image proofs; it does not apply a renamed resolution.
   Independent leanfinder, loogle and grep searches found ordinary field matrix
   diagonalization and PID Smith normal form, but no continuous integral pro-etale
   chart theorem; searched the upstream and Sheaf sources for the same concepts.
   Completing the remaining cover-compatible diagonalization is substantial work,
   rather than a missing short application of one of those algebraic results.

4. **Shortest route and pruning: repaired, then pass.** Found the upstream
   `Functor.constantSheafsheafPullbackIso` and replaced the reconstructed terminal
   sections argument in `constPullbackIso`, using the generic comparison with the
   constructed inverse image. Replaced the proof import of
   `Sheaf.Paper.FiniteDiscreteSchemeRing` in `IntegralLfpFiniteQuotientCharts` with
   `WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf`. The finite-discrete
   theorem remains used by the principal quotient calculations in the local module,
   so no whole-library module becomes unreachable. Listed the sole old proof
   dependency above; no existing module is claimed as pruned. Checked
   `dag/units/sk-thm-properbasechange.json` and its realized statement/steps: this
   resolution is an auxiliary node below the unit, and the realized route is kept.

5. **Node agreement: repaired, then pass.** Read all five node records and matched
   the new signatures with their Lean declarations. Each new node has its source,
   self-contained statement, statement dependencies, proof steps, search records,
   provenance, split status, creation record, blueprint ancestry, chapter/unit and
   Lean record. The proof-dependency lists equal the unions of the steps' uses.
   Changed the global quotient-chart node to record the upstream constant-sheaf
   comparison and terminal preservation, removing its unused finite-discrete-ring
   theorem dependency. Corrected the generator node's generic provenance note to
   describe its actual categorical proof. The resolution node records the actual
   generator/pullback construction and decreasing-source-rank image induction.

Second reading changed only the private constant-pullback proof, its proof import,
two node descriptions/dependency records, and the pruning/review documentation.
No further holes were closed or added: one of one original item holes is closed,
one strictly local hole is split off, and the net hole count is zero.

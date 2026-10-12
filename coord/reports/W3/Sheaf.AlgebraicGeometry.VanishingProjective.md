## What changed

Replaced the sole hole in `Sheaf.AlgebraicGeometry.VanishingProjective` by a complete
Lean reduction. The theorem's name, universes, binders, result and public imports are
unchanged. Each formal kernel piece is shown quasi-coherent using the existing
coherence criterion and the source library's kernel theorem. A finite polynomial
algebra supplies the graded algebra input; Mathlib proves its grading and algebra
finite type. The local degree-zero generators are converted to the shifted-generator
format required by `graded_serre_vanishing`. Its natural bound is converted to an
integer. A `Sigma.desc` projection splits every coproduct inclusion, and applying
`tensorRight` followed by `moduleCohomology` proves each summand's identity is zero.
This includes the degree-zero piece F_1 and requires no preservation of infinite sums
by cohomology.

Added `Sheaf.AlgebraicGeometry.FormalKernelPolynomialAction`, containing the remaining
algebraic bridge as one public named theorem with a source and complete proof in words.
It needs a Noetherian scheme and a map to Spec A, but no properness or ample module,
and concludes only the action and finite local degree-zero generation. It contains
no cohomological conclusion. The polynomial ring and its homogeneous submodules are
Mathlib constructions. No definition or instance is introduced using a witness of an
unproved existence theorem; the existential action is used only inside a Prop-valued
proof. The bridge covers steps 2--4 of the old plan, using the existing kernel-Rees
and extended-ideal lemmas. The node records now follow this polynomial-cover route.

Both modules compile without warnings through lcompile.py. The complete reduction
was compiled before and after removing unused imports. New theorem edge cases were
checked mathematically: I=0 allows zero variables and has zero positive kernels;
I=A makes all formal terms zero; the zero ring and empty scheme cause no failure of
the action laws or the local generation quantifiers. Constants act through f-sharp,
including the unit, and the composition order agrees with graded_serre_vanishing.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.coherentFormalModule_kernel_twist_vanishing`
(node `lem-weil-pbc-vanishing-projective`). No sorry remains in the item's module.

Added exactly one hole:
`AlgebraicGeometry.formalKernel_polynomial_action`
(node `lem-weil-pbc-formal-kernel-polynomial-action`), whose whole proof is `by sorry`.
This is a decomposition: one original hole closed, one strictly algebraic hole added,
net zero before any pruning of transitive imports. The existing
`AlgebraicGeometry.graded_serre_vanishing` and
`AlgebraicGeometry.formalSystems_kernel_rees_finite` remain dependencies with their
existing holes; this delivery does not claim to close them.

## No longer needed

Removed these eight proof-only direct imports from VanishingProjective:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct`
- `Sheaf.AlgebraicGeometry.AssociatedModule`
- `Sheaf.AlgebraicGeometry.AssociatedModuleHom`
- `Sheaf.AlgebraicGeometry.FormalSystemsKernelReesFinite`
- `Sheaf.AlgebraicGeometry.ModulePullbackAffineSections`
- `Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Sheaf.Paper.PQFCohomology`

FormalSystemsKernelReesFinite and ModulePullbackIdealQuotient remain proof-plan
imports of the new bridge. AssociatedModule and several other removed imports can
remain reachable through existing dependencies; no whole-library unreachability is
claimed. Added proof-only imports of CoherentFiniteTypeLocallyNoetherian,
FormalKernelPolynomialAction and the source library's QuasicoherentKernel.

The original node no longer directly uses
`pqf-def-locnoeth`, `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact`,
`def-weil-proper-morphism`, `lem-weil-pbc-module-pullback-ideal-quotient`,
`lem-weil-pbc-spec-module-tilde-sections`, `def-weil-pbc-noetherian-ring`,
`def-weil-pbc-associated-module`, `lem-weil-pbc-associated-module-hom`,
`def-pc-module-pullback`, `lem-weil-pbc-module-pullback-affine-sections`,
`lem-weil-pbc-formal-systems-kernel-rees-finite`, or `pqf-def-cohomology`
as proof dependencies. Definitions needed in statements and dependencies retained
by the bridge or graded vanishing remain needed there. In particular the separate
associated-module adjunction, affine tensor sections and long-exact-sequence theorem
are unnecessary to the summand argument: only functor laws are used.

## Where the brief, the DAG or earlier work was wrong

The planned finite graded algebra action is not provided in the interface of
FormalSystemsKernelReesFinite: that theorem gives an action of the associated graded
ideal sheaf algebra, whereas GradedSerreVanishing asks for homogeneous actions of a
finite type algebra over the base ring. The new bridge records precisely this gap.
Using a polynomial cover of the associated graded base algebra simplifies the input
and avoids constructing its ring structure and internal grading in this delivery.

The previously documented correction of the Stacks proof's claimed equality with
a pulled-back associated graded algebra is retained: only a local surjection is
used. The existing statement and its ampleness convention are unchanged. The unit
sk-thm-p1 and every node in its realized statement and steps are untouched.

The local checkout lacks literature/stacks-project/coherent.tex. The Stacks primary
pages for Tags 0884 and 087Z were read to verify the source argument. LeanSearch
returned Internal Server Error and is recorded as unavailable. LeanFinder found
the homogeneous-polynomial ideal-power lemma and grading primitives, but no
formal-system sheaf action theorem. Recorded Mathlib grep found no formal-kernel
declarations. Blueprint search for graded kernel found no duplicate blueprint node.

## New nodes

`lem-weil-pbc-formal-kernel-polynomial-action`, in
`dag/nodes/sec-proper-base-change/`, states the finite polynomial action and finite
local degree-zero generation of the successive formal kernel pieces. Its module is
`Sheaf.AlgebraicGeometry.FormalKernelPolynomialAction`; its four proof steps expand
the algebraic part of Stacks 0884 using 087Z. It inherits the original node's chapter,
unit and blueprint ancestry. Its sole hole is strictly a part of the original
argument, with no properness, ample module or cohomological bound. No change records
or forced adaptations are needed because every existing interface is unchanged.

## Second reading by W3

1. **Existing interfaces: pass.** Read the full diff against the repository module.
   The existing theorem signature is byte-for-byte identical, including the explicit
   Noetherian instance on F; all six public imports are identical. Only proof-only
   imports and the proof body change. There are no changed definitions, interface
   changes, change records, or forced adaptations.
2. **Proof and axioms: pass as a decomposition.** Independently compiled both delivered
   files in import order through lcompile.py, without errors or warnings. The item has
   zero sorries; the new module has exactly the reported named theorem with `by sorry`.
   Neither file has an axiom, unsafe/opaque declaration, external implementation, or
   hollow definition. Scratch copies with `#print axioms` for both declarations report
   exactly propext, Classical.choice, Quot.sound, and sorryAx. Thus the reduction is
   checked, but the original result is not yet an axiom-free theorem: the algebraic
   bridge and existing upstream proof holes remain open. The existential action is
   eliminated inside a theorem proof, never used to define an arbitrary data object.
3. **Split statement: pass.** Read the formal-system conditions, homogeneous pieces,
   graded sheaf action and local-generation definitions, the kernel-Rees theorem,
   and the extended-ideal theorem. The polynomial bridge asserts only their algebraic
   combination, with no properness, ampleness, or vanishing conclusion; it is strictly
   part of the original argument, not a renamed restatement. Checked I=0, I=A, zero
   base ring, empty scheme, degree zero, and composition order. For a concrete
   non-flat check X=Spec(A/I), the extended ideal is zero, all positive kernels
   vanish, and the polynomial variables act by zero; constants still act correctly.
   Finite ideal generators give the degree-m monomials generating the ideal power,
   and finitely many coefficient lifts can be made on a common neighbourhood.
   Independently read [Stacks 0884](https://stacks.math.columbia.edu/tag/0884) and
   [087Z](https://stacks.math.columbia.edu/tag/087Z). Repeated searches with different
   words: LeanFinder on adic sheaf kernels gave completion/Rees-module primitives,
   Loogle on homogeneousSubmodule gave grading and ideal-span primitives, and Mathlib
   grep on adic kernels and graded sheaves gave no matching bridge. Repository rg
   found the existing kernel-Rees input but no duplicate polynomial-action theorem.
   Constructing its sheaf action and proving local generation is substantial work,
   not a hole that can be closed in a few minutes from the present interfaces.
4. **Route and pruning: pass.** Checked the grading, scalar and multiplication inputs
   to graded_serre_vanishing, degree-zero insertion into the shifted generator span,
   conversion of the natural bound to an integer, and the coproduct retraction after
   tensoring and cohomology. The retraction only uses functor laws and zero morphisms;
   no commutation with infinite sums is asserted. The kernel zero branch is F_1.
   The eight removed direct imports and all twelve removed old proof_deps are listed
   under No longer needed; dependencies retained by the algebraic bridge are expressly
   distinguished from global pruning. Read sk-thm-p1's realized record: none of its
   statement or step nodes is bypassed or edited. All new imports in the item's
   module are proof-only. The new module's public imports supply its signature and
   its proof-only imports supply the documented pending proof.
5. **DAG agreement: pass.** Both nodes' proof_deps equal the unions of their proof-step
   uses. The existing node changes only proof, proof_deps, and proof_origin. Its steps
   follow the Lean reduction, including individual quasi-coherence and retraction.
   The new node has the required source, complete proof steps, three search records,
   created/blueprint/chapter/unit fields, and Lean record matching its declaration.
   The remaining sorry has a sourced complete proof in words and its matching node.

Second-reading changes: appended this independent review and its explicit axiom and
non-flat edge-case evidence. No Lean or node repair was needed. This delivery closes
one original hole and adds one algebraic hole: a decomposition with net zero holes,
with eight direct proof-import removals and no claim of globally pruned modules.

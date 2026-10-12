## What changed

Replaced the sole sorry in
`CategoryTheory.filteredComplex_page_differential_exists_unique` with a complete Lean
assembly of related component differentials, zero components elsewhere, square-zero,
and uniqueness. All existing signatures, definitions, and public imports are unchanged.
The proof uses two new private proof imports:
`Sheaf.CategoryTheory.FilteredComplexSingleDifferentialDescent` and
`Sheaf.CategoryTheory.FilteredComplexDifferentialRepresentativesCover`.

The representative-cover theorem is fully proved. Its source object is the actual
pullback of the ungraded cycle intersection into the source filtration step. Two
proved private subobject lemmas identify its graded image with the defined cycles;
image factorization makes the resulting representative map epic. The derivative
factors through the target filtration and its target graded cycles using `K.d_comp_d`.
This uses Mathlib's images, subobject map/pullback adjunctions, and cokernel condition,
without countable sums, elementwise lifts, or projectivity assumptions.

The remaining single-component descent theorem asserts only existence and the
representative equation for one related pair. It does not assert shape, square-zero,
uniqueness, or existence of an entire page. The original module proves all those
additional facts by explicit Lean equations and epi cancellation. Every descended
component is uniquely determined by its representative equation, as demonstrated
by the proved epic cover and the component cancellation in the uniqueness proof;
there is no arbitrary object chosen from an unproved existence theorem.

The original existential binder `D` does not occur in its predicate `True`. A scoped
unused-variable linter option before the original theorem preserves this existing
signature while avoiding the warning; no other linter is disabled.

## Proved and sorry left

Closed the original hole:
`CategoryTheory.filteredComplex_page_differential_exists_unique`
(node `lem-sp-filtered-complex-page-differential`). No sorry remains in the item.

Fully proved the new theorem:
`CategoryTheory.filteredComplex_differential_representatives_cover`
(node `lem-sp-filtered-complex-differential-representatives-cover`), together with
its two private helpers `map_pullback_of_le` and `graded_image_sup`.

Added exactly one hole:
`CategoryTheory.filteredComplex_single_differential_descent`
(node `lem-sp-filtered-complex-single-differential-descent`). Its proof is exactly
`:= by sorry`, with its source and complete natural-language argument in its docstring.

Thus this delivery is a decomposition of one original hole into one strictly smaller
single-map descent hole, plus a proved representative-cover construction and proved
page assembly, square-zero, and uniqueness. It is not a net hole reduction.
The three modules compile together through `lcompile.py --all` without warnings.

## No longer needed

Removed the direct private imports
`Sheaf.Algebra.Homology.FilteredComplexSubquotients` and
`Sheaf.CategoryTheory.Filtration` from the item. Their definitions remain necessary
and publicly available through the unchanged public import of
`FilteredComplexBoundariesLECycles`; neither module is removed from the actual
transitive import closure. No existing DAG node or module is pruned.

No successor-page, page-homology, spectral-object, exact-couple, or quotient-image
comparison module is imported. In particular, the quotient-image comparison lemma
does not state the epic representative map needed here and is not used.
The unit record `sk-prop-av-pqf-finite` has empty realized statement/step lists;
no unit realization is bypassed or changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was disputed or changed. The representative-cover fact
in step 3 of the existing node was correct but not an existing Lean declaration.
It is now constructed and proved in its own module. It holds for every integer r,
so its new statement needs no positive-page hypothesis. The original page theorem
and the remaining descent theorem retain r ≥ 1, which is needed for the boundary
calculation.

The local literature payload is absent on this machine. Read Stacks Tag 012K at
https://stacks.math.columbia.edu/tag/012K, specifically its displayed cycle, boundary,
and differential formulas before Lemma 12.24.2. The finite-component reasoning is
an explicit expansion of those formulas, marked as agent-written in the nodes.
The new proof agrees with the existing plan while separating the kernel/cokernel
descent from the fully formalized representative test and record assembly.

Mathlib searches: LeanFinder for filtered differential descent returned unrelated
homological-complex constructions; Loogle on Subobject/Epi found the image-factor
and pullback APIs used in the cover proof; LeanSearch for epic image representatives
was unavailable (Internal Server Error). Local rg covered Mathlib homology/subobjects,
both project roots, and the DAG, including the quotient-image comparison signature.
No existing statement supplies the single-map filtered descent.

## New nodes

`lem-sp-filtered-complex-differential-representatives-cover`, in
`dag/nodes/sec-abelian-varieties/`, is the proved epimorphic family of simultaneous
source and derivative representatives. It applies for every integer r and uses only
the genuine subquotient definitions. Edge cases checked in the construction: a zero
complex or zero filtration gives a zero source with an epic zero-to-zero map;
constant filtration has zero graded cycles; zero and negative r still give the same
image-factorization argument. No arbitrary global lifting through an epi is assumed.

`lem-sp-filtered-complex-single-differential-descent`, in the same chapter, is the
remaining existence/representative property for one related component of the actual
cokernels. The docstring explains both kernel annihilations and both descents. At r=1,
the incoming target boundary filtration is p+1, exactly the ambiguity filtration;
for larger r it is still (p+r)-r+1=p+1. Zero or constant filtrations give zero quotient
objects and satisfy the formula. No square-zero, nonrelated components, or uniqueness
is hidden in this theorem. Both nodes inherit the parent unit and blueprint ancestor,
record the three search kinds, and introduce no import or DAG cycle.

No interface change record or forced adaptation is needed.

## Second reading by F2

1. **Repository comparison:** Compared the delivered page module with the repository version. The existing declarations and signatures are unchanged; only proof imports, a private extensionality helper, and the target proof changed. The two additional modules are new declarations recorded by nodes.

2. **Compilation and axioms:** Compiled all three modules with `lcompile.py --all`; compilation succeeds without warnings. The page theorem has no `sorry`; the only remaining `sorry` is the explicitly named single differential descent theorem, exactly as listed above. No axiom, unsafe, opaque, extern, or implemented_by declaration was added. The proof uses ordinary classical choice only through theorem witness selection.

3. **Statements and new nodes:** Read both new statements and their docstrings against the construction. The representative-cover statement is true for every integer r and is stronger only where the construction proves the stated epic cover; the descent statement is a strict one-pair reduction and does not restate the page theorem. Both have matching DAG nodes, sources, proof routes, and Lean records. Local searches found no existing equivalent declarations.

4. **Pruning and imports:** The page proof uses the two new private imports and the unchanged public boundary/cycle import. The former direct imports of subquotients and filtration are no longer needed as direct imports. No old proof dependency is bypassed at the unit level; the unit has no realized statement or step entries, and no downstream module is pruned by this delivery.

5. **Unit route and edge cases:** The page construction preserves related-pair shape, square-zero, and epi-based uniqueness. The representative construction handles zero, constant, and negative filtrations/r values through the same subobject/image argument; the page and descent hypotheses retain r ≥ 1 where required. The unit route and target statement remain unchanged.

**Changes made during second reading:** Added this review section only. No Lean or DAG repair was necessary after compilation and signature comparison.

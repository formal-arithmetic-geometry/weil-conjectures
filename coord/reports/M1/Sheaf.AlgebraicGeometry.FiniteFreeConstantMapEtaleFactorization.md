## What changed

Completed `AlgebraicGeometry.Scheme.exists_etale_factorization_of_finite_free_constant_map`
without changing its signature or its public imports. Three proved private helpers implement
the existing plan: represent finitely many basis images on one pointed neighbourhood;
refine until a finite family of germ equalities holds as section equalities; and assemble
a compatible section map into a sheaf factorization using the constant-sheaf adjunction.

Proof imports added: `WeilConjectures.ConstructibleSheaf.Pullback`,
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver`, and
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf`.
The main proof transports the given stalk equation by germ naturality, restricts along
the common refinement, applies the assembly helper, and uses its geometric lift to show
that the resulting neighbourhood contains x. It needs no monomorphism assumption.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.exists_etale_factorization_of_finite_free_constant_map`
(node `lem-weil-pbc-finite-free-constant-map-etale-factorization`).
No sorries remain and no holes were added. All three private helpers are proved:
`exists_finite_free_stalk_sections`, `exists_finite_free_section_germ_equality`, and
`exists_finite_free_section_factorization`. This is a proof, not a decomposition.

Single-file compilation passes without warnings. `#print axioms` lists exactly
`propext`, `Classical.choice`, and `Quot.sound` for the completed theorem. The argument covers n = 0 using
cofiltered nonemptiness and equality on the empty basis; it also covers the zero ring.
The point x excludes an empty base, while the assembly helper works on empty etale objects.

## No longer needed

Removed the redundant sandbox proof import `Mathlib.LinearAlgebra.StdBasis`: the module
compiles without it. None of the library's original imports, nodes, or modules is pruned. The existing DAG proof route
is retained. The earlier sandbox-only rank-zero and positive-rank statement modules
and their incomplete node drafts were discarded; they never entered the library.
No imports of other unproved Sheaf modules are needed.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox claimed a second reading written by its worker, used new-node
records with incorrect module names and no complete statements or proof steps, and left
nearly the whole theorem as a positive-rank sorry. Those drafts and that claimed reading
have been replaced. The original library statement and DAG plan are correct and usable.
This report leaves the independent second-reading section to the designated reader.


## Second reading by M1

1. Compared the sole delivered module with the repository using diff, then checked the
   existing theorem signature byte for byte in a script. PASS: its hypotheses,
   conclusion, visibility, docstring, and two public imports are unchanged. No existing
   definitions were edited and no change record is needed.
2. Read all three private helpers and the main proof. PASS: local compilation is clean;
   no sorry, axiom, unsafe, opaque, implemented_by, or extern occurs in the delivered
   module. A scratch copy with #print axioms for the completed public theorem compiled
   and printed only propext, Classical.choice, and Quot.sound. All choices select
   representatives from proved stalk/cofilteredness facts; no data is chosen from an
   unproved existence statement.
3. PASS: no statement is split off and no new hole or public statement is added. The
   three private helpers are proved, strictly constituent parts of the lifting argument.
   Checked rank zero (empty basis and cofiltered nonemptiness), the zero ring, and empty
   etale objects in the assembly helper. An empty base cannot supply the input point x.
   Searched the library and Mathlib point modules for finite lifting and germ equality:
   the proof already uses the available stalk representation and equality lemmas; no
   existing whole factorization theorem was found.
4. PASS after import repair: individually removing each added proof import showed that
   StdBasis is redundant, while Pullback, ConstantSheafOver, and Point.ConstantSheaf
   each supply declarations the proof needs. Removed only StdBasis. The finite-basis
   route uses the existing cofilteredness and constant-sheaf adjunction dependencies.
   All four old proof_deps remain used, so no old dependency is omitted from the report.
   Read dag/units/sk-thm-p1.json realized: this below-unit lifting proof bypasses no
   realized statement or step, and the unit route is preserved.
5. PASS after record repair: retained the unchanged statement, lean signature, and all
   four proof_deps. Updated the existing node's proof and proof_origin to describe the
   actual unified finite-basis argument (including rank zero) and over-site transport.
   There are no new nodes to validate.

Second reading changed the redundant StdBasis proof import, the existing DAG proof
narrative/origin, and this report. The Lean proof itself required no repair.

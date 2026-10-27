## Worker report

The module `Sheaf.CategoryTheory.DgFreeModuleHomCohomology` states
`CategoryTheory.DgAlgebra.exists_freeModuleHomCohomologyEquiv`. Its only proof
is `sorry`; it defines no replacement algebra, module, cohomology or localization.
The statement remains unchanged. The already landed definition node
`def-sfb-dg-derived-category` was added to statement dependencies to cite its
published interface (the authorization to add landed nodes in brief-stage2 §5).

Source read: Stacks `literature/stacks-project/dga.tex`, definition-shift,
lemma-hom-from-shift-free (09K1), and lemma-hom-derived (09KY), part (1).
The current blueprint size convention was read at
`literature/blueprint/latest/blueprint/sec-picard-framework/sk-thm-picard-perfect/def-weil-size-convention.md`.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The universe convention is explicit `universe u`, `Algebra.{u}` and its
  `ModuleCat.{u} (ULift.{u} ℤ)` components. The fixed localization uses the
  library's path localization in the larger category universe. Arbitrary input
  algebra/module sizes can be enlarged to a common u; no finite/countable bound
  or relation to a scheme universe is imposed.
- An associative unital integer DG algebra, including d²=0 and the signed
  Leibniz rule, is precisely `B : Algebra.{u}`, the existing monoid object in
  integer cochain complexes. There is no commutativity assumption.
- A right DG module with its signed Leibniz identity is `M : RightModule B`,
  the existing module object in the reversed tensor category.
- `Derived B` and `Q B` are the existing actual quasi-isomorphism localization,
  equivalent to localizing the homotopy category, not an arbitrary category or
  functor. `[DerivedStructure B]` names its standard triangulated/additive/shift
  structure, which the node already specifies. It is structural data on that
  fixed localization, with no compactness, freeness or projectivity assumption.
- `k : ℤ` ranges over all integers. `S : RightModule B` with
  `e : ShiftComparison B k M S` ranges over every realization of M[k]. Its
  underlying complex comparison uses precisely the (-1)^k differential and
  its `action` field pins the unchanged right action. `DerivedStructure.shifts_exist`
  supplies such representatives, so this quantification excludes no shift.
- A cycle is `x : ((underlying B).obj M).cycles k`; `iCycles k x` is its actual
  element in M^k. `homologyπ k x` is its cohomology class in H^k(M).
- The conclusion supplies `μ : regular B ⟶ S`, hence an actual degree-zero
  right-linear chain map. The `∀ r b, HEq ... (act B M k r ... b)` equation
  says its value on every homogeneous b is xb. The left hand side reads μ(b)
  through e into M^(r+k); the right side is in M^(k+r). HEq handles exactly
  that index reassociation, without changing the element, differential or action.
  This equation determines μ uniquely since e is invertible and underlying
  module morphisms are determined by all their degree components.
- `E : H^k(M) ≃+ (Q(B) ⟶ Q(S))` is an isomorphism of abelian groups, including
  additivity, injectivity and surjectivity. The equation
  `E (homologyπ k x) = (Q B).map μ` forces it to be the map prescribed by the
  node, rather than an unspecified additive equivalence.
- The final implication explicitly renders the boundary clause: if
  `iCycles k x = d (k-1) k y` for some y in M^(k-1), the image `(Q B).map μ`
  is zero. It also follows from the preceding equivalence and its normalization.
- There are no boundedness, countability, termwise projectivity, nonzero-ring
  or characteristic hypotheses.

Dependency declarations read in full from the current server using
`scompile.py --source Sheaf.CategoryTheory.DgAlgebraDerivedCategory`:
`CategoryTheory.DgAlgebra.Complex`, `Algebra`, `RightModule`, `underlying`,
`regular`, `act`, `quasiIsomorphisms`, `Derived`, `Q`, `ShiftComparison`, and
`DerivedStructure`, all in that module. In particular the structure's shift
comparison is action-preserving and its distinguished triangles are exactly
isomorphic images of the specified mapping cones. The size node's Lean record
is a metatheoretic convention and explicitly requires no import/declaration.
Mathlib's `HomologicalComplex.cycles`, `iCycles`, `homology`, `homologyπ`
were read in `Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex.lean`.
These are imported publicly by the DG interface.

The two proof dependencies `lem-sfb-dg-homotopically-projective-hom-derived`
and `lem-sfb-dg-derived-admissible-triangles` currently have no recorded Lean
module, so there is no proof-only module to import. Their three-step proof plan
is included completely in the theorem docstring. The additional already
published homotopy, acyclic-localization and bimodule sources were read to
check whether they already supplied this statement; they do not.

Edge cases checked mathematically before writing: B=0 and M=0 give zero groups;
acyclic M gives a zero Hom group by homotopical projectivity of B; B=ℤ in
only degree zero gives ordinary cohomology; k=0 gives unshifted evaluation;
negative and odd k keep the unchanged right action and the (-1)^k homotopy
sign; characteristic 2 removes signs consistently. Unbounded modules and
noncommutative algebras remain permitted. No empty-family hypothesis occurs.
The equality is on every homogeneous degree, including negative degrees.

Searches made:

- `msearch.py ... leansearch` query: "Cohomology of an unbounded right
  differential graded module as morphisms from its algebra in the derived category".
  Eight results concern ordinary derived functors and ordinary complexes,
  including `DerivedCategory.Q` and resolution/Ext comparisons; none is this result.
- `msearch.py ... leanfinder` query: "Morphisms from a differential graded
  algebra to a shifted right DG module in the derived category compute cohomology".
  Eight results include `CochainComplex.HomComplex.CohomologyClass.toHom`,
  `toSmallShiftedHom`, and projective/injective resolution Ext comparisons.
  They concern ordinary complexes and not arbitrary right DG B-modules.
- `msearch.py ... loogle` query: `"DGModule", "DGAlgebra"`: zero hits.
- `msearch.py ... grep` query `DGAlgebra|DGModule|DifferentialGraded` in
  `Algebra/Homology`: zero hits.
- `rg` of DGAlgebra/DGModule/DifferentialGraded/differential graded in
  `lean/WeilConjectures` and `lean/Sheaf`: local results are Koszul and divided
  power algebras and dg-category frameworks; none states the result. Searching
  the item's blueprint id in `lean/WeilConjectures` found no declaration.
- DAG inspection found the already landed `def-sfb-dg-derived-category` and
  the related DG homotopy/bimodule nodes; their server modules were opened
  through `scompile.py --source` because this read checkout lacks the files.
  Those are reused, not redefined. The unrecorded shift-transposed node
  `lem-sfb-dg-free-shift-derived-hom` has no declaration to reuse.
- The proposed declaration name and free/cohomology variants were searched in
  `dag/lean_names_upstream.json`, project CategoryTheory sources and Sheaf
  CategoryTheory sources; no collision or exact statement was found.

No statement dispute, correction, new definition node or dependency repair.
Independent review is performed by the maintainer, as specified in the dispatcher brief;
this worker did not start another agent or represent a self-check as independent review.

Validation: the final module, including the explicit boundary clause, compiled
cleanly using the prescribed server `scompile.py` wrapper, both as the sandbox
probe and as its real library module. No errors or warnings were printed.

## Second reading by Q66

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

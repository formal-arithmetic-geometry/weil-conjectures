## Worker report

Stage 2, group O1, item lem-sfb-dg-homotopy-acyclic-localization.
The accepted nine-step split, statement, source and proof dependencies are unchanged.
The prior worker's stage-1 blocker does not apply: coord/brief-stage2.md §0 expressly
permits statement work on an already reviewed split. The current queue lists stage 2.

The delivery states `CategoryTheory.DgAlgebra.homotopy_acyclic_localization` in
`Sheaf.CategoryTheory.DgHomotopyAcyclicLocalization`. Its only theorem proof is `sorry`.
It asserts the existence of the specified standard structure on the actual homotopy
quotient, together with all three conclusions. It does not assume a triangulation,
acyclic closure, quasi-isomorphism criterion or derived-category structure on A.
All definitions have real data. A structure type specifies data and laws; the theorem,
not a definition or an additional hypothesis, asserts that this structure is inhabited.

Hypotheses and clauses, in the order of the unchanged node:

- Size convention: explicit `universe u`; the dg algebra and component modules live
  in `u`, their bundled categories in the larger universe. No finite or countable
  bound and no independent test-object universe restricts the statement.
- Arbitrary associative unital dg integer algebra: the sole theorem parameter is
  `A : Algebra.{u}`, the existing `Mon Complex` definition. The chain-map multiplication
  is the signed Leibniz rule. Mon does not impose commutativity.
- Right dg modules: the existing `RightModule A` is a module in the reversed tensor
  category of integer cochain complexes. Its differential and signed module rule
  are those of its actual underlying complex and action chain map.
- Degree-zero action-preserving chain maps: these are precisely morphisms in
  `RightModule A`, using the existing `Mod` category.
- Homotopy quotient: `homotopyRel A` requires `Homotopy` of the underlying chain maps,
  together with right A-linearity of each degree-minus-one component. The `Homotopy`
  commutation equation is f-g=dh+hd. Its `zero` equation makes all other degrees zero.
  `HEq` only transports between the equal degrees p+q-1 and (p-1)+q.
  `HomotopyCategory A` is `CategoryTheory.Quotient (homotopyRel A)`; it is not the
  homotopy category of complexes of modules over the underlying ungraded ring.
  Homotopy is already an additive compositional equivalence relation, so the general
  quotient's equivalence/composition closure identifies exactly these homotopies.
- Shifts: `HomotopyStructure.shifts_exist`, `shiftIso`, and `shift_natural` use the
  landed `ShiftComparison`. Its underlying complex is the integer cochain shift
  with differential (-1)^k d, and its action equation preserves the unchanged right
  action. This covers all integers and all dg maps, not just objects up to replacement.
- Cones: `cones_exist` and the landed `ConeComparison` fix the actual underlying
  mapping cone, both component actions, inclusion and connecting arrow. Mathlib orders
  its components as M[1] then N, rather than N then M[1]; the differential is
  (-d_M x, f x+d_N y), and its triangle uses the negative first projection.
  Thus swapping the coordinates gives exactly the node's (y,x) and -p convention.
- Distinguished triangles: `HomotopyStructure.distinguished_iff` is an iff with
  isomorphisms to precisely those cone triangles in the fixed homotopy quotient.
  An arbitrary class or arbitrary third arrow is not permitted.
- Triangulated category: the existentially supplied `HomotopyStructure A` includes
  canonical addition, zero, additive shift and `Pretriangulated`, i.e. TR1--TR3.
  The first conjunct of `HomotopyStructure.AcyclicLocalization` is Mathlib
  `IsTriangulated (HomotopyCategory A)`, i.e. TR4. The dg-module preadditive structure
  is pinned by the additive faithful underlying functor; quotient addition is pinned
  by the full additive quotient functor.
- Acyclic modules in every degree: `homotopyAcyclic A` applies `.Acyclic` to the
  actual underlying complex of `M.as`. This is all-degree cohomology vanishing,
  equivalently the kernel/image quotient in the statement, without extra boundedness.
- Strict fullness: the second conjunct is `(homotopyAcyclic A).IsClosedUnderIsomorphisms`.
- Full triangulated subcategory: an `ObjectProperty` has its canonical full subcategory;
  the third conjunct is `(homotopyAcyclic A).IsTriangulated`, the dependency's recorded
  Mathlib class (zero, all shifts, and the middle-object triangle closure).
- The class W_E: the fourth conjunct uses `(homotopyAcyclic A).trW`, whose definition
  is exactly the existential distinguished triangle with specified first arrow and
  acyclic third object. Its equality with `fun _ _ f => ∀ n, IsIso (...)` is equality
  of morphism classes. `cohomology_factors` fixes these functors on every dg map
  to the actual underlying cohomology functors; it does not use arbitrary functors.
- No other hypothesis is present: modules and A may be unbounded, noncommutative,
  non-flat, infinite or zero.

Dependency declarations read and used:

- def-weil-size-convention is the recorded metatheoretic convention, with no module.
- def-weil-triangulated-category: `CategoryTheory.Pretriangulated` in
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated` and `CategoryTheory.IsTriangulated`
  in `Mathlib.CategoryTheory.Triangulated.Triangulated`.
- def-weil-triangulated-subcategory: `CategoryTheory.ObjectProperty.IsTriangulated`
  and `ObjectProperty.trW` in `Mathlib.CategoryTheory.Triangulated.Subcategory`.
- The new node imports `Sheaf.CategoryTheory.DgAlgebraDerivedCategory`, owned by
  def-sfb-dg-derived-category. Its live server source was read with `scompile.py --source`.
  Reused declarations: `DgAlgebra.Algebra`, `RightModule`, `underlying`, `act`,
  `ShiftComparison`, `ConeComparison`. No assumption `DerivedStructure A` is used.
- Proof dependency lem-sf-triangle-morphism-iso uses `Pretriangulated.isIso₃_of_isIso₁₂`
  and its other two variants in the publicly imported Mathlib pretriangulation module.
  The cone-rotation and composite-cone-contraction proof dependencies have no Lean
  record or Mathlib match yet; their statements were read. There is no stated module
  to import. They remain in proof_deps and are named in the proof docstring.

Edge cases checked before writing:

- A and modules equal to zero: zero rings are permitted by Mon, no Nontrivial binder
  appears, and the all-degree acyclic predicate includes the zero module.
- f=identity: its cone contracts by (y,x) maps to (0,y); the signed triangle is TR1.
- f=0: the cone is N plus M[1]; it is acyclic exactly when both are, as the class
  equality requires. For zero source or target this reduces to the same vanishing test.
- Multiplication by 2 on the degree-zero integral regular module is not a
  cohomology isomorphism; its cone has nonzero cohomology, so it is excluded from W_E.
- Shifts k=0, k=1, k=-1 and arbitrary negative degrees retain the unchanged right
  action. The Leibniz sign is (-1)^degree(m), not a sign from degree(a).
- The cone's connecting arrow is -p, not p; the reused comparison's defining
  equation and Mathlib's `mappingCone.triangle` use precisely the negative projection.
- No empty-index issue is introduced: only finite sums in cones are required.

Searches before construction (raw service results are in the new node's mathlib_searches):

1. msearch LeanFinder: homotopy category of differential graded right modules,
   triangulation, acyclic cone class and quasi-isomorphisms. Eight hits were ordinary
   HomotopyCategory/DerivedCategory results, not the dg-module quotient for arbitrary A.
2. msearch Loogle: `"DGModule", "HomotopyCategory"`: zero hits.
3. msearch grep: `DGModule|DGAlgebra|DifferentialGraded|dgModule|dgAlgebra`: zero hits.
4. msearch LeanSearch: differential graded module homotopy quotient by A-linear
   degree-minus-one cochains. Eight hits supplied ordinary Homotopy, the general
   quotient and underlying-complex homotopy category, not action-linear homotopies.
5. msearch grep `HomotopyStructure|homotopyRel|DgAlgebra`: only abstract model-category
   left/right homotopy hits, not the specified dg-module construction.
6. rg over live Sheaf, WeilConjectures, upstream names and definition-node statements,
   plus the requested item-id upstream grep: the recently landed DG derived definition
   is reused. SmallDgCategory is a dg-category notion and not this quotient. No
   existing theorem states the item. `blueprint_refs.py search 'dg homotopy'` found
   no blueprint node. The ancestor command reports inherited blueprint.from.node=None;
   the new node preserves it and prepends this item to its inherited via chain.

No statement correction, disputed statement or dependency repair is needed.
The only item changes are its lean record and the added new-definition stmt_dep.
Both delivered modules compiled separately through scompile.py against the live build;
no errors or non-sorry warnings were reported. The theorem docstring includes all nine
proof steps, including the direct cycle computation and arbitrary-cone reduction.

## New nodes

`def-sfb-dg-homotopy-structure` defines the actual A-linear homotopy relation,
quotient category, quotient functor, acyclic object predicate, and the standard
pretriangulation datum. Source: Stacks dga, definition-homotopy, definition-shift,
definition-cone, section-distinguished, Tags 09KH and 09KW. The datum only specifies
what the structure is; its existence is asserted by the item's theorem. It does not
assume any conclusion on A. The underlying dg modules, action, shift and cone
comparisons are imported from def-sfb-dg-derived-category rather than duplicated.
The searches above distinguish this quotient from ordinary complex homotopy categories,
the existing derived localization, and abstract enriched dg-category definitions.
Its node is in the item's chapter, with real Lean definitions and no postponed theorem.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

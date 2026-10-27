## Worker report

The module `Sheaf.AlgebraicGeometry.DmCoarseProperLocallyQuasiFinite` states
`AlgebraicGeometry.dmCoarseProperLocallyQuasiFinite`. Its only theorem has
`by sorry`; its docstring retains the node's complete seven-step proof.
There are no definitions, new nodes, dependency modules or statement corrections.

Hypothesis and clause correspondence:

- `(k : Type u) [Field k]` is the field, with base `Spec (.of k)`.
- `X : BasedCategory.{v, w} (Over (Spec (.of k)))` is the category over k-schemes;
  its object and morphism universes are explicitly bound and independent.
- `hX : IsDeligneMumfordModuliStack X` gives stack descent, an algebraic-space
  diagonal and a surjective etale scheme atlas, with actual base-change maps.
- `hft : HasFiniteTypeEtaleModuliAtlas X` expresses finite type over the field:
  an etale surjective atlas whose structure morphism is locally of finite type
  and quasi-compact. The empty atlas is allowed.
- `hdiag : HasFiniteModuliDiagonal X` requires scheme representatives for every
  two-scheme test, with both projections identified and finite induced map to
  their product. It is the finite diagonal, not just finite point stabilizers.
- `Q : Over (Spec (.of k))` is the specified k-scheme, and `q : BasedFunctor X
  (discreteModuli (yoneda.obj Q))` is the given morphism to its functor of points.
- `hq : IsCoarseModuliScheme X Q q` is initiality into every algebraic space
  and bijectivity of q's induced map on isomorphism classes over every
  algebraically closed field. Both concern this same q.
- `IsProperModuliMap q` is local finite type, quasi-compactness, universal
  closedness on the actual base changes, and proper relative diagonal.
  Thus finite type and all of the properness clauses in the node are retained.
- `IsLocallyQuasiFiniteModuliMap q` is local finite type, locally quasi-finite
  relative diagonal by algebraic-space tests, and discrete field-fibre points.
  It expresses discreteness by closed complements of singletons. The field is
  arbitrary, and every map of its spectrum to Q is tested.
- The reused `ModuliPoints` identifies field objects by the relation generated
  by arrows; `ModuliPointIsClosed` detects closed sets on etale atlases, and
  `moduliPointMap` is induced by the actual functor. These are Q01's intrinsic
  predicates, used also by the downstream composition theorem.
- No representability of q, tameness, linear reductivity, characteristic
  restriction, perfectness of k or separatedness of Q/k is assumed.

Dependency declarations used (read in their recorded source modules):

- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.IsProperModuliMap`, `IsLocallyQuasiFiniteModuliMap`,
  `ModuliPoints`, `ModuliPointIsClosed`, `moduliPointMap`,
  `IsLocallyFiniteTypeModuliMap`, `IsQuasiCompactModuliMap`,
  `IsUniversallyClosedModuliMap`, `ModuliSchemeTest`, `ModuliSpaceTest`,
  and `moduliRelativeDiagonal`.
- `Sheaf.AlgebraicGeometry.FiniteStackSchemeTests`:
  `CategoryTheory.HasFiniteTypeEtaleModuliAtlas`, `HasFiniteModuliDiagonal`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids` (publicly imported
  through the two modules above): `CategoryTheory.IsDeligneMumfordModuliStack`,
  `IsCoarseModuliScheme`, `discreteModuli`, `BasedFunctor` and the 2-fibre products.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`;
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`, including local finite type.
- Mathlib `Field` is the `mathlib_match` of `def-weil-field`; no replacement node.

The existing finite/quasi-finite proof imports remain private:
`WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite` and
`WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite`.
The local finite-type cancellation is available through the finite-type import.
The Keel--Mori proof node remains referenced in the proof docstring; it has no
recorded module to import. No proof or auxiliary theorem is invented here.

Source checks: local `literature/stacks-project/stacks-more-morphisms.tex`,
`theorem-keel-mori` (0DUT), gives the separated, quasi-compact universal
homeomorphism. Local `stacks-morphisms.tex`, `definition-proper` (0CL5) and
`definition-locally-quasi-finite` (06PU), give the conclusion clauses. The
statement is the finite-diagonal DM consequence described by the node, not
an assertion that the coarse map is representable.

Edge cases reread: empty source and empty coarse scheme; schemes as discrete
stacks and their identity coarse maps; BG for finite constant G, including
p-groups in characteristic p; imperfect and non-algebraically closed field
fibres; nonseparated coarse schemes; nonreduced tests; independent total-category
universes. These require no additional hypotheses and none was added.
No STATEMENT-DISPUTED or mathematical node fault was found.

Searches retained from the original packet: msearch.py LeanFinder on the exact
coarse-morphism assertion returned scheme finite/proper/quasi-finite results;
Loogle on `AlgebraicGeometry.IsProper, AlgebraicGeometry.LocallyQuasiFinite`
returned scheme predicates; Mathlib grep on
`CoarseModuli|DeligneMumford|ProperModuli|ModuliPoint` found no stack analogue.
The packet's logged searches remain in the sandbox. These old results do not
establish current absence: the repair's fresh DAG and Sheaf source inspection
finds `def-sfb-dm-stack-morphism-properties`, landed by Q01, with exactly the
required point and morphism notions. Fresh rg for this item/declaration in
WeilConjectures and Sheaf finds the downstream proof citation, but no existing
theorem stating the item. Q01's definitions are reused without copies.

## Returned-delivery repair

The return on immutable head `b096141f1526` identified H12/H4: our two helper
nodes duplicated Q01's definitions, already landed in `7b4b850d` and present
in the delivery parent's history. The required initial dry run of the retained
packet passed (`63972ea696b`), but its passing mechanical checks did not repair
the independently identified duplication. The explicit return was therefore
applied before another delivery:

- Removed the sandbox nodes `def-sfb-moduli-point-topology` and
  `def-sfb-scheme-target-moduli-properties` and their two Lean modules.
- Replaced the latter id in the item's `stmt_deps` by
  `def-sfb-dm-stack-morphism-properties`; retained the existing finite-stack
  scheme-test dependency needed for the hypotheses.
- Publicly imported `Sheaf.AlgebraicGeometry.DmStackMorphismProperties` and
  `Sheaf.AlgebraicGeometry.FiniteStackSchemeTests`.
- Changed the conclusion to `IsProperModuliMap q ∧ IsLocallyQuasiFiniteModuliMap q`.
- Updated `lean.statement` verbatim from the file and the UTC date. The node's
  mathematical statement, hypotheses, source and proof remain unchanged.

The downstream `lem-sfb-inertia-free-finite-cover-coarse` invokes this item
and `lem-sfb-stack-proper-locally-quasifinite-composition`. Inspection of
`proper_locallyQuasiFinite_moduli_comp` confirms that it now receives exactly
the same predicates, rather than a second definition of them.

## Second reading by Q69

Self-check of the repaired node, declaration and imported definitions: every
hypothesis and conclusion clause matches the correspondence above. The defect
found by the maintainer's independent reading was the duplicated predicate
interface; both duplicate constructions and nodes are removed, and the theorem
now returns Q01's predicates. The original seven-step proof docstring and the
single sorry remain. All variables and universes are explicitly bound, the
signature record is verbatim, and only lean and the authorized dependency
additions differ from the current main node. No separate worker was started,
as the dispatch brief forbids additional agents. The maintainer supplies the
independent delivery review.

Validation: the repaired module compiled through scompile.py both as a sandbox
and under its library module name, with exit code 0 and no errors or warnings.
The packet self-check confirms exactly one Lean module and one node, one
expected sorry, lines at most 100 characters, a verbatim signature record, and
only lean and the authorized landed dependency additions changed against main.

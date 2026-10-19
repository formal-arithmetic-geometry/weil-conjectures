## Worker report

Repair of the stage-2 return on immutable head 5ae0d1e80fba. H1 is repaired by the
new module `lean/Sheaf/AlgebraicGeometry/ProperBirationalCurveFinite.lean`, containing
exactly one theorem, `AlgebraicGeometry.isFinite_of_isProper_birational_curve`, with
`by sorry` as its whole proof. H2 is repaired by taking the current main-branch node
unchanged except for its `lean` record: there is no `split_report.summary` edit and
no stage-1 re-split. The retained sandbox initially contained only dispatcher markers,
so there was no delivered Lean source to preserve. The delivery wrapper rebases this
packet on current `newtargets-dag`.

The module and theorem docstrings cite Stacks Varieties 0AB6/0AB7 and More on
Morphisms 02LS, carry the item's blueprint id, and give both proof steps. Step 1
uses finite type over a field to obtain a Noetherian target, the dimension-one
local-ring bound, and the finite generic extension to apply 0AB6 (the node
`lem-trf-birational-curve-quasifinite`). Step 2 applies proper plus locally
quasi-finite implies finite. Nothing is proved at this stage.

Clause-by-clause correspondence:

- Field: `{k : Type u} [Field k]`.
- Schemes: `{C E : Scheme.{u}}`; the common universe includes every pair in the
  project's scheme category, with an arbitrary universe `u` explicitly declared.
- Over k: `[C.Over (Spec (.of k))] [E.Over (Spec (.of k))]`.
- Integral: `[IsIntegral C] [IsIntegral E]`. This includes nonemptiness,
  reducedness, and irreducibility through the recorded Mathlib definition.
- Separated over k: `IsSeparated (C ↘ Spec (.of k))` and the corresponding
  instance for E, on the two structure morphisms.
- Finite type over k: `LocallyOfFiniteType` together with `QuasiCompact` for
  each structure morphism; neither global quasi-compactness condition is omitted.
- Dimension exactly one for both: `hdimC : topologicalKrullDim C = 1` and
  `hdimE : topologicalKrullDim E = 1`.
- The given map: `(p : E ⟶ C)`.
- It is a k-morphism: `[p.IsOver (Spec (.of k))]`, the commuting structure triangle.
- Proper: `[IsProper p]`, the recorded proper-morphism definition.
- Dominant: `[IsDominant p]`, dense range of the underlying map.
- The induced function-field map is an isomorphism: `hbirational` states
  `Function.Bijective` for the actual map `p.stalkMap (genericPoint E)`, whose
  target is `E.functionField`. Its source is `C.presheaf.stalk (p (genericPoint E))`.
  Dominance of a map of irreducible schemes sends the generic point to the generic
  point: continuity puts the image in the closure of that image point; density
  makes this closure all of C; sobriety gives uniqueness. Thus the source is
  canonically `C.functionField`. A bijective commutative-ring homomorphism is
  precisely a ring isomorphism; the hypothesis is about the induced map, not an
  unrelated field isomorphism. This is the same canonical-stalk-map formulation
  as the accepted parent `isIso_of_isProper_birational_normal_curve`.
- Conclusion: `IsFinite p`, without any further conclusion or hypothesis.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (available transitively).
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  `Mathlib.AlgebraicGeometry.Properties`, available through FunctionField.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim`,
  `Mathlib.Topology.KrullDimension`.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` and `IsSeparated`,
  `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its Separated import.
- `def-sc-function-field`: recorded module `Sheaf.AlgebraicGeometry.FunctionField`
  is imported publicly; its documented integral-scheme clause uses Mathlib's
  `AlgebraicGeometry.Scheme.functionField`, the generic stalk. The product over
  components is for the general nonintegral clause and is unnecessary here.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`, public through Proper.
- Supporting Mathlib notions are `LocallyOfFiniteType`, `QuasiCompact`,
  `IsDominant`, and `Scheme.Hom.stalkMap`; their source signatures and docstrings
  were read. No private replacement definition is introduced.
- Proof-only imports are `Mathlib.AlgebraicGeometry.Noetherian` for
  `LocallyOfFiniteType.isLocallyNoetherian` and the quasi-compactness result,
  `Mathlib.AlgebraicGeometry.ZariskisMainTheorem` for
  `IsFinite.of_isProper_of_locallyQuasiFinite`, and the recorded
  `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism` for `pqf-def-quasifinite`.
  The latter includes local finite type; properness supplies it, so the
  difference from Mathlib's fibre-discreteness predicate causes no loss.
  `lem-trf-birational-curve-quasifinite` has no Lean record in the read snapshot,
  so no nonexistent proof-only module was imported. It is not needed to type
  this theorem and its future proof import is the maintainer's bookkeeping.

Source and edge-case checks: opened `varieties.tex`, labels
`lemma-quasi-finite-in-codim-1` and `lemma-finite-in-codim-1`, and the current
blueprint ancestor proof. The local dimension bound and finite generic extension
match 0AB6 condition (1), and 0AB7 gives the stated finiteness on target open
neighbourhoods. Identity on an integral curve is covered. Normalization of a cusp
is covered and shows why neither normality of C nor smoothness was added. An open
immersion of a punctured affine line is excluded by properness. A blow-up of an
integral surface is excluded by the dimension equations. Constant maps are
excluded by dominance. The empty scheme is excluded by integrality, as in the
node, and a point by dimension one. Positive characteristic and imperfect fields
remain allowed; no perfection, algebraic closure, normality, or smoothness was
assumed. No statement correction or disputed statement is needed.

Searches performed for this repair (the msearch wrappers record their raw results):

- LeanFinder: "A proper dominant morphism between integral one dimensional
  separated schemes of finite type over a field inducing an isomorphism of
  function fields is finite". Eight hits: global-section finiteness,
  IsFinite, finite maps proper/integral, and normalization dominance. None is
  the curve theorem.
- LeanSearch: "A proper birational morphism between integral curves over a field
  is finite". Eight hits: IsProper, IsFinite, proper-affine and integral-finite-type
  characterizations. None supplies the dimension-one theorem.
- Loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.IsProper`. Nine hits,
  including `IsFinite.of_isProper_of_locallyQuasiFinite`, which supplies only
  proof Step 2 and requires local quasi-finiteness, not the curve hypotheses.
- msearch grep: `birational|Birational` in Mathlib/AlgebraicGeometry. Eight
  returned hits, in RationalMap and Birational modules. They define birationality
  of schemes through partial isomorphisms and do not state this finiteness result.
- Direct `rg` for `proper.*birational|birational.*finite|isFinite_of_isProper_birational`
  in upstream WeilConjectures, the side Sheaf library, and the upstream name index.
  The existing side normal-curve theorem adds normality and concludes IsIso; it
  is a consumer of this node, not an exact match. Normalization's birationality
  theorem is about its particular canonical map, not arbitrary proper curve maps.
- Direct `rg` for the item id in upstream WeilConjectures found no declaration.
  Direct `rg` for the proposed full theorem name in upstream and Mathlib found
  no collision. The node's existing Mathlib search records were preserved.

## Second reading by Q55

I reopened the completed module and the current node for a separate clause-by-clause
reading after writing the statement. This is a second pass by the author; no other
agent was started, as the dispatch brief requires. The maintainer supplies the
independent review.

I checked that both scheme structure maps, not p alone, have separatedness and
finite type; that finite type includes both local finite type and quasi-compactness;
that integrality and dimension one occur for both C and E; and that the conclusion
is finiteness of the given p. I checked the field, common Spec k, commuting triangle,
properness, and dominance binders. I inspected the `stalkMap` signature and the
`functionField` abbreviation again: the target is definitionally the generic stalk
of E and the source becomes the generic stalk of C by dominance. Bijectivity is
therefore the required isomorphism of the induced map, with no extra arbitrary map.
No normality, perfection, smoothness, projectivity, or field extension finiteness
assumption beyond the required isomorphism was inserted. All variables and the
universe are explicit; there are no local definitions, extra theorems, or hidden
proof obligations. The theorem body is only sorry.

No mathematical mismatch was found in this second pass. The node comparison shows
only `lean` differs from current main; in particular H2's split-report edit is gone.
The Lean record is extracted verbatim from the declaration keyword through the
signature before `:=`, preserving newlines. The module has the required source and
blueprint docstrings and both proof steps, repairing H1 rather than re-pushing the
stage-1 packet. Compilation and server preflight results are recorded below.

Validation: `scompile.py Q55 lem-trf-proper-birational-curve-finite` passed both
sandbox and library-path compiles with exit 0, no errors or warnings (23.2 s and
33.5 s in the initial run). A local text check confirmed one theorem with one
sorry, line widths at most 100, and an exactly verbatim signature in `lean.statement`.
`deliver2.py Q55 lem-trf-proper-birational-curve-finite --no-push` then compiled
the file again and reported `OK (dry run): commit 0ab0baa014 passes the preflight
and compiles; nothing pushed`. Its staged set was exactly the module, item node,
and this stage-2 report. No extra node or dependency module is delivered.

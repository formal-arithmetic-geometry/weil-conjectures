## Worker report

The delivery states `AlgebraicGeometry.Scheme.CommAlgebraSheaf.directed_colimit_finiteType`
in `Sheaf.AlgebraicGeometry.AlgebraDirectedColimitFiniteType`. Its only theorem has proof
`by sorry`. The definitions are complete and contain no postponed data or proofs.
The existing node's statement, proof, and proof dependencies are unchanged; `stmt_deps`
gains the two definition nodes described below.

Source: [Stacks 05JT](https://stacks.math.columbia.edu/tag/05JT), statement and proof,
and [05JS](https://stacks.math.columbia.edu/tag/05JS), especially the symmetric-algebra
construction in its proof. The local `literature/stacks-project/properties.tex` is absent,
so those source pages were read online. The node's expanded four-step proof is reproduced
in the theorem docstring, with every proof dependency named.

Hypothesis and clause correspondence:

- A scheme X: `(X : Scheme.{uC})`, using Mathlib `AlgebraicGeometry.Scheme`.
- Quasi-compact X: `[CompactSpace X]`, Mathlib's quasi-compact topological-space predicate.
- Quasi-separated X: `[QuasiSeparatedSpace X]`, expressing quasi-compact intersections
  of affine opens; no separation or Noetherian hypothesis is added.
- A sheaf of commutative O_X-algebras: `(A : X.CommAlgebraSheaf)`. This is
  `Under X.sheaf` in the category of sheaves of commutative rings on all opens of X.
  `A.hom` is the structure map, `A.right` the ring sheaf. Its morphisms are algebra maps,
  since the under-category triangle forces compatibility with O_X.
- Quasi-coherent underlying module: `(hA : A.toModule.IsQuasicoherent)`.
  `toModule` restricts the rank-one module of the algebra ring sheaf along `A.hom`,
  using Mathlib `SheafOfModules.restrictScalars` and `SheafOfModules.unit`.
- Subalgebras are `Subobject A` in this algebra-sheaf category. A monomorphism of
  commutative ring sheaves is sectionwise injective, so these subobjects correspond
  precisely to subsheaves closed under the commutative algebra operations; there is
  no quotient-algebra interpretation. Representatives chosen by `Subobject.underlying`
  differ only by isomorphisms commuting with the inclusion into A.
- Sigma is exactly `A.finiteTypeQuasiCoherentSubalgebras`: the subtype with
  `(toModule (B : X.CommAlgebraSheaf)).IsQuasicoherent` and, for every affine U,
  `((B.hom.hom.app (op U)).hom).FiniteType`. Here `RingHom.FiniteType` means the
  target is finitely generated as an algebra for that specific structure map.
  Finite generation of the underlying module is not imposed.
- Sigma is ordered by inclusion: it inherits `Subobject A`'s partial order.
  `finiteTypeQuasiCoherentSubalgebraDiagram` is its monotone inclusion into
  `Subobject A`, followed by `Subobject.underlying`. Its maps are the inclusions.
- Conclusion (a): `Nonempty Sigma ∧ Directed (· ≤ ·) (fun B : Sigma ↦ B)`.
  `Directed` states the existence of a common upper bound for any pair, with no
  hidden nonempty-index assumption replacing the explicit nonemptiness conclusion.
- Conclusion (b): an existential `c : Cocone A.finiteTypeQuasiCoherentSubalgebraDiagram`,
  `h : c.pt = A`, `Nonempty (IsColimit c)`, and, for each B,
  `c.ι.app B ≫ eqToHom h = Subobject.arrow B.val`. These equalities identify the
  cocone maps with the actual inclusions. This is the universal property saying
  the inclusions exhibit A as the colimit in ALL algebra sheaves, equivalently
  that the canonical map from any chosen colimit to A is an isomorphism. The
  ambient category is not restricted to quasi-coherent or finite type objects.
  No separate existence hypothesis for a chosen colimit has been added.
- Conclusion (c): for every `U : X.Opens` with `IsAffineOpen U`, and every
  `a : A.right.obj.obj (op U)`, there exist B in Sigma and a section b of B over U
  satisfying `(Subobject.arrow B.val).right.hom.app (op U) b = a`.
  This is membership in the included subalgebra on sections, independently of
  the arbitrary representative chosen for B.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `AlgebraicGeometry.Scheme.Hom` (full definition and source docstrings read).
- `def-weil-pbc-scheme-conventions`: a convention record, not a declaration;
  `CompactSpace` and `QuasiSeparatedSpace` supply exactly the two properties needed.
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` explicitly relates the latter
  to quasi-separatedness of the structure morphism.
- `def-weil-sheaf-of-modules-category`: `Mathlib.Algebra.Category.ModuleCat.Sheaf`,
  `SheafOfModules`, its structure and category; restriction of scalars in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.Coherent` was opened and read in full.
  Its docstring explicitly assigns quasi-coherence to Mathlib's
  `SheafOfModules.IsQuasicoherent`; its recorded `RingedSpace.IsCoherent` realizes
  the coherent clause, which this item does not use. Accordingly the module imports
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent` and uses the shared
  quasi-coherence predicate, without inventing a new specialization or importing
  the unused coherent predicate. Its full definition and docstring were read.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone` and `IsColimit`
  (both listed in this node's `lean.declarations`) are used to state the colimit
  without a chosen-colimit binder. Their structures and the `colimit` definition
  in `Mathlib.CategoryTheory.Limits.HasLimits` were read.

Additional Mathlib constructions are `CategoryTheory.Under` (objects and morphisms),
`Subobject` (isomorphism classes of monomorphisms, partial order, underlying functor
and arrow), `Monotone.functor`, `sheafCompose`, and `RingHom.FiniteType`.
No dependency module is necessary: all required dependency notions are usable.

Edge cases checked before writing:

- The empty scheme is allowed. Quasi-compactness and quasi-separatedness hold;
  its algebra sheaf has the singleton ring on the empty open and the unique
  subalgebra gives a nonempty Sigma. The empty open is included in clause (c).
- The zero algebra sheaf is allowed. The theorem has no nontriviality or domain
  assumptions; its subalgebra is a finite type quotient of O_X.
- A itself need not be finite type, and the set of subalgebras need not be finite.
  Sigma includes all finite type quasi-coherent subalgebras, not a selected cofinal
  family. The conclusion proves nonemptiness, rather than assuming it.
- Finite type is algebra finiteness: a polynomial algebra can qualify without
  being finite as an O_X-module. No finite-presentation condition is imposed.
- Arbitrary characteristic and non-Noetherian qcqs schemes are retained.
- All scheme and section universes are explicitly bound. The subobject index type
  is the canonical set supplied by Mathlib (in `Type (uC+1)`), not an independent
  smaller index universe or an arbitrary diagram assumed to have a colimit.
  `IsColimit` of this particular diagram states the universal property directly.

Searches performed with `/home/ubuntu/weil-launcher/msearch.py`:

- LeanFinder: "quasi coherent sheaf of algebras is directed colimit of finite type
  subalgebras" returned module finite-type and quasi-coherence declarations,
  including `SheafOfModules.IsFiniteType`; no algebra-sheaf theorem.
- Loogle: `Subalgebra.FG, Directed` returned zero hits.
- Grep: `SheafOfAlgebras|AlgebraSheaf|sheaf.*algebra|algebra.*sheaf` in `Algebra`
  returned module-sheaf imports only, no algebra-sheaf category.
- LeanSearch: "sheaf of commutative algebras underlying module subalgebra finite type
  quasi coherent", and both new-node queries, returned `UNAVAILABLE 0 hit(s)`,
  `service unavailable: Internal Server Error`. No negative mathematical conclusion
  is inferred from this outage. The required verdict metadata is recorded solely
  as "unavailable (no mathematical search verdict)".
- LeanFinder for algebra sheaves and underlying modules returned
  `SheafOfModules.restrictScalars` and its object lemma, `forget`, `toSheaf`,
  `Scheme.Modules.toPresheaf`, `toPresheafOfModules`, `SheafOfModules.val`,
  and `Scheme.Modules.toPresheaf_obj`. These supply the module construction, not
  a duplicate algebra-sheaf definition.
- LeanFinder for finite type quasi-coherent subalgebras returned eight module
  finiteness / presentation declarations, with no algebra subobject family.
- `rg` in pinned Mathlib, `WeilConjectures`, and `lean/Sheaf` for
  `SheafOfAlgebras|CommAlgebraSheaf|finiteTypeQuasiCoherentSubalgebras|quasi.?coherent.*[Ss]ubalgebra`
  found no implementing declarations. The exact item's id was also searched
  in `WeilConjectures`, with no match. DAG hits use the algebra notions in
  statement nodes, rather than providing separate definition nodes.
- `tools/blueprint_refs.py search 'algebra sheaf'` found only the specific Rees
  algebra definition. The search for `subalgebra` found ring-level/Lie-algebra
  nodes and ring-level directed-union statements, not this sheaf notion.
  Neither `def-pc-derived-category-qcoh-algebra` (derived modules) nor the Rees
  algebra node supplies the category or subalgebra set defined here.

Server validation: `scompile.py` compiled all three sibling modules together,
using their actual dependency order, in 2.6 seconds, with exit code 0 and no errors
or warnings. The delivery dry run is the final mechanical check. No mathematical
statement fault or disputed statement was found.

## New nodes

`def-weil-pbc-comm-algebra-sheaf`: the category of commutative O_X-algebra sheaves,
encoded by `Under X.sheaf`, with its underlying module obtained by restriction
of scalars from the algebra's rank-one module. Source is the algebra notion in
Stacks 05JT. The module uses Mathlib's existing generic category and module
constructions. This is an abbreviation and a module construction, not a private
implementation of sheaves, algebra maps, or modules. Its searches found the
restriction-of-scalars tools but no existing specialized algebra-sheaf declaration
or DAG definition node. The record names both declarations in its module.

`def-weil-pbc-finite-type-quasi-coherent-subalgebras`: the set Sigma and its
inclusion diagram, using Mathlib subobjects, quasi-coherence, and sectionwise
ring-map finite type on affine opens. Source is Stacks 05JT and the preceding
finite-type definition. Searches found module-finiteness declarations and
ring-level subalgebras, not this sheaf-algebra set. It depends on the new
algebra-sheaf node and the existing scheme and quasi-coherence notions. Its
record names the subtype and diagram declarations.

## Second reading by F1

I independently opened the item node, all three delivered modules, both new node
records, and the statement dependencies. Verdict: the Lean states exactly the
node's assertion. No mathematical, signature, definition, or docstring repair
was needed; this reading adds only this report section.

Source check: the local properties.tex is absent. I read the raw Stacks
properties.tex at https://raw.githubusercontent.com/stacks/stacks-project/master/properties.tex,
the paragraph immediately before `lemma-algebra-directed-colimit-finite-type`,
that lemma and its proof, and the preceding 05JS proof. I also checked the pages
https://stacks.math.columbia.edu/tag/05JT and https://stacks.math.columbia.edu/tag/05JS.
The source introduces an arbitrary scheme and explicitly assumes quasi-compactness
and quasi-separatedness. There is no standing field, characteristic, Noetherian,
separatedness, or finite-presentation assumption. The preceding definition is
finite generation as an algebra on every affine open. The node's expanded clauses
(a)-(c) and its four-step proof express that result without changing its strength.

Object, hypothesis, and conclusion checklist (each item passes):

- Scheme X: `(X : Scheme.{uC})`. I read the recorded `def-pc-scheme`
  signature and Mathlib's scheme carrier; no affine restriction is imposed.
- Quasi-compactness: `[CompactSpace X]`, compactness without a Hausdorff
  condition. Quasi-separatedness: `[QuasiSeparatedSpace X]`; Mathlib's
  `Morphisms.QuasiSeparated` connects this space property to scheme
  quasi-separatedness. There are no additional property binders.
- Commutative algebra sheaf A: `(A : X.CommAlgebraSheaf)` unfolds to
  `Under X.sheaf`. Its structure morphism is `A.hom : X.sheaf ⟶ A.right`,
  and under-category morphisms commute with it. Thus it is precisely a sheaf
  of unital commutative O_X-algebras, rather than a module with extra unspecified
  multiplication. The open-set topology is the topology of X, not an étale site.
- Quasi-coherence of A's underlying module: `(hA : A.toModule.IsQuasicoherent)`.
  I read `SheafOfModules.unit`, `restrictScalars`, and `IsQuasicoherent`.
  The unit has A's additive sections, and restriction gives the scalar action
  through A.hom. The recorded `pqf-def-coherent` module explicitly assigns
  quasi-coherence to this Mathlib predicate (locally a cokernel of free modules,
  equivalent to the affine-local tilde form on schemes). Its separate coherent
  predicate is irrelevant here. The generic module category matches the
  `def-weil-sheaf-of-modules-category` node.
- Subalgebras B: `Subobject A` in the same under category. Subobjects are
  isomorphism classes of monomorphisms, not quotients or abstract algebra maps.
  In this category monomorphisms are exactly inclusions up to isomorphism:
  ring-sheaf monomorphisms are injective on sections, and compatibility with the
  structure map makes their images O_X-subalgebras. The usual free algebra on
  an open detects sectionwise injectivity, so passing to the under category
  does not introduce other monomorphisms. I read `Subobject.underlying`,
  `Subobject.arrow`, and `underlying_arrow`: the chosen representatives and
  transition maps commute with the actual arrows into A.
- Sigma: `A.finiteTypeQuasiCoherentSubalgebras` is the subtype of all those
  subobjects whose underlying module is quasi-coherent and whose structure
  ring map has `.FiniteType` for every `U : X.Opens` with `IsAffineOpen U`.
  This is algebra finite type, not module finite type, and not finite
  presentation. Both predicates are invariant under an algebra-sheaf
  isomorphism, so representative choice changes neither the set nor its meaning.
- Inclusion order and diagram: the inherited Subobject partial order and
  `finiteTypeQuasiCoherentSubalgebraDiagram`, the monotone inclusion followed
  by `Subobject.underlying`, give exactly B ↦ B and inclusion transitions.
- Clause (a): `Nonempty Sigma ∧ Directed (· ≤ ·) (fun B : Sigma ↦ B)`.
  This both proves nonemptiness and gives a common upper bound to every pair.
  No nonempty or directedness hypothesis is smuggled into the binders.
- Clause (b): `∃ c : Cocone ..., ∃ h : c.pt = A, Nonempty (IsColimit c) ∧
  ∀ B, c.ι.app B ≫ eqToHom h = Subobject.arrow B.val`.
  I read the recorded colimit node's `Cocone`/`IsColimit` definitions. This is
  precisely the universal property of A with its inclusions; it is equivalent
  to the canonical comparison from a chosen colimit being an isomorphism.
  The equality of cocone maps prevents an unrelated colimit presentation.
  The ambient category is all algebra sheaves, and no `HasColimit` assumption
  or smaller quasi-coherent category is substituted.
- Clause (c): `∀ U, IsAffineOpen U → ∀ a : A.right.obj.obj (op U),
  ∃ B, ∃ b, (Subobject.arrow B.val).right.hom.app (op U) b = a`.
  The quantifiers agree with the node: B may depend on the affine open and the
  section. The equation means membership in the image of the included algebra
  on sections, without requiring representatives to be literal subsets.

Edge cases: the empty scheme and empty affine open are included (their section
rings are the zero ring), as is the zero algebra; there is no `Nontrivial`
assumption. The identity subobject of the zero algebra is finite type. An empty
index family is not assumed away: Sigma's nonemptiness is part of the conclusion,
including for the empty scheme. Zero generators are permitted by ring-map finite
type, and polynomial algebras need not be finite modules. Arbitrary characteristic
and non-Noetherian qcqs schemes are retained. `uA`, `uB`, `uC` are explicit,
and instantiate compatibly at the scheme universe. The index is the canonical
Subobject subtype (not an independent small testing universe); all cocones are
on that diagram. There is no vacuous test-algebra hypothesis or free implicit
variable. No natural-number parameter occurs in the theorem.

Independent H4/H12 searches used different queries from the first worker:

- `msearch.py ... leanfinder "sheaf of rings subobjects finitely generated algebra
  filtered union on a scheme"`: eight results, all module finite-type/local
  generator declarations or a Noetherian-scheme result; no algebra-sheaf category
  or directed-colimit theorem.
- `msearch.py ... loogle '"restrictScalars"'`: twelve linear-map restriction
  results; no exact specialized algebra-sheaf declaration.
- `msearch.py ... leansearch "commutative algebra objects in ring sheaves and
  finitely generated subobjects"`: service unavailable, explicitly no negative
  mathematical verdict inferred from the outage.
- `rg -n -i 'sheaf.*(commutative.*algebra|subalgebra)|algebra.*sheaf|filtered.*algebra'`
  over Mathlib's Algebra/Category, WeilConjectures, and the repository's lean/Sheaf:
  module sheaf constructions and ring-level AlgCat filtered colimits, no match.
  Exact searches for `CommAlgebraSheaf` and
  `finiteTypeQuasiCoherentSubalgebras` over the full Mathlib and both project
  trees found no pre-existing implementing declaration.
- `tools/blueprint_refs.py search 'commutative algebra'` and `search 'subalgebra'`:
  ring-level, Lie-algebra, and coefficient-approximation nodes, no node defining
  this algebra-sheaf category or the Sigma diagram. The new notions are therefore
  not private copies of an existing definition.

New-node review: `def-weil-pbc-comm-algebra-sheaf` is self-contained, cites scheme
and module category, and states the source's algebra-sheaf notion using the
existing generic `Under`, unit, and restriction-of-scalars constructions.
`def-weil-pbc-finite-type-quasi-coherent-subalgebras` cites scheme, that new algebra
node, and quasi-coherence; its Sigma and inclusion diagram match exactly the
paragraph before 05JT and the subalgebra system in its proof. I checked both
records' source, empty proofs, search metadata, creation record, blueprint
ancestor/via, chapter/unit, audit states, and lean records against §5. Both are
new definition nodes of this delivery, and the item cites both. No dependency
module, statement correction, or disputed statement is required.

H5/H6/H8/H9 check: definition data are complete and contain no `sorry`; the only
postponed proof is the named theorem with `by sorry`. Every declaration has its
own node's source and blueprint tag. The theorem docstring preserves all four
node proof steps and names every dependency they use. Imports supply the actual
constructions, names have the upstream namespace, and all lines fit 100 columns.
The node signatures agree with the corresponding source signatures under the
preflight's whitespace normalization.

Validation: the prescribed `scompile.py` compiled all three modules together in
actual dependency order with exit code 0, no errors, and no warnings (2.7 s).
The delivery dry run and push follow this reading. No mismatch was found and no
Lean or node content was rewritten.

## Worker report

The delivery states `CategoryTheory.SheafDg.compact_exists_finiteCell_retract` in
`Sheaf.CategoryTheory.DgCompactFiniteCellRetract`. Its sole proof is `sorry`.
It defines the missing finite-cell filtration in a separate definition node/module.
There is no statement correction or disputed statement.

The source is Stacks dga.tex Tag 09R3, proposition-compact, implication (1) to (2),
read at lines 6285–6338. The opposite-algebra and left-shift signs were checked at
lines 1186–1210 and 1271–1334, including Tag 0FQ0. The node's proof is reproduced
in the theorem docstring in its five steps, including the forward telescope shift,
the reduction to one finite filtration stage, and the finite-subcell factorization.

Hypothesis and clause correspondence:

- The size convention is explicit universe `u`. Coefficient groups and the small
  coproduct index types live in `u`; the actual word localization inherits its
  larger object/morphism universe. No independent smaller test universe is used.
- An arbitrary associative unital dg algebra over Z is
  `A : Algebra (pointIntegers.{u})`. `pointIntegers` is the constant ULift Z sheaf
  on the discrete singleton category with the trivial topology. This is a site
  for the topos of a point: every presheaf is a sheaf, and evaluation at its sole
  object identifies coefficient module sheaves with integer modules. ULift only
  sets the universe and excludes no algebra. `Algebra` is precisely the existing
  monoid in cochain complexes, so d squared is zero and multiplication satisfies
  the signed Leibniz identity. It imposes no graded commutativity.
- Left dg modules, their signed shifts, homotopies and the actual localization
  D(C) are the dependency's `LeftModule`, `shift`, `Derived` and `moduleQ`,
  without a replacement category or a copied dg module definition.
- `Preadditive (Derived A)` and `HasCoproducts.{u} (Derived A)` expose the
  additive category with all small sums that the statement uses in defining
  compactness. They are structural instance parameters of that same category;
  no generator, boundedness, algebraic flatness or countability assumption is
  imposed. The theorem is independent of choices of coproduct representatives.
  In this category the direct-sum dg modules represent coproducts as specified
  in the node. There is no additional requirement of preserved coproducts.
- `M : Derived A` and `hM : IsCompactObject.{u} M` render the given compact
  object. This is the recorded compactness definition, literally bijectivity of
  the canonical direct sum of Hom groups to Hom into a coproduct, for every
  family indexed by a `Type u`.
- `∃ P : LeftModule A` gives an actual dg module, rather than just a derived
  object. `HasFiniteCellFiltration A P` supplies a natural `t`, `t+2` stages
  `F : Fin (t+2) → LeftModule A`, and the `t+1` consecutive dg inclusions.
  `F 0` is F_(-1) and `F (Fin.last (t+1))` is F_t. The former is `IsZero`;
  the latter is isomorphic to P. Composing the monomorphisms and final iso
  realizes every stage as an actual dg submodule of P.
- For each inclusion `f j`, `cokernel (f j)` is the quotient dg module,
  using the inherited cokernel action, and is isomorphic in the dg category
  to a finite coproduct indexed by `Fin n` of `shift A (k a) (regular A)`.
  Thus the filtration quotients are dg isomorphic to finite sums of integer
  shifts of C, rather than merely isomorphic after localization. The existing
  `shift` includes both the differential sign and the shifted left-action sign.
- The maps `i` and `p` have source/target M and the canonical derived image
  `(moduleQ A).obj P`. `i ≫ p = 𝟙 M` is exactly p composed with i equals 1_M.
- Zero modules are allowed: take t=0, both filtration stages zero and n=0.
  Empty layers, arbitrary signed shifts, and repeated filtration stages are
  permitted. There is no bound on the algebra's degrees or its cardinality.

Dependency declarations used:

- `Sheaf.CategoryTheory.SheafDgModuleLocalization`:
  `CategoryTheory.SheafDg.Algebra`, `LeftModule`, `Derived`, `moduleQ`,
  `regular` and `shift`; the recorded module was read in full at the relevant
  definitions, including the shifted-action characterization and localization.
- `WeilConjectures.CategoryTheory.CompactObject`:
  `CategoryTheory.IsCompactObject`, read with its complete signature and body.
  The old example under Sheaf is withdrawn, so the recorded upstream module is
  imported directly.
- The size-convention node has a metatheoretic `convention: true` record and no
  declaration; the explicit universe above is its rendering.
- Mathlib `CategoryTheory.Mod` supplies the finite coproducts and cokernels of
  module objects through the existing imports. These are the actual quotient
  and direct-sum constructions. `Presheaf.isSheaf_bot` supplies the proof in
  the fully constructed point coefficient sheaf.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated` is a proof-only import
  for `lem-weil-pbc-hom-into-triangle-exact`, whose recorded Mathlib match is
  `Pretriangulated.Triangle.coyoneda_exact₂` (and the companion clauses listed
  in its mathlib_match). The other proof dependencies have no recorded modules
  in the inspected live DAG, so their imports are deferred.

Searches actually run:

- msearch LeanFinder: “Compact object in derived category of differential graded
  modules is a retract of a finite cell module”: eight ordinary derived-category
  bounded-representative/fraction results, no dg finite-cell retract theorem.
- msearch Loogle: `"IsCompactObject", "Retract"`: zero hits.
- msearch grep: `finiteCell|FiniteCell|compact.*finite.*cell`: zero hits.
- msearch LeanSearch: “A dg module with a finite filtration whose successive
  quotients are finite direct sums of shifts of the regular dg module”: eight
  ordinary filtered-module/ideal results, no dg filtration notion.
- msearch LeanFinder: “finite cell differential graded module finite filtration
  quotients shifts”: eight ordinary filtration/filtered-colimit results.
- rg of Sheaf, WeilConjectures, Mathlib and dag/lean_names_upstream.json for the
  finite-cell terminology and chosen declaration names found no existing match.
  The separate right-module DgAlgebra interface was read; it does not define this
  left finite-cell filtration, so the prescribed SheafDg interface is reused.
- rg of dag/nodes and `tools/blueprint_refs.py search 'finite cell'`: zero
  blueprint matches. Relevant existing DG nodes are theorem statements or the
  different complete dual-free filtration; none defines this notion.
  `tools/blueprint_refs.py ancestor` reports None, matching the item's existing
  null blueprint ancestor; that value and its via path are inherited.

Validation: both modules compiled separately in dependency order with scompile.py;
server times were 1.7 and 1.3 seconds. The wrapper reported local disk exhaustion
and automatically confirmed against current server sources successfully. No
compiler errors or warnings other than the expected theorem sorry remain.

## New nodes

`def-sfb-dg-finite-cell-module` defines `HasFiniteCellFiltration` and its
`pointIntegers` specialization helper in `Sheaf.CategoryTheory.DgFiniteCellModule`.
It is a real existential filtration predicate over the existing dg module category,
with fully constructed coefficient sheaf and no postponed proof of a definition.
Source: Tag 09R3 (2), with Tag 0FQ0 and the left-shift convention. Its LeanSearch,
LeanFinder, Mathlib grep and project/DAG/blueprint searches are recorded above and
in mathlib_searches; no existing definition carries the notion. The item gains
only this new definition id in stmt_deps. Its own statement, proof and all other
fields remain unchanged apart from lean.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

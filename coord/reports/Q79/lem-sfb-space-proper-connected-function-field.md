## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceProperConnectedFunctionField` states
`AlgebraicGeometry.AlgebraicSpace.globalFunctions_isField_finite_of_proper_reduced_connected`.
Its sole proof is `sorry`; there are no new definitions or auxiliary theorems.
The node statement and its accepted stage-1 split are unchanged.

Source read: `literature/stacks-project/spaces-over-fields.tex`,
`lemma-proper-geometrically-reduced-global-sections` (Tag 0DMY), lines 2429 onward,
clauses (1)--(3) and their proofs. These clauses require ordinary reducedness, with
no restriction on the characteristic or separability of the resulting field.

Hypothesis and conclusion correspondence:

- The arbitrary field k is `(k : Type u) [Field k]`.
- An algebraic space over Spec k is
  `(X : AlgebraicSpace (Spec (CommRingCat.of k)))`. This is the recorded full
  subcategory of fppf sheaves with representable diagonal and an etale atlas,
  not a scheme specialization.
- The structure morphism is
  `f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec (CommRingCat.of k))))`.
  Its target is the representable base space. There is only one morphism to
  this terminal representable object over the base; f is not an arbitrary
  auxiliary map whose existence is assumed instead of a canonical construction.
- Properness is `hf : MapIsProper f`, whose definition is precisely separatedness,
  finite type, and universal closedness. Its existing chart and base-change
  quantifiers are retained.
- Reducedness is `hred : X.IsReduced`, the existing predicate requiring every
  etale scheme chart to be reduced. This is equivalent to reduced rings on all
  affine etale charts: affine opens of an etale chart are again etale charts,
  and reducedness of a scheme is affine local.
- The atlas topology is the recorded `pointTopologicalSpace` on `Point X.obj.obj`.
  `[ConnectedSpace (Point X.obj.obj)]` says exactly nonempty and connected.
- The actual ring of global functions is
  `RingCat.sectionsSubring X.smallStructureRings.obj`: compatible regular functions
  on the already defined small affine etale model, with pointwise operations.
  It computes the existing small etale structure sheaf on an affine basis,
  without a newly chosen ring or a noncanonical isomorphism as an assumption.
- The field conclusion is
  `IsField (RingCat.sectionsSubring X.smallStructureRings.obj)`.
  This predicate asserts nontriviality, commutativity and inverses for all
  nonzero elements and extends the existing ring operations.
- Finite-dimensionality over k is the second conjunct `@Module.Finite k ...`.
  The module structure is supplied explicitly by
  `(affineGlobalScalar k (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    (Iso.refl _) X f).toModule`.
  This is multiplication by the canonical pullback of each scalar on every
  chart. Over a field finite generation is exactly finite dimensionality.
  Using `RingHom.toModule` avoids introducing a second algebra/ring instance.
- No geometric reducedness, geometric connectedness, irreducibility,
  algebraic-closedness, separability, or identification of the resulting field
  with k occurs in the signature.

Recorded dependencies read and used:

- `def-weil-field`: Mathlib `Field`, from `Mathlib.Algebra.Field.Defs`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-trf-algebraic-space`: `AlgebraicGeometry.AlgebraicSpace`, `EtaleSite`,
  `structurePresheaf`, `structureSheaf`, from
  `Sheaf.AlgebraicGeometry.AlgebraicSpace`.
- `def-sfb-space-morphism-properties`: `AlgebraicGeometry.AlgebraicSpace.MapIsProper`,
  from `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`.
- `def-a1-space-point-topology`: `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace`,
  from `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`, available through
  the morphism-property imports.
- Added the already landed `def-sfb-reduced-algebraic-space` to stmt_deps and
  imported `Sheaf.AlgebraicGeometry.ReducedAlgebraicSpace`, using its `IsReduced`.
- Added the already landed `def-sfb-space-affine-global-sections` to stmt_deps and
  imported `Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections`, using
  `affineGlobalScalar` with its recorded underlying small ringed model.
  Both additions are authorized additions of landed notion nodes; neither node
  is edited. Their complete recorded declarations and docstrings were read.

The proof docstring follows both accepted steps: apply
`lem-sfb-space-proper-global-algebra-components`, then specialize its product to
one connected component. That proof dependency has no Lean record or usable
Mathlib match yet, so it has no module to import. It is not needed to elaborate
this stage-2 statement. Its proof and statement are not replaced.

Edge cases checked before writing:

- Spec k has global functions k and satisfies the statement.
- Spec L for an arbitrary finite field extension L/k is allowed, including
  purely inseparable extensions; the conclusion is L, not necessarily k.
- Two proper reduced components meeting at a point remain allowed: connectedness
  does not impose irreducibility.
- The empty space is excluded by ConnectedSpace nonemptiness.
- A disjoint union of two copies of Spec k is excluded by connectedness.
- Spec of the dual numbers is excluded by reducedness.
- Affine line is excluded by properness.
- All test schemes and coefficient fields use the library's scheme universe u;
  no equality between independently existing universes is imposed.

Searches performed (the msearch calls were logged for this item):

1. LeanFinder: `Global sections of the structure sheaf of a proper reduced nonempty
   connected algebraic space are a finite field extension` returned 8 candidates,
   including `AlgebraicGeometry.isField_of_universallyClosed` and
   `finite_appTop_of_universallyClosed`. Read Mathlib Proper.lean lines 150--163:
   both require an integral scheme, so neither states this algebraic-space result.
2. Loogle: `"IsProper", "IsField"` returned zero hits.
3. msearch grep: `globalSections|GlobalSections|AlgebraicSpace` in AlgebraicGeometry
   returned 8 hits about Proj and affine structure-sheaf sections, no exact match.
4. LeanSearch: `The ring of global functions on a proper reduced connected algebraic
   space is a field finite over the base field` returned 8 hits, again integral
   scheme results and scheme global-section constructions, no exact match.
5. Direct rg searches of `lean/WeilConjectures` for the item id, algebraic-space
   names and proper global functions found no declaration of this statement.
6. Direct rg of `lean/Sheaf` found the previously defined reducedness predicate,
   canonical scalar map, and compatible-function ring used above. The downstream
   `SpaceDualEffectiveLineTriviality` and `SpaceProperFieldGlobalFunctions` modules
   cite this item in proof prose but do not state it. A declaration-name search of
   Mathlib, both project trees and `dag/lean_names_upstream.json` found no collision.

There is no statement dispute, correction, dependency repair, or new node.

## Second reading by Q79

Self-check with the node and source open; the maintainer supplies the independent
review after delivery. Compared every binder with the node: arbitrary field,
actual algebraic space over Spec k, its proper structure map, ordinary chartwise
reducedness, and nonempty connected point topology. Compared both conjuncts:
fieldness of compatible regular functions and finite dimensionality for the
canonical scalar action on that same ring. Confirmed that ConnectedSpace carries
nonemptiness and that the scalar map lands in precisely the displayed subring.
There are no implicit auto-bound variables, local notation, let binders in the
statement, extra geometric hypotheses or proved assertions. The only metadata
changes are the Lean record and the two landed notion dependencies named above.

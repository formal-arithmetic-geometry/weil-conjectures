## Worker report

The module `Sheaf.CategoryTheory.RoosComparisonHorizontalCoherence` states the full
canonical additive comparison and horizontal coherence on the recorded strict
`CategoryTheory.roosF` model. It has three helper definitions and seven theorem
statements, each with `sorry`. The comparison is constructed directly using
Mathlib's `CochainComplex.mappingCocone.lift`: the two inputs are the mapped
`fst` chain map and the `snd.map F` cochain, each postcomposed with the canonical
`roosProductComparison`. All data is explicit. The named theorem
`roosAdditiveComparison_lift_condition` postpones only the signed differential
compatibility of these fixed inputs (DAG steps 1-3). No object or map is chosen
from an existence theorem.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A, B and D are separately bound `Type uA`, `Type uB`, `Type uD`, each with its
  independent `Category.{vA}`, `Category.{vB}`, `Category.{vD}`, `Abelian` and
  `HasCountableProducts` instances. They need no smallness, exact products, limits
  of towers, derived categories or coefficient ring.
- A strict tower of unbounded cochain complexes is encoded using the recorded
  model's `X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ`. Its `X.asFunctor` is precisely the
  tower of complexes used to form the termwise product. Index n represents
  positive level n+1, consistent with the recorded strict model.
- `F : A ⥤ B` and `[F.Additive]` give exactly additivity on morphisms. The helper
  `roosTowerAction F` applies `Functor.whiskeringRight` and
  `Functor.mapHomologicalComplex`, so it applies F at every tower level and degree.
- `roosP`, `roosU`, `roosF`, and `roosχ` are imported from the recorded dependency.
  Thus the cone, signs, shift, braiding and fixed degree-p+1 coordinates are the
  existing construction, not a second cone model or an arbitrary triangle map.
- `roosProductComparison F X` is the cochain-level `piComparison` for the family
  `fun n : ℕ ↦ X.asFunctor.obj (op n)`. Mathlib's
  `piComparison_comp_π` identifies its nth projection with F(pi_n).
- `roosAdditiveComparison_lift_condition` records the differential equation for
  the two prescribed coordinates, using the square of `roosProductComparison`
  with `roosU = 1-s`. Its proof docstring spells out DAG steps 1-3 and the
  projection argument for that square. The proof has `sorry`; the inputs do not.
- `roosAdditiveComparison F X` is the prescribed cochain map κ, defined directly
  by `mappingCocone.lift` of F(fst) followed by the product comparison, and the
  cochain snd.map F followed by the product comparison. This realizes the
  additive cocone comparison followed by the product-comparison square in one
  lift. `roosF.obj X` is definitionally Mathlib's mapping cocone of `roosU X`.
- `roosAdditiveComparison_coordinates` gives the degree-p+1 map exactly: apply
  F to `roosχ X p`, then `F.biprodComparison`, then `biprod.map` of the two product
  comparisons. Postcomposition with the target `roosχ` expresses the same formula
  without choosing inverse coordinates. Both product summands are specified.
- `roosAdditiveComparison_natural` quantifies over every strict tower cochain map
  h and states actual equality of cochain maps, giving naturality in X.
- The main `roosComparison_horizontal_coherence` takes additive `F`, `G`, `L` and
  every `α : F ⋙ G ⟶ L`. Lean's `F ⋙ G` means the paper's GF. Its left side is
  G(κ_F) followed by κ_G followed by `roosF.map α_X`; its right side is the
  termwise `α` at `roosF.obj X` followed by κ_L. Termwise α_X is
  `NatTrans.mapHomologicalComplex ((Functor.whiskeringRight ℕᵒᵖ A D).map α) ...`.
  This is the node's right-to-left equation written with Lean's left-to-right `≫`.
  There is no invertibility, exactness or product-preservation premise.
- `roosAdditiveComparison_isIso` asserts `IsIso` for this same κ under
  `[PreservesLimitsOfShape (Discrete ℕ) F]`. This is preservation of countable
  products: arbitrary countable indexing types transport to subsets/repetitions
  of ℕ; finite and empty products are already preserved by additivity.
- `roosAdditiveComparison_id` states equality with the canonical identity
  identifications from `Functor.mapHomologicalComplexIdIso` on complexes and on
  tower-valued complexes. It includes all identity cases rather than introducing
  an arbitrary isomorphism between the two presentations of the same object.
- `roosAdditiveComparison_augmentation` binds every complex P, every family q_n,
  and its successor compatibility `hq`. It uses the recorded `roosAugment q hq`
  and states that F(q) followed by κ has the biproduct coordinates
  `biprod.lift 0 (Pi.lift (fun n ↦ F.map(q n))).f`. The first coordinate is zero
  and the second is the product family F(q_n), in every integer degree p+1.

Dependency declarations read and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`; its preadditive and limit instances.
- `def-weil-category-product`: `piObj`, `Pi.π`, `Pi.lift`, `Pi.map` in
  `Mathlib.CategoryTheory.Limits.Shapes.Products`, and `HasCountableProducts`
  in `Mathlib.CategoryTheory.Limits.Shapes.Countable`.
- `def-weil-pbc-additive-functor`: `CategoryTheory.Functor.Additive` in
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`.
- `def-weil-strict-roos-model`: `CategoryTheory.roosF` and its `roosP`, `roosU`,
  `roosχ`, `roosAugment`, `roosAugment_χ` helpers in
  `Sheaf.CategoryTheory.StrictRoosModel`. The full module was read.
- Proof dependency `def-weil-tower-transition-endomorphism`:
  `CategoryTheory.towerTransitionEndomorphism` and its projection theorem in
  `WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism`, imported
  transitively through the public strict-model import.
- Mathlib's `CochainComplex.mappingCocone.lift`, `fst`, `snd` from
  `Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone`, and
  `CochainComplex.HomComplex.Cochain.map`, `.comp`, `.ofHom`, `δ` from
  `Mathlib.Algebra.Homology.HomotopyCategory.HomComplex`; read their full
  signatures and projection/differential equations. These are available through
  the public strict-model import.
- Mathlib's `Functor.biprodComparison` is used directly, as are
  `NatTrans.mapHomologicalComplex` and `Functor.mapHomologicalComplexIdIso`.
  Read their signatures and docstrings.

Source read: `literature/stacks-project/sites-cohomology.tex`, the full statement
and proof of `lemma-derived-limit-is-ok` (Tag 0941), including its termwise
product-cone model, and all seven coordinate proof steps of the assigned node.
The extra additive comparison/coherence is explicitly credited in the node as
agent-written; the seven theorem docstrings distribute all seven steps with their
coordinate arguments. No derived-category isomorphism is asserted here: the item
is an equality of strict cochain maps and a strict cochain isomorphism criterion.

Edge cases checked mathematically: the zero tower and zero additive functor have
zero coordinate maps and satisfy every equation; the identity functor gives the
canonical identity; α=0 gives equality of zero maps; constant towers and arbitrary
successor maps impose no additional assumption. Negative integer degrees are
included, since p ranges over ℤ. Tensoring abelian groups with ℤ/2 need not be
exact but is permitted for construction and coherence. Tensoring with ℚ need not
preserve infinite products, and is permitted except in the isomorphism clause.
No term requires α invertible. The product index is the nonempty fixed ℕ of the
node, not a freely chosen finite set. The countable-preservation hypothesis is
confined to the isomorphism theorem. No statement fault or dispute was found.

Searches actually run:

- msearch LeanFinder: “Horizontal composition coherence of canonical additive
  Roos cone comparison natural transformations”; eight generic cone/naturality
  hits, including `Functor.mapConeMapCone` and `mappingCone.map_δ`, no complete
  Roos horizontal comparison result.
- msearch Loogle: `piComparison, biprodComparison`; no result, with the service
  reporting unknown unqualified identifier `piComparison`. This was not treated
  as evidence of absence; the fully qualified declarations were read in source.
- msearch grep: `Roos|roos|piComparison.*comp`, in `CategoryTheory`; eighteen
  generic product comparison references, none giving the assigned statement.
- msearch LeanSearch: “Canonical additive functor comparison with Roos mapping
  cone is compatible with horizontal composition of natural transformations”;
  eight mapping-cone/derived natural-transformation hits, no full assigned result.
- rg on `lean/WeilConjectures` and `lean/Sheaf` for Roos/roos and the proposed
  names: the existing strict model and scalar comparison were found;
  no declaration of the horizontal equation was found. The mandated grep for
  the item's blueprint id in `lean/WeilConjectures` returned no matches.
- Read Mathlib `Limits/Shapes/Products.lean` (piComparison and projections),
  `Limits/Preserves/Shapes/Products.lean` (preservation criterion),
  `Limits/Preserves/Shapes/Biproducts.lean` (canonical biproduct comparison),
  and `Algebra/Homology/Additive.lean` (termwise actions and transformations).

Validation: `scompile.py Q140 lem-pur-roos-comparison-horizontal-coherence <module>`
passed in both sandbox and final library-module naming modes, with no errors and
no unexpected warnings. Every variable/universe is explicitly bound and
`autoImplicit` is false. All theorem proofs remain `sorry`. All writes were in
the assigned sandbox; no direct git command or live-library edit was made.

## Repair of returned delivery

The return at immutable head `d0147e80e63c` identified one fault (C6, stage-2
rule 7 and H2): importing `Sheaf.Paper.IntegralOperationsScalarComparisons`
would make the stage-3 cycle IOSC → FFCEC → this item → IOSC. The extra existing
node `def-sf-additive-roos-map` was also an unauthorized stmt_deps addition.
The saved packet's first dry run passed the mechanical preflight, but the
maintainer's import-cycle finding still required this concrete repair.

Removed that import and removed the added `def-sf-additive-roos-map` dependency,
restoring stmt_deps exactly to the live base. Defined κ directly on the recorded
`roosF` using Mathlib's mapping cocone lift and product comparison, as requested.
Retained `roosAdditiveComparison_coordinates` with its exact signature as the
pin on both coordinates. The six item-clause theorem signatures are unchanged;
only their construction's implementation and one explanatory proof sentence
changed. Added the named lift-compatibility theorem to `lean.declarations`.

Overlap with `def-sf-additive-roos-map`: its `WeilConjectures.scalarRoosMap` is
the same coordinate-characterized construction. It lives in the downstream
integral scalar-comparison module and cannot be imported by this foundational
item. The direct Mathlib lift here is the repair expressly required by the
maintainer, rather than a new independent notion or new DAG node. No scalar
extension hypothesis or object enters this item.

Self-check against the current base and the returned implementation: the node
changes only `lean`; stmt_deps is restored, statement/proof/proof_deps are intact.
The source module has no scalar-comparison import or scalarRoosMap reference.
The sole Sheaf import is the recorded strict model, whose own imports do not
include IntegralOperationsScalarComparisons or finite-free completion coherence.
Independently bound category and morphism universes are retained. The coordinate,
naturality, horizontal equation for arbitrary α, product-preservation IsIso,
identity and compatible-augmentation clauses remain exactly as matched above.
The zero functor, zero tower, α=0, identity functor, nonexact additive functors,
functors failing countable-product preservation, and all integer degrees remain
allowed in the same clauses. Every theorem proof is `sorry`; definition bodies
contain only the explicit mapped projections and canonical product comparison.

Repair validation: the repaired module passed `scompile.py` in sandbox and library
naming modes (5.6 s and 5.4 s), with no errors or unexpected warnings.

## Second reading by Q140

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

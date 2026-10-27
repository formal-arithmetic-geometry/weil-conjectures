## Worker report

The module `Sheaf.AlgebraicGeometry.ArtinSquareZeroEffectivityOpenness` states
`AlgebraicGeometry.ArtinCriterion.opennessOfVersality_of_strongSquareZeroEffectivity`.
Its only theorem is postponed by `sorry`; no proof is supplied. Two definition modules
supply the missing square-zero axioms with real predicates and an explicit compatible
system structure. The item's original statement, source and proof are unchanged;
only `lean` and added definition-node dependencies change. This repaired packet also
records the existing integer-base vocabulary and cites its groupoid vocabulary.

Source checked: literature/stacks-project/artin.tex, definition-RS-star (lines 2648ff),
remark-strong-effectiveness (3040ff), Tag 0CXU (3065ff), definition-limit-preserving
(1450ff), definition-versal (1670ff), and definition-openness-versality (1997ff).
This item is a supporting lemma, not the blueprint unit's own statement.

Clause-by-clause rendering:

* Schemes over Spec Z: `F : BasedCategory.{v, w} (Over Base.{u})`, where the existing
  `Base` is `Spec (CommRingCat.of (ULift.{u} ℤ))`. `integerScheme` and `overMap`
  give the unique integer structures on every test scheme and map. Universes u, v,
  w are explicit and independent. This is the size convention, not a new base.
* Fibred in groupoids: `hFibred : IsFibredInGroupoids F`. Its definition supplies
  cartesian lifts and states that every total-category arrow is strongly cartesian.
  No fppf or étale descent axiom is imposed: the source assumes a fibred groupoid
  on that site's underlying category, not a stack.
* (1) Algebraic-space Isom presheaves: `hDiagonal : HasAlgebraicSpaceDiagonal F`.
  The existing predicate represents the 2-fibre product of any two scheme maps by
  an actual `AlgebraicSpace`. Taking the two maps over T and then its diagonal
  gives the Isom space in the statement; conversely relative Isom spaces give
  these scheme tests. Algebraic spaces are the recorded fppf sheaves with
  representable diagonal and surjective étale scheme atlas. Neither a scheme
  diagonal nor an algebraic-stack hypothesis is substituted.
* (2) Arbitrary square-zero diagrams: `hGluing : SquareZeroGluing F`. The four
  `CommRingCat.{u}` objects and `IsPullback p q f g` range over exactly the ring
  fibre products. `Function.Surjective g.hom` and `RingHom.ker g.hom ^ 2 = ⊥`
  are the two restrictions on B' to B. No local/Artinian/finite type condition.
  The span `a,b` from z over B records the specified comparison of restrictions.
  The object t and arrows c,d give a gluing with `a.val ≫ c.val = b.val ≫ d.val`.
  The `∀ t' c' d', ... → ∃! e : t ⟶ t', ...` clause gives unique gluing of arrows
  in the fibre over the pullback. Because every arrow is cartesian and vertical
  arrows are invertible, this is the essential-surjectivity and full-faithfulness
  formulation of the stated groupoid equivalence. In particular it retains
  automorphisms and does not merely assert gluing of isomorphism classes.
* (3) `hLimits : IsLimitPreserving F` reuses the existing conjunction
  `ObjectsDescend F ∧ ArrowsDescend F ∧ ArrowEqualitiesDescend F`.
  All quantify over nonempty directed preorders `I : Type u`, affine diagrams,
  and an affine limiting cone. The first descends objects, the second arrows
  with the two specified limit identifications, and the third equality of arrows.
  These are precisely the three clauses of the node, with a common later stage.
* (4) `hEffective : StrongSquareZeroEffectivity F` quantifies over every ring
  diagram `D : ℕᵒᵖ ⥤ CommRingCat.{u}` and every limit cone c. All n ≤ m, not
  merely adjacent indices, have surjective maps and square-zero kernels.
  `SquareZeroSystem.obj`, `.transition`, `.identity`, `.composition` give the
  objects, specified pullback identifications and their coherence. The conclusion
  gives `x : Object F (integerScheme (Spec c.pt))` and arrows a from every stage
  over `Spec.map (c.π.app (op n))`. The equality involving `s.transition` and a
  is compatibility with every specified transition. Index n is source index n+1,
  a bijective reindexing of the positive integers, so no stage is discarded.
* Conclusion `OpennessOfVersality F` uses the existing definition, unfolded as:
  every scheme U locally of finite type via `specULiftZIsTerminal.from U`, every
  object x and point u0 satisfying `FiniteTypePoint U u0` and `IsVersalAt F U x u0`,
  admit `V : U.Opens` containing u0 such that every finite type t in V is versal.
  `FiniteTypePoint` is exactly local finite type and quasi-compactness of
  `U.fromSpecResidueField u0`. `IsVersalAt` quantifies over Artinian local A,A',
  surjective residue maps to the actual residue field with maximal-ideal kernels,
  a surjection g with nilpotent kernel, and their commuting residue triangle.
  The equation involving `Spec.map ρ` pins the reduced map to u0. Arrows b,c
  retain the specified reduction isomorphism, and the lifted arrow d satisfies
  both the base lift equation and `b.val ≫ d.val = c.val`. Thus there is no loss
  of residue-field identifications, automorphisms, or the specified isomorphism.
  The open V is a neighbourhood in U, as required, not a global open-locus claim.

Dependency declarations read and used:

* Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
* Mathlib.AlgebraicGeometry.Sites.Fpqc: `Scheme.fppfPrecoverage`, `fppfTopology`.
* Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, its fppf-sheaf encoding,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsRepresentableWith`, `IsRepresentable`,
  `IsEtale` and `IsSurjective`.
* Mathlib.AlgebraicGeometry.Morphisms.FiniteType and .QuasiCompact:
  `LocallyOfFiniteType`, `QuasiCompact`.
* Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids: `IsFibredInGroupoids`,
  `HasAlgebraicSpaceDiagonal` and `BasedCategory` vocabulary (imported transitively).
* Sheaf.AlgebraicGeometry.ArtinRepresentableDiagonalCriterion: existing helper
  declarations `ArtinCriterion.Base`, `integerScheme`, `overMap`, `Object`, `Lift`,
  `IsLimitPreserving`, `FiniteTypePoint`, `IsVersalAt`, `OpennessOfVersality`.
  These are real definitions and are reused without restatement. The Artin
  algebraicity theorem itself is not assumed or used. Its Artinian-local
  `RimSchlessinger` and complete-local `FormalObjectsEffective` are NOT the two
  hypotheses here and were not substituted for them.
* Plain proof-plan imports for the already stated proof dependencies:
  Mathlib.AlgebraicGeometry.Noetherian;
  WeilConjectures.Mathlib.Algebra.Category.Ring.FilteredColimits
  (`CommRingCat.isColimitSubalgebraCocone`);
  WeilConjectures.AlgebraicGeometry.LimitAffineTransition
  (`exists_limit_affine_transition`);
  WeilConjectures.AlgebraicGeometry.Thickening (`IsFirstOrderThickening`).
  The four unstated Artin/tower/smooth-space lemmas and the countable-antichain
  lemma have no module record and are not imported. They remain named in the
  complete eight-step natural-language proof docstring. No proof dependency is
  needed to elaborate this stage-2 statement.

Edge cases checked before writing and again after elaboration:

* A zero square-zero kernel, identity transition maps, constant towers, and zero
  rings are included. No nontriviality hypothesis excludes the empty spectrum.
* Groupoids and individual fibres may be empty; the gluing and effectivity clauses
  quantify over actual compatible objects, with no spurious Nonempty assumption.
* Automorphisms are retained: the unique arrow clause is among extensions of the
  specified boundary arrows, not a claim that the whole fibre is contractible.
* The inverse sequence includes all nonconsecutive maps and all coherence data.
  A nilpotent kernel is not substituted for a square-zero kernel in this axiom.
* Versality uses nilpotent Artinian extensions, without coefficient-field
  embeddings or an assumption that U is affine or globally finite type.
* Limit diagrams use the same object universe u as their rings and schemes;
  there is no lower independent test universe that would make the axiom vacuous.
* The conclusion is conditional on a versal finite type point, so the empty
  scheme and schemes without such points are handled by the original quantifiers.

Searches performed through the prescribed msearch.py wrapper:

* LeanFinder: the full natural-language item, then “Rim Schlessinger square zero
  gluing and effectiveness of compatible systems of objects in fibred groupoids”.
  Hits were generic gluing/effective epi objects; no matching theorem or axioms.
* Loogle: `IsFibredInGroupoids, IsLimitPreserving, OpennessOfVersality`: zero hits,
  unknown identifier `IsFibredInGroupoids` in Mathlib's search index.
* LeanSearch and LeanFinder: “Rim Schlessinger square zero gluing and strong
  effectivity of fibred groupoid systems”; raw responses are recorded in both
  new nodes' mathlib_searches. No exact match.
* msearch grep: `SquareZeroGluing|StrongSquareZeroEffectivity|SquareZeroSystem|
  RimSchlessinger` (one regular expression): zero Mathlib hits. Direct rg in both
  lean/WeilConjectures and lean/Sheaf found only the different Artinian-local
  RimSchlessinger predicates and their consumers. Direct search for the item's
  blueprint id in WeilConjectures found no declaration. The generic Artin helpers
  were found, read in full, and reused.
* DAG definition-node grep for RS-star/strong-effectiveness/SquareZeroGluing:
  no owning definition node. `tools/blueprint_refs.py search 'strong effectiveness'`
  and `'Rim.Schlessinger'` found zero blueprint nodes. Broader 'versality' searches
  located the generic Artin criterion and the proper-curve specialization;
  neither states this lemma. The existing curve-versality definition is specific
  to curve families and does not replace the generic criterion.

Validation: all three files compile separately, in dependency order, through
scompile.py against the live server, clean apart from the permitted theorem sorry.
No statement fault, source correction, or STATEMENT-DISPUTED finding.

## New nodes

`def-sfb-artin-integer-base-versality` is an `existing: true` node on
`Sheaf.AlgebraicGeometry.ArtinRepresentableDiagonalCriterion`, recording exactly
12 existing declarations: `Base`, `integerScheme`, `overMap`, `Object`, `Lift`,
`ObjectsDescend`, `ArrowsDescend`, `ArrowEqualitiesDescend`, `IsLimitPreserving`,
`FiniteTypePoint`, `IsVersalAt`, and `OpennessOfVersality` in namespace
`AlgebraicGeometry.ArtinCriterion`. Its TeX defines the integer base, fibre/arrow
notation, three limit descent conditions, finite type points, the Artinian lifting
condition including the specified isomorphism, and openness of versality. Sources
are artin.tex definition-limit-preserving, definition-versal and
 definition-openness-versality. There is no new module or duplicate Lean definition.
It cites the newly landed general-base `def-sfb-fibred-groupoid-limit-preserving`
for specialization of its three limit predicates. That node does not own the
integer-base declarations or the versality definitions. Searches include fresh
LeanSearch, LeanFinder and Mathlib/project grep; their raw outputs are in the node.
The existing declaration's signature is copied verbatim from current main.

`def-sfb-artin-square-zero-gluing` owns
Sheaf.AlgebraicGeometry.ArtinSquareZeroGluing and the predicate SquareZeroGluing.
It states definition-RS-star of artin.tex for arbitrary rings over the integers,
including the universal property on arrows. The existing RimSchlessinger helper
restricts to finite type Artinian local rings, so it is insufficient and is not
redefined. All three search kinds and their raw outputs are in the node.

`def-sfb-artin-strong-square-zero-effectivity` owns
Sheaf.AlgebraicGeometry.ArtinStrongSquareZeroEffectivity, the compatible system
structure SquareZeroSystem, and predicate StrongSquareZeroEffectivity. It states
remark-strong-effectiveness with the precise square-zero condition of Tag 0CXU(4).
FormalObjectsEffective in the generic criterion instead concerns powers of the
maximal ideal in a complete Noetherian local ring; that is a different axiom.
All three search kinds and their raw outputs are in the node. Both new nodes
retain the item's chapter/unit and the ancestor/via returned by blueprint_refs.

## Second reading by Q88

The dispatcher explicitly requires a single worker and prohibits starting other
agents; the maintainer supplies the independent delivery review. This section
records my final rereading, not a claim of an independent second worker.

I reread the item statement, Tag 0CXU, and the three Lean files with the existing
Artin definitions open. The five theorem binders give fibredness plus the four
source conditions. The conclusion unfolds to precisely the finite-type-point
neighbourhood statement with the original Artinian lifting definition. I checked
that gluing quantifies over arbitrary rings (not just Artinian ones), that its
uniqueness clause is on compatible arrows in the fibre, and that effectivity
quantifies over all n ≤ m and retains identity/composition/limit compatibility.
No extra stack axiom, arbitrary replacement comparison map, or unproved data is
present. I separated the new independent notions into two definition modules and
nodes; the existing limit/versality helpers remain shared. Definitions contain
no sorry; the sole sorry is the theorem with the complete source proof docstring.
All variables and universes are explicit, and all Lean lines have width ≤ 100.

Dry-run repair: current preflight additionally requires `import_flags: []` on new
definition nodes; both records now include it. Combined bracket citations in the
new statements were expanded to individual `[id]` citations for the citation gate.

## Repair of return on immutable head 326b495c311f

H2/H12 (all parts): added `def-sfb-artin-integer-base-versality` with an
existing:true record for the twelve requested declarations in the original module.
The item and both new square-zero definition nodes now cite this new definition
node. Both definition nodes explicitly cite it in their TeX for the integer-base,
fibre-object and lifted-arrow notation. Added
`def-sfb-stable-pointed-moduli-groupoids` to the item's stmt_deps for its actual
`IsFibredInGroupoids` and `HasAlgebraicSpaceDiagonal` hypotheses. Their meanings
and the TeX rendering of all four hypotheses/conclusion are unchanged. These
metadata additions are exactly the maintainer's repair instruction; there is no
source-statement correction and no theorem-node dependency is introduced.

Compared the retained returned sandbox with current main: the two square-zero
nodes/modules remain unlanded; the main item differs only in lean and stmt_deps.
Preserved current main's other item fields. The prescribed delivery wrapper
rebases the packet on the current server main branch. The three retained Lean
files are unchanged from the returned sandbox, with SHA256:

* ArtinSquareZeroEffectivityOpenness.lean:
  f81b2ab79d937b1b5505c6660023609efa8d3a24c3b4b8969e73185a1a1bcbc6
* ArtinSquareZeroGluing.lean:
  d08be86cfabc5532c0de088f124b86558a8fe1731c53ad0b28f3ca219348180d
* ArtinStrongSquareZeroEffectivity.lean:
  ff5e4f659edef3274fe2324474469a4a0e70a88e6d05ae4db57294b6ae7a509b

Reread all twelve existing declarations and their docstrings on current main,
including the full IsVersalAt binders and both compatibility equations, and the
new general-base limit node. The new node describes actual definitions, not an
assumption of the Artin algebraicity theorem. The new dependency arrows are
from the consumer to vocabulary definitions and introduce no theorem cycle.
The reviewer already independently accepted the mathematics, universes, edge
cases, docstrings and Lean; this repair addresses the omitted ownership and
citations without changing them. No other return points were given.

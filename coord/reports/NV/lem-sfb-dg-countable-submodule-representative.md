## Worker report

The module `Sheaf.CategoryTheory.DgCountableSubmoduleRepresentative` states
`CategoryTheory.DgAlgebra.exists_countable_submodule_quasiIso`, with its entire
proof postponed by `sorry`. No definitions or other theorems are introduced.
The node's statement and proof are unchanged. Its statement dependencies gain
the already landed `def-sfb-dg-derived-category`, whose definitions are used
rather than duplicated.

Source checked: `literature/stacks-project/dga.tex`, Tag 0CRM, lemma-countable,
proof (2) to (1), especially the paragraph beginning “Assume A is countable”.
That paragraph refers back to the successive adjoining-primitives construction
for subalgebras. The module docstring reproduces the node's seven proof steps,
including differential closure, finite-list coding, initial cohomology
representatives, adjoining primitives, the union, and both cohomology directions.
Also read definitions definition-dga and definition-dgm. The inherited blueprint
route was checked in the latest blueprint's six-functor stability unit and
its direct-images proof, part (3).

Hypotheses and clauses, in order:

- The size convention is represented by explicitly declared `universe u`.
  All degrees are `ℤ`, not just nonnegative degrees. Algebra components and
  module components have the same arbitrary ambient universe; smaller types
  can be placed there by cumulativity. No ring/module cardinality equality is
  imposed, and the ambient module need not be countable.
- The associative unital integer DG algebra is `A : Algebra.{u}`. The existing
  definition is `Mon (CochainComplex (ModuleCat (ULift ℤ)) ℤ)`. Its monoid laws
  give associativity and unit; multiplication is a chain map for the signed
  tensor differential, giving exactly the stated Leibniz identity. The complex
  identities give square-zero differential. No commutativity is assumed.
- The right DG module is `N : RightModule A`. This is the existing module object
  in the reversed tensor category, with underlying complex `(underlying A).obj N`.
  It has the specified right action and signed module Leibniz identity.
- Countability throughout is Mathlib `Countable`: its field
  `exists_injective_nat'` is an injection into `ℕ`, exactly the dependency
  `def-sfb-countable-set`. No encodability, infinitude or nonemptiness is added.
- Countability of the degree-labelled algebra elements is exactly
  `hA : Countable (Σ i : ℤ, A.X.X i)`.
- Cohomology is `((underlying A).obj N).homology i`. For the cochain shape this
  is the standard kernel modulo image at degrees `i-1,i,i+1`; it is an actual
  module, not an abstract group standing in for cohomology.
  `hN : ∀ i : ℤ, Countable (...)` includes every cohomology degree.
- A DG submodule is represented by `∃ (M : RightModule A) (ι : M ⟶ N)` with
  `∀ i : ℤ, Function.Injective (((underlying A).map ι).f i)`.
  This is the concrete embedded-submodule representation: the image of the
  degree-`i` map is the actual subgroup of `N^i`, and injectivity identifies
  `M^i` with that subgroup. Since `ι` is a DG module morphism, the images are
  stable under the right action and differential. Conversely, an actual
  graded DG submodule supplies this witness with its inclusion. Thus no
  arbitrary quasi-isomorphic replacement without an embedding is allowed.
- Countability of its homogeneous elements is exactly
  `Countable (Σ i : ℤ, ((underlying A).obj M).X i)`. Injectivity transports
  this to the actual degree-labelled image submodule.
- The inclusion is a quasi-isomorphism exactly when
  `QuasiIso ((underlying A).map ι)`. Mathlib's `QuasiIso` requires every induced
  homology map to be an isomorphism. Under the preceding image identification,
  these are precisely the maps induced by the inclusion, not unrelated
  cohomology isomorphisms.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.DgAlgebraDerivedCategory`:
  `CategoryTheory.DgAlgebra.Complex`, `Algebra`, `RightModule`, `underlying`,
  and the definition of `act` and `quasiIsomorphisms` were read for the signs
  and underlying-complex interpretation. This supplies the added landed
  statement dependency `def-sfb-dg-derived-category`.
- `Mathlib.Data.Countable.Defs`: `Countable` (definition dependency).
- `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`:
  `HomologicalComplex.homology` (via the DG framework).
- `Mathlib.Algebra.Homology.QuasiIso`: `HomologicalComplex.QuasiIso` and its
  equivalence to isomorphisms on `homologyMap` (via the DG framework).
- Proof imports are `Mathlib.Data.Set.Countable` for
  `Set.Countable.biUnion`, `Set.countable_iUnion`, `Set.Countable.union`
  (`lem-trf-countable-unions`) and `Mathlib.Logic.Equiv.List` for
  `List.countable` (`lem-sfb-countable-finite-lists`). Their signatures were read.
  The size convention explicitly has no declaration or required module.

Edge cases checked mathematically: the zero algebra and zero module are allowed;
all zero cohomology groups are countable, and no nonzero unit is assumed.
Finite rings/modules are included. Empty lists include zero in each degree of
the generated submodule; even the zero module has one degree-labelled zero per
integer, a countable set. Negative degrees and unbounded modules are included.
The ambient module may have arbitrarily large components. The degreewise
injectivity conjunct is essential: dropping it would assert only existence of
a replacement rather than the submodule representative required here.

Searches performed before writing:

- `msearch.py ... leanfinder`: “A module over a countable differential graded
  ring with countable cohomology has a countable quasi-isomorphic differential
  graded submodule”. Eight hits, including `DerivedCategory.exists_iso_Q_obj_of_isLE`,
  `DerivedCategory.exists_iso_Q_obj_of_isGE`, `CochainComplex.IsKProjective`,
  and `CochainComplex.IsKInjective`; none constructs this DG submodule.
- `msearch.py ... loogle`: `DGModule, DifferentialGraded, GradedRing`.
  No hits; unknown identifier `DGModule`.
- `msearch.py ... leansearch`: “A differential graded module over a countable
  dg ring with countable cohomology has a countable dg submodule quasi-isomorphic
  to it”. Eight hits, mostly `HomogeneousSubmodule` APIs and one model-theory
  countably generated substructure; none concerns DG cohomology representatives.
- `msearch.py ... grep`: `DGModule|DGRing|DifferentialGraded|differential graded`
  in `Algebra`. Five hits in `DifferentialObject.lean`; these concern underlying
  differential objects, not modules over a DG ring or the target theorem.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib with the same
  patterns and `countable.*[Ss]ubmodule|countable.*[Qq]uasi` found no target.
  An initial case-sensitive search missed the recently landed `DgAlgebra`
  spelling; reading the DAG's `def-sfb-dg-derived-category` record found the
  exact existing framework, which is imported. Divided-power DG algebras are
  nonnegative strictly commutative and are not used here.
- `rg` of the item id in `lean/WeilConjectures` and search for
  `exists_countable_submodule_quasiIso` in the library/upstream name index found
  no existing target declaration. DAG searches found the distinct countable
  subalgebra and semi-free-resolution statements, not a duplicate theorem.
- `tools/blueprint_refs.py search 'countable DG submodule'`: no matching
  blueprint nodes. No new definition node is needed.

Validation: `scompile.py NV lem-sfb-dg-countable-submodule-representative` compiled
this module in both sandbox and library module modes, cleanly (8.3 s and 5.1 s).
All variables and universes are explicit and `autoImplicit` is disabled.
There are no disputed statements, corrected statements, or dependency repairs.

## Second reading by NV

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

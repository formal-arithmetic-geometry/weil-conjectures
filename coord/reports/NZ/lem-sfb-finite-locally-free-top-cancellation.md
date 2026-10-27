## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocallyFreeTopCancellation` states
`AlgebraicGeometry.Scheme.Modules.exists_local_finiteLocallyFree_top_cancellation`.
Its only theorem proof is `sorry`; the docstring supplies the accepted five-step
natural-language proof. No definition, extra node, dependency repair, or statement
correction is needed. The accepted stage-1 split is preserved.

Statement correspondence, hypothesis by hypothesis and clause by clause:

- Scheme: `(X : Scheme.{u})` uses the recorded `AlgebraicGeometry.Scheme`.
- Integer degree: `(r : ℤ)` includes negative integers.
- Cochain complex of structure-sheaf modules: `(P : CochainComplex X.Modules ℤ)`.
  Mathlib's `X.Modules` is the category of sheaves of modules on the scheme's
  structure ring sheaf; its cochain-complex morphisms are chain maps.
- Every term finite locally free: `hfree : ∀ i : ℤ, (P.X i).IsFiniteLocallyFree`.
  This is the recorded variable-rank notion, with no fixed rank added.
- Zero terms above r: `hzero : ∀ i : ℤ, r < i → IsZero (P.X i)`.
  Categorical zero is the invariant meaning of the sheaf being zero.
- Vanishing top cohomology: `hcohomology : IsZero (P.homology r)`.
  Mathlib homology for the shape `ComplexShape.up ℤ` is cohomology, the quotient
  of cycles by boundaries in the abelian category of module sheaves.
- Every point and its open neighbourhood: `∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ...`.
- Complex on the neighbourhood: `∃ Q : CochainComplex V.toScheme.Modules ℤ`.
- All new terms finite locally free: `∀ i : ℤ, (Q.X i).IsFiniteLocallyFree`.
- New upper bound r-1: `∀ i : ℤ, r - 1 < i → IsZero (Q.X i)`.
- Chain map to the restricted original complex: the existential `f : Q ⟶
  ((restrictFunctor V.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj P`.
  `restrictFunctor V.ι` is the canonical open-immersion restriction functor,
  applied degreewise by `mapHomologicalComplex`.
- Isomorphisms on every cohomology sheaf: `QuasiIso f`; its definition requires
  `QuasiIsoAt f i` for every integer i, equivalently invertibility of each
  induced homology map. This asserts the specified map, not merely a derived
  isomorphism between the objects.
- No lower bound: there is no strict lower-support or boundedness hypothesis.
  No affine, noetherian, reducedness, or characteristic hypothesis is imposed.

Recorded statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declaration
  `AlgebraicGeometry.Scheme` (including its morphism structure).
- `def-pc-cochain-complex-modules`:
  `Mathlib.Algebra.Homology.HomologicalComplex`, declaration `CochainComplex`;
  its morphisms have degreewise maps satisfying the chain-map equations.
- `def-sc-finite-locally-free-sheaf`:
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`,
  declaration `SheafOfModules.IsFiniteLocallyFree`. Its finite local generators
  are locally free, and the finite rank may vary across the covering.

Proof-dependency modules are imported without `public`, as required:

- `WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting`:
  `AlgebraicGeometry.RingedSpace.module_exactness_local_lifting` (sectionwise
  kernels, zero-cokernel/epi equivalence, and local lifting for exactness).
- `WeilConjectures.AlgebraicGeometry.Modules.LocalSectionOfEpi`:
  `AlgebraicGeometry.Scheme.Modules.exists_local_section_of_epi` (a local
  section for an epi onto a finite locally free target, no source QC assumption).
- `WeilConjectures.AlgebraicGeometry.SingleFiniteRetractSheafAffineTrivialization`:
  `AlgebraicGeometry.Scheme.exists_affine_trivialization_of_finite_retract`
  (finite free retract trivializes on a smaller affine neighbourhood).

The source text was read in Stacks `cohomology.tex`, labels
`lemma-finite-cohomology` (08DN) and `lemma-local-lift-map` (08C6), and
`modules.tex`, label `lemma-direct-summand-of-locally-free-is-locally-free`
(0BCI). The latest blueprint unit and direct-image proof were read. This
auxiliary theorem states the single cancellation construction in 08DN; it
changes no unit statement. The source's bounded-below condition on the initial
strictly perfect complex is not used by this single cancellation construction.

Edge cases checked mathematically: the empty scheme has no point to check;
rank zero and zero terms are allowed by the recorded finite locally free
notion; if the top term is already zero the same conclusion holds; an identity
pair in degrees r-1 and r cancels to zero; r=0 and negative r use the same
integer arithmetic. A complex unbounded below is permitted: only its two
highest terms are changed. Nonreduced schemes and all characteristics are
included because scheme stalks remain local rings. The conclusion does not
require a single neighbourhood trivializing all infinitely many terms.
No statement dispute or node fault was found.

Searches made (the service results are saved by msearch in `searches.jsonl`):

- LeanFinder: "A complex of finite locally free sheaves with zero highest
  cohomology is locally quasi-isomorphic to a complex vanishing one degree
  earlier". Eight hits: derived t-structure support and generic truncation
  results, including `CochainComplex.quasiIso_ιTruncLE_iff`; none supplies
  finite locally free terms in the local shortened complex.
- Loogle: `"SheafOfModules", "QuasiIso"`. Zero hits.
- Mathlib grep: `finiteLocallyFree.*trunc|IsFiniteLocallyFree.*kernel|cancel.*top|top.*cancel`.
  Twenty-five unrelated algebraic, homological, and analytic hits; no match.
- LeanSearch: "A complex of finite locally free sheaves with vanishing highest
  cohomology admits locally a shorter quasi-isomorphic complex". Eight generic
  quasi-isomorphism and localization results; no local finite-locally-free theorem.
- `rg` in the upstream `lean/WeilConjectures` and project `lean/Sheaf` for the
  item id, finite locally free shortening/kernel/truncation, and top cancellation;
  also inspected the upstream declaration-name index. No exact duplicate.
  `exists_split_top_differential_cancellation` was read: it assumes lower bound
  zero, a natural top index, and an already split differential, and has different
  term hypotheses. `split_top_differential_cancellation_homotopy` also requires
  a supplied splitting and natural index. The ring-level finite-free split
  cancellation theorem is over a ring, not scheme module sheaves. None states
  this item.

Validation: `scompile.py NZ lem-sfb-finite-locally-free-top-cancellation` on the
single delivered module succeeded against the live published build: the library
module compiled in 4.9 seconds, with no errors or unexpected warnings. All
variables/universes are explicitly bound, with `set_option autoImplicit false`.
The node copy changes only `lean`, records the signature verbatim up to `:=`,
and uses the required one-space JSON indentation and final newline.

## Second reading by NZ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

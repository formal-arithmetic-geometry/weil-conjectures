## Worker report

The module `Sheaf.AlgebraicGeometry.EquivariantProjectiveModelNormalization` states
`AlgebraicGeometry.equivariant_projective_model_normalization`, with one postponed theorem
and no new definitions. Only the item's `lean` field changes. No statement correction or
new/dependency node is needed. The five proof steps in the node are reproduced in the
proof docstring with their dependency ids.

Hypothesis-by-hypothesis correspondence:

- The field is `(k : Type u) [Field k]`. The integral projective finite-type k-schemes
  are `S C : Scheme.{u}`, `[IsIntegral S] [IsIntegral C]`, structure maps `s c`,
  `[IsHProjective s] [IsHProjective c]`, and the respective
  `LocallyOfFiniteType` and `QuasiCompact` instances. Both maps to Spec k are explicit.
- The finite group is `(J : Type v) [Group J] [Finite J]`. Its actions are the monoid
  homomorphisms `rho : J →* (k ≃+* k)`, `aS : J →* Aut S`, `aC : J →* Aut C`.
  `hs` and `hc` are the semilinear compatibility squares. No injectivity, faithfulness,
  or trivial scalar action is assumed. Field actions are left actions on functions;
  scheme actions use inverse pullback, explaining `rho g⁻¹` in those squares.
- The equivariant k-morphism is `p`, with `hp : p ≫ s = c` and the square `heq`.
- `K` is exactly `S.functionField`, not a separately chosen field. The extension is
  `(M : Type u) [Field M] [Algebra S.functionField M]` with
  `[FiniteDimensional S.functionField M]`; no separability is imposed.
- The specified generic-fibre isomorphism is `e`. Its compatibility over Spec K is `heS`.
  The specified identification k(C)=M is `eC`; `heC` says the first projection is the
  canonical generic-point map after that identification. These equations unpack the
  node's specified identification, rather than assuming dominance as extra input.
- W and nu are exactly `C.normalization` and `C.fromNormalization`, from the recorded
  normalization definition; no arbitrary normal model or chosen cover is substituted.

Conclusion-by-conclusion correspondence:

- Finiteness and surjectivity of nu are the first two conjuncts.
- `IsIntegral C.normalization` and the pointwise conjunction of `IsDomain` and
  `IsIntegrallyClosed` express normal integral, with the node's local-ring convention.
- `IsHProjective (C.fromNormalization ≫ c)`, `LocallyOfFiniteType` and `QuasiCompact`
  express projective finite type over k.
- `eW` identifies k(W) with M. Its first equality says the generic-point morphism
  composed with nu is the one obtained from `eC`. Thus the isomorphism is induced by
  nu, and nu is birational in the node's function-field convention.
- `eF` identifies the generic fibre of b with Spec M. Its two projection equations
  identify its first projection with the eW generic-point map and its second with the
  specified map of the original fibre e. Together with the preceding equality, these
  equations identify eF with the map induced by nu over the original fibre.
- `aW : J →* Aut C.normalization` is an actual group action by scheme automorphisms.
  The first universal square lifts each given automorphism. The following quantifier
  over every endomorphism `l` asserts uniqueness among all morphism lifts, not merely
  among the chosen automorphisms. The next square gives semilinearity over k.
- `rhoM : J →* (M ≃+* M)` is constrained by the inverse-pullback square on C. The next
  inverse-pullback square uses this same rhoM on W. Hence the two identifications induce
  exactly the same action on M; rhoM is not an unconstrained auxiliary action.
- The next square asserts b's equivariance. `IsHProjective b` is precisely the recorded
  global closed-projective-space-embedding convention; finite homogeneous coordinate
  types are equivalent to an embedding in some P^n, including the harmless empty-coordinate
  presentation already explained in def-kun-projective's record. Properness and
  surjectivity are the next conjuncts. The final `U : S.Opens`, `Dense`, and
  `IsFinite (b ∣_ U)` express finiteness over a dense open subscheme. Since S and W
  are integral, these are exactly the node's stated alteration condition, with no
  stronger convention (e.g. generically etale) imposed.

Dependency declarations read and used:

- `Field` (Mathlib.Algebra.Field.Defs), `Algebra` (Mathlib.Algebra.Algebra.Defs),
  and `FiniteDimensional` (Mathlib.LinearAlgebra.FiniteDimensional.Defs).
- `AlgebraicGeometry.IsIntegral` (Mathlib.AlgebraicGeometry.Properties).
- `AlgebraicGeometry.IsHProjective`
  (WeilConjectures.AlgebraicGeometry.Morphisms.Projective), using its finite global
  closed immersion field, not an affine-local replacement.
- `LocallyOfFiniteType` and `QuasiCompact` in Mathlib.AlgebraicGeometry.Morphisms.FiniteType
  and Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `Scheme.functionField` from Mathlib.AlgebraicGeometry.FunctionField, imported through
  the recorded WeilConjectures.AlgebraicGeometry.FunctionField module. That node's
  docstring explicitly reuses this definition for arbitrary integral schemes.
- `pullback`, its projections, and the pullback universal property in
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback.
- `Scheme.normalization` and `Scheme.fromNormalization` in the recorded
  WeilConjectures.Mathlib.AlgebraicGeometry.Normalization module; read the full
  signatures and construction from the function-field generic morphism.
- `IsFinite` (Mathlib.AlgebraicGeometry.Morphisms.Finite), `Surjective`
  (Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap), `IsClosedImmersion`
  (Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion), `IsProper`
  (Mathlib.AlgebraicGeometry.Morphisms.Proper), and `IsOpenImmersion`
  (Mathlib.AlgebraicGeometry.OpenImmersion). The open subscheme is `U.toScheme`
  with canonical open immersion; `b ∣_ U` is the canonical restriction.

All already recorded proof-dependency modules are imported: FiniteOverProjective,
ReducedNormalization, ComponentDominantNormalizationLift, ProjectiveImpliesProper,
and the recorded upstream Normalization and pullback modules. The remaining proof
nodes have no Lean record at this reading, so no invented import is added. Their
uses remain explicit in the proof docstring. There is no import cycle.

Source checks: read varieties.tex lemma-normalization-locally-algebraic (0BXR) and
lemma-normalize-projective (0GK4), morphisms.tex lemma-normalization-normal (035Q),
and lemma-finite-over-dense-open (0BAI) in the supplied local Stacks sources.
The node is a derived assembly, not a blueprint unit statement. These sources
support the normal finite birational normalization, projectivity, uniqueness of
lifts and the dense-open finiteness conclusion.

Edge cases checked before writing: J trivial, J nonfaithful on any of its three
objects, nontrivial scalar action, M=K, purely inseparable finite M/K, arbitrary
characteristic and dimension-zero S or C. All remain admitted. Integral schemes
are nonempty by the recorded definition, so empty S/C are excluded by the original
hypotheses; a zero ring is excluded by Field. Non-dominant p is already excluded
by the given nonempty Spec M generic fibre. Dense U is necessarily nonempty.
No connectedness, smoothness, perfectness of k, or dimension-one hypothesis is added.
Group universe v is independent; all schemes and fields may be placed in a common
arbitrarily large u.

Searches made with the prescribed msearch.py wrapper under Q145 and this item:

- LeanFinder: “Normalization of an integral projective scheme with a finite semilinear
  group action is projective and preserves its finite generic fibre”. Eight hits on
  relative normalization, integral normalization, and its universal property; none
  contains the assembled equivariant projective/finite-generic-fibre conclusion.
- Loogle: `"normalization", "projective"`. Zero hits.
- grep: `normalization|IsHProjective`, subdirectory/file
  `AlgebraicGeometry/Normalization.lean`. Five relative-normalization header hits;
  no assembled result.
- LeanSearch: “normalization integral projective scheme finite group action projective
  alteration”. Eight hits, including relative normalization instances and invariant
  ring integrality; no exact statement.
- Local rg of projective/normalization and semilinear patterns in lean/Sheaf and
  lean/WeilConjectures; exact item-id search in lean/WeilConjectures; exact proposed
  theorem-name and generic-fibre phrase searches including dag/lean_names_upstream.json.
  No duplicate. SemilinearEquivariantChowModification was read for its action convention;
  it has different inputs and gives a modification, not this normalization theorem.

Validation: scompile.py compiled the module both as sandbox and under its final library
module name, cleanly (no errors or non-sorry warnings). `autoImplicit false` is explicit;
all variables and universes are bound, every Lean line has at most 100 characters.
No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q145

A separate pass over the node and final Lean file matched every hypothesis and conclusion
listed above. This is the worker's second reading, not a claim of an independent agent
review: the dispatcher expressly prohibits starting another agent, and the maintainer's
independent review follows delivery. The pass checked eC/e/eW/eF orientations: all field
isomorphisms point from the function field to M, so their Spec maps point from Spec M
into the appropriate generic point. It also checked both original and normalized actions
use rhoM at g inverse, as required for left actions on functions. Uniqueness quantifies
all endomorphism lifts, so no automorphism-only weakening is present. All finite-type and
normal-local-ring conjuncts are present. Explicit direct imports for the recorded
statement notions were added during this pass; no mathematical statement changed.

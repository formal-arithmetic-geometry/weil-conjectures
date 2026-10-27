## Worker report

The module `Sheaf.AlgebraicGeometry.NeronLftFiniteSetAffine` states
`AlgebraicGeometry.exists_affineOpen_of_neronLft`, with the single proof `sorry`.
No definitions, helper theorems, dependency repairs or statement changes are needed.
The node copy changes only `lean`.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- The Noetherian integrally closed domain is `D : Type u` with `[CommRing D]`,
  `[IsDomain D]`, `[IsNoetherianRing D]`, `[IsIntegrallyClosed D]`.
  Exact dimension one is `hdim : ringKrullDim D = 1`, so fields are not silently
  included by replacing this with dimension at most one.
- The fraction field is `K : Type u` with `[Field K]`, `[Algebra D K]` and
  `[IsFractionRing D K]`. This allows any specified fraction-field realization,
  without restricting the field characteristic. `S` is written out as
  `Spec (CommRingCat.of D)`. The generic-point morphism is the canonical
  `Spec.map (CommRingCat.ofHom (algebraMap D K))`.
- `V : Over (Spec (CommRingCat.of K))` is a K-scheme, with `[GrpObj V]` and
  `[IsCommMonObj V]` providing its group structure and commutativity.
  `[Smooth V.hom]` and `[IsSeparated V.hom]` express smoothness and separatedness.
  Finite type is `[LocallyOfFiniteType V.hom]` together with `[QuasiCompact V.hom]`,
  as prescribed by the finite-type dependency's record.
- `N : Over (Spec (CommRingCat.of D))` with `[GrpObj N]`, `[IsCommMonObj N]`,
  `[Smooth N.hom]`, `[IsSeparated N.hom]` is the smooth separated commutative
  S-group scheme. Smoothness already supplies local finite type; no quasi-compactness
  or finite-type assumption on `N` is added.
- The specified generic-fibre isomorphism is
  `e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D K)))).obj N ≅ V`.
  `[IsMonHom e.hom]` says it respects the group laws. Its source monoid/group
  structure is the canonical functorial base-changed structure, activated with
  `open scoped CategoryTheory.Obj`; it is not an arbitrarily supplied group structure.
  An invertible multiplicative morphism of group objects is a group isomorphism.
- The Néron mapping property is `hN`: for every `Y : Over (Spec (.of D))`,
  smoothness of `Y.hom` implies bijectivity of the function on *all scheme morphisms*
  `f : Y ⟶ N` given by `(Over.pullback ...).map f ≫ e.hom`. This is the actual
  restriction/base-change function, not an arbitrary equivalence between Hom sets.
  `Y` is not required to be quasi-compact, separated or a group scheme.
- The arbitrary finite subset is `(P : Set N.left) (hP : P.Finite)`.
  The conclusion `∃ U : N.left.Opens, IsAffineOpen U ∧ P ⊆ (U : Set N.left)`
  gives an open subscheme, affineness of its induced scheme structure, and containment
  of every point of `P`. Mathlib's `IsAffineOpen` is `IsAffine` of the open subscheme,
  i.e. isomorphism to the spectrum of a commutative ring.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Spec`, `Spec.map` (scheme, morphisms, affine base and generic-point map).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: its recorded
  `baseChange_morphism_projections` and module documentation specify that scheme and
  morphism base change use the existing `CategoryTheory.Over.pullback` functor.
  Read the full module including `Scheme.Modules.moduleBaseChange`, the iterated
  and fibre comparisons, `Scheme.Hom.geometricFiberAt`, and the section comparison.
  This theorem uses scheme base change, not the module-only declaration.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`;
  `Mathlib.CategoryTheory.Monoidal.Mon`: `IsCommMonObj`, `IsMonHom`.
  Read also `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, which explicitly
  documents this same encoding for the group-scheme dependency. The typeclass
  `GrpObj` works over an arbitrary base, so no field-only private definition is needed.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Over`: the canonical cartesian monoidal
  structure on `Over` and monoidal `Over.pullback`. Its induced group object is
  `CategoryTheory.Functor.grpObjObj` (the `CategoryTheory.Obj` scoped instance).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated`, defined precisely
  as closed immersion of the diagonal, as the node requires.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; Mathlib's canonical
  `Scheme.Opens` open subschemes use this notion. No replacement predicate is introduced.
- Proof-only import `Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine` supplies
  `AlgebraicGeometry.Scheme.exists_affineOpen_of_isAmple` for the final proof step.
  The other currently unstated proof-dependency theorems need no declaration to type
  this statement; their full natural-language proof steps are retained in its docstring.
  The smooth-open restriction dependency is already matched to Mathlib Smooth results,
  which are available through the statement import.

Edge cases checked before writing: `P = ∅` is allowed (the empty affine open suffices);
points may be generic, nonclosed, or in different fibres. There is no nonemptiness or
single-fibre restriction on `P`. The model may have infinitely many components and may
be non-quasi-compact. No assumption of connected generic fibre, properness, finite
component groups, algebraic closure, or characteristic zero is imposed. The domain
and dimension hypotheses exclude the zero ring and fields, as the node does. The
trivial group remains included. All schemes and fields live in arbitrary `u`, and
smooth test schemes have the same ambient universe as the base, not a smaller
independent universe that could make the mapping property vacuous. Every binder and
universe is explicit. The group structure on a pullback is inferred canonically.

Searches for an existing statement (performed with the prescribed `msearch.py`):

- LeanFinder: “Every finite subset of a Neron lft group model over an affine Dedekind
  scheme is contained in an affine open subscheme”: 8 hits; single-point affine
  neighbourhoods, affine covers and basic opens, no Néron-model statement.
- Loogle: `"Neron"`: zero hits.
- Mathlib grep: `Neron|Néron|finite.*(set|subset).*affine` in `AlgebraicGeometry`:
  zero hits.
- LeanSearch: “Every finite subset of a Neron locally finite type group scheme over
  a Dedekind domain is contained in an affine open”: 8 hits, including `IsAffineOpen`,
  affine bases and single-point neighbourhoods; no matching assertion.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for Neron/Néron/neron and
  finite-set affine neighbourhoods: no Néron declaration. Existing ample-line-bundle
  results, effective-descent hypotheses and generic-point affine neighbourhoods do
  not state the item. The required literal node-id search in `WeilConjectures` and
  search for the proposed full declaration name in Mathlib and both project roots
  have no hits.

Source verified in the primary BLR scan linked by the node: PDF pp.296–297
(printed pp.290–291), 10.1 Definition 1 and the discussion after it, and the first
sentence of Proposition 4's proof. The latter states the finite-set affine-neighbourhood
input used here. No source-based statement correction is needed.

Validation: the prescribed `scompile.py` compiled the sandbox and delivery module
separately in 1.6 seconds each, with no errors or warnings. The initial compile found
an incorrect import spelling; it was repaired to
`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` before the successful compile.
The module is in module mode, uses public statement imports and a private proof
import, and has maximum line length 96. Its only postponed proof is the theorem
matching this DAG node, whose docstring contains the five-step proof with dependencies.

## Second reading by Q71

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

The module `Sheaf.AlgebraicGeometry.ProperFinitePresentationClosedLimit` states
`AlgebraicGeometry.exists_proper_finitePresentation_closedImmersion_limit` with a single
`sorry` proof. It introduces no definition. Its docstring gives all eight steps of the
node's proof and names their dependencies. No statement correction or new node is needed.
The source was read at https://stacks.math.columbia.edu/tag/09ZR (Lemma 32.13.2 and proof);
the local Stacks source is absent on this machine.

Hypotheses and clauses, in order:

- The schemes and proper morphism `f : X → S` are `{X S : Scheme.{u}} (f : X ⟶ S)
  [IsProper f]`. Proper includes separatedness, universal closedness and local finite
  type; universal closedness implies quasi-compactness, so this is finite type.
- The qcqs base is `[CompactSpace S] [QuasiSeparatedSpace S]`. CompactSpace means
  quasi-compactness here, without any Hausdorff requirement.
- The nonempty directed set is the existential `I : Type u`, `PartialOrder I`,
  `Nonempty I`, `IsDirected I (· ≤ ·)`. The index universe agrees with the schemes'
  universe, following the project rule; the finite-type ideal system in the source can
  be chosen in this universe.
- The inverse system consists of `D : Iᵒᵖ ⥤ Scheme.{u}`. The natural transformation
  `p : D ⟶ (Functor.const Iᵒᵖ).obj S` supplies the structure maps and says that
  transitions are S-morphisms. An arrow `i ⟶ j` in the opposite ordered category
  corresponds exactly to `unop j ≤ unop i`.
- The compatible morphisms from X are `π : (Functor.const Iᵒᵖ).obj X ⟶ D`.
  Naturality expresses compatibility with all transitions, and
  `∀ i, π.app i ≫ p.app i = f` says they are S-morphisms for the given f.
- Every stage is proper: `∀ i, IsProper (p.app i)`. Its finite presentation is
  the conjunction `LocallyOfFinitePresentation (p.app i) ∧ QuasiCompact (p.app i) ∧
  QuasiSeparated (p.app i)` as specified by the conventions node (Stacks 01TP).
  The latter two conjuncts, though also consequences of properness, make explicit
  the full finite-presentation convention.
- All transitions are closed immersions:
  `∀ (i j : Iᵒᵖ) (a : i ⟶ j), IsClosedImmersion (D.map a)`.
- All projections are closed immersions: `∀ i, IsClosedImmersion (π.app i)`.
- X is the inverse limit in schemes: `Nonempty (IsLimit (Cone.mk X π))`.
  The vertex is literally X and the cone maps are literally π; the assertion is
  the complete universal property in Scheme, rather than merely in Over S.
- The final 'in particular' is a separate conjunct asserting existence of a scheme Y,
  `i : X ⟶ Y`, `g : Y ⟶ S`, with `IsClosedImmersion i`, `IsProper g`, the three
  finite-presentation properties, and `i ≫ g = f`.

Dependency records and source signatures read:

- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper` (class extending IsSeparated, UniversallyClosed and
  LocallyOfFiniteType).
- `def-weil-pbc-scheme-conventions`: a convention-only node, intentionally with no
  declaration. Its recorded meanings are Mathlib `CompactSpace`, `QuasiSeparatedSpace`,
  `QuasiCompact`, `QuasiSeparated`, and `LocallyOfFinitePresentation`. The local-finite-
  presentation class in `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` checks
  finite presentation of every induced affine-open ring map; QuasiSeparated checks
  quasi-compactness of the diagonal. We use these meanings directly, without copying them.
- `def-weil-closed-immersion`: its Mathlib match is
  `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: closed embedding plus
  surjective stalk maps. This is used for each transition, projection and envelope.
- `lem-weil-pbc-limit-affine-transition`:
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`,
  `AlgebraicGeometry.exists_limit_affine_transition`. Its full statement and docstring
  were read; it represents inverse limits by `Cone D` and `Nonempty (IsLimit c)`.
  We import its module and reuse that Mathlib cone/limit encoding; its affine-transition
  existence theorem is a proof dependency, not an additional hypothesis on our statement.

Edge cases checked before writing: empty X is allowed; empty S forces empty X and
causes no excluded case; a singleton directed set works when f is already finitely
presented; nonempty I is explicit, so no empty-system limit is being asserted; identities
are included among transitions and are closed immersions. No reducedness, Noetherian
condition, field, characteristic, nonempty scheme, or affine-base assumption is added.
The conclusion does not assert that X itself has finite presentation (a proper closed
subscheme can be defined by a non-finitely-generated ideal). The upper-tail restriction
in the source proof is nonempty and directed and preserves the scheme limit.

Searches for an existing statement:

- `msearch.py ... leansearch`: "proper scheme is an inverse limit of proper finitely
  presented schemes over a quasi compact quasi separated base". Service unavailable
  (Internal Server Error); no verdict inferred from this search.
- `msearch.py ... leanfinder`: "proper scheme over a quasi-compact quasi-separated base
  is a limit of proper finitely presented schemes with closed immersion transitions".
  Eight hits: isProper_eq/iff, finite morphisms proper, limits preserving affine or
  quasi-affine properties, compactSpace_of_isLimit. None supplies this approximation.
- `msearch.py ... loogle`: "AlgebraicGeometry.IsProper,
  AlgebraicGeometry.LocallyOfFinitePresentation, AlgebraicGeometry.IsClosedImmersion".
  Zero hits.
- `msearch.py ... grep`: "09ZR|IsProper.*IsLimit|IsLimit.*IsProper", AlgebraicGeometry.
  Zero hits.
- `rg` in WeilConjectures and lean/Sheaf for
  `proper.*(finitePresentation|finite_presentation|FinitePresentation)|09ZR|` followed
  by the exact item ID: no hits. Reading/searching the source AffineTransitionLimit
  module also finds no proper-limit approximation.
- `rg` for the proposed full declaration suffix in Mathlib, WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json: no collision.

No disputed statement or dependency fault was found. The convention-only dependency
needs no replacement module.

## Second reading by G1

I read the node statement, its Stacks source place (Limits, Tag 09ZR), the dependency
records, and the submitted module independently. The item-by-item rendering is:

- `f : X ⟶ S` and `[IsProper f]` render the proper morphism hypothesis exactly.
- `[CompactSpace S] [QuasiSeparatedSpace S]` render the qcqs base convention.
- The existential binders `I : Type u`, `PartialOrder I`, `Nonempty I`, and
  `IsDirected I (· ≤ ·)` render a nonempty directed index set in the scheme universe.
- `D : Iᵒᵖ ⥤ Scheme.{u}`, `p : D ⟶ const S`, and `π : const X ⟶ D` render the inverse
  system of S-schemes and compatible maps from X.
- The first conjunction gives, at every stage, `IsProper`, `LocallyOfFinitePresentation`,
  `QuasiCompact`, and `QuasiSeparated` for `p.app i`, exactly the finite-presentation
  convention used by the node.
- The next conjunction quantifies every arrow and asserts `IsClosedImmersion (D.map a)`,
  rendering all transition maps as closed immersions.
- The projection conjunction asserts both `IsClosedImmersion (π.app i)` and
  `π.app i ≫ p.app i = f` for every stage, rendering the compatible S-morphisms.
- `Nonempty (IsLimit (Cone.mk X π))` renders the scheme inverse-limit clause with the
  stated vertex and cone maps.
- The final existential over `Y`, `i`, and `g` has closed immersion, properness, all
  three finite-presentation clauses, and `i ≫ g = f`, rendering the in-particular clause.

No mismatch was found; no source, dependency, or Lean statement change was needed.
The empty scheme and empty base cases remain admitted where the source admits them;
the index is explicitly nonempty, singleton directed systems are allowed, identities
are covered among transitions, and no Noetherian, reducedness, characteristic, field,
or affine hypotheses are introduced. Universes are shared (`I : Type u` and
`Scheme.{u}`), so no case is excluded. Existing-definition searches (LeanSearch,
LeanFinder/Loogle, and repository/Mathlib `rg`) found no equivalent declaration.

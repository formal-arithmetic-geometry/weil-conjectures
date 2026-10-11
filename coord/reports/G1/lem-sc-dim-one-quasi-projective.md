## Worker report

The module Sheaf.AlgebraicGeometry.DimOneQuasiProjective states
AlgebraicGeometry.exists_closed_open_immersion_projectiveSpace_of_dim_le_one,
with a single sorry proof and no new definitions. The node is unchanged outside lean.

Hypothesis and clause correspondence:
- A field k: `{k : Type u} [Field k]`, with arbitrary explicitly declared universe u.
- A scheme X over k: `{X : Scheme.{u}} (f : X ⟶ Spec (.of k))`. This is the explicit
  structure-morphism presentation of Scheme.Over, rather than a new notion of scheme over k.
- Separated structure morphism: `[IsSeparated f]` (not the stronger IsProper f).
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, exactly the two conditions
  of def-weil-finite-type-morphism.
- Topological Krull dimension at most one: `hdim : X.dim ≤ 1`, using the dependency's
  Scheme.dim. Its companion Scheme.dim_eq_topologicalKrullDim identifies this with
  the topological dimension, including the empty scheme. This equality is a stage-2
  theorem with sorry, as expected; the definition itself has real data.
- An integer N ≥ 0: `∃ N : ℕ`, covering exactly all nonnegative integers, including zero.
- A scheme U over k: `∃ (U : Scheme.{u}) (g : U ⟶ Spec (.of k))`.
- Closed immersion X → U: `i : X ⟶ U` and `IsClosedImmersion i`.
- Open immersion U → P^N_k: `j : U ⟶ Proj.projectiveSpaceOverAffine
  (ULift.{u} (Fin (N + 1))) k` and `IsOpenImmersion j`.
- P^N_k is literally Proj(k[x_0,...,x_N]): the existing project's
  Proj.projectiveSpaceOverAffine is Proj of MvPolynomial.homogeneousSubmodule,
  the total-degree grading. ULift merely places the N+1 variable indices in universe u.
  We intentionally use this absolute polynomial Proj instead of the project's relative
  ProjectiveSpace, whose source records its comparison with the affine Proj as a TODO.
- Both maps are over k: `i ≫ g = f` and
  `j ≫ Proj.projectiveSpaceOverAffineToSpec (ULift.{u} (Fin (N + 1))) k = g`.
- The equivalent locally closed immersion clause is the exhibited closed/open factorization;
  it introduces no additional hypothesis or extra choice of unrelated immersion.

Dependency declarations inspected and used:
- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Scheme and Scheme.Hom.
- def-weil-scheme-over-base: Mathlib.AlgebraicGeometry.Over, Scheme.Over and Hom.IsOver;
  use their explicit structure morphisms and defining commutativity equations.
- def-pc-proj: Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme, AlgebraicGeometry.Proj;
  instantiated through WeilConjectures.AlgebraicGeometry.ProjectiveSpace,
  Proj.projectiveSpaceOverAffine and Proj.projectiveSpaceOverAffineToSpec.
- def-pc-dimension: Sheaf.AlgebraicGeometry.Dimension, Scheme.dim;
  Scheme.dim_eq_topologicalKrullDim justifies the topological reading.
- def-weil-proper-morphism: Mathlib.AlgebraicGeometry.Morphisms.Separated, IsSeparated
  (the separated clause of the node's recorded proper-morphism notion).
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  LocallyOfFiniteType, and Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact, QuasiCompact.
- def-weil-open-immersion: Mathlib.AlgebraicGeometry.OpenImmersion, IsOpenImmersion.
- def-weil-closed-immersion: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion,
  IsClosedImmersion; the closed/open factorization is the definition of immersion.
The imports supply these declarations transitively where no separate import is needed.

Source checked: https://stacks.math.columbia.edu/tag/0A25, Lemma 33.43.3.
The local Stacks TeX file is absent on this machine; the official online tag states precisely
separated, finite type over a field, dimension ≤ 1, and concludes an isomorphism to a locally
closed subscheme of projective n-space over Spec k. Its proof follows the three steps of
this node: ample invertible sheaf (09NZ), immersion (01VS), definition of H-quasi-projectivity.
The docstring carries each step and its DAG dependency. No correction or dispute is needed.

Edge cases checked before writing: the empty scheme has dimension bottom and is allowed,
with its closed immersion into an empty open U of P^0_k. Dimension-zero schemes are allowed,
including nonreduced finite k-schemes. Reducible, singular and nonreduced curves are not
excluded; there is no smoothness, integrality, connectedness or nonemptiness hypothesis.
N=0 is allowed. Fields of every characteristic and arbitrary universe u are allowed.
Using the common scheme/ring universe is the standard Scheme category interface: any
particular field and scheme can be placed in a common larger universe.

Searches:
- msearch.py leanfinder: "A separated finite type scheme over a field of dimension at most
  one admits a locally closed immersion into projective space" returned eight hits, chiefly
  Proj separatedness and finite-type/proper structure morphisms; none states this theorem.
- msearch.py loogle: "AlgebraicGeometry.IsQuasiProjective, topologicalKrullDim" returned no
  hits, with unknown identifier AlgebraicGeometry.IsQuasiProjective in Mathlib.
- msearch.py leansearch: "separated finite type scheme dimension at most one quasi projective"
  was unavailable (Internal Server Error), not a negative mathematical result.
- msearch.py grep: "quasi.?[Pp]rojective|dim.*one.*projective" in AlgebraicGeometry returned
  zero Mathlib hits.
- rg on WeilConjectures and lean/Sheaf for quasi-projectivity, dimension-one projectivity,
  and the item ID found IsQuasiProjective and IsCurve.isQuasiProjective in the source.
  Reading the full signatures shows the latter requires IsCurve and Smooth, hence is
  strictly narrower. Group-scheme and abelian-variety results are also special cases.
- rg for the new full declaration suffix in Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found no name collision.

Validation: server compilation succeeded in 1.6 seconds with exit code 0 and no warnings.
The deliver2.py --no-push dry run printed OK: compilation and preflight passed except
for the independent second reading, which the tool explicitly reserves for the second reader.
Nothing was pushed.
The second reading is left to the independent second reader, as instructed.

## Second reading by G1

I independently compared the node with the Stacks source (Varieties, Lemma 0A25,
Tag 0A25) and then matched every binder and conclusion clause with
`AlgebraicGeometry.exists_closed_open_immersion_projectiveSpace_of_dim_le_one`.
The field `k` is rendered by `{k : Type u} [Field k]`; `X` and its structure map
by `{X : Scheme.{u}} (f : X ⟶ Spec (.of k))`.  The separated and finite-type
hypotheses are exactly `[IsSeparated f]`, `[LocallyOfFiniteType f]`, and
`[QuasiCompact f]`, with no Noetherian, smoothness, connectedness, or
nonemptiness assumption.  The dimension bound is `(hdim : X.dim ≤ 1)`, using
the dependency's scheme dimension and its comparison with topological Krull
dimension.  The conclusion introduces `N : ℕ` (therefore `N ≥ 0`), `U`, its
structure map `g`, and maps `i` and `j`; the four conjuncts render respectively
closed immersion, open immersion, `i ≫ g = f`, and
`j ≫ Proj.projectiveSpaceOverAffineToSpec ... k = g`.  Thus the maps are over
`k`, and the displayed Proj is the absolute polynomial Proj used by the node.
Every node clause and quantifier is present in the same order.  I found no
mismatch and changed no Lean declaration or statement.

Edge cases checked: `N = 0`, empty and zero-dimensional schemes (including the
empty scheme), reducible or nonreduced dimension-one schemes, all field
characteristics, and arbitrary common universe `u` are admitted.  The empty
scheme has `X.dim = ⊥`, so the bound is meaningful.

Searches were repeated with `rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`,
and with the recorded LeanFinder/Loogle/LeanSearch queries.  They found only
generic or narrower quasi-projectivity predicates (for example `IsCurve` with
smoothness), no declaration of this theorem.  No full-name collision exists.
The module compiles cleanly with `scompile.py`; no warning occurs other than the
permitted `sorry` proof warning (suppressed by project options).

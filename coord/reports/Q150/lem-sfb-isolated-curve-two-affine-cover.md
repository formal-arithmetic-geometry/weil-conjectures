## Worker report

The delivery states `AlgebraicGeometry.exists_isolated_curve_two_affine_cover` in
`Sheaf.AlgebraicGeometry.IsolatedCurveTwoAffineCover`. Its proof is `sorry`, the
only postponed declaration in the module. No definitions or helper nodes are
introduced. The node copy changes only `lean`.

Source checked: `literature/stacks-project/examples-defos.tex`, Tag 0DZP,
`lemma-curve-isolated`, statement and first proof paragraph (lines 2814–2852).
That paragraph chooses U₂ containing the marked and generic points, U₁ avoiding
the marked points and covering the complement, and U₁₂ their intersection.
The node supplies the finite-type and affine-intersection details explicitly.
The Lean statement keeps these details and makes no source correction.

The hypothesis and conclusion correspondence is:

| Node text | Lean rendering |
| --- | --- |
| k is a field | `(k : Type u) [Field k]` |
| X is a k-scheme | `(X : Scheme.{u}) (f : X ⟶ Spec (.of k))`, with f its structure morphism |
| separated | `[IsSeparated f]` |
| finite type over k | `[LocallyOfFiniteType f] [QuasiCompact f]`, the recorded finite-type conjunction |
| topological dimension at most one | `hdim : topologicalKrullDim X ≤ 1` |
| P is a finite set of points | `(P : Set X) (hP : P.Finite)` |
| each marked point is closed | `hclosed : ∀ x ∈ P, IsClosed ({x} : Set X)` |
| f is smooth on X minus P | `hsmooth : ∀ x ∉ P, ∃ W : X.Opens, x ∈ W ∧ Smooth (W.ι ≫ f)` |
| affine open subschemes U and V | `∃ U V : X.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ ...` |
| X = U union V | `U ⊔ V = ⊤` |
| P is contained in V | `P ⊆ (V : Set X)` |
| U avoids P | `Disjoint (U : Set X) P` |
| intersection is affine | `IsAffineOpen (U ⊓ V)` |
| U is finite type over k | `LocallyOfFiniteType (U.ι ≫ f) ∧ QuasiCompact (U.ι ≫ f)` |
| V is finite type over k | `LocallyOfFiniteType (V.ι ≫ f) ∧ QuasiCompact (V.ι ≫ f)` |
| intersection is finite type over k | `LocallyOfFiniteType ((U ⊓ V).ι ≫ f) ∧ QuasiCompact ((U ⊓ V).ι ≫ f)` |
| U is smooth over k | `Smooth (U.ι ≫ f)` |
| intersection is smooth over k | `Smooth ((U ⊓ V).ι ≫ f)` |
| empty scheme and empty P are allowed | no nonemptiness, positive-dimension, integrality or nonempty-marking binders |

Here `W.ι`, `U.ι`, `V.ι` and `(U ⊓ V).ι` are the actual open-subscheme
inclusions; composition with f is their induced k-structure. The local form of
`hsmooth` is exactly smoothness away from P: smoothness is local on the source,
and P is closed since it is a finite union of closed singletons. Restrict each
smooth neighbourhood to the open complement to obtain smoothness there;
conversely its open inclusion into X gives the displayed neighbourhoods. Thus
this formulation neither assumes that the marked points are singular nor
requires global smoothness of X. An explicit structure map follows the recorded
`exists_isAmple_of_dim_le_one` interface and the adjacent isolated-curve modules.

All statement dependency declarations were read in their recorded source files:

| Dependency | Module and declarations used |
| --- | --- |
| def-weil-field | `Mathlib.Algebra.Field.Defs`: `Field` |
| def-weil-proper-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Proper`: the recorded `AlgebraicGeometry.IsSeparated` clause, defined in its Separated import |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact` |
| def-kun-topological-krull-dimension | `Mathlib.Topology.KrullDimension`: `topologicalKrullDim` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` |
| def-pc-scheme | `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms; `Mathlib.AlgebraicGeometry.AffineScheme`: `AlgebraicGeometry.IsAffineOpen` |

All recorded proof dependency modules are imported, using plain imports for
those needed only by the proof. In particular:

- `Sheaf.AlgebraicGeometry.ExistsAmpleOfDimLEOne`:
  `AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_dim_le_one`.
- `Sheaf.AlgebraicGeometry.AmpleFiniteSetAffine`:
  `AlgebraicGeometry.Scheme.exists_affineOpen_of_isAmple`.
- `Sheaf.AlgebraicGeometry.AmpleFinitePrincipalAffine`:
  `AlgebraicGeometry.Scheme.Modules.exists_affine_section_neighbourhood_of_finite`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`:
  `IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero`.
- The remaining Mathlib leaves are provided by the explicit Noetherian.Defs,
  Noetherian, Properties, Irreducible, Affine and QuasiSeparated proof imports,
  or the public Scheme, FiniteType, Proper, Smooth and KrullDimension imports.
  These give Noetherianity over a field, finitely many components, sobriety,
  component containment, affine intersections, affine quasi-compactness and
  quasi-separatedness, `QuasiCompact.of_comp`, finite type of open immersions,
  composition/base change of finite-type maps, and smooth composition of open
  immersions. No import cycle is introduced and no recorded import is omitted.

Edge cases checked before writing and again on the final signature:

- X empty: topological dimension is bottom, P must be empty, and both opens may
  be empty affine schemes. Every finite-type and smoothness clause is valid.
- P empty: `hsmooth` requires smooth neighbourhoods at every point, exactly
  global smoothness; it does not force a point or a nonempty open.
- Dimension zero, including P = X: the finite-type scheme is affine, and U may
  be empty with V = X. Smoothness is not imposed on V or the marked points.
- Finite fields, imperfect fields, disconnected schemes and nonreduced schemes
  remain allowed: there are no assumptions excluding them.
- A marked smooth point is allowed; membership in P is not equated with failure
  of smoothness. No equidimensionality or rationality of marked points is added.

Searches for an existing declaration (all performed before writing):

1. `msearch.py ... leanfinder` with query
   “A separated finite type curve over a field has a two affine open cover
   separating a finite set of closed points with smooth first open and smooth
   intersection”: eight hits, including `IsSeparated.hasAffineProperty`,
   `Scheme.affineCover`, `Scheme.affineBasisCover` and affine refinements;
   none has this two-open, finite-point separation statement.
2. `msearch.py ... loogle` with query
   `AlgebraicGeometry.IsAffineOpen, AlgebraicGeometry.Smooth`: six hits for
   `Smooth.mk`, `Smooth.smooth_appLE`, its alias, `smooth_iff`,
   `Smooth.exists_isStandardSmooth`, and its local characterization. These
   concern smooth charts, not a two-affine cover.
3. `msearch.py ... grep` with expression
   `two_affine|isolated.*curve|curve.*isolated|affine.*cover`, restricted to
   `AlgebraicGeometry`: 25 hits for general affine covers and Proj charts,
   none supplying the required marked-point separation.
4. `rg` over `lean/WeilConjectures`, `lean/Sheaf` and
   `dag/lean_names_upstream.json` for
   `two_affine|isolated.*curve|curve.*isolated|exists.*[Aa]ffine.*[Cc]over`;
   and `grep -rn lem-sfb-isolated-curve-two-affine-cover lean/WeilConjectures`:
   no exact declaration. `exists_affine_complement_reciprocal_cover` was read:
   it assumes integrality and exact dimension one and constructs reciprocal
   functions; it is a different statement. `exists_affineOpen_image_away_closed_cover`
   was also read and concerns an affine image in a closed cover.
5. A narrower `rg` for `two.affine|two affine|P ⊆.*V|Disjoint.*P|isolated_curve_two_affine`
   found adjacent isolated-curve statements and general geometry, not this
   declaration. The upstream name index contains no proposed-name collision.

The module compiled cleanly through `scompile.py`, in both its sandbox and
library-module checks. No warning or error was printed. The first SSH attempt
reported a session refusal; the normal retry completed successfully.

No STATEMENT-DISPUTED flag, node fault, new node, dependency repair or statement
correction is needed.

## Second reading by Q150

I reopened the node and final module in this dispatcher-started worker session
and checked every row of the correspondence above. This is a second reading by
the same worker; no second agent was started, as the assignment forbids that.
The maintainer's separate review supplies the independent reading.

The reading checked especially the six finite-type conjuncts (both components
for each of three opens), both smoothness conjuncts, all three affineness
conjuncts, cover equality, containment and disjointness. It also checked that
closedness is only imposed on members of P, that local smoothness is only
assumed off P, and that neither V nor all of X is asserted smooth. Every binder
and the universe u is explicit; the same map f occurs in every structural
composition. No hidden choice, local notation, local instance, helper theorem
or hollow definition occurs. No mismatch was found and no statement change
was made. The docstring contains the seven proof steps and names their DAG
inputs; all theorem proofs in this delivery are `sorry`.

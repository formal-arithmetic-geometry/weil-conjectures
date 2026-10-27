## Worker report

The module `Sheaf.AlgebraicGeometry.NodalNonspecialSmoothDivisor` states
`AlgebraicGeometry.exists_nodal_nonspecial_smooth_divisor`. Its only theorem proof is
`sorry`. There are no new definitions, axioms, dependency repairs, or node corrections.
The node copy changes only `lean`.

Source read: Deligne, *Le lemme de Gabber*, Astérisque 127 (1985), Lemma 4.4 and its
proof, printed p.143, in the primary [Numdam PDF](https://www.numdam.org/item/AST_1985__127__131_0.pdf),
PDF page 13 (zero based). The proof inductively adds smooth rational points to kill
sections of the dualizing sheaf, and obtains the global-sections assertion by
Riemann--Roch. The node's nodal/projective specialization and the refinement avoiding
previously selected points are unchanged. The complete seven-step DAG argument is in
the theorem docstring, including the empty family and the canonical constants map.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| A field k | `(k : Type u) [Field k]` |
| Separably closed | `[IsSepClosed k]`, with no algebraic-closedness or perfectness assumption |
| X/k | `(X : Scheme.{u}) [X.Over (Spec (.of k))]`; the specified structure map is `X ↘ Spec (.of k)` |
| Nonempty | `[Nonempty X]` |
| Projective | `[IsHProjective (X ↘ Spec (.of k))]`, the dependency's finite projective-space embedding convention |
| Geometrically reduced | `[GeometricallyReduced (X ↘ Spec (.of k))]` |
| Geometrically connected | `[GeometricallyConnected (X ↘ Spec (.of k))]`; irreducibility is not assumed |
| Curve | `hdim : topologicalKrullDim X = 1` |
| Nodal geometric fibres | `hnodal : HasNodalGeometricFibres (X ↘ Spec (.of k))`, with its full nonempty connected dimension-one fibre condition and completed local-ring condition |
| Put g = dim H^1(X,O_X) | `(g : ℕ)` and `hg : g = Module.finrank k ((Scheme.Modules.moduleCohomologyOverField k X 1).obj (Scheme.Modules.unit X))` |
| Effective Cartier divisor E | `∃ J : X.IdealSheafData, J.IsInvertible ∧ ...`; E is `J.subscheme` with inclusion `J.subschemeι` |
| O_X(E) | The existing `J.toModulesᵛ = Hom(J.toModules, Scheme.Modules.unit X)` |
| Supported in the smooth locus | `∀ x : J.subscheme, J.subschemeι x ∈ (X ↘ Spec (.of k)).smoothLocus` |
| Degree g | `J.toModulesᵛ.degree k = (g : ℤ)` |
| Degree convention | Existing `Scheme.Modules.degree` is literally `eulerChar k O_X(E) - eulerChar k O_X` |
| H^1(X,O_X(E)) = 0 | `Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj J.toModulesᵛ)` |
| Canonical k -> H^0(X,O_X(E)) is an isomorphism | Bijectivity of the explicitly constructed function described below, with codomain `Γ(J.toModulesᵛ, ⊤)` |
| Sum of g distinct k-rational smooth points | `∃ e : (∐ fun _ : Fin g ↦ Spec (.of k)) ≅ J.subscheme`, with `e.hom ≫ J.subschemeι ≫ X ↘ Spec (.of k) = Sigma.desc (fun _ ↦ 𝟙 _)`; the support clause makes them smooth |
| For g = 0 it is empty | `g = 0 → J = ⊤`, the unit ideal defining the empty subscheme; the displayed coproduct is also empty |

The binder `g` with the equality `hg` is an explicit way to bind the integer introduced
by “Put g”; it does not assume an independent value or a genus constraint. It avoids a
statement-local `let`. The scalar-restricted cohomology functor is the existing
`Scheme.Modules.moduleCohomologyOverField` from the reduced-curve dualizing dependency:
it is `RingedSpace.moduleCohomology` followed by restriction along the specified
`Scheme.globalSectionsRingHom`. Thus genus uses the recorded module-sheaf cohomology,
with its canonical k-action, not the unrelated abelian-sheaf Ext construction.

The canonical constants function sends `a : k` to
`((SheafOfModules.homObjSectionsEquiv J.toModules (Scheme.Modules.unit X)).symm
(a • J.toModulesι)).1 (op ⊤)`.
Here `J.toModulesι` is the actual ideal inclusion. Scalar multiplication is the existing
k-action on sheaf-module morphisms, via `Scheme.globalSectionsRingHom`. The existing
internal-Hom sections equivalence identifies this morphism with a compatible family
of sections of the dual ideal, and evaluation at `op ⊤` is its global section.
Consequently the function is precisely the canonical constants map into H^0, expressed
as global sections; it is k-linear by construction. `Function.Bijective` therefore says
that this particular linear map is an isomorphism, without choosing an arbitrary
isomorphism or merely asserting that the two spaces have equal dimensions.

The disjoint-union clause is scheme-theoretic, not a set-theoretic description of
support. Its isomorphism over k says that E is the reduced disjoint union of g copies
of Spec k. Since `J.subschemeι` is the existing closed immersion, the images of distinct
summands are distinct closed points of X. This supplies multiplicity one and residue
field k, including the required rationality. No arbitrary maps or extra smoothness of
all of X are assumed.

Dependency declarations read and reused:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-pc-separably-closed`: `IsSepClosed`, in `Mathlib.FieldTheory.IsSepClosed`.
- `def-kun-projective`: `AlgebraicGeometry.IsHProjective`, in
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`.
- `def-trf-nodal-geometric-fibres`: `AlgebraicGeometry.HasNodalGeometricFibres`, in
  `Sheaf.AlgebraicGeometry.NodalGeometricFibres`.
- `def-pc-geometrically-irreducible`: the relevant two declarations
  `AlgebraicGeometry.GeometricallyReduced` and `AlgebraicGeometry.GeometricallyConnected`
  from Mathlib's corresponding `AlgebraicGeometry.Geometrically` modules. These are
  exactly the reduced and connected clauses of that multi-notion dependency.
- `def-sc-sheaf-cohomology-functor`: `AlgebraicGeometry.RingedSpace.moduleCohomology`, in
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`. The already defined scalar
  restriction abbreviation is in `Sheaf.AlgebraicGeometry.ReducedCurveDualizingModule`.
- `def-pc-divisor-line-bundle`: `Scheme.IdealSheafData.toModules` and `toModulesι`, in
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`; `Scheme.Modules.dual`,
  in `WeilConjectures.AlgebraicGeometry.Modules.Dual`; and the affine-local Cartier
  predicate `Scheme.IdealSheafData.IsInvertible`, in
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`.
  `WeilConjectures.AlgebraicGeometry.EffectiveCartier` imports them and supplies the
  recorded `Scheme.IdealSheafData.IsInvertible.isInvertible_dual_toModules`.
  The recorded `IsEffectiveCartierCenter` and its equivalence with an invertible kernel
  in `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier` were read;
  the theorem directly uses the ideal-sheaf form of exactly this Cartier notion.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` and `Scheme.Hom.smoothLocus`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, publicly imported by the nodal-fibre module.
- `def-pc-degree-line-bundle`: `AlgebraicGeometry.Scheme.Modules.degree`, in
  `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`.
- `def-pc-euler-characteristic`: `AlgebraicGeometry.Scheme.Modules.eulerChar`, in
  `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`, imported by `EulerChar`.

The module also imports the already stated proof dependencies: projectivity implies
properness; projective coherent finiteness; cohomological dimension and degree from
`EulerChar`; global functions/geometric connectedness; Gorenstein relative dualizing;
reduced-curve dualizing; dense smooth locus from `Morphisms.SlicingFlat`; rational-point
density from `DensePoints`; and the Cartier criterion from `RelativeEffectiveCartier`.
Invertible modules and divisor-line properties are already imported through
`EffectiveCartier`. No statement or proof dependency module needs repair. Local finite
presentation for both `HasNodalGeometricFibres` and `smoothLocus` is inferred from
projectivity/properness, finite type, and the Noetherian field base; it is not imposed
as an extra binder.

Edge cases checked mathematically:

- Genus zero: P^1 and trees of rational components use the empty coproduct and J=top;
  the source's nonemptiness excludes the zero ring of global functions.
- Genus one: a smooth elliptic curve, an irreducible nodal rational cubic, or two P^1's
  meeting twice require one smooth rational point, not a singular point.
- Reducible nodal curves are permitted: neither geometric integrality nor smoothness
  of the entire structure morphism is assumed.
- Separably closed imperfect fields remain permitted; rational-point density is used
  on the smooth open, where it applies over a separably closed field.
- The selected points have multiplicity one because the divisor itself is isomorphic
  to the disjoint union, rather than merely having the same underlying finite support.
- The scheme and field universes are both u, as in the recorded geometric-fibre
  definition. No smaller test universe or independent scalar action is introduced.

Searches actually run (before completing the statement):

- `msearch.py ... leanfinder` with query “A projective connected reduced nodal curve over
  a separably closed field has a nonspecial divisor of degree genus which is a sum of
  distinct smooth rational points”: 8 hits, all Weierstrass-curve nonsingularity or
  point-group formulas; none states this general nodal-curve theorem.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.HasNodalGeometricFibres, AlgebraicGeometry.Scheme.Modules.degree`:
  0 hits; the remote Mathlib search reports the project-specific nodal predicate as an
  unknown identifier. This was not treated as evidence that the project lacked it.
- A second `msearch.py ... loogle` query `IsSepClosed, Module.finrank`: 0 hits.
- `msearch.py ... grep 'nonspecial|Nonspecial|nodal.*divisor' AlgebraicGeometry`:
  0 Mathlib hits.
- `rg` for nonspecial/nodal-divisor words in `lean/WeilConjectures` and `lean/Sheaf`:
  no equivalent theorem; nodal-chart, dualizing, and normalization modules are related
  but do not assert the nonspecial-divisor existence statement.
- `grep -rn` for this item id in `lean/WeilConjectures`: no hits.
- `rg 'nonspecial|Nonspecial' dag/lean_names_upstream.json`: no hits.
- `rg` for `homObjSectionsEquiv`, canonical divisor sections, and dual maps found and
  reused the existing internal-Hom/ideal-inclusion construction. Related inline uses
  in `NodalNormalizationAdjunction`, `NodalLogCanonicalReconstruction`, and the section
  `supportedDivisorSection` of `OrdinarySupportedKummerBoundary` were read. The latter
  is a sheaf morphism for a closed-immersion kernel, not the field-to-global-sections
  map here. The final statement simply uses the existing equivalence inline, adding
  no second definition of the divisor section.

No `STATEMENT-DISPUTED` issue was found. Every universe and variable is explicitly bound;
`autoImplicit` is disabled. The maximum Lean line length is 94 characters.

Validation: `scompile.py Q25 lem-sfb-nodal-nonspecial-smooth-divisor` compiled the module
against the live published build in both its sandbox and final library module names,
with no errors and no unexpected warnings. The final packet is also checked with the
prescribed `deliver2.py --no-push` before delivery.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

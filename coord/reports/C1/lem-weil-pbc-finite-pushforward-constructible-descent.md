## Worker report

The module `Sheaf.AlgebraicGeometry.Curve.FinitePushforwardConstructibleDescent` states
`AlgebraicGeometry.CurveCoefficientPair.isConstructible_of_finite_pushforward`, with
`sorry` as its only proof. No definitions, new nodes, dependency modules or statement
corrections are needed. The node copy changes only `lean`.

Hypothesis and conclusion correspondence:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- X separated, finite type over k, dimension at most one: `P : CurveCoefficientPair k`,
  whose `P.C`, `P.toSpec`, and `P.isCurve` supply X and its structure morphism and
  `IsCurve` property. `IsCurve` extends `IsSeparated`, `LocallyOfFiniteType`,
  `QuasiCompact`, and requires `topologicalKrullDim P.C ≤ 1`.
- Y with these same properties: `{Y : Scheme.{u}}`, `g : Y ⟶ Spec (.of k)`, `[IsCurve g]`.
- Finite k-morphism f: `(f : P.C ⟶ Y) [IsFinite f]` and `hf : f ≫ g = P.toSpec`.
  The latter is exactly compatibility with the structure maps.
- Torsion abelian sheaf F on X: `P.F : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1}`,
  with `P.isTorsion : P.C.IsTorsionAbelianSheaf P.F`.
- Direct image: `(Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F`.
- Direct image is torsion: the explicit binder `hT : Y.IsTorsionAbelianSheaf ...`.
  This is retained even though finiteness of f also implies it.
- The two curve coefficient pairs: P and the literal structure with C = Y, toSpec = g,
  isCurve = inferInstance, F = the direct image, and isTorsion = hT.
  This is ordinary structure assembly using supplied data, not a new definition.
- Constructibility of f_*F: `CurveCoefficientPair.IsConstructible` of that structure,
  the antecedent of the implication. Constructibility of F: `P.IsConstructible`,
  its consequent. This uses exactly the dependency's finite constructible locally closed
  stratification, locally constant restriction, and finite geometric stalk predicate.

Recorded dependencies read and used:

- `def-weil-algebraic-closure`: Mathlib `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic` (available through the curve import).
  Read its polynomial-splitting definition and equivalence with existence of roots.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`,
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`. Read the affine inverse-image and
  finite section-ring map definition. Only the finite clause is needed here.
- `def-weil-pbc-direct-image`: `AlgebraicGeometry.Etale.lowerStar`,
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`. Read the full declaration,
  variables and docstring: it is sheaf precomposition by etale base change.
- `def-weil-pbc-curve-setting`: `AlgebraicGeometry.CurveCoefficientPair`,
  `Sheaf.AlgebraicGeometry.CurveCoefficientPair` (transitive import). Read every field,
  its docstring, and the source's `AlgebraicGeometry.IsCurve` declaration.
- `def-weil-pbc-constructible-torsion`: `AlgebraicGeometry.CurveCoefficientPair.IsConstructible`,
  `Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf`. Read its signature, docstring,
  and underlying `Scheme.IsConstructibleEtaleSheafOfSets` definition in EtaleSheaves.
  The source `Scheme.Stratification` includes constructibility of each locally closed stratum.

Edge cases checked: the empty scheme is allowed by `IsCurve` (dimension bottom ≤ 1);
zero-dimensional, disconnected and nonreduced curves are allowed. No smoothness,
properness, connectedness, nonemptiness, surjectivity of f, or characteristic restriction
is imposed. The zero sheaf has singleton underlying stalks, hence finite stalks.
A finite map need not cover Y; empty fibres there cause no problem, since the counit
argument only projects at points of X. Both schemes and the field have the same arbitrary
universe u, as required by the recorded curve-pair and direct-image definitions; the
coefficient category is exactly their AddCommGrpCat.{u + 1}.

Searches (2026-10-11):

- msearch.py leansearch: "constructibility of an abelian etale sheaf descends from its
  finite pushforward"; service unavailable (Internal Server Error), no verdict inferred.
- msearch.py leanfinder: "An abelian etale sheaf is constructible if its direct image
  along a finite morphism is constructible"; eight hits, on constructible images/preimages
  of subsets, module finite type, condensed locally constant modules, and the etale site;
  none states descent of constructibility of an etale sheaf.
- msearch.py loogle: "AlgebraicGeometry.Etale.lowerStar, IsConstructible"; no hits,
  unknown identifier AlgebraicGeometry.Etale.lowerStar (project declaration is not indexed).
- msearch.py grep: "constructible|Constructible", Mathlib/CategoryTheory; zero hits.
- rg in WeilConjectures and lean/Sheaf for constructible with lowerStar or pushforward,
  in either order: forward pushforward/embedding theorems, pro-etale adic results and
  the sibling finite curve assertions; no descent theorem for torsion abelian curve pairs.
- grep of the item id in WeilConjectures: no hits.
- rg in WeilConjectures/ConstructibleSheaf for constructible with "of" in either order:
  refinement, inverse image, kernel/cokernel and open/closed results; no matching theorem.
- rg of the chosen declaration names in dag/lean_names_upstream.json, Mathlib,
  WeilConjectures and lean/Sheaf: no collision.

Source verification: the local Stacks .tex is absent on this machine. Read the official
[095G](https://stacks.math.columbia.edu/tag/095G),
[03QP](https://stacks.math.columbia.edu/tag/03QP), and
[09BH](https://stacks.math.columbia.edu/tag/09BH) pages. These give pullback stability,
the finite stalk formula, and closure under quotients on Noetherian schemes respectively.
The theorem docstring records the node's six proof steps and their named dependencies.
No mathematical fault or statement dispute found.


## Second reading by C1

Independent second reading on 2026-10-11. Opened the sandbox node, its complete
six-step proof, and the delivered module; then opened all five statement-dependency
nodes and the declarations they record. No mathematical or Lean mismatch found.
The module and node copy are retained verbatim; this section is the only repair
needed to complete the delivery.

Objects, hypotheses, and conclusion, in the node's order:

| Node item | Lean rendering checked | Verdict |
| --- | --- | --- |
| Algebraically closed field k | `{k : Type u} [Field k] [IsAlgClosed k]` | Exact. Mathlib `IsAlgClosed` requires polynomial splitting, equivalent to the node's root condition; no chosen algebraic closure is required. |
| Scheme X over k | `P : CurveCoefficientPair k`, with X = `P.C` and structure morphism `P.toSpec` | Exact. Opened `CurveCoefficientPair`: its fields are C, toSpec, isCurve, F, isTorsion, with no further data or conditions. |
| X separated, finite type, dimension at most one | `P.isCurve : IsCurve P.toSpec` | Exact. Opened the upstream `IsCurve`: it extends `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, and adds `topologicalKrullDim C ≤ 1`. |
| Scheme Y over k with the same curve hypotheses | `{Y : Scheme.{u}} (g : Y ⟶ Spec (.of k)) [IsCurve g]` | Exact. This is the same curve definition, with its structure map explicit. |
| Morphism f : X → Y | `(f : P.C ⟶ Y)` | Exact domain and codomain. |
| f finite | `[IsFinite f]` | Exact. Read Mathlib's class: affine inverse images and finite ring maps on all affine opens. No separate finite-presentation or surjectivity hypothesis is introduced. |
| f a k-morphism | `(hf : f ≫ g = P.toSpec)` | Exact commutativity with the two structure maps; its presence is required even though the proof can use a more general finite map. |
| Torsion abelian sheaf F on the small etale site of X | `P.F : Sheaf P.C.smallEtaleTopology AddCommGrpCat.{u + 1}` and `P.isTorsion` | Exact. Read `Scheme.IsTorsionAbelianSheaf`: the canonical colimit of the positive-integer torsion kernels maps isomorphically to F. |
| Actual direct image G = f_*F | `(Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F` | Exact. Opened upstream `Etale.lowerStar`: continuous sheaf pushforward by the etale base-change functor, objectwise F(V ×_Y X). The general coefficient-category instances are supplied by AddCommGrpCat, not additional hypotheses. |
| f_*F torsion | `(hT : Y.IsTorsionAbelianSheaf (Etale.lowerStar AddCommGrpCat.{u + 1} f |>.obj P.F))` | Exact explicit node hypothesis; retained despite its mathematical redundancy. |
| Both are curve coefficient pairs | P and the literal target structure `{ C := Y, toSpec := g, isCurve := inferInstance, F := ..., isTorsion := hT }` | Exact. The target structure uses exactly G and the supplied torsion proof. This is structure assembly, not another definition of a pair. |
| If G is constructible | `CurveCoefficientPair.IsConstructible` of that target structure, before the implication arrow | Exact recorded dependency predicate. |
| Then F is constructible | `P.IsConstructible`, after the implication arrow | Exact, with the same X and F; neither an existence claim nor the forward implication. |

Read `ConstructibleTorsionCurveSheaf.lean` through `EtaleSheaves.lean` and the
upstream `Scheme.Stratification` and `Topology.Stratification` definitions.
The predicate forgets only the abelian group structure, and requires a finite
partition into locally closed constructible subsets with immersed scheme
representatives. Each inverse-image restriction must be etale locally constant
and have finite geometric stalks. This is precisely the dependency node's
constructibility condition. The set-sheaf pullback is an actual Kan-extension
and sheafification construction, not unspecified data. All dependencies used
by the statement are the recorded declarations, with no private replacement.

Source check: the local Stacks .tex tree is absent. Independently read the official
`etale-cohomology.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex,
at labels `lemma-pullback-constructible`,
`proposition-finite-higher-direct-image-zero`,
`proposition-constructible-over-noetherian`,
`lemma-finite-pushforward-constructible`, and
`section-noetherian-constructible`. Also read the official tag pages
https://stacks.math.columbia.edu/tag/095G,
https://stacks.math.columbia.edu/tag/03QP,
https://stacks.math.columbia.edu/tag/09BH, and
https://stacks.math.columbia.edu/tag/095R.
The source supports the node's composition: inverse image preserves
constructibility, the finite stalk formula makes the counit onto every stalk,
and a quotient is constructible on a Noetherian scheme. The required
Noetherian condition follows from finite type over k. The coefficient-ring
Noetherian hypothesis belongs to the module-sheaf version, not this abelian
version. Tag 095R states the forward direction, with finite presentation;
the delivered converse is expressly the node's composition, rather than a
claim that Stacks directly states it. On these Noetherian curves finite
presentation would in any event follow, so there is no missing source
hypothesis. No node correction, new definition node, or dependency module
is needed, and there is no `statement_change` to review.

Edge cases: `IsCurve` permits the empty scheme (dimension bottom), dimension
zero, disconnected and nonreduced schemes. The finite map may have empty
fibres and need not be surjective. A geometric point of X selects an existing
factor of the finite product, so the counit argument does not require any
factor over points outside the image. The zero abelian sheaf has singleton
underlying stalks and is allowed. The stratification parameter is `n : ℕ`
with indices `Fin n`, so n = 0 is allowed for the empty scheme. No prime,
characteristic, or invertibility condition occurs. The arbitrary universe u
is consistently the field/scheme universe of the recorded curve-pair notion;
all objects can be placed in a common larger universe. Stalk test fields use
this same u, not a smaller independent universe, and coefficient objects
have the stipulated universe u + 1. No unbound universe or variable appears.

Independent searches with different phrasing from the worker:

- `msearch.py ... leanfinder "constructible sheaf reflected by direct image for a finite map of schemes"`: eight hits, all constructible images or inverse images of topological/spectral subsets; none is the sheaf descent statement.
- `msearch.py ... loogle '"IsConstructible", "lowerStar"'`: zero hits.
- `msearch.py ... grep 'IsConstructibleSheaf|constructibleSheaf'`: zero Mathlib hits. The worker's LeanSearch service failure remains explicitly recorded; no match was inferred from that failure.
- Independent rg for constructibility together with `of_`, `lowerStar`, or `pushforward` in upstream ConstructibleSheaf, Mathlib CategoryTheory, and repository lean/Sheaf: forward finite or closed pushforward results, finite-pushforward embeddings, and the sibling curve assertions; no matching converse.
- Broader case-insensitive rg for constructibility with `reflect`, `descent`, `lowerStar`, or `pushforward` throughout upstream WeilConjectures: pro-etale/adic finiteness results and Noetherian approximation descent, which have different sites, coefficients, or conclusions. No existing declaration states this item.
- Exact name and blueprint-id search in `dag/lean_names_upstream.json`, upstream WeilConjectures, and repository lean/Sheaf: no declaration collision; only the sibling proof docstring cites this node.

H5/H6/H8/H9: no definition is added; the only theorem proof is `by sorry`.
The module and theorem docstrings name the source and this blueprint id.
The theorem docstring follows all six proof steps, including stalk counit
surjectivity, cokernel detection, pulled-back stratification and finite
stalks, torsion of the kernel, and quotient constructibility. Imports are
used for the curve constructibility predicate, actual direct image, and
finite morphism hypothesis. All lines are at most 100 characters. Checked
by exact string comparison that `lean.statement` is verbatim the theorem
signature before `:=`, with every binder accounted for above.

Validation: `scompile.py C1 lem-weil-pbc-finite-pushforward-constructible-descent
lean/Sheaf/AlgebraicGeometry/Curve/FinitePushforwardConstructibleDescent.lean`,
run from the sandbox, compiled on the server in 1.9 seconds with exit code 0
and no diagnostics. No statement or implementation change was warranted.

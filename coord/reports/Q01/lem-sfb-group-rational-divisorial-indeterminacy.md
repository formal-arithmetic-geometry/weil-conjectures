## Worker report

The module `Sheaf.AlgebraicGeometry.GroupRationalDivisorialIndeterminacy` states
`AlgebraicGeometry.group_rational_divisorial_indeterminacy`, with a single `sorry`.
The accepted stage-1 split, its statement, and every other node field are preserved;
only the item's `lean` record is added. The inherited stage-1 unchanged-item failure
is superseded by this stage-2 delivery, as coord/brief-stage2.md §0 directs.
No definition node or dependency repair is needed.

I read Milne, Algebraic Groups (2017), 8.17, printed p.152 (PDF p.164), and
Abelian Varieties I, Lemma 3.3, printed pp.17–18 (PDF pp.23–24). These state
empty or pure codimension-one indeterminacy and explicitly identify the latter
with a finite union of prime divisors. The source imposes no properness on G.
The docstring records all six accepted proof steps, including the integral
component of the product and the nonflat diagonal pullback argument.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base field is `(k : Type u) [Field k]`.
- The k-schemes X and G are `Over (Spec (.of k))`; their scheme and structure
  morphism are `.left` and `.hom`. No absolute separatedness is substituted.
- Nonempty integral X is `[IsIntegral X.left]`, whose Mathlib definition includes
  `Nonempty X.left` and integral sections on every nonempty open.
- Separated, finite-type, smooth X is `[IsSeparated X.hom]`,
  `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]`, `[Smooth X.hom]`.
  The two finite-type classes are precisely the convention node's conjunction.
- G's multiplication, inverse, identity and group axioms are the existing
  `[GrpObj G]` in the category of schemes over Spec k. Connectedness is
  `[ConnectedSpace G.left]`. Smoothness, separatedness and finite type are
  the same four classes applied to G.hom. There is no commutativity requirement.
- The dense open is `U : X.left.Opens` with `hU : Dense (U : Set X.left)`.
- The morphism is `f : U.toScheme ⟶ G.left`; the equation `hf` says exactly
  that it is a k-morphism using the canonical structure map `U.ι ≫ X.hom`.
- `D : X.left.Opens` is bound with its exact defining equation `hD`. This is
  an equation for the D introduced in the node, not an extra geometric assumption:
  for every input there is exactly one such D, namely the displayed `sSup`.
  Suprema of opens are unions. Each member V has `hUV : U ≤ V`, an actual
  scheme morphism F, the equation `F ≫ G.hom = V.ι ≫ X.hom` expressing
  k-linearity, and `X.left.homOfLE hUV ≫ F = f` expressing restriction to U.
  Thus the collection is exactly the collection in the node's displayed formula.
  No separately defined maximal-domain notion is introduced or duplicated.
- The first alternative D=X is `D = ⊤` in the opens lattice.
- The second uses `∃ r : ℕ, 1 ≤ r` and families `Z : Fin r → Set X.left`
  and `z : Fin r → X.left`. Fin r merely numbers the node's r subsets.
- The complement equation is `(D : Set X.left)ᶜ = ⋃ i, Z i`.
- For each i the conjunction explicitly gives `(Z i).Nonempty`,
  `IsIrreducible (Z i)`, `IsClosed (Z i)`, the exact generic-point condition
  `closure ({z i} : Set X.left) = Z i`, and
  `ringKrullDim (X.left.presheaf.stalk (z i)) = 1`.
  No multiplicity, distinctness or disjointness is added.

Dependency declarations read and used:

- `Field` (Mathlib's field class), def-weil-field's Mathlib match.
- `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- The convention record fixes no declaration; finite type is the existing
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`
  from Morphisms.FiniteType and Morphisms.QuasiCompact; separatedness is
  `AlgebraicGeometry.IsSeparated` from Morphisms.Separated.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `Mathlib.CategoryTheory.Monoidal.Grp`, `CategoryTheory.GrpObj`, specialized
  exactly as def-sc-group-scheme instructs. The imported upstream
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` documents this encoding
  and supplies the relevant group-scheme environment.
- `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`.
- The canonical open schemes and inclusions are `Scheme.Opens.toScheme`,
  `Scheme.Opens.ι`, `Scheme.homOfLE` in Mathlib.AlgebraicGeometry.Restrict.

Proof-only imports retain the stated dependencies: SmoothGeometricallyNormal
(`smooth_geometrically_normal`), IsRegularScheme (`IsRegularScheme`),
NormalTopologicallyNoetherianComponents (`normal_topologicallyNoetherian_components`),
upstream RegularLocalRing.UniqueFactorization
(`IsRegularLocalRing.uniqueFactorizationMonoid`), upstream EffectiveCartier
(the recorded divisor/line-bundle interface), and Mathlib's FinitePresentation,
Pullbacks, Noetherian and Gluing. Separated and finite-type APIs already enter
through the public imports. The three proof nodes
lem-sfb-group-difference-diagonal-domain, lem-sfb-factorial-affine-rational-poles,
and lem-sfb-factorial-cartier-prime-decomposition have no Lean binding at present;
there is no module to import. They are proof dependencies only, and are retained
in the DAG and named in the proof docstring.

Edge cases checked before writing: U=X and a constant map give D=top. The trivial
group has the same outcome. A zero-dimensional smooth integral X admits no
nonempty codimension-one complement, agreeing with the first alternative.
An empty U cannot be dense in the nonempty integral X. For G_a and f=1/t
on A1 minus zero the complement is the single origin with stalk dimension one;
for G_m and f=t the same complement checks that extension is into G, not its
affine compactification. No characteristic restriction, rational-point choice,
geometric-integrality assumption, or proper-target assumption occurs. Every
scheme point, including nonclosed generic points, is allowed in z. Universes
are explicitly bound and autoImplicit is false; the standard Scheme universe
convention is shared by all recorded scheme-morphism interfaces.

Searches actually run using `/home/ubuntu/weil-launcher-all/batch2/msearch.py`:

- LeanFinder: "The indeterminacy locus of a rational map from a smooth variety
  to a smooth connected algebraic group is a finite union of prime divisors".
  Eight hits, all RationalMap/PartialMap domain, dense-domain or representative
  APIs; no divisorial-indeterminacy theorem.
- Loogle: `"RationalMap", "domain"`. Five hits: RationalMap.domain,
  openCoverDomain, PartialMap.le_domain_toRationalMap, dense_domain, mem_domain.
  I read the local Birational/RationalMap.lean domain definition: it is a union
  of domains of equivalent representatives. It supplies no codimension result.
- Mathlib grep: `indeterminacy|divisorial|rational.*group`, AlgebraicGeometry.
  Zero hits from the wrapper.
- LeanSearch: "The indeterminacy locus of a rational map from a smooth variety
  to an algebraic group has pure codimension one". Eight hits, RationalMap,
  IsOver and function-field/representative/domain APIs; none is this assertion.
- `rg` of both live `lean/WeilConjectures` and `lean/Sheaf` for the item id:
  no existing declaration. Searches for extensionDomain/maximalDomain,
  group indeterminacy and divisorial indeterminacy likewise found no match.
  Broader `divisorial|indeterminacy|rational map.*group` matches concern log
  divisors and blowup elimination of indeterminacy, not this unchanged-source
  group-target purity assertion. All sources were read without modification.

No statement dispute or node fault was found. No statement correction was made.
Initial scompile.py validation compiled the sandbox and library forms cleanly
in 1.6 seconds each. The final delivery dry run recompiles the final file.

## Second reading by Q01

I reread the node and the completed signature in a separate self-review pass;
this is not a claim that a second agent participated. The independent delivery
review remains with the maintainer, as the assignment specifies. The matching
above was checked against the actual binders and conjunction order. In
particular both extension maps are over k, U is contained in every V in the
union, genericity is closure equality, dimension is that of the ambient stalk,
and the second alternative has r positive. The defining equality for D avoids
an opaque helper or a hidden let binder. There were no mathematical mismatches.
I added explicit proof-only imports for the recorded finite-presentation,
fibre-product, regular-scheme and Noetherian inputs during this reading.

The first preflight found the recorded signature included the terminator `:=`;
I corrected the record to end immediately before `:=`, as the gate requires.
The Lean statement itself was unchanged.

## Worker report

Stage-2 statement of `lem-sfb-perfect-solvable-unipotent-torus` in
`lean/Sheaf/AlgebraicGeometry/PerfectSolvableUnipotentTorus.lean`, declaration
`AlgebraicGeometry.perfect_solvable_unipotent_torus`. Its only theorem proof is
`sorry`. The supporting definition module is
`lean/Sheaf/AlgebraicGeometry/SolvableGroupStructure.lean`; every definition has real
data, and none uses a postponed existence statement. No statement correction, no
STATEMENT-DISPUTED flag, and no dependency modules.

The inherited BLOCKED report concerned the already accepted **stage-1** split.
The present live node is split/reviewed by ND with no Lean record and no released
repair note. The 2026-10-22 stage-handoff paragraph of brief-stage2 explicitly
permits this assignment. I preserve the accepted split and source, adding only
its Lean record and the new terminology node to stmt_deps.

### Hypotheses and clauses

- Field and perfectness: `{k : Type u} [Field k] [PerfectField k]`. Mathlib's
  `PerfectField` says irreducible polynomials are separable; its existing
  `Algebra.IsAlgebraic.isSeparable_of_perfectField` implements the stated
  every-algebraic-extension characterization. This is the same notion, not a
  separability hypothesis imposed on later extension fields.
- H is a k-group scheme: `H : Grp (Over (Spec (.of k)))`. The bundle contains the
  recorded `CategoryTheory.GrpObj H.X`, without a second definition of group law.
- Affine and finite type: `hH : IsAlgebraic H` abbreviates `IsAffine H.X.left ∧
  LocallyOfFiniteType H.X.hom ∧ QuasiCompact H.X.hom`. This is the exact finite-type
  convention of the recorded dependency. Every quantified auxiliary subgroup W and
  ambient group G has the same `IsAlgebraic` condition. U and Q have it as conclusions.
- Smooth: `hsm : Smooth H.X.hom`. Connected: `hc : ConnectedSpace H.X.left`,
  which includes nonemptiness. Solvable: `hs : IsSolvable H`, a finite subnormal
  closed series ending at the trivial group, with every predecessor's commutators
  factoring through its successor on all commutative k-algebras. This expresses
  commutativity of the group-scheme quotients, rather than abstract solvability
  merely on k-points. Successive closed immersions into H ensure every term is
  itself affine and of finite type.
- Existence: `∃ U i Q q`. U and Q are bundled k-group schemes; `i : U ⟶ H` and
  `q : H ⟶ Q` are morphisms in the group-object category, hence homomorphisms.
- Smooth connected unipotent subgroup: `Smooth U.X.hom ∧ ConnectedSpace U.X.left
  ∧ IsUnipotent U`, together with `IsClosedSubgroupScheme i.hom.hom` and
  `IsNormalSubgroupScheme i.hom.hom`. The unipotence predicate includes smoothness
  and a closed faithful representation into GL of a finite matrix index, requiring
  `(r(x)-1)^N=0` for an explicit positive natural N on every algebraically closed
  extension field. For smooth affine algebraic groups this is Milne 14.12, exactly
  the node's geometric-point interpretation. It is NOT used for nonsmooth μ_p.
- Torus quotient: `IsTorus Q ∧ IsFppfQuotient i.hom.hom q`. The first says scalar
  extension to the actual Mathlib `AlgebraicClosure k` is group-isomorphic to the
  rank-d product of the recorded standard G_m, for some d : ℕ. The second says q
  is flat, surjective, locally of finite presentation, with U identified with its
  scheme-theoretic kernel, compatibly with i. This represents precisely the fppf
  sheafification of A ↦ H(A)/U(A): q locally lifts every section by its own fppf
  base-change cover, and two lifts have identical image iff their ratio is in U.
  Conversely the algebraic-group fppf quotient map is such an fppf cover and has
  that kernel (Milne Chapter 5). On affine schemes this is the faithfully flat
  finitely presented algebra-cover convention of the node. No arbitrary map,
  arbitrary quotient sheaf, or noncanonical chosen comparison is substituted.
- Maximality: every closed smooth unipotent `j : W ⟶ H` with `IsAlgebraic W`
  factors as `∃ l : W ⟶ U, l ≫ i = j`. This is containment as subgroup schemes.
- Formation under every field extension: `∀ (K : Type u) [Field K] [Algebra k K]`.
  The actual pullback group functor is `extend K`, implemented by
  `(Over.pullback (Spec.map ...)).mapGrp`; its object and map carry the group
  operations by Mathlib, rather than an independent group structure. The theorem
  states that the base-changed U is unipotent, connected, closed and normal, with
  base-changed torus quotient and fppf quotient map, and contains every closed
  smooth unipotent subgroup of H_K. Thus it is the same characterized largest
  subgroup, including extensions K that are imperfect or transcendental. No
  perfectness, algebraicity, or finiteness assumption is imposed on K.
- Automorphisms after every field extension: for each group isomorphism
  `a : H_K ≅ H_K`, `∃ b : U_K ≅ U_K, b.hom ≫ i_K = i_K ≫ a.hom`. This is equality
  of the subgroup with its automorphic image, not just an inclusion on rational
  points. It is weak characteristicness (Milne 1.89), not characteristicness under
  arbitrary nonreduced base-algebra automorphisms (1.91).
- Ambient normality: for every affine finite-type G, `j : H ⟶ G`, smooth G,
  closed j and normal j, conclude `IsNormalSubgroupScheme (i ≫ j).hom.hom`.
  No connectedness or solvability is required of G; its smoothness is retained.

### Dependencies and source declarations

Read all seven original stmt_deps, their records, source signatures and docstrings.
Used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`, `Grp.homMk`;
  the group-object bundle has X and its group structure. Hom maps are `f.hom.hom`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: the recorded
  `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme`,
  `IsNormalSubgroupScheme`. The latter two include the homomorphism and injective
  R-point conditions; closedness is `IsClosedImmersion i.left` and normality is
  normality of its image on every R-point group. Their full source was read.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`, `.Smooth`:
  `LocallyOfFiniteType`, `QuasiCompact`, `Smooth` with their morphism signatures.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` (nonempty preconnected space).
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: the recorded
  `AlgebraicGeometry.StandardGroupSchemes.multiplicative k` and its
  `multiplicativeGroup`, with the Laurent-polynomial Hopf algebra construction.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`:
  `AlgebraicGeometry.GeneralLinearGroup` and `.homMulEquiv`, as recorded on
  **sk-d-geometry**'s closed upstream audit. The separate node
  def-sc-general-linear-group contains additional SL/determinant clauses and has
  no usable binding; it is not restated or rebound just to use the already existing
  GL interface. Its GL notion is already owned by the audited sk-d-geometry.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Over` and `.Monoidal.Grp`:
  `Over.pullback`, `Functor.mapGrp`, group-category product, `Grp.trivial`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`, `IsAlgClosure`;
  `Mathlib.FieldTheory.Perfect`: `PerfectField`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: the recorded `Flat`.
  `LocallyOfFinitePresentation` is the recorded class of
  def-sbc-locally-finite-presentation in `.Morphisms.FinitePresentation`.
- The sole stated proof dependency is the Mathlib-backed
  lem-trf-smooth-fpqc-base-descent: `of_pullback_snd_of_descendsAlong` with the
  `Smooth.DescendsAlong` instance in `Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent`,
  imported as a proof import. Read its type and the instance. The other eight
  proof dependencies have neither lean records nor mathlib_match yet; no imports
  can be attached for them. All nine proof inputs are named in the theorem's six-step
  natural-language proof docstring; those names and the accepted proof are preserved.

### Edge cases and validation

Rank-zero torus is the actual trivial group object; the recursive product handles
all d : ℕ. Series length zero covers the trivial group (the two endpoint isomorphisms
then say G ≅ 1). Matrix dimension zero is allowed and faithful only for the trivial
group; it does not exclude rank zero or zero-dimensional groups. `ULift (Fin n)`
puts the finite index in the required scheme universe without a nonempty-index
assumption. Nilpotence uses N > 0, so no accidental N = 0 condition appears.
The unit section excludes the empty group scheme, consistently with the dependency's
nonempty connectedness convention. Disconnected smooth unipotent W is allowed.
All characteristics are allowed; no false inference of unipotence from points of
nonsmooth μ_p is made. K = k, arbitrary transcendental K, and imperfect K remain
quantified. Fields, schemes and test algebras use the same explicit universe u;
there is no independent smaller test universe that could make a condition vacuous.
Both files have `module`, public dependency imports, exposed public declarations,
`set_option autoImplicit false`, explicit u, and lines of at most 100 characters.
No theorem beyond the item's theorem is postponed.

Server validation with the required scompile.py, both modules together in dependency
order: SolvableGroupStructure clean (8.4 s), PerfectSolvableUnipotentTorus clean
(2.5 s). The initial diagnostic was the scoped Hom group instance for commutators;
`open scoped MonObj` uses Mathlib's existing group instance and repaired it. No
local instance or private notion is introduced.

### Searches

msearch.py searches (all executed and logged in searches.jsonl):

1. LeanFinder: “Smooth connected solvable affine algebraic group over perfect field
   has characteristic unipotent radical and torus quotient”: eight unrelated
   root-pairing/Lie-algebra results, no group-scheme theorem.
2. Loogle: `"Unipotent", "IsSolvable"`: zero hits.
3. grep: `IsSolvableGroupScheme|IsUnipotentGroupScheme|IsTorus|FppfQuotient`: zero hits.
4. LeanSearch: “Solvable group scheme unipotent group scheme torus fppf quotient”:
   eight abstract-group solvability hits, no group-scheme interface.
5. LeanSearch: “Definitions of solvable affine group scheme, torus split over
   algebraic closure, smooth unipotent group scheme and fppf represented quotient”:
   abstract-group solvability plus existing IsAffine/Smooth, which are reused.
6. LeanFinder: “Solvable group scheme finite closed subnormal series commutative
   quotients, torus and geometric matrix unipotence definitions”: abstract groups,
   no matching group-scheme notion.

Local rg searches over lean/WeilConjectures and lean/Sheaf for the item id and
`torus|Torus|Unipotent|unipotent|Solvable|solvable`, then targeted declaration
patterns, found only unrelated Lie/profinite/toric material and the existing
standard and general linear groups. A JSON scan of all definition nodes' statements
found only Lie-algebra solvability, representation-theoretic ind-unipotence, and
monoscheme tori, none the algebraic-group notions here. Whole DAG text search agrees.
`tools/blueprint_refs.py search unipotent` found only sk-lem-curve-sylow-trace;
`search torus` found zero; `ancestor` reports None, preserving the inherited
blueprint.from.node = null with its existing via chain.

Read Milne PDF locally with pdftotext: Theorem 16.33(a)--(c), Definition 6.26,
Section 2.11, Corollary 14.12 (including the nonsmooth μ_p counterexample),
Definition 1.89, Proposition 1.90 and Remark 1.91. The node's weakening from all
unipotent subgroup schemes to smooth ones is retained exactly, not silently
strengthened. No source or blueprint change is needed.

## New nodes

`def-sfb-solvable-group-structure` owns the seven real definitions in
SolvableGroupStructure.lean: the affine finite-type wrapper, actual scalar-extension
functor, rank-d split torus, torus predicate, smooth geometric matrix unipotence,
finite closed-subnormal-series solvability, and represented fppf quotient predicate.
Its source is Milne Chapters 1, 5, Definition 6.26, Section 2.11/Chapter 12, and
Corollary 14.12. These are the missing terminology the item's statement itself
introduces. Existing primitive definitions are reused, notably GrpObj, the subgroup
classes, StandardGroupSchemes.multiplicative and GeneralLinearGroup. All six
executed search records are copied exactly as returned, with their digests, into
mathlib_searches. The new node is cited in the item's stmt_deps; no existing node is
changed except that item's allowed Lean binding and added definition dependency.

Dry-run validation: initial preflight requested `import_flags` on the new node;
added the empty list required by the current schema. Repeated deliver2.py --no-push
passed server preflight and both per-file compiles (0e9af6accb8). The final node
additionally cites the already recorded locally-finite-presentation definition.

## Second reading by Q116

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

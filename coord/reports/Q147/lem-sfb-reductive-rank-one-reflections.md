## Worker report

The main module `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveRankOneReflections`
states `AlgebraicGeometry.RankOneRoots.reductive_rankOne_reflections`. Its only theorem
proof is `sorry`. The companion definition module introduces concrete interfaces needed
by the statement, with no chosen or postponed data. The existing node statement and
accepted ten-step proof plan are unchanged. All statements bind universe `u` and all
variables explicitly, with `autoImplicit false`.

Clause correspondence, in the order of the node:

- Algebraically closed field: `{F : Type u} [Field F] [IsAlgClosed F]`.
- Affine finite-type reductive G: `hG : ReductiveTorusCentralizer.IsReductive G` includes
  affine finite type, smoothness, geometric connectedness and trivial smooth connected
  normal unipotent subgroups. Over an algebraically closed base this is the node's
  reductivity convention. `hT : IsMaximalTorus i` includes the closed torus inclusion.
  Closed subgroups of these affine algebraic groups are affine of finite type, so the
  conclusion does not introduce arbitrary nonalgebraic subgroups.
- Solvability and unipotence conventions: reuse `IsSolvableGroupScheme` (termination of
  the scheme-theoretic derived series), `SolvableGroupStructure.IsUnipotent` (smoothness
  and faithful matrix unipotence), and the existing reductivity predicate. They are not
  new assumptions on G.
- X and Y: `Character T` and `Cocharacter T` are exactly the group-scheme Hom types
  `T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)` and the reverse Hom type.
  Characters use pointwise multiplication in the underlying Hom type: the additive
  reflection formula is therefore `x.hom.hom / α.val.hom.hom ^ pairing x ν`.
- Pairing: the first universal equation says `ν.hom.hom ≫ χ.hom.hom = (𝟙 Gm) ^ pairing χ ν`.
  This characterizes the integer by the actual power endomorphism of Gm, in every
  characteristic; the theorem does not assume a root datum or an arbitrary pairing.
- Adjoint action: existential `a : ModObj T.X G.X` is constrained by
  `a.smul = adjointMap i`, the explicit map `(t,g) ↦ i(t) g i(t)⁻¹`.
- Finite weight decomposition: `(roots T G a).Finite`, `iSupIndep (weight T G a)`,
  `(⨆ χ, weight T G a χ) = ⊤` and the zero-character weight equality with the range
  of `GrpObj.differential i.hom.hom`. Nonroot nontrivial characters have zero weight
  by the definition of `roots`, so this is exactly Lie(T) plus the finite root sum.
  The trivial character in the bundled Hom category is `0`, whose underlying map is `1`.
- W: `Weyl i` is the actual quotient of the all-scalar-extension normalizer by its
  intersection with T(F); since i is a subgroup inclusion, T(F) is contained in that
  normalizer, so the denominator is exactly T(F). `Finite (Weyl i)` asserts finiteness.
- W acts on X and Y: `act : Weyl i →* Aut T` and the all-algebra conjugation equation
  fix the action on T to conjugation by its representative. The character action is
  `(act w).inv ≫ χ`, and the cocharacter action is `ν ≫ (act w).hom`. The next two
  universal clauses assert pairing preservation and permutation of the roots.
- T_α: `s : S ⟶ Grp.mk (GrpObj.ker α.val.hom.hom)` with
  `MultiplicativeType.IsLargestSubtorus s` is the largest subtorus of the actual kernel.
- G_α: `h : H ⟶ G` is closed; its image on every algebra A is precisely
  `ReductiveTorusCentralizer.centralizerPoints (s ≫ kerι ≫ i) A`. That existing
  centralizer definition quantifies over every further algebra extension. The factor
  `j : T ⟶ H` satisfies `j ≫ h = i`.
- Reductive semisimple rank one: `IsReductive H ∧ HasSemisimpleRankOne H`. The latter
  asserts existence of the largest smooth connected solvable closed normal subgroup,
  its represented fppf quotient, existence of a maximal torus in that quotient, and
  dimension one for every such torus. It does not replace semisimple rank by dim H.
- v_α: `v : SL2Hom H` is a natural family of group homomorphisms on actual determinant-one
  2 by 2 matrices over every commutative algebra. This is exactly the affine
  functor-of-points form of the group-scheme homomorphism, by Yoneda. No matrix-group
  representation or arbitrary map is substituted for SL2.
- Central kernel: `(v.app A).ker ≤ Subgroup.center _` for every algebra A, including
  nonreduced A. Derived image: `IsDerivedGroupScheme d.hom.hom ∧ v.IsImage d`; the latter
  is the smallest closed subgroup containing the natural family's images on all algebras.
- Upper unitriangular restriction: `upper : Grp.mk Ga ⟶ H` is closed, is stable under T
  after composition with h, and its differential has image exactly `weight T G a α`.
  The displayed 2 by 2 matrix equation identifies v on every upper-unitriangular point
  with this closed Ga inclusion, hence is an isomorphism onto a one-dimensional root
  subgroup. The tangent image lies in Lie(G), as required.
- Coroot: for every algebra and every multiplicative-group point z, v of the matrix
  `diag(val z, val z⁻¹)` equals z followed by `coroot α` and j. This fixes the same
  cocharacter in Y that the SL2 construction defines, including inseparable central kernels.
- Local reflection: `localReflection : Weyl j` is nonidentity and every other
  nonidentity class equals it. `nH` represents it, `nG.val = nH.val ≫ h.hom.hom`, and
  `QuotientGroup.mk nG = reflection α` identify its image with the global reflection.
- Reflection identity, normalization, uniqueness: the first root clauses assert
  `pairing α (coroot α) = 2`, the formula for every x, and equality of every cocharacter
  satisfying the same formula with `coroot α`.
- Equivariance: for every global Weyl element and roots α,β with
  `β.val = (act w).inv ≫ α.val`, the final equation is
  `coroot β = coroot α ≫ (act w).hom`. Representatives have the specified conjugation
  action, so this is the stated assertion for n in N_G(T)(F).
- Dimension and rational multiples: `Module.finrank F (weight ... α) = 1`; the rational
  line uses `∃ m n : ℤ, n ≠ 0 ∧ χ^n = α^m`. In the free torus character lattice this
  is exactly χ in Qα. Its intersection with roots is expressed as the iff with α or α⁻¹.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.FieldTheory.IsAlgClosed.Basic`:
  `IsAlgClosed`; `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `CategoryTheory.GrpObj`,
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`, `GrpObj.ker` and `GrpObj.kerι`.
  The convention dependency `def-pc-morphism-conventions` has no declaration: properties
  are the existing morphism classes imported through these modules.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `multiplicative`, `additive`,
  `affine`, `map`; `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `IsLargestSubtorus`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`: `IsReductive`,
  `IsMaximalTorus`, `centralizerPoints`; `Sheaf.AlgebraicGeometry.SolvableGroupStructure`:
  `IsAlgebraic`, `IsUnipotent`, `IsFppfQuotient`.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`: `IsSolvableGroupScheme`,
  `IsDerivedGroupScheme`; `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights`:
  `weightSpace`, `IsStable`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Differential`: `GrpObj.Lie`,
  `GrpObj.differential`; `pointsPrecomp` from its infinitesimal-points imports.
- `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`: `Matrix.SpecialLinearGroup`, `map`;
  `Mathlib.GroupTheory.QuotientGroup.Basic`: quotient and `QuotientGroup.mk`;
  `Subgroup.normal_subgroupOf_of_le_normalizer` supplies the normality instance directly.
  `topologicalKrullDim` is Mathlib's existing dimension; no new dimension is defined.

The existing statement dependencies with usable records are imported transitively through
the definition module. Existing proof-dependency modules for self-centralizers, largest
subtori and perfect-solvable groups are imported nonpublicly. The remaining proof
prerequisites have no recorded Lean module in the read repository; they are named in the
main theorem's complete ten-step proof docstring and remain future proof work.

Edge cases checked: T and G trivial or tori have empty root set; all root-indexed
existentials are then vacuous while the weight decomposition and finite W remain. Rank
zero tori are allowed. No CharZero or reducedness hypothesis is imposed. For SL2 in
characteristic two, α = 2χ is a nonzero character even though its differential vanishes;
weights are evaluated using Laurent characters. For PGL2, a central kernel μ₂ may be
nonreduced and v need not be injective on Lie algebras; the statement only requires
centrality on every algebra, the exact root tangent image, and the diagonal formula.
The SL2 and GL2 pairings are 1 and ±1 on coordinate characters; PGL2 pairs its root
with the coroot as 2. The natural-family formulation tests nonreduced rings and the zero
algebra as well as fields. All tests live in the same universe as the base, so there is
no independent small universe making the test condition vacuous.

Searches actually run with msearch.py (recorded in searches.jsonl):

- LeanFinder: "For a reductive algebraic group over an algebraically closed field
  construct root coroot SL2 homomorphisms and Weyl reflections from centralizers of
  root kernels"; eight hits, abstract root pairings or characteristic-zero Lie theory.
- Loogle: `RootDatum, GrpObj.Lie, SpecialLinearGroup`; zero hits, with unknown identifier
  `GrpObj.Lie` in the search service. This was not treated as an exact negative result.
- Grep: `IsReductive|IsMaximalTorus|cocharacter|rootSubgroup`, AlgebraicGeometry; zero hits.
- LeanSearch: "Reductive algebraic group schemes root spaces coroot SL2 Weyl group
  reflections"; eight hits, abstract root pairings and Lie weights, no group construction.
- LeanSearch: "Group scheme normalizer scalar extension quotient maximal torus
  semisimple rank one and natural homomorphisms from SL2"; eight hits, chiefly
  abstract subgroup normalizers, no matching scheme interface.
- Loogle: `"normalizer", "SpecialLinearGroup"`; zero hits.
- Grep: `Weyl|IsReductive|SL2Hom|HasSemisimpleRankOne`, AlgebraicGeometry; zero hits.
- Project rg searches in both `lean/WeilConjectures` and `lean/Sheaf` found the existing
  reductive, torus and weight definitions listed above and no rank-one reflection theorem,
  `SL2Hom`, or semisimple-rank interface. Searching the item id upstream gave no hit.
- DAG definition-node searches and `tools/blueprint_refs.py search` for "root normalizer",
  "semisimple rank", "normalizer quotient", "rank-one root", and "character pairing"
  found no equivalent blueprint definition. `ancestor` reports `blueprint.from.node = None`,
  as in the inherited item; the new node preserves its explicit inherited place and via.

No statement correction, disputed statement, or dependency-record repair is needed.
The Milne source pp.428--430 was read, including the SL2 construction, inseparable
kernel case, and uniqueness. Its 21.1--21.2 and the existing terminology give the
finite-normalizer and character-weight setup. The exact theorem statement and the
new definition module both compiled separately through scompile.py without warnings.

## New nodes

`def-sfb-rank-one-root-interfaces`, in the item's chapter and unit, records only the
missing character/normalizer/rank-one SL2 interfaces. Source: Milne 6.44--6.46,
21.1--21.2, 20.32 and 21.11(a)--(e). `Character` and `Cocharacter` are abbreviations
for existing Hom types, `weight` aliases the existing weight space, roots are its
nonzero nontrivial support, and the conjugation morphism is explicit. The normalizer
is an intersection of comaps of actual point-image normalizers; its quotient uses
Mathlib's quotient group. Semisimple rank one uses the radical's universal property
and the existing fppf quotient predicate. SL2 morphisms are natural maps from actual
matrix SL2 points; their image predicate is the universal smallest closed image.
No assertion from the main theorem is presumed by these definitions. The three
logged search kinds and project/DAG searches are recorded in the node. They found
abstract algebraic tools that are reused, but no existing group-scheme interface.

## Second reading by Q147

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

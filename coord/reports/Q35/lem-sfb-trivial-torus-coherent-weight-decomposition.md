## Worker report

This delivery states the full coherent weight-decomposition node in
`Sheaf.AlgebraicGeometry.TrivialTorusCoherentWeightDecomposition`, with named
statements for its exactness, restriction, vector-bundle, tensor, exterior,
Grothendieck-group and clopen-partition clauses. All these theorem proofs are
`sorry`; their docstrings give the corresponding steps of the node's proof.
The supporting definitions have actual data, not postponed data constructions.
The stage-1 PASS does not obstruct this stage-2 statement delivery.

Hypotheses and objects are rendered as follows.

| Node | Lean |
| --- | --- |
| Field F | `{F : Type u} [Field F]` |
| Split torus of rank r, including zero | `T : Grp (Over (Spec (.of F)))`, `r : ℕ`, `Nonempty (T ≅ MultiplicativeType.splitTorus F r)` |
| Noetherian F-scheme, with no finite-type assumption | `Z : Over (Spec (.of F))`, `[IsLocallyNoetherian Z.left] [CompactSpace Z.left]` |
| Trivial action on Z | `Linearization` acts on each unchanged `z^*M`, for every test-scheme point z |
| Coherent sheaf with descent identity/cocycle | `Linearized` combines the actual module, `RingedSpace.IsCoherent`, and natural group homomorphisms `T(W) →* Aut (z^*M)` |
| Forward action, not inverse weight | `HasWeight` and `IsPure` use multiplication by `characterValue χ t`, not its inverse |
| Character group and integral ring | `Character` is additive notation for actual group-scheme homomorphisms to Gm; `CharacterRing` is `AddMonoidAlgebra ℤ (Character T)` |

Each conclusion is represented as follows.

| Node clause | Lean |
| --- | --- |
| Unique finite coherent weight subobject decomposition | `existsUnique_weightDecomposition`, using `∃! P`, finite nonzero support, coherence and `HasWeight` for every Pχ, and the actual inclusion coproduct cocone |
| Scalar-character condition on geometric fibres and after every algebra extension | `HasWeight` quantifies over every F-test scheme W, point z and torus point t; taking W affine, including nonreduced coefficient algebras over geometric points, gives the required tests. The coproduct and scalar-character conditions characterize the entire weight subobject, rather than just choosing scalar subspaces. |
| Exact extraction and induced morphisms | `weight_summand_exact` gives unique maps between the subobjects, the two inclusion squares, and `ExactTriple` |
| Restriction and field extension | `weight_summand_restriction_fieldExtension` uses every open U and every algebra extension K/F, with the canonical scheme maps and `IsPulledBackDecomposition` |
| Finite locally free summands | First conjunct of `weight_summand_locallyFree_and_closedFibres` uses the existing variable-rank `IsFiniteLocallyFree` |
| Tensor weights add | `tensor_weight_convolution` gives the canonical tensor linearization and the full coproduct indexed by χ+ψ=weight, with the inclusion maps normalized through the actual tensor isomorphism |
| Ordinary/equivariant coherent groups | `ordinaryRelations` and `equivariantRelations` impose all isomorphism and short exact sequence relations. The latter also presents the required character-twist R-action. |
| Normalized R-linear comparison | `existsUnique_characterComparison` and `IsCharacterComparison` send `eχ ⊗ [A]` to the pure-character linearization of A. `pure_character_exists` ensures that this normalization is nonvacuous. The tensor factors are exchanged by the standard ℤ-tensor symmetry to use Mathlib's standard left R-module instance. |
| Tensor operators | `tensor_operators` supplies coherent tensor products and uniquely normalized ordinary and equivariant operators; `comparison_tensor_weights` gives their character-weight formula under the comparison. |
| Exterior polynomial identity | `exterior_operator_polynomial` supplies the actual equivariant exterior powers and pure-zero exterior powers of the underlying weight bundles, all finite locally free, their normalized tensor operators, and a uniform bound beyond which the coefficients vanish. Its polynomial identity is exactly the displayed product with scalar `single (j • χ i) 1`. A list product expresses the finite product in the potentially noncommutative operator ring. Every enumeration of the finite support is allowed. |
| Finite clopen constant-rank partition for every finite family | `finite_clopen_rank_partition` gives clopen U, pairwise disjointness, `iSup U = ⊤`, and a constant `IsFiniteLocallyFreeOfRank` for each bundle on each piece. |
| Groups, comparison and operators componentwise | The same theorem gives ordinary and equivariant product linear equivalences, their restriction normalization on every class (with existence of the restricted objects), the comparison square, and the componentwise identities for all finite locally free tensor operators. This includes each exterior-power operator in the preceding theorem. |
| Closed-fibre vanishing | Second conjunct of `weight_summand_locallyFree_and_closedFibres`: assuming local finite freeness of the summand itself, all closed-point residue fibres subsingleton implies the weight module is zero. No local-freeness assumption on the ambient module gates this clause. |

The functor-of-test-schemes formulation is the full geometric linearization,
not an action only on geometric fibres. Evaluate at `T × Z` to recover the
forward universal action; invert it for the descent isomorphism. Naturality
recovers all its pullbacks, and the monoid-homomorphism law recovers the identity
and cocycle. Thus there is no extra trivialization or assumed decomposition.
All composition, tensor and exterior comparisons are the canonical ones;
section formulas fix the tensor/exterior comparisons, and no arbitrary map
or mere choice of a nonempty type replaces a canonical map.

Dependency declarations used:

- `Mathlib.Algebra.Field.Defs`: `Field`; `Mathlib.AlgebraicGeometry.Scheme`:
  `AlgebraicGeometry.Scheme`; `Mathlib.AlgebraicGeometry.Noetherian`:
  `AlgebraicGeometry.IsLocallyNoetherian`; `CompactSpace` supplies quasi-compactness.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.Grp`, `GrpObj` and actual
  homomorphisms; `Sheaf.AlgebraicGeometry.StandardGroupSchemes`:
  `StandardGroupSchemes.multiplicative` and its recorded group structure.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`:
  `MultiplicativeType.splitTorus`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the current landed Q24
  superset keeps Q25's `Scheme.Modules.IsQuasiCoherentFiniteType` and publicly
  exposes `RingedSpace.IsCoherent` from the upstream coherence module. The
  delivery uses this exact kernel predicate and imports both the recorded
  module and its upstream owner explicitly, since the compiler cache initially
  exposed the older version of the recorded module.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Scheme.Modules.tensorPullback`, `tensorPullbackSection`, and
  `tensorPullbackSectionComp`. The local helpers merely expose their actual
  object, map, and composition components.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `Scheme.Modules.smulHom`; `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`:
  `Scheme.Modules.exteriorSheaf` and `exteriorSheafSection`;
  `WeilConjectures.AlgebraicGeometry.Modules.ResidueFiber`:
  `Scheme.Modules.residueFiber`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree` and `IsFiniteLocallyFreeOfRank`.
- Mathlib `Subobject`, `Cofan`, `IsColimit`, `ShortComplex.ShortExact`,
  `Finsupp`, `Submodule.span`, quotient modules, `AddMonoidAlgebra`,
  `TensorProduct`, `Module.End`, and `Polynomial` give the standard underlying
  constructions. All stated proof-dependency modules are imported, preferring
  the upstream WeilConjectures module over its retired Sheaf twin.

Edge cases checked: rank-zero torus; zero coherent module; empty scheme;
empty support and the empty product (the exterior degree-zero unit);
characteristic two; disconnected schemes and variable ranks; arbitrary
nonreduced test algebras; non-finite-type Noetherian schemes. Pullback of a
split decomposition remains a decomposition even without flatness. The
field-extension clause does not incorrectly require the extended scheme to
remain Noetherian. Closed-fibre detection uses a closed point in a nonempty
clopen positive-rank locus, not a Jacobson assumption. Universes and all
parameters are explicitly bound; field extensions and test schemes use the
same arbitrary ambient universe as the source scheme, with no extra equation
on distinct site/coefficient universes.

Searches: `msearch.py` LeanFinder for torus-equivariant coherent weight
classification returned unrelated condensed/representation hits; Loogle
`SheafOfModules, AddMonoidAlgebra, FreeAbelianGroup` returned zero hits;
Mathlib grep `weightSpace|WeightDecomposition|GrothendieckGroup` in
AlgebraicGeometry returned zero hits. LeanSearch for the exact coherent
Grothendieck group returned generic `Algebra.GrothendieckAddGroup` monoid
completion and unrelated character results, not the exact-sequence group.
LeanFinder for character Hom groups found Mathlib's pointwise Hom group
instances; these are used after exposing the missing commutativity property
of the existing Gm multiplication. Project rg and the required literal item
grep found no geometric coherent weight interface. Blueprint search found
no corresponding definition. DAG candidates were read: `def-trf-k0-group`
is finite-projective module K0, `def-sfb-hopf-action-module-data` is the affine
coaction interface, and `def-sfb-pgl-linearized-polarization` concerns PGL
quotient linearizations; none supplies these geometric coherent objects.
The new nodes record the searches and their results.

No statement correction or disputed mathematical clause is needed. The landed
coherence and exterior-power dependency records are retained unchanged.

## New nodes

`def-sfb-trivial-torus-coherent-data` introduces characters, their actual
integral group ring, universal forward linearizations on a trivially acted
scheme, coherent objects, equivariant maps, scalar weights and finite
subobject decompositions. Source: Stacks Groupoids 03LF and 0EKK--0EKL, and
Milne Theorem 12.12. The searches above found no existing geometric definition.
The helper `multiplicative_commutative` states the commutativity of the
already-recorded Gm multiplication; its proof is postponed as a named theorem
with its coordinate proof in its docstring. Its instance contains only that
proof, not any new mathematical data. The new node explicitly includes this
property. All other definitions contain their full actual data.

`def-sfb-coherent-group-presentation` defines the exact ordinary/equivariant
coherent group presentations, their generators, character twist, and the
canonical tensor/exterior/restriction and normalized-comparison predicates.
Source: the item's explicit presentations and Stacks 03LF/0EKL. No existing
exact coherent group or equivariant geometric module interface was found;
the generic monoid group completion and finite-projective module K0 do not
have these generators or relations. No theorem is assumed in constructing
the presented groups.

## Repair of returned delivery

H13 (1): restored `pqf-def-coherent` from current main, retaining the
landed module, file and Q25 primary declaration. During the final dry-run
refresh, Q24's independently landed superset extension became visible. The
sandbox now retains that newer record byte-identically, including its full
`declarations` list. Its public import of the upstream coherence module exposes
`RingedSpace.IsCoherent` alongside Q25's original predicate. `Linearized`,
`Coherent` and `IsWeightDecomposition` use the exact kernel predicate through
`Sheaf.AlgebraicGeometry.CoherentFiniteType`, with an explicit public import of
the upstream owner for the compiled cache predating Q24. No dependency module or record
change is delivered by Q35.

H13 (2): restored the complete `def-sc-sheaf-exterior-power` node byte-identically
from current main, including all eight E1 declarations. `IsExterior` now uses
`Scheme.Modules.exteriorSheaf` and `exteriorSheafSection`, including the section
normalization before and after pullback and the action on each wedge factor.
`exterior_operator_polynomial` uses `exteriorSheaf` for the ordinary weight
summands. The upstream exteriorPower/wedge import has been replaced by the
recorded E1 module.

H3: `weight_summand_locallyFree_and_closedFibres` now has two independent
implications: local finite freeness of M implies that of Pχ; local finite
freeness of Pχ together with vanishing at every closed residue fibre implies
Pχ = 0. The second implication does not assume local finite freeness of M.
Thus it applies even when another weight summand of M fails to be locally free.

Advisory: the item now directly lists the landed owner
`def-sfb-tori-multiplicative-type` in `stmt_deps`. The Gm commutativity helper
remains the same named proposition with its coordinate proof docstring, matched
by the new data node's commutativity clause; it supplies only a Prop field.

Self-check: read the repaired node and all three delivered modules together.
The changes retain the rank-zero, empty-scheme, empty-support, degree-zero and
nonreduced-test cases described above. The two dependency nodes are byte-equal
to main; neither dependency module is delivered. All three delivered modules
are compiled separately through scompile.py before the final dry run.

## Second reading by Q35

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

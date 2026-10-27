## Worker report

Stage 2, NP. The inherited BLOCKED ending confused the NR stage-1 split with a
stage-2 statement delivery. The current item has reviewed.result = pass but no
lean or reviewed_lean record; coord/queue.tsv queues it at stage 2. Its NR report
is headed Stage-1 delivery, and the ledger records the split landing. There is
no released repair note. We preserve that entire accepted split and statement.

The delivery states AlgebraicGeometry.split_solvable_torsors_and_variety in
Sheaf.AlgebraicGeometry.SplitSolvableTorsorsAndVariety. Nothing is proved: its
only theorem has proof sorry. The definition module contains real data and no
sorry. Source read directly from Milne, Algebraic Groups (2017): Definition 6.33
and the following paragraph (printed pp.132--133), Proposition 16.52 and
Corollary 16.53 (p.343), Proposition 16.55 and Corollary 16.56 (p.344).

Hypotheses and conclusions, clause by clause:

- Field k: `{k : Type u} [Field k]`.
- k-group scheme H: `H : Grp (Over (Spec (.of k)))`, with Mathlib's internal
  group operations on H.X, rather than a new group-scheme definition.
- Smooth: `[Smooth H.X.hom]`; connected: `[ConnectedSpace H.X.left]`;
  affine: `[IsAffine H.X.left]`; finite type:
  `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`.
- Split solvable: the antecedent `IsSplitSolvable H` of the first conjunct.
  `SplitSolvableLength` recursively records a finite series, closed normal
  successor inclusions, smoothness and connectedness of every term, and actual
  represented fppf quotient maps with group isomorphisms to the recorded G_a
  or G_m. Length zero is the trivial group, including its group structure.
- Every k-scheme S and represented right torsor P: `∀ (S : Over (Spec (.of k)))
  (P : RepresentedRightTorsor H S)`. P has an actual scheme, structure map,
  action morphism, flatness, surjectivity, local finite presentation,
  quasi-compactness and quasi-separatedness (the latter three say finite
  presentation). The unit and right-associativity laws hold on ALL test schemes.
  `IsPullback (fst P.space H.X) P.action P.projection P.projection`
  says exactly that (p,h) maps isomorphically to (p,ph) in P ×_S P. In particular
  the action is over S; this is not merely an arbitrary action on the point set.
- Zariski local triviality: `P.IsZariskiLocallyTrivial`. For every base point x
  it gives an open immersion j:U→S containing x and t:U×H→P, cartesian over S.
  Hence t identifies U×H with P×_S U over U. The displayed identity
  `t(a,gh) = P.action(t(a,g),h)` is equivariance for the SAME supplied right
  action. This pointwise neighbourhood formulation is equivalent to an open
  cover, with no quasi-compactness assumption on S and no finiteness of the cover.
- Integers r,s≥0: `∃ r s : ℕ`. The isomorphism is in Over(Spec k), hence is a
  k-scheme isomorphism. Its affine factor is the actual spectrum of
  `MvPolynomial (Fin r) k`, via `StandardGroupSchemes.affine`, and its torus is
  the existing `MultiplicativeType.splitTorus k s`. No group decomposition or
  homomorphic splitting is asserted.
- EVERY extension K/k: `∀ (K : Type u) [Field K] [Algebra k K]`, with no
  separability, algebraicity, perfectness or algebraic-closedness restriction.
  `MultiplicativeType.baseChange` is the actual pullback along Spec K→Spec k.
  For every module L on that scheme, `L.IsInvertible` gives
  `Nonempty (L ≅ SheafOfModules.unit _)`. Invertibility is exactly the
  dependency's `Scheme.Modules.IsInvertible`, and the unit is the structure
  sheaf. Universes and variables are explicitly bound and autoImplicit is false.
- Algebraically closed final clause: the second top-level conjunct is
  `IsAlgClosed k → IsSolvableGroupScheme H.X → IsSplitSolvable H`.
  It is OUTSIDE the splitness implication, so it does not assume its conclusion.
  The existing solvability predicate is termination of the scheme-theoretic
  derived series, including nonreduced subgroup structure, as the item specifies.

Dependency declarations used (recorded modules were read with their signatures
and docstrings):

- Mathlib.Algebra.Field.Defs: Field.
- Mathlib.CategoryTheory.Monoidal.Grp: CategoryTheory.GrpObj and Grp; scheme
  specialization and subgroup classes from
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:
  IsClosedSubgroupScheme and IsNormalSubgroupScheme (which extend IsMonHom).
- Mathlib.AlgebraicGeometry.Scheme: Scheme and Scheme.Hom; Over for k-schemes.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: Smooth;
  Mathlib.Topology.Connected.Basic: ConnectedSpace;
  Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed.
- Sheaf.AlgebraicGeometry.StandardGroupSchemes: affine, additive,
  additiveGroup, multiplicative and multiplicativeGroup; these use precisely
  Spec k[y] and Spec k[t,t⁻¹] with their recorded group operations.
- WeilConjectures.AlgebraicGeometry.Modules.Invertible:
  Scheme.Modules.IsInvertible; SheafOfModules.unit is the structure sheaf.
- Sheaf.AlgebraicGeometry.SolvableGroupStructure:
  SolvableGroupStructure.IsFppfQuotient, retaining the quotient map and actual
  kernel isomorphism, with flat surjective locally finitely presented map.
- Sheaf.AlgebraicGeometry.ToriMultiplicativeType:
  MultiplicativeType.baseChange and splitTorus, including the rank-zero product.
- Sheaf.AlgebraicGeometry.GroupScheme.Semisimple:
  IsSolvableGroupScheme and its recursive GroupSchemeDerivedLength, with
  IsDerivedGroupScheme and groupSchemeCommutator; no abstract-rational-points
  replacement for scheme-theoretic solvability.
- New definition dependency listed below: IsSplitSolvable,
  RepresentedRightTorsor and RepresentedRightTorsor.IsZariskiLocallyTrivial.

The available proof dependencies are plain imports: AffineSpaceInvertibleTrivial,
GroupScheme.AffineNormalQuotientGeometry, PerfectSolvableUnipotentTorus,
Mathlib Noetherian, FlatMono, Polynomial.UniqueFactorization,
MonoidLocalization.UniqueFactorization and Localization.AtPrime.Basic. The
stalk-localization Mathlib declarations are already exposed by the scheme imports.
The unstated proof nodes (additive affine torsors, torus frames, normal extension
torsor reduction, factorial-complement extension, unipotent additive series,
and smooth connected derived subgroups) have no module to import. Their exact
steps and node IDs remain in the theorem's proof docstring and unchanged DAG.

Edge cases checked against the definitions and source:

- H=1: series length zero; r=s=0; torsor square forces the projection to be an
  isomorphism. Both zero-dimensional factors use their real terminal objects.
- H=G_a and H=G_m: the two series alternatives; the first gives (r,s)=(1,0),
  the second (0,1). Nontrivial G_m-torsors over general S are allowed: only
  local triviality is concluded.
- Empty S: neighbourhood condition is vacuous, as an open-cover formulation
  requires; the surjective torsor map then also has empty source.
- Arbitrary nonaffine and non-quasi-compact S: no omitted cases or extra binder.
- Arbitrary characteristic, including positive characteristic and k imperfect:
  the first clause only assumes an actual split series. Algebraic closedness is
  required only for the final clause.
- Arbitrary field extensions, including identity, purely inseparable and
  transcendental extensions, are included. Rank s=0 gives the whole affine
  space; r=0 gives the pure torus. No assertion requires r or s to be positive.
- Scheme-theoretic solvability is used rather than solvability of k-points;
  this retains the meaning needed by the Borel-group consumers.

Searches made before writing:

- LeanFinder, "Split solvable algebraic group torsors are Zariski locally trivial
  and the variety is affine space times a torus": 8 hits, led by AffineSpace
  and its affineness/structure-map instances; no theorem matching this item.
- LeanSearch, "Split solvable group scheme finite series additive multiplicative
  quotients and represented right fppf torsor": 8 hits, abstract IsSolvable and
  AddTorsor; no represented group-scheme split series or right torsor.
- LeanFinder, "Represented right group scheme torsor flat surjective finite
  presentation and split solvable group scheme additive multiplicative series":
  8 hits, abstract solvable groups, finite Galois-category automorphisms and
  affine-space maps; no matching definition.
- Loogle, `"torsor"`: abstract Torsor/AddTorsor declarations; Loogle,
  `"split", "solvable"`: gal_isSolvable_of_splits only. The earlier
  `GrpObj, Torsor, IsSolvable` query reported unknown identifier GrpObj;
  the subsequent valid searches above replaced that unsuccessful name query.
- msearch grep, `SplitSolv|splitSolv|Torsor|IsSolvable` in AlgebraicGeometry:
  no Mathlib hits. msearch grep,
  `SplitSolvable|RightFppfTorsor|RightGroupSchemeAction`, globally: no hits.
- rg in WeilConjectures and Sheaf found the existing SolvableGroupStructure,
  ToriMultiplicativeType, GroupScheme.Semisimple and StandardGroupSchemes APIs,
  which are reused. The scheme-action groupoid module gives left-action torsors
  with an equivariant map to a chosen action scheme; it does not give the
  right-action represented torsor and its finite-presentation presentation here.
  Existing EtaleTorsor interfaces concern finite constant groups, and the
  additive sheaf Torsor interface only accepts abelian additive coefficients.
- grep of the item's blueprint ID in WeilConjectures: no existing declaration.
  rg of the proposed declaration names in Mathlib, WeilConjectures and Sheaf:
  no collisions. DAG definition search found no split series definition.
  tools/blueprint_refs.py search 'split solvable' and 'represented right torsor':
  no blueprint nodes. The ancestor command gives blueprint.from.node = None;
  the existing item's full imported via chain is retained in the new node.

No STATEMENT-DISPUTED flag and no statement correction: the original statement
and proof split are unchanged. The item only gains its lean record and definition
statement dependencies. No library source or launcher file was edited directly.

Validation: scompile.py compiled both delivered files separately, including the
private sibling overlay, with no errors or warnings (definition 4.7 s; theorem
17.5 s in library mode). Delivery dry run and final delivery are recorded below.

## New nodes

`def-sfb-split-solvable-right-torsors` introduces the missing split-series and
represented right-torsor interfaces, with their equivariant Zariski triviality
predicate, in Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions. Its source
is Milne Definition 6.33, Sections 2.66--2.72 and Proposition 16.55(c). The new
node cites all existing foundational notions and uses their actual declarations;
it does not replace the standard groups, subgroup schemes, fppf quotient
interface or scalar-extension functor. Its three kinds of actual search records
are included verbatim in mathlib_searches. Abstract set torsors and left-action
moduli torsors are different interfaces; no existing node defines this split
series or this represented right torsor. All four declarations have source and
blueprint docstrings, with no postponed proof or chosen opaque data.

The item also cites the already landed def-sfb-tori-multiplicative-type and
def-sfb-semisimple-group-scheme to name its canonical split torus, base change
and scheme-theoretic derived-series solvability. Those nodes are not changed.

Dry-run repairs: added the empty import_flags list required by the live new-node
schema, separated definition citations into individual brackets, and recorded the
whole theorem signature (the first text occurrence of := was a named argument,
not the declaration body). No Lean or mathematical statement changed.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

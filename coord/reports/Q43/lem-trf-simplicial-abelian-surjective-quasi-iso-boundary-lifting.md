## Worker report

Existing declaration reused: `CategoryTheory.SimplicialObject.trivialKanFibration_of_surjective_of_quasiIso`
in `Sheaf.AlgebraicTopology.SurjectiveQuasiIsoTrivialKan`, already recorded by
`lem-trf-surjective-qis-simplicial-group-trivial-kan`. No new Lean module or declaration.
Read the full declaration and docstring locally and through `scompile.py --source`;
the server source agrees. Read Stacks `simplicial.tex`, Tag 08P1,
`lemma-qis-simplicial-abelian-groups`, including its kernel and normalized-cycle proof.
The mathematical statement is unchanged; a retired explanatory DAG citation is removed with the statement_change record below.

Hypotheses and clauses, individually:

- Simplicial abelian groups: `{X Y : SimplicialObject AddCommGrpCat.{u}}`, for an explicit
  arbitrary universe `u`. The dependency `CategoryTheory.SimplicialObject` is the functor
  category `SimplexCategoryᵒᵖ ⥤ C` (Mathlib.AlgebraicTopology.SimplicialObject.Basic).
- Their morphism: `(f : X ⟶ Y)` is a natural transformation, hence commutes with every
  simplicial operator. The faces are the dependency's `SimplicialObject.δ`.
- Every degree is surjective: `hsurj : ∀ n : ℕ, Function.Surjective
  (f.app (Opposite.op (SimplexCategory.mk n)))`. In particular zero is included.
- The associated alternating complex: `(AlgebraicTopology.alternatingFaceMapComplex
  AddCommGrpCat.{u}).map f` has term `X_n`, differential
  `∑ i : Fin (n+2), (-1 : ℤ)^i.val • X.δ i` from degree `n+1` to `n`, and component
  `f.app (op [n])`. Read AlternatingFaceMapComplex.lean:64–69, 122–163.
- Integer indexing and zero terms: `HomologicalComplex.extendMap ...
  ComplexShape.embeddingUpNat.op` extends the nonnegative chain complex by zero in negative
  chain degrees. Here `Embedding.op` preserves the index function; it reverses the complex
  shapes, NOT the indices. Thus this existing declaration is written with chain indices
  `j`, rather than the node's cochain indices `r=-j`. Its integer chain degree `j` is
  precisely the node's cochain degree `-j`: both have the same group `X_j`, the same outgoing
  map to `X_(j-1)`, and the same incoming map from `X_(j+1)`. Consequently
  `H_j(extend C(X)) = ker(d_j)/im(d_(j+1)) = H^(-j)(s(X))`, naturally in `f`.
  Negative chain degrees (positive cochain degrees) are zero, and degree zero retains `X_0`
  with zero OUTGOING differential. No sign or extra hypothesis arises from this relabeling.
  Read Embedding/Basic.lean:77–83, 209–234 and Embedding/Extend.lean:118–139, 186–192.
- Quasi-isomorphism in EVERY integer degree: `hqis : ∀ n : ℤ, IsIso
  (HomologicalComplex.homologyMap (HomologicalComplex.extendMap ...) n)`.
  Replacing this universally quantified chain index by its negative gives exactly the
  node's universally quantified cohomology condition, including the automatically zero
  groups in the other half of the integers. Read `homologyMap` in
  Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex and the recorded derived-category
  dependency Mathlib.Algebra.Homology.DerivedCategory.Basic (the localization at QuasiIso).
- Underlying simplicial-set map: `Functor.whiskerRight f (forget AddCommGrpCat.{u})`.
  Its domain/codomain are exactly `X ⋙ forget _` and `Y ⋙ forget _`.
- Trivial Kan fibration / every square: `SSet.modelCategoryQuillen.I.rlp` of this map.
  `I` is `.ofHoms (fun n ↦ ∂Δ[n].ι)` for all naturals, and `MorphismProperty.rlp`
  demands `HasLiftingProperty` against each such inclusion. This is a filler with both
  triangles commuting for each commutative square. It assumes no model structure.
- Dimension zero: `SSet.boundary_zero : boundary 0 = ⊥` makes the boundary empty;
  maps from the represented zero-simplex are vertices, so this lifting clause is exactly
  vertex surjectivity. For positive dimension it is the stated boundary condition.
  `boundary` consists exactly of nonsurjective monotone maps, including degenerate ones.
- No multiplicative, finite, model-category or realization hypothesis occurs in the type.
  Imports that construct fibrations do not add hypotheses to the theorem.

Edge cases checked before choosing the record: degree zero uses `X_0`, not the zero group;
only its outgoing differential is zero. In dimension one there are two prescribed vertices
and no face compatibility equations; boundary RLP includes this unchanged. Empty/zero
abelian groups, identity maps, the map zero-to-zero, and arbitrary coefficient universe are
all covered. A nonzero constant kernel would fail the H_0 isomorphism hypothesis, as it must.
Degenerate boundary simplices are included by `boundary`, not just nondegenerate faces.

Source/docstring observation for the maintainer: the reused theorem's proof docstring says
"zero in degree 0 and positive degrees" when describing the reindexed cochain complex.
The term in degree zero is actually `X_0`; it is the outgoing differential that is zero.
The declaration's type has the correct term, and this prose slip does not affect the match.
Its docstring also refers to the current node as a proof dependency. No import is added and
no circular proof is proposed: the current node retains its independent seven-step proof
from 08P1. A stage-3 proof of the shared declaration should use this node's kernel,
normalization, horn and face-factorization proof, rather than apply the twin theorem to
itself. The existing theorem is still `sorry`; stage 2 does not assert a completed proof.

Searches actually run:

- msearch leanfinder: "A degreewise surjective quasi-isomorphism of simplicial abelian
  groups lifts all simplex boundaries". Eight hits: DoldKan inclusion, PInfty and homotopy
  equivalence declarations plus ComplexShape.QFactorsThroughHomotopy. None states the
  boundary-lifting implication.
- msearch loogle: `AlgebraicTopology.alternatingFaceMapComplex, QuasiIso`. Zero hits.
- msearch grep: `quasiIso|[Ss]urjective|trivialFib`, subdirectory AlgebraicTopology/DoldKan.
  Four hits, all NCompGamma.lean:60–65; these concern nonsurjective simplex operators.
- rg of `alternatingFaceMapComplex|surjective.*[Qq]uasi|[Qq]uasi.*surjective|boundary.lifting`
  in the project's Sheaf/AlgebraicTopology and WeilConjectures trees found the existing
  twin theorem above. Its full type and full docstring were read, and its DAG binding was
  located by rg of `trivialKanFibration_of_surjective_of_quasiIso|SurjectiveQuasiIsoTrivialKan`.
- grep of the exact item id in WeilConjectures returned no hits.
- rg of `trivialKanFibration|trivialKan` in the upstream and project AlgebraicTopology
  trees found only the twin theorem; the recorded Enhanced definition was absent.

No new nodes and no STATEMENT-DISPUTED flag.

## Statement corrected

The original statement is preserved verbatim as `statement_change.old_statement` in the
node JSON. The sole text change removes `[def-weil-pbc-trivial-kan-fibration]` after
"trivial Kan fibration". The subsequent explicit definition remains verbatim: every
commutative boundary square in every dimension has a filler, with dimension zero included.
All hypotheses and conclusions remain unchanged. Source: Stacks 08P1 and Definition 08NL.

Reason: the first server preflight rejected the original `stmt_deps` edge because that
node is in `coord/route-pivot-dropped.txt`. The twin theorem already has the same correction.
The retired module is absent locally and `scompile.py --source` reports it unavailable.
Rather than restore retired machinery, use the exact existing Mathlib interface `I.rlp`.
The dependency's original Mathlib match already names this interface. Full definitions
and docstrings were read in CategoryWithFibrations.lean:36–39,
MorphismProperty/LiftingProperty.lean:38–41 and Boundary.lean:33–40, 91–97.
No dependency node/module is delivered. The obsolete statement edge and proof edges are
removed; the last proof step now names Stacks Definition 08NL directly. All seven proof
steps and their mathematical arguments remain intact. The old dependency lists and proof
are preserved verbatim in `statement_change`.

Citer audit: grep of the exact quoted item id found four node files. The item itself
and the horn-filling node reference the id only in metadata, not in dependency lists.
Exactly two nodes cite it in `stmt_deps` or `proof_deps`; both were read in full:

- `lem-trf-cotangent-resolution-coherence`: holds true. Step 3 uses the item for a
  termwise surjective augmentation whose alternating complex is a quasi-isomorphism;
  all-dimensional boundary lifting, including vertices, is unchanged. Its own retired
  definition citations remain a separate inherited issue; its use of this item is valid.
- `lem-trf-surjective-qis-simplicial-group-trivial-kan`: holds true. Steps 1–2 reindex
  chain degrees and apply the item for precisely the same boundary fillers. This binding
  reuses that node's Lean theorem, so future proof work must use the independent Stacks
  proof carried here rather than a circular application. No citer is edited.

## Validation

The delivery wrapper compiles server probes importing the existing theorem module and checking
the recorded existing declaration. The dry-run preflight and the delivery compile
are recorded by the tool output. There are no new files requiring separate module compiles.

## Second reading by Q43

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

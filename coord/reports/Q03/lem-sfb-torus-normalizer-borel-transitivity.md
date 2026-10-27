## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.TorusNormalizerBorelTransitivity`
states `AlgebraicGeometry.torus_normalizer_borel_transitivity`, with `sorry` as its
entire proof. It introduces no definitions and proves nothing. The statement is
unchanged. Its `stmt_deps` gains the two already landed definition nodes
`def-sfb-reductive-torus-centralizer-terminology` and
`def-sfb-borel-subgroup-scheme`, whose existing declarations supply exactly the
maximal-torus and Borel predicates needed here.

Source read: Milne, *Algebraic Groups* (2017), Corollary 17.11, final assertion
and proof, printed p.355, with Theorems 17.9(b) and 17.10, printed pp.354--355.
The final assertion is precisely normalizer transitivity on the Borels containing T.
The latest blueprint is `literature/blueprint/latest/`; the node's recorded
stage-1 source audit identifies this as a supporting algebraic-group prerequisite,
not a standalone blueprint unit. The example module `CompactObject.lean` is now
withdrawn and contains no declarations; the delivered header and public section
follow the current neighboring `BorelMaximalTorusConjugacy.lean` instead.

Hypothesis and conclusion correspondence:

- Algebraically closed field k: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Group schemes over k and homomorphisms: `G T B₁ B₂ : Grp (Over (Spec (.of k)))`,
  with the maps `iT`, `i₁`, `i₂`, `j₁`, `j₂` morphisms in this group-object category.
  The group structures and group-homomorphism compatibility are bundled, and are
  the recorded `GrpObj`/`IsMonHom` notions, not additional data hypotheses.
- Affine finite-type ambient group: `[IsAffine G.X.left]`,
  `[LocallyOfFiniteType G.X.hom]`, `[QuasiCompact G.X.hom]`.
  All named subgroups are closed by their maximal-torus or Borel predicates;
  hence they inherit affineness and finite type from G. Repeating those derived
  properties as hypotheses is unnecessary. Inclusions between closed subgroups
  of G are also closed immersions.
- Smooth connected G: `[Smooth G.X.hom] [ConnectedSpace G.X.left]`.
- Maximal torus T in G: `hT : ReductiveTorusCentralizer.IsMaximalTorus iT`.
  Unfolding gives the closed subgroup property, `MultiplicativeType.IsTorus T`,
  and maximality among closed torus inclusions by factorization. `IsTorus`
  means that scalar extension to `AlgebraicClosure k` is isomorphic as a group
  scheme to `splitTorus ... n`. Since k is algebraically closed, its algebraic
  closure is a k-isomorphic field, so this is equivalent to the node's finite
  product of G_m over k. The recursive `splitTorus` includes its rank-zero unit.
- Borel B₁ and B₂: `hB₁ : IsBorelGroupScheme i₁.hom.hom` and
  `hB₂ : IsBorelGroupScheme i₂.hom.hom`. Unfolding gives closed, smooth, connected,
  scheme-theoretically solvable subgroups and maximality among such subgroups.
  The embedded `IsSolvableGroupScheme` is termination of `GroupSchemeDerivedLength`;
  each successor uses `IsDerivedGroupScheme`, the smallest closed subgroup through
  which the commutator morphism factors. This does not substitute rational-point
  solvability for scheme-theoretic solvability.
- Containment of T in both Borels: `j₁ : T ⟶ B₁`, `hj₁ : j₁ ≫ i₁ = iT`,
  and `j₂ : T ⟶ B₂`, `hj₂ : j₂ ≫ i₂ = iT`. Giving the factorization is equivalent
  to the containment of these closed subgroup schemes. Such a factorization is
  unique because a closed subgroup inclusion is a monomorphism, so these binders
  impose no stronger choice or hypothesis.
- Rational normalizing conjugator: `∃ n : 𝟙_ (Over (Spec (.of k))) ⟶ G.X`.
  The tensor unit of schemes over Spec k is Spec k, so these are exactly G(k).
- Scalar extension n_A: `toUnit (StandardGroupSchemes.affine k A) ≫ n`, the composite
  Spec A → Spec k → G. `affine k A` is the recorded relative Spec of the algebra A.
- Equality nTn⁻¹ = T: the first `Set.range` equality, whose left map sends an
  arbitrary A-point t of T to `n_A * (t ≫ iT.hom.hom) * n_A⁻¹` and whose right map
  is the inclusion of T(A) in G(A).
- Equality nB₁n⁻¹ = B₂: the second `Set.range` equality, with conjugated B₁(A)
  on the left and included B₂(A) on the right. The same n occurs in both equalities.
- Equality as subgroup schemes and the node's functor-of-points clause:
  both equalities lie under `∀ (A : Type u) [CommRing A] [Algebra k A]`.
  The two range maps are images of the given closed subgroup inclusions, and their
  conjugates are natural subfunctors of G's functor of points. Equality on all
  these affine test schemes is equality of the represented closed subgroups,
  not merely an equality on k-points or reduced points. The shared universe u is
  the upstream group-scheme convention and includes the coordinate algebras of
  the schemes in question; it does not use an independent smaller test universe.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (through the field imports).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraic-closedness
  component explicitly identified in `def-weil-algebraic-closure.mathlib_match`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, bundled
  `CategoryTheory.Grp`, and the group structures on hom-sets into group objects.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `AlgebraicGeometry.IsSubgroupScheme`, `IsClosedSubgroupScheme` and their
  pointwise/closed-immersion meaning, used inside the two subgroup predicates.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` as in the
  recorded finite-type conjunction (the finite-type import exposes it).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, including nonemptiness.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `StandardGroupSchemes.affine`,
  `multiplicative` and `multiplicativeGroup` (the latter two through the torus definition).
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsMaximalTorus`.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `MultiplicativeType.IsTorus`,
  `baseChange` and `splitTorus`, read through the maximal-torus definition.
- `Sheaf.AlgebraicGeometry.GroupScheme.Borel`: `IsBorelGroupScheme`.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`: `groupSchemeCommutator`,
  `IsDerivedGroupScheme`, `GroupSchemeDerivedLength`, `IsSolvableGroupScheme`,
  read through the Borel definition.

Proof-only imports follow all currently stated proof dependencies:
`HomogeneousQuotient.exists_homogeneousQuotient`,
`BorelQuotientProperGeometry.homogeneousQuotient_geometry`,
`HomogeneousOrbitQuotientGeometry.exists_homogeneous_fppf_quotient`,
`BorelMaximalTorusConjugacy.borel_contains_maximal_torus_and_conjugacy`
(all in namespace `AlgebraicGeometry`), and Mathlib's subcanonical fpqc topology
in `Mathlib.AlgebraicGeometry.Sites.Fpqc` for representable descent.
`lem-sfb-solvable-proper-fixed-point` has no recorded Lean declaration or Mathlib
match at inspection time, so there is no corresponding module to import yet.
It is a proof dependency only and remains explicitly in the proof docstring.

Edge cases checked before writing: the trivial group and rank-zero torus are
allowed; in a connected solvable group the only Borel is G, so n = 1 satisfies
the intended conclusion; when B₁ = B₂ the identity normalizes T and conjugates
the Borel to itself; for GL₂ with the diagonal torus, a permutation matrix
conjugates the upper and lower Borels and normalizes T, over every test algebra.
No characteristic restriction is imposed. A may be nonreduced (e.g. dual numbers),
or the zero algebra; all are included by the commutative-algebra binders.
An empty ambient group scheme cannot satisfy the group-object identity section,
and connectedness here also includes nonemptiness.

Searches for an existing statement (all using the prescribed `msearch.py Q03
lem-sfb-torus-normalizer-borel-transitivity` wrapper):

- LeanFinder: `The normalizer of a maximal torus acts transitively on Borel subgroups
  containing it in a smooth connected affine group scheme`: 8 hits, including
  `MulAction.IwasawaStructure.is_generator`, `Sylow.isPretransitive_of_finite` and
  Galois-category transitivity; no algebraic-group Borel result.
- Loogle: `"normalizer", "Borel"`: 0 hits.
- Mathlib grep: `borelSubgroup|BorelSubgroup|IsBorelGroupScheme|normalizer.*torus|torus.*normalizer`:
  0 hits.
- LeanSearch: `Two Borel subgroups containing a maximal torus are conjugate by a
  rational point normalizing the torus`: 8 abstract-group hits, including
  `Subgroup.conjAct_pointwise_smul_eq_self` and `Subgroup.conjAct_pointwise_smul_iff`;
  none states this theorem for group schemes.
- Direct rg over `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for `torus.*normalizer.*borel|normalizer.*borel.*trans|borel.*normalizer.*trans`
  found only the proof-docstring citation in `BorelConjugationCover.lean`, not a
  declaration. Searching the exact node id in `lean/WeilConjectures` found nothing.
- Direct rg for `IsBorel`, `IsMaximalTorus` and `IsSolvable` found the reusable
  definitions listed above and the distinct maximal-torus conjugacy theorem.
  Their full signatures and docstrings were read; none states this node's result.

No disputed statement, dependency-module repair, new definition node or statement
correction was needed. Validation used only the prescribed per-file server compile
and delivery wrappers. `scompile.py` successfully compiled the delivered file both
under its sandbox module name and its actual library module name, with no reported
errors or warnings. `deliver2.py --no-push` printed `OK (dry run)` and confirmed
that the commit passes server preflight and compiles. The only postponed proof is
`AlgebraicGeometry.torus_normalizer_borel_transitivity`.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

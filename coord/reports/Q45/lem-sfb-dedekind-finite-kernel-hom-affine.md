## Worker report

The delivery states `AlgebraicGeometry.isAffineHom_of_finite_geometricKernel_over_dedekind`
in `Sheaf.AlgebraicGeometry.GroupScheme.DedekindFiniteKernelAffine`. Its only proof is
`sorry`; it defines no new data. The original node is unchanged except for `lean`.
No statement correction, new node, dependency repair or disputed statement is needed.

Source checked: Conrad, *Reductive Group Schemes*, proof of Proposition 6.3.16,
printed p.229 (PDF page index 228),
https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf. The passage first obtains
quasi-finiteness from finite geometric kernels, then states affineness for a
quasi-finite homomorphism between separated flat groups of finite type over a
Dedekind base. The node combines those assertions. Its independent six-step
proof plan is reproduced in the theorem docstring, with every dependency named.

Hypothesis and conclusion correspondence:

- The commutative domain B is `(B : Type u) [CommRing B] [IsDomain B]`.
- Noetherianity is `[IsNoetherianRing B]`, and integral closedness in its fraction
  field is `[IsIntegrallyClosed B]`. Krull dimension exactly one is the explicit
  hypothesis `(hB : ringKrullDim B = 1)`, not merely dimension at most one.
- The base S is written directly as `Spec (.of B)`; there is no separate arbitrary
  scheme or unrecorded identification of a base scheme with this spectrum.
- Schemes G and J over S are `(G J : Over (Spec (.of B)))`. Their structure maps
  are `G.hom` and `J.hom`; their underlying schemes are `G.left` and `J.left`.
- `[GrpObj G] [GrpObj J]` supply multiplication, unit, inverse and all group diagrams
  in schemes over S. No commutativity assumption is imposed. These are the existing
  Mathlib group objects, as used by the upstream group-scheme interface.
- Separatedness of both structure maps is `[IsSeparated G.hom]` and
  `[IsSeparated J.hom]`. Mathlib defines these by a closed-immersion diagonal.
- Flatness over S is `[Flat G.hom] [Flat J.hom]`.
- Finite type of G and J over S is `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`
  and `[LocallyOfFiniteType J.hom] [QuasiCompact J.hom]`. These are exactly the
  two clauses of the recorded finite-type definition.
- The S-morphism f is `(f : G ⟶ J)` in the over category. `[IsMonHom f]` preserves
  multiplication and unit, and therefore also inverse for group objects.
  Its underlying scheme map is `f.left`.
- Finite type of f is `[LocallyOfFiniteType f.left] [QuasiCompact f.left]`.
- Every algebraically closed field and specified ring map are quantified by
  `∀ (k : Type u) [Field k] [IsAlgClosed k] (φ : B →+* k)` in `hker`.
  The universe is the common scheme/ring universe, not an independently smaller
  test universe. It contains algebraic closures of the residue fields needed
  for every geometric fibre. The result is universe-polymorphic.
- The geometric kernel is
  `((Over.pullback (Spec.map (CommRingCat.ofHom φ))).obj (GrpObj.ker f))`.
  The existing `GrpObj.ker f` is the actual fibre product of f with the identity
  section in the over category. `Over.pullback` forms its actual base change.
  Pullback associativity identifies this with G_k ×_{J_k} Spec k: the identity
  section also base changes, and iterated fibre products represent the same
  functor. This expression avoids choosing or introducing any extra kernel map.
- `IsFinite (...).hom` says that this kernel scheme is finite over k. It does
  not say merely that its k-points form a finite set, and does not assume that
  the kernel over B itself is finite.
- The entire conclusion is `IsAffineHom f.left`, exactly affineness of f. There
  are no extra clauses and no assumptions of smoothness, connectedness,
  affineness of G or J, surjectivity of f, or flatness of f.

Statement dependencies read and used:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Spec` and `AlgebraicGeometry.Spec.map` (source lines 470,479).
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat` (source line 42; its affine-local definition has the
  documented stalkwise equivalence).
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`,
  `AlgebraicGeometry.QuasiCompact` (both source line 43).
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`,
  `AlgebraicGeometry.IsFinite` (source line 39). The integral-morphism predicate
  in the dependency is not needed by this statement.
- `pqf-def-affine-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Affine`,
  `AlgebraicGeometry.IsAffineHom` (source line 47).

The upstream module `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` publicly
imports the existing scheme, finite, affine, separated and quasi-compact modules.
It also imports `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`,
whose `CategoryTheory.GrpObj.ker` signature and full docstring were read:
`ker f := pullback f η[H]`. Mathlib's `GrpObj`, `MonObj` and `IsMonHom`
signatures and group diagrams were read, as was `Over.pullback` in
`Mathlib.CategoryTheory.Comma.Over.Pullback` (its structural map is
`pullback.snd g.hom f`). No alternative group-scheme or kernel definition is added.

Proof-only imports cover the already stated dependencies: algebraic closures,
proper/finite morphisms and finite fibres, surjective base change,
`WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite`
(`locallyQuasiFinite_and_quasiCompact_iff_finite_preimage_singleton`),
`WeilConjectures.AlgebraicGeometry.QuasiFiniteLocallyQuasiFinite`
(`Scheme.Hom.isQuasiFinite_iff_isLocallyQuasiFinite_and_quasiCompact`), and
`WeilConjectures.Mathlib.AlgebraicGeometry.QuasiAffine`
(`IsQuasiAffineHom.of_locallyQuasiFinite`). Separated cancellation, affine
composition and open-immersion base change are supplied by the imported Mathlib
modules. The three proof-only nodes
`lem-sfb-relative-quasiaffine-group-envelope`,
`lem-sfb-field-open-group-image-closed`, and
`lem-sfb-dedekind-vertical-clopen-open-affine` have no recorded Lean modules at
inspection, so no fictitious imports are added for them. Their interfaces are
not required to type this statement.

Edge cases checked before writing:

- The zero ring and fields are intentionally excluded by the domain and exact
  dimension-one hypotheses, respectively; this agrees with the node.
- A group over this nonempty base has a unit, so an empty G or J cannot be a
  group object here. Fibres of f away from its image can still be empty; neither
  the statement nor hker assumes f surjective.
- For the identity on a non-affine abelian scheme, each geometric kernel is the
  unit scheme and the conclusion is affineness of the identity morphism, which
  does not require the group scheme itself to be affine.
- The trivial-group inclusion into a separated group is allowed. Its geometric
  kernel is trivial; the conclusion accords with affineness of a closed unit
  section. This checks the absence of an accidental surjectivity assumption.
- Nonreduced finite kernels, including characteristic-p infinitesimal kernels,
  are allowed by `IsFinite`; no reducedness or characteristic restriction appears.
- Disconnected and nonsmooth group schemes are included. No abstract or
  commutative-group replacement is used.

Searches for an existing exact statement (all on 2026-10-24):

1. `msearch.py ... leansearch` with query "A homomorphism of flat separated finite
   type group schemes over a Dedekind domain with finite geometric kernels is
   affine" returned eight hits: `IsFinite.toIsAffineHom`,
   `IsIntegralHom.toIsAffineHom`, `IsAffineHom`, `isAffineHom_of_isAffine`,
   `IsFinite.recOn`, `IsAffineHom.of_comp`, `IsSeparated.of_isAffineHom`, and the
   affine postcomposition-property instance. None has the group/Dedekind/kernel
   hypotheses or yields this result without an extra assumption.
2. `msearch.py ... leanfinder` with query "A homomorphism of separated flat finite
   type group schemes over a Dedekind domain with finite scheme theoretic kernels
   on geometric fibres is affine" returned eight general affine-morphism hits,
   including `affineAnd`, `IsFinite.toIsAffineHom`, `IsAffineHom.of_comp`, affine
   space, `isAffineHom_of_isAffine`, `isFinite_iff`, `isAffine_of_isAffineHom`, and
   `affineAnd_apply`; no exact match.
3. `msearch.py ... loogle 'IsAffineHom, IsFinite, IsDedekindDomain'` returned no
   hits and reported that the unqualified `IsAffineHom` identifier was unknown.
   This search was inconclusive; LeanFinder and local source searches supplied
   the usable search results.
4. `msearch.py ... grep 'Dedekind|finiteKernel|finite_kernel' AlgebraicGeometry/`
   returned three unrelated uses of Dedekind domains in elliptic-curve sources.
5. `rg` over `lean/WeilConjectures` and `lean/Sheaf` for this exact node id found
   no declaration. The combined query
   `dedekind.*[Aa]ffine|[Aa]ffine.*dedekind|finiteKernel.*[Aa]ffine|finite_kernel.*affine`
   found only the unrelated affine-line `support_finite_kernel_unit_app`.
   The exact id also has no entry in `dag/lean_names_upstream.json`.
6. Concept/source searches for group objects located the existing upstream
   `GroupScheme.Defs`, the Mathlib `GrpObj`/`IsMonHom` structures, the upstream
   canonical kernel, and Mathlib's `Over.pullback`. These are reused.

Validation: the module is compiled individually using the prescribed server
`scompile.py` wrapper. The delivery dry run and final delivery use `deliver2.py`;
no local/global library build or direct Git command is run.

## Second reading by Q45

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

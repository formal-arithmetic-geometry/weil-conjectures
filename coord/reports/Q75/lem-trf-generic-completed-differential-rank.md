## Worker report

Q75 states `Algebra.generic_completed_differential_rank` in
`Sheaf.RingTheory.GenericCompletedDifferentialRank`. There is one theorem, with `sorry`,
and no new definitions or helper theorems. The natural-language statement, proof and
proof dependencies are unchanged.

Hypothesis and clause correspondence (write A = `Localization.AtPrime m`,
R = `Algebra.LocalCompletion A`, N = `KaehlerDifferential k A`, and
M = `Algebra.CompletedDifferentials k A` in this explanation only):

- The perfect base field is `[Field k] [PerfectField k]`.
- The reduced commutative finite-type k-algebra is `[CommRing S] [Algebra k S]
  [Algebra.FiniteType k S] [IsReduced S]`. `Algebra.FiniteType` is the same finite-generation
  condition as the recorded `RingHom.FiniteType (algebraMap k S)`; the latter's body is
  exactly `Algebra.FiniteType` for the map's algebra structure.
- The nonnegative dimension is `(d : ℕ)`. Pure dimension is
  `hpure : (Spec (CommRingCat.of S)).IsPureDimension d`, using the recorded definition.
- The maximal ideal is `(m : Ideal S) [m.IsMaximal]`. The residue-field hypothesis is
  `hresidue : Nonempty (m.ResidueField ≃ₐ[k] k)`, an isomorphism as k-algebras,
  not just an abstract field isomorphism.
- A is the actual quotient-type localization; R is the actual maximal-ideal completion,
  not arbitrary rings with chosen maps. `[IsReduced R]` is retained explicitly.
- N is Mathlib's actual Kähler differential module. M is the existing abbreviation
  `R ⊗[A] N`, canonically the node's `N ⊗[A] R` by tensor symmetry.
- Geometric reducedness is the first conjunct, reducedness of `K ⊗[k] S` for every field
  extension K/k. This reverses the node's tensor factors by the canonical algebra symmetry.
  K ranges over `Type (max u w)`; the universe w is arbitrary and covers larger extensions.
- The second conjunct quantifies over every `q : PrimeSpectrum S` whose ideal belongs
  to `minimalPrimes S`. Smoothness is an open neighbourhood U of q with
  `AlgebraicGeometry.Smooth (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k S)))`.
  This is precisely membership in the smooth locus and uses the dependency's actual
  smooth-morphism definition. `topologicalKrullDimAt q = (d : WithBot ℕ∞)` is the
  local topological dimension, not the Krull dimension of S localized at q.
- The third conjunct quantifies over every minimal prime a of A, and asserts both
  `IsField (Localization.AtPrime a.asIdeal)` and
  `Module.rank (Localization.AtPrime a.asIdeal) ((Localization.AtPrime a.asIdeal) ⊗[A] N)
  = (d : Cardinal)`. Over the asserted field, this is exactly finite dimension d.
  Cardinal rank avoids requiring a field structure as an additional hypothesis; it also
  avoids finrank's value zero on infinite-dimensional spaces.
- The fourth conjunct quantifies over every minimal prime p of R. The comap of p along
  the actual `algebraMap A R` belongs to `minimalPrimes A`. It asserts `IsField R_p`.
  `Localization.localRingHom` is the canonical fraction map from A localized at the
  contraction to R localized at p; its equality-of-contraction argument is `rfl`.
  `Function.Injective` of this particular map says it is a field extension; the domain
  is a field by the third conjunct and the contraction assertion. No arbitrary map is
  substituted. The last part is `Module.rank R_p (R_p ⊗[R] M) = (d : Cardinal)`,
  the stated completed differential rank, with tensor factors symmetrically reordered.
- The last conjunct quantifies over every field L in `Type (max u w)` and every
  `_θ : R →ₐ[A] L`. `[Algebra k L] [Algebra A L] [IsScalarTower k A L]` specify the
  restriction to A. This encodes exactly the original arbitrary k-algebra map from R:
  given it, use its restriction as the A-action, making it A-linear; conversely the
  tower makes each displayed A-algebra map k-linear. These compatibility structures
  impose no injectivity, finiteness or separability on θ or L.
- Its factorization hypothesis supplies a minimal prime a of A, smoothness at its
  contraction in S, local topological dimension d there, and
  `Nonempty (Localization.AtPrime a.asIdeal →ₐ[A] L)`. The A-algebra condition says
  precisely that the factorization agrees with θ on A, not merely that some unrelated
  field map exists. Its conclusion is `Module.rank L (L ⊗[A] N) = (d : Cardinal)`.

Dependency declarations read and used:

- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`, `Algebra.FiniteType`.
- `Sheaf.AlgebraicGeometry.PureDimension`: `AlgebraicGeometry.Scheme.IsPureDimension`.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`,
  `Localization.localRingHom`. `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`:
  `Ideal.ResidueField`. The recorded fibre declaration was also read; no fibre is used here.
- `Mathlib.RingTheory.AdicCompletion.Basic` and `.Algebra`: `AdicCompletion` and its
  actual algebra structure. `Sheaf.RingTheory.FormalLocalPresentation`:
  `Algebra.LocalCompletion` unfolds exactly to this maximal-ideal completion.
- `Mathlib.RingTheory.Kaehler.Basic`: `KaehlerDifferential`, its universal derivation
  and `KaehlerDifferential.linearMapEquivDerivation`.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `TensorProduct`, `LinearMap.baseChange`;
  only the actual tensor product is needed by this statement.
- `Sheaf.RingTheory.CompletedJacobianPresentation`: `Algebra.CompletedDifferentials`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`.
- All stated proof dependencies are imported without `public`, including the recorded
  dense smooth-open, equidimensional local-dimension and smooth-differential statements,
  perfect reduced tensor products, going down, minimal-prime fields, differential
  localization, affine stalks, and Noetherian flat completion. The docstring follows
  the node's six proof steps with their dependency IDs and tensor balancing formulas.

The item gains three already-landed definition dependencies: `def-trf-formal-local-presentation`,
`def-trf-completed-jacobian-presentation`, and `def-kun-topological-dimension-at-point`.
They own the existing LocalCompletion, CompletedDifferentials and local topological
dimension declarations used here. This is the permitted addition of landed notions;
there are no new nodes and no dependency repairs.

Edge cases checked before drafting: d = 0 gives zero-dimensional vector spaces (including
zero completed differentials); a field S = k gives the expected maximal ideal zero and
completion k. The zero ring cannot have a maximal ideal with residue k, so is already
excluded by the actual hypotheses, not by an extra nontriviality assumption. Reducible
pure-dimensional rings retain all minimal primes, including multiple completion branches;
no domain assumption is made. Imperfect fields are correctly excluded, but all
characteristics of perfect fields are allowed. Arbitrary large field extensions use max u w.
Noninjective θ is allowed. A prime at a generic point has zero-dimensional local ring,
while its neighbourhood dimension may be d; these are not conflated. No statement fault
or STATEMENT-DISPUTED flag remains.

Searches actually run using the prescribed `msearch.py Q75` wrapper:

- LeanFinder: “Generic ranks of Kahler differentials of a reduced pure dimensional finite
  type algebra over a perfect field at minimal primes of its reduced local completion”.
  Eight hits, principally standard-smooth rank and rankAtStalk facts; none states this
  combined geometric-reducedness, contraction, completion and arbitrary-factorization result.
- Loogle: `KaehlerDifferential, Module.rank`. Three hits: standard-smooth rank,
  its converse characterization and submersive-presentation rank; none is an exact match.
- Grep, RingTheory/: `rank.*[Kk]aehler|[Kk]aehler.*rank`. Six hits in
  Smooth/StandardSmoothCotangent.lean and Smooth/StandardSmooth.lean, the same special cases.
- LeanSearch: “The dimension of localized Kahler differentials of a reduced pure dimensional
  finite type algebra at minimal primes of its completion over a perfect field”. Eight hits:
  localized differentials, minimal-prime dimension zero, and standard-smooth rank;
  no exact match.
- Local rg of both `lean/WeilConjectures` and `lean/Sheaf`, the upstream name table and
  the exact node ID found no existing combined theorem. Related completion/Jacobian modules
  led to the existing abbreviations reused above. Read the sources of the recorded
  dependencies, including the existing withdrawn CompactObject example and its node record.

Sources read: Stacks varieties.tex, labels lemma-geometrically-reduced-dense-smooth-open
(056V) and lemma-dimension-locally-algebraic (0A21), especially (3), (5);
algebra.tex, lemma-flat-going-down (00HS), lemma-minimal-prime-reduced-ring (00EU);
morphisms.tex, lemma-smooth-omega-finite-locally-free (02G1). The node is an agent-formulated
consequence, not a changed blueprint unit statement.

Validation: scompile.py is used for every compiler invocation. An initial attempt to use
Mathlib smoothLocus exposed a missing inferred LocallyOfFinitePresentation instance;
it was replaced by the equivalent explicit smooth open neighbourhood, with no extra
hypothesis. A subsequent namespace-resolution error was corrected by qualifying
AlgebraicGeometry.Smooth (inside namespace Algebra). No proof was supplied. The final module passed both sandbox and library compilation.
The prescribed deliver2.py --no-push returned OK: preflight and per-file compilation pass.

## Second reading by Q75

This is a separate second pass by the assigned worker, with the node and final signature
open; no additional agent was started, as instructed. The maintainer performs the independent
review of this delivery. I rechecked every hypothesis and all five conjuncts against the
node, rather than treating successful compilation as a semantic check. The tensor factors
are reversed only by the canonical symmetry. The generic local fields and the induced
fraction map are the specified localizations, not residue fields or arbitrary fields/maps.
The completion is the existing actual AdicCompletion abbreviation. The last A-algebra map
is exactly an arbitrary k-algebra map together with its induced A-action; its factorization
is forced to commute with that action. There is no lost θ-identity case or hypothesis of
injectivity. The two smooth-neighbourhood clauses assert the recorded scheme Smooth
predicate. The local-dimension equality uses open neighbourhoods and the rank equalities
are cardinal equalities over asserted fields. The second pass found no statement mismatch;
it added the three existing owning-node dependencies so all reused notions are named.

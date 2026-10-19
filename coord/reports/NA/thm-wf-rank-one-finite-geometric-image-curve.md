## Worker report

The module `Sheaf.AlgebraicGeometry.FundamentalGroup.RankOneFiniteGeometricImageCurve`
states `AlgebraicGeometry.Scheme.FiniteEtale.rankOne_finite_geometricImage_curve`,
with a single `sorry` proof and no definitions. Its docstring reproduces all five
steps of the current DAG proof, including the logarithm-domain comparison at ℓ = 2.
No mathematical statement correction or dependency repair was needed.

Hypothesis and clause correspondence:

- The finite field F_q is `(k₀ : Type u) [Field k₀] [Finite k₀]`, with
  `q = Nat.card k₀`. The structure morphism `p : U₀ ⟶ Spec (.of k₀)` is explicit
  because the recorded Weil-group declarations take that morphism.
- Normality is `hnormal : ∀ z : U₀, IsDomain (U₀.presheaf.stalk z) ∧
  IsIntegrallyClosed (U₀.presheaf.stalk z)`: every local ring is an integrally closed
  domain. This is the same encoding as the landed normal-curve compactification.
- Geometric connectedness is `[GeometricallyConnected p]`; separatedness is
  `[IsSeparated p]`; finite type is `[LocallyOfFiniteType p] [QuasiCompact p]`.
- Pure dimension one is `hdim : U₀.IsPureDimension 1`, using the existing
  `Sheaf.AlgebraicGeometry.PureDimension`, `AlgebraicGeometry.Scheme.IsPureDimension`.
  The already-landed `def-weil-pure-dimension` is added to `stmt_deps` to record
  this direct use, as brief-stage2 §5 permits.
- A geometric base point is `{Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (x : Spec (.of Ω) ⟶ U₀)`, the interface of the recorded Weil-group dependency.
  The arithmetic base point determines the geometric subgroup; the geometric
  base-change scheme does not need a separate independent parameter. As in the
  landed compact-logarithm dependency, Π is represented by
  `(weilGroupDeg p x (Aut (fiber x))).ker`. This is the degree-zero subgroup
  identified with π₁(U₀ × F̄_q) by the exact-sequence convention, not an arbitrary
  chosen subgroup or an added hypothesis identifying it.
- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`; `hℓ : ¬ ℓ ∣ Nat.card k₀` is exactly
  ℓ not dividing q. In particular it implies ℓ differs from the characteristic.
- The finite coefficient extension is `(E : Type v) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]`, in an independent universe.
- The rank-one character is `χ : weilGroup p x (Aut (fiber x)) →* Eˣ`.
  Its continuity `hχ` is continuity of its underlying E-valued map for
  `(spectralNorm.normedField (Padic ℓ) E).toUniformSpace.toTopologicalSpace`.
  This is the uniquely extended adic topology, exactly as in the landed
  compact-character logarithm. For units, continuity of the underlying field map
  is equivalent to continuity into the usual unit-group topology: the inverse
  coordinate is composition with continuous field inversion.
- Finiteness of χ(Π) is
  `(Set.range (fun g : (weilGroupDeg p x (Aut (fiber x))).ker ↦ χ g.val)).Finite`.
- The equivalent exponent conclusion is the second conjunct:
  `∃ N : ℕ, 1 ≤ N ∧ ∀ g : (weilGroupDeg p x (Aut (fiber x))).ker,
  χ g.val ^ N = 1`. Giving both equivalent conclusions records both clauses.
  The docstring also explains the converse by the exponent of the finite image.

Dependency declarations read and reused:

- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup`:
  `Scheme.FiniteEtale.constantCover`, `arithmeticFrobenius`, `constantCoverAction`,
  `geometricFrobenius`, `weilGroup`, and `weilGroupDeg`. These are the actual
  arithmetic fibre-functor group and constant-cover Frobenius, not an abstract
  replacement Weil group.
- `def-weil-pbc-scheme-conventions` has a convention-only record, with no module
  to import. Its Mathlib finite-type and separatedness meanings are used directly.
- `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`.
- Proof imports: `Sheaf.AlgebraicGeometry.FundamentalGroup.CompactCharacterLogarithm`
  (`Scheme.FiniteEtale.exists_compactCharacterLogarithm`),
  `Sheaf.AlgebraicGeometry.FundamentalGroup.PadicCharactersH1`
  (`exists_padicCharactersH1`), `Sheaf.CategoryTheory.Galois.AutProfinite`
  (`CategoryTheory.SetFunctorAut.evaluation_isClosedEmbedding_and_profinite`),
  `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr` (`Padic.extension_integers_dvr`),
  and `Mathlib.Topology.Algebra.Module.FiniteDimension`
  (`LinearMap.continuous_of_finiteDimensional`).
- `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale.fiber` and
  `MonoidHom.exact_weilGroupDeg` are already available through the public
  Weil-group dependency; `Padic` is imported publicly and used in the signature.
- `lem-wf-deep-principal-unit-log` and
  `prop-wf-open-curve-h1-no-frobenius-fixed` have no recorded Lean declarations
  in the supplied DAG, so there are no proof modules to import for them yet.
  They are not needed to type this statement; their full proof roles remain
  explicit in the docstring and the unchanged `proof_deps`.

Edge cases: the trivial character is included and admits N = 1. No ramification
restriction on E is imposed. The prime ℓ = 2 is included and the proof records
r = 2e > e/(ℓ-1). There is no properness, affineness, or smoothness hypothesis.
The empty scheme is excluded by geometric connectedness, not by an extra
nonemptiness assumption; dimension zero is excluded exactly by pure dimension one.
The base and coefficient universes are explicitly bound and independent. Separably
closed points are the standard finite-etale-fibre interface and give the same
fundamental group as algebraically closed geometric points.

Searches for an existing statement (2026-10-18):

- `msearch.py leanfinder`, query “A continuous rank one Weil character of a normal
  geometrically connected curve over a finite field has finite geometric image”:
  eight hits about function-field class numbers, norms, and embeddings; no match.
- `msearch.py leansearch`, query “A continuous character of the Weil group of a
  curve over a finite field has finite geometric image”: eight hits including
  cyclotomic-character continuity, Galois compactness, and characters; no match.
- `msearch.py loogle`, query `"Weil", "finite"`: zero hits.
- `msearch.py grep`, query `WeilGroup|finite_geometric_image|rankOne.*finite`:
  one irrelevant positive-operator rank-one decomposition hit.
- Direct `rg` in Mathlib-facing results, the project upstream-name index,
  `WeilConjectures/`, and `lean/Sheaf/`, including the exact blueprint id, found
  `WeilConjectures.EtaleCohomology.Purity.RealSheaves.RankOne`. Its full
  signatures and surrounding section binders were read. The declarations
  `AlgebraicGeometry.WeilGroup.exists_pow_eq_one_of_continuous` and
  `finite_range_of_continuous` concern characters into `PadicAlgCl`, a bundled
  `WeilGroup p` on an `IsCurve p` scheme, and require
  `[SmoothOfRelativeDimension 1 p] [W.IsEtaleQuotient]`. They do not give this
  node's actual recorded scheme Weil group with arbitrary finite coefficient
  extension and the normal/pure-dimension hypotheses, so they are not an exact
  `existing: true` binding. No exact declaration was found in `lean/Sheaf/`.

Validation uses only `scompile.py`, followed by `deliver2.py --no-push` and
`deliver2.py`. Every variable and universe is explicit; there is no local
notation, local instance, hidden auxiliary definition, or proved theorem.

## Second reading by NA

No second reading by another worker: the dispatch brief requires direct delivery
and prohibits starting other agents. The maintainer's independent review reads
this delivery. The worker rechecked the source statement against every binder
and both conclusions above; no mismatch was found and no statement was corrected.

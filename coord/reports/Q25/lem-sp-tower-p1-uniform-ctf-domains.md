## Worker report

The module `Sheaf.Paper.TowerP1UniformCtfDomains` states
`AlgebraicGeometry.ProEtale.SpTowerP1Uniform.towerP1_uniform_ctf_domains`.
Its sole postponed proof is that named theorem. The owning-node helpers `push`,
`pullTwist`, `bounds`, `comparisonModel`, `lineModel`, and `LocalModel` are actual
functor compositions, predicates, or a structure of retained witnesses; their data
contain no `sorry`. They package this item's clauses, without introducing an
independent mathematical notion. No dependency record or natural-language statement
was changed, and no new DAG node was needed.

Hypotheses and coefficients:

- Distinct primes p and ell: `p`, `[Fact p.Prime]`, `l`, `[Fact l.Prime]`, `_hlp : l ≠ p`.
  The characteristic-p field is `k : Type u`, `[Field k]`, `[CharP k p]`.
- The separated finite-type k-scheme is `S : Scheme.{u}`, `[S.Over (Spec (.of k))]`,
  `[IsSeparated (S ↘ Spec (.of k))]`, `[LocallyOfFiniteType ...]`, and
  `[QuasiCompact ...]`. Finite type is the latter two classes together.
- The finite extension is `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
  `[FiniteDimensional (Padic l) E]`. The actual integer ring is
  `Padic.coefficientExtensionIntegers l E`.
- `SpTowerShriek.R l E n` is precisely the quotient by `spEllIdeal l E ^ (n+1)`;
  the exponent is positive and `n : Nat` indexes paper level n+1. It is ell-power,
  not uniformizer-power, including ramified extensions. `ULift` changes only the
  coefficient size for fixed-scalar sheaves; the intrinsic category is the recorded
  `Scheme.proEtaleDerivedCategory`.
- `ProjectiveLine S` is the existing `ProjectiveSpace (ULift (Fin 2)) S`, and
  `ProjectiveLine S ↘ S` is its first projection. No independent scheme or map is used.
- `DS`, `DP : SpCoefficientTowersAbelian ...` supply the existing ordinary derived
  localizations and exact level evaluations. `c : TowerClasses l E S hS` fixes the
  already normalized coefficient and Tate-line construction and geometric calculus.
  `hS : IsUnit (l : Γ(S,⊤))` is the invertibility needed to name that recorded data;
  it follows from l ≠ p over the characteristic-p field. It imposes no additional
  geometric restriction. This is the same explicit-data convention as the recorded
  tower classes and tower bound, not a choice of arbitrary functors.

Clause-by-clause correspondence:

1. U(T) is exactly `spConstructibleTorTowers l E T D`. The theorem's first conjunct
   quantifies over T equal to S or `ProjectiveLine S`, every recorded tower interface
   D, and every member K. Its conclusion gives the whole realized tower a lower bound
   and, at every level, `Nonempty (SpTowerShriek.Origin ... K)`. That existing structure
   retains a fixed-scalar bounded-below level, its realization isomorphism, and
   `FixedEtaleOriginWitness`, whose fields are the bounded-below etale antecedent and
   its specified comparison isomorphism. Thus it is exactly membership in C+(T).
   No compatibility is imposed between origins at different levels.
2. `push` conjugates the existing `SpTowerShriek.push` for `c.projective.geometry`
   through `spTowerShriekRealization` on P and S. It is proper Rq_*, not an arbitrary
   compactification-dependent functor. The second conjunct preserves the exact U
   predicate under this functor. The proof specializes the compact-support bound
   to the identity-open compactification, as required by the node.
3. `pullTwist` conjugates the existing exact tower pullback, then tensors with
   `(SpTowerClasses.line l E c.chernP)⟦2⟧`, and returns to the original tower
   coordinates. The third conjunct preserves U under this actual functor.
4. `bounds ... r s a b` gives level cohomological bounds via `IsGE r`, `IsLE s`,
   intrinsic constructibility in each degree, and `HasProEtaleTorAmplitude ... a b`.
   The final conjunct quantifies over every K and every prescribed containing
   interval r,s,a,b satisfying this predicate and asserts `bounds` on the actual
   output with all four endpoints decreased by two. The same endpoints precede
   the quantifier over all levels, so they are independent of n.
5. For each level, the first `Nonempty (LocalModel ...)` gives the global ordinary
   etale antecedent, bounded constructibility, the same [r,s] and [a,b], its specified
   intrinsic comparison to the actual input level, and a flat constructible complex
   supported in [a,b] representing that antecedent.
6. `lineModel` is the existing `etalePullbackLineModel` applied to q, the actual
   `finiteEtaleTateLine` for ell^(n+1), and shift 2. The annihilation proof is
   `SpTowerClasses.coefficient_annihilates`, transported through the coefficient lift.
   `LocalModel.strata` uses the existing `etalePullbackLineAssertions`, including
   flatness, support [a-2,b-2], K-flatness, comparison invertibility, constructible
   cohomology, Tor bounds, and every prescribed pulled-back finite locally closed
   stratification with finite local module values on the actual common covers.
   `line_trivial` and `cover` retain the root-line trivializing data.
7. `comparisonModel` is the actual termwise site inverse image followed by the
   existing intrinsic associated-module-sheaf functor. `pro_flat`, `pro_support`,
   `pro_kflat`, and `pro_represents` assert that this very complex has flat terms,
   support [a-2,b-2], K-flatness against arbitrary acyclic complexes, and represents
   the actual output level. It is not an unrelated complex chosen at the endpoint.
8. The final quantifiers are `∀ (U : S.Opens), IsAffineOpen U → Nonempty (LocalModel ...)`.
   The input is restricted by `proEtaleConstantRingDerivedPullback ... U.ι`; the output
   is restricted by the same canonical functor along
   `ProjectiveSpace.map (ULift (Fin 2)) U.ι`. Thus the models lie on U and P1_U and
   represent exactly the restrictions in the node, with the same r,s,a,b endpoints.
   The preceding global model and global bounds make the local intervals global.

Constructibility is the recorded finite constructible locally closed stratification
predicate, not finite stalks alone. No `IsSpNormalizedTower` or reduction-isomorphism
hypothesis occurs. No adjunction is assumed or concluded, and the constructible
restriction is asserted only in the stated finite-type field setting.

Dependency declarations used:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`:
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`, read for the
  standing setting; its explicit separated finite-type binders are rendered here.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the underlying integer-ring construction
  reexported from `CoefficientExtension`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  `AlgebraicGeometry.ProjectiveSpace`, `ProjectiveLine`, its projection, and `ProjectiveSpace.map`.
- `Sheaf.Paper.SmoothPurityCoefficientTowers`:
  `AlgebraicGeometry.ProEtale.spCoefficientTowers`, `spEllIdeal`.
- `Sheaf.Paper.SmoothPurityCoefficientTowersAbelian`:
  `SpCoefficientTowersAbelian`, exact `spCoefficientEvaluation`, and its ordinary localization.
- `Sheaf.Paper.SmoothPurityNormalizedTowers`:
  `spDerivedCoefficientTowers`, `spDerivedCoefficientEvaluation`,
  `spConstructibleTorTowers`, `spFiniteConstructibleTor`.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.FixedEtaleOriginWitness`, through `SpTowerShriek.Origin`.
- `Sheaf.Paper.SmoothPurityTowerClasses`: `TowerClasses`, its projective geometric
  operation and `SpTowerClasses.line`, with quotient annihilation.
- `Sheaf.Paper.SmoothPurityTowerBound`: `spTowerShriekRealization`; the proof uses
  `sp_tower_bound`. Its public dependency `SmoothPurityTowerShriekLevels` supplies
  `SpTowerShriek.push`, `pull`, `tensor`, and `Origin` without importing the downstream
  projective-line adjunction theorem.
- `Sheaf.AlgebraicGeometry.EtalePullbackLineFlatModel`:
  `Etale.etalePullbackLineModel` and `etalePullbackLineAssertions`.
- `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`:
  `Etale.IsBoundedFlatComplex` and the ordinary derived category conventions.
- `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and the proof-stage bounded-flat criterion.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`:
  `Scheme.finiteEtaleTateLine` and its cover trivializations.

All available proof-dependency modules are imported. The six-step proof docstring
follows the node's accepted split: finite coefficients and geometry, origins, proper
image, prescribed-interval flat models, normalized level comparisons, affine restriction.
There is no import of `SmoothPurityTowerP1Adjunction`, which would close a dependency
cycle once the maintainer adds this item's proof import to that consumer.

Edge cases checked before drafting: S empty; empty affine opens; zero tower; one-point
interval a=b; endpoints r or a negative; shift convention H^j(K[2]) = H^(j+2)(K);
positive first level n=0 meaning exponent one; ramified E (ell-powers retained);
non-normalized and zero transition maps. The local model is a containing-interval
assertion, not a claim that endpoint terms are nonzero. Bounds impose Tor order as
part of the existing Tor predicate; cohomological bounds also permit a zero object
in a reversed interval. All binders and the universe are explicit, with autoImplicit false.

Searches (all before choosing the statement interface):

- `msearch.py leanfinder`: "Projective line tower functors preserve uniformly bounded
  constructible finite Tor amplitude and etale origin witnesses". Eight generic
  etale, projective-space and Tor hits; no statement covering this node.
- `msearch.py loogle`: "DerivedCategory, HasTorAmplitude". No hits; the latter is not
  a Mathlib identifier. The project owns the recorded amplitude predicate.
- `msearch.py grep`: `spConstructibleTorTowers|EtaleOriginWitness|Uniform.*Tor`.
  Generic unrelated Mathlib uniformity hits, no tower statement.
- `msearch.py leansearch`: "uniformly bounded constructible finite Tor amplitude
  coefficient towers projective line pullback twist". Eight generic pullback/sheaf
  hits, no matching tower domain-and-bound theorem.
- `rg` in `lean/WeilConjectures` for tower/P1 names and `spConstructibleTorTowers`,
  and for the exact blueprint id: no matching theorem.
- `rg` in `lean/Sheaf`: the existing normalized-tower predicate, compact-support
  tower bound, and projective-line adjunction restriction were found and read.
  The adjunction statement only supplies preservation as a final clause; it does
  not supply the prescribed intervals and retained global/affine-local models.
  The parent cites this node, so it is not used as a premise. The smaller tower
  classes, bound, flat-line-model and intrinsic realization interfaces are reused.
- Exact helper namespace/name searches in Mathlib, upstream, Sheaf, and
  `dag/lean_names_upstream.json`: no conflicting full declarations.

No STATEMENT-DISPUTED flag or node correction is needed.

## Second reading by Q25

The maintainer's independent second reader (cc review service, 2026-10-25) wrote
this section in place of the worker's self-check, which was not an independent
reading (delivery-errors H11). The Lean module and the node record are unchanged.

Node statement, item by item, against the delivered Lean:

| Node | Lean | Verdict |
|---|---|---|
| distinct primes p, ℓ; field k of char p > 0 | `p`, `[Fact p.Prime]`, `l`, `[Fact l.Prime]`, `_hlp : l ≠ p`, `k : Type u`, `[Field k]`, `[CharP k p]` | exact |
| S separated, finite type over k (sk-def-sfb-dc-setting) | `[S.Over (Spec (.of k))]`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` of `S ↘ Spec k` | exact (finite type = lft + qc) |
| E/Q_ℓ finite, O_E, B_n = O_E/ℓ^n | `[Algebra (Padic l) E] [FiniteDimensional ..]`; `SpTowerShriek.R l E n` = O_E/(ℓ)^(n+1), n ↦ paper level n+1 | exact; ramified E keeps ℓ-powers |
| P = P¹_S, q | `ProjectiveLine S`, `ProjectiveLine S ↘ S` (def-nagata-projective-space-base-change) | exact |
| towers, D(Tow), level evaluation | `spDerivedCoefficientTowers`, `spDerivedCoefficientEvaluation` for `DS`, `DP` | exact |
| U(T) | `spConstructibleTorTowers` (uniform cohomological and Tor intervals, constructible finite-Tor levels, no normalization) | exact |
| C⁺(T): bounded below, levels in ess. image of ν_T^* | `∃ a, IsGE` of the realized tower ∧ `∀ n, Nonempty (SpTowerShriek.Origin ..)` (level in D⁺, realization iso, `FixedEtaleOriginWitness`) | exact; the same formula as the landed parent's `SpTowerP1.domain` |
| U(T) ⊆ C⁺(T), T = S, P | first conjunct, `∀ T D, T = S ∨ T = ProjectiveLine S → ..` | exact (holds for every tower interface D) |
| Rq_* (U(P)) ⊆ U(S), q proper (identity compactification) | `push` = realization ⋙ `SpTowerShriek.push` on `c.projective.geometry` (geometry of q, the parent's `Presentation.F` via `q_geometry`) ⋙ inverse | exact |
| q^*(-)(1)[2] (U(S)) ⊆ U(P) | `pullTwist` = realization ⋙ `pull` ⋙ `tensor` with `(line c.chernP)⟦2⟧` ⋙ inverse (the parent's `Presentation.G`) | exact |
| [r,s], [a,b] ↦ [r−2,s−2], [a−2,b−2], constructible, the same for every n | `bounds .. K r s a b → bounds .. (pullTwist K) (r-2) (s-2) (a-2) (b-2)`; endpoints bound before `∀ n` | exact; the sign is right: H^j(K[2]) = H^(j+2)(K) |
| affine U: bounded constructible étale representative of K_n‖U, the same intervals; flat representative in [a,b] | `LocalModel` on `U.toScheme`: `etale`, `etale_constructible`, `IsGE r`/`IsLE s`, `hasTorAmplitudeIn a b`, `origin` iso to `proEtaleConstantRingDerivedPullback U.ι` of K_n, `complex` + `represents` + `IsBoundedFlatComplex a b` + constructible terms | exact |
| its pullback ⊗ B_n(1) [2] is a K-flat representative in [a−2,b−2] of the level on P¹_U | `lineModel` = `etalePullbackLineModel` (q_U, `finiteEtaleTateLine (l^(n+1))`, 2); `pro_flat`, `pro_support`, `pro_kflat`, and `pro_represents` ≅ pullback along `ProjectiveSpace.map U.ι` of the output level | exact |
| constructibility by stratifications and their inverse images | `strata` (`etalePullbackLineAssertions`), `IsConstructible*ModuleSheaf` | exact |
| "these local intervals hold globally" | `bounds` on the output plus a global `LocalModel` on S | slightly stronger (a global model too). Proof steps 4–5 build it globally (lem-sf-etale-flat-constructible needs only Noetherian S), so it is true and accepted |
| no adjunction, no normalization, no arbitrary schemes | none assumed or concluded | exact |

Hypothesis `hS : IsUnit (l : Γ(S, ⊤))` follows from l ≠ p over the char-p field
(even for S = ∅). It only types `TowerClasses`, whose data (geometry of q, Chern
and level normalizations) are pinned, so the statement is for every such c.

Edge cases: S = ∅ (all categories zero; hS holds); U = ∅; the zero tower; a = b;
negative endpoints; n = 0 (exponent 1); ramified E; non-normalized or zero
transition maps. Each one is covered, and the bounds are containing bounds.

Searches: `spConstructibleTorTowers`, `SpTowerP1`, `etalePullbackLineModel`,
`IsKFlatIndependentCoefficients` in lean/Sheaf and lean/WeilConjectures. The
only related statement is the parent det-sp-tower-p1-adjunction, which cites
this item. No duplicate.

Advisory (no change): the statement uses declarations of nodes that are not in
the stage-1 `stmt_deps`: def-sp-tower-shriek-realization, def-asd-finite-etale-tate-twist,
def-pc-kflat-complex, def-weil-pbc-proetale-operations, and the theorem node
lem-sp-etale-pullback-line-flat-model (`etalePullbackLineModel`, `etalePullbackLineAssertions`).
An S2 fix cannot change `stmt_deps`, and they are unchanged from the base, so this is advisory.

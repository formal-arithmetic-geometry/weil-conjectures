## Worker report

Repair of returned head 61ae2ddb625a. The retained packet first passed the required
`deliver2.py NH cor-coef-finite-verdier --no-push` (dry-run commit 527a41e3d4).
That mechanical success did not resolve the independent mathematical return.
The repaired packet changes only the Lean record of the original node and its module;
the current shared node and saved node were compared field by field and differed only
in `lean`. No mathematical statement correction or new DAG node is needed.

The module states `WeilConjectures.finite_coefficient_verdier`. Its auxiliary definitions
spell out this node's own comparison diagrams and their normalization. They do not
introduce new independent mathematical notions. Only the final theorem has `sorry`.

### Hypotheses and objects

| Node text | Lean rendering |
| --- | --- |
| Global finite-field datum, algebraic closure k | `(D : FiniteFieldDatum.{u})`, with base `D.k` |
| Prime ell different from char k | `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)` |
| Finite extension E/Q_ell, its prescribed ring and uniformizer | `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`; `finiteDualizingCoeff l E n` uses exactly `Padic.coefficientExtensionRing l E (n+1)` and its standard ULift |
| Positive levels 1 ≤ m ≤ n | The family in `FiniteVerdierCoherentComparison` binds natural indices `{n m}` with `h : m ≤ n`; their actual positive levels are `n+1,m+1`. This bijective indexing includes every positive level and permits the same family to occur in the cocycle. |
| Canonical quotient A -> B | `finiteDualizingQuotient l E h`, the published ULift of `Ideal.Quotient.factor` for the powers of the fixed coefficient ideal |
| X over k | `(X : Scheme.{u}) [X.Over (Spec (.of D.k))]` |
| Separated and finite type | `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on `X ↘ Spec (.of D.k)`; no properness hypothesis |
| Dimension bound | `(d : ℕ)` and `hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)` |
| Etale D^b_ctf | `finiteTorConstructibleEtale l E (n+1) ... X`, using bounded constructible cohomology and the recorded finite Tor predicate |
| Pro-etale D^b_ctf | `finiteTorConstructibleProEtaleModule`, which applies the recorded intrinsic `finiteTorConstructible` under the canonical realization |
| K_B = K tensor^L_A B | `pbcFixedScalarExtension J (finiteDualizingQuotient l E h)`, the actual left adjoint to exact scalar restriction; the etale abbreviation is `Etale.scalarExtension` |
| Etale omega = a_X^times A | `finiteDualizingEtaleTerm l E D X n`, the published exceptional right adjoint at the regular constant complex |
| Pro-etale transported omega | `(F n).obj (W n)` for `F n = comparisonUpperStar ... X |>.mapDerivedCategory` and `W n = finiteDualizingEtaleTerm ... n`; this is literal transport, without an ambient pro-etale exceptional adjunction |
| D_AK = RHom_A(K,omega_A) | `MonoidalClosed.internalHom.flip.obj (W n)`; on these derived module categories this is the existing `Etale.derivedHom` / `ProEtale.derivedHom` wrapper, not a second Hom construction |

### Every conclusion clause

1. Natural comparison: `comparison h` has type `D_A ⋙ S ⟶ S.op ⋙ D_B`.
   It is a natural **transformation**, not a natural isomorphism on the entire
   unbounded derived category. `P n K → IsIso ((comparison h).app (op K))` supplies
   exactly the isomorphisms on finite-Tor constructible inputs (H3(a)).
2. Reduced-input constructibility is the adjacent clause `P m (S.obj K)`, which
   ensures successive coefficient comparisons apply to the reduced input.
3. Evaluation: `((T m).map d_K).app K_B ≫ ev_B = μ.inv.app (D_AK,K) ≫ S.map ev_A ≫ uMap h`.
   Thus, after the specified balancing identification, `ev_B ∘ (d ⊗ 1) = u ∘ S(ev_A)`.
   The etale `uMap` is exactly `finiteDualizingEtaleComparison`. On the pro-etale
   site it is `pbcComparisonReduction.hom.app omega_A ≫ F_B.map u`, so it is the
   transported canonical coefficient map. Evaluations are extracted from the
   recorded `AmbientDualityPairing`, whose counit and Koszul normalization fix them.
4. Double dual: `S.map (δ n K) ≫ d_(D_AK) = δ m K_B ≫ D_B.map d_K.op`.
   The `δ` parameters are exactly the published `AmbientDualityPairing.bidualityMap`
   projections. This is the requested square with both sides ending at `D_B(S D_AK)`.
5. Quotient cocycle: for `r ≤ m ≤ n`, the final clause of `FiniteVerdierCoherentComparison`
   equates `S_BC.map d_AB ≫ d_BC(K_B) ≫ D_C.map associator.inv.op` with
   `associator.hom.app D_AK ≫ d_AC`. Its associator is the published
   `pbcFixedScalarExtensionComp` using `finiteDualizingQuotient_comp`.
6. Identity quotient: the preceding clause explicitly fixes `d_AA` to
   `scalarUnit.hom.app D_AK ≫ D_A.map scalarUnit.hom.op`, where `scalarUnit` is
   `normalizedOriginScalarUnit` using `finiteDualizingQuotient_id`. Equality levels
   are permitted in the cocycle too; no strict inequality or excluded first level.
7. Tor interval: for every ordered `[a,b]` and input with that interval, the paired
   `Tor m (-b-2*d) (-a)` clauses concern `S.obj (D_AK)` **and** `D_B(S.obj K)`.
   They do not concern `K_B` (H3(c)). The etale interval is the recorded
   `Etale.DerivedCategory.hasTorAmplitudeIn`. The pro-etale interval is the recorded
   `Scheme.HasProEtaleTorAmplitude` applied through the canonical intrinsic
   realization, thus quantifying over all degree-zero module sheaves on that site.
8. Both sites: the two conjuncts of `FiniteVerdierTwoSitesComparison`, specialized by
   `FiniteCoefficientVerdierComparison`, apply
   this same complete interface, including evaluation, biduality, identity, cocycle
   and both Tor bounds, separately to the etale and pro-etale sites.

The tensorator is not arbitrary: each `μ h` is required, by `HEq`, to equal
a witness satisfying the published `Etale.ExceptionalCoefficients.TensorNormalizationAux`.
Heterogeneous equality equates the complete natural isomorphisms, including endpoints;
it avoids expanding the canonical derived monoidal structure during type conversion.
This is the same adapter technique used by the imported `siteTensorIso_existsUnique`. Its ordinary extension is
`Sheaf.composeAndSheafify (ModuleCat.extendScalars φ)`, its oplax structure is
`composeAndSheafifyOplaxMonoidal`, and its representative comparison is the adjunct
of the localized ordinary scalar unit (`finiteVerdierScalarRepresentative`). Hence
it is the balanced tensor comparison on K-flat representatives, even for nonflat B/A.
All these helpers have real data. There are no extra hypotheses on canonical arrows.

H3(d): the two `FiniteDualitySiteComparison` conclusions were removed. That theorem
is a proof input, not a conclusion of this coefficient-change corollary. Literal
transport specifies the pro-etale object without asserting the site-comparison
statement again. H8: the final theorem's docstring now has seven explicit proof
steps, matching the node's proof, including the balanced-tensor calculation.

### Dependency declarations read and used

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.Paper.FiniteTorAmplitude`: the recorded intrinsic `finiteTorConstructible`;
  `Sheaf.Paper.FiniteTorAmplitudeSites`: its etale presentation;
  `Sheaf.Paper.FiniteTorAmplitudeProEtaleModule`: its fixed-module presentation.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`:
  `Etale.DerivedCategory.isBoundedConstructible`, used by the etale predicate.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: the intrinsic Hom
  construction; the fixed-module derived monoidal closed presentation is used
  through the existing `derivedHom` wrappers, without a second construction.
- `Sheaf.Paper.DualityPairing`: both `AmbientDualityPairing` predicates,
  `CategoryTheory.dualityDoubleFunctor`, and both `bidualityMap` projections.
- `Sheaf.SixFunctors.FiniteDualitySiteComparison`: the canonical transport and
  compatibility proof interface, imported as a proof dependency.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `.Proper`:
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` (no use of `IsProper`).
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  the recorded universal/cochain model, imported as the scalar computation input;
  `Sheaf.Paper.EtaleDerivedScalarTensor` / `.WitnessCompatibility`: its fixed scalar
  realization, the scalar associator, and exact restriction.
- `Sheaf.SixFunctors.FiniteDualizing`: coefficient rings, quotient maps and their
  identity/composition equations; etale dualizing object and counit-defined u.
- `Sheaf.Paper.ExceptionalCoefficientComparison`: the shared representative-normalized
  scalar tensor comparison predicate, reused for either site.

### Searches and edge cases

The source was reopened at
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/`
`cor-coef-finite-verdier.md` and its `.proof.md` (current order 2486), and compared
with the recorded master statement and seven-step DAG proof (order 2142).

Repeated searches during repair:

- `msearch.py NH cor-coef-finite-verdier leanfinder "natural transformation Verdier dual coefficient quotient evaluation biduality cocycle"`:
  eight results concerning evaluation of complexes, Ext and cocycles; none this theorem.
- `msearch.py ... loogle '"scalarExtension"'`: zero hits.
- `msearch.py ... grep 'Verdier|dual.*[Bb]ase[Cc]hange|[Bb]ase[Cc]hange.*dual' CategoryTheory`:
  19 hits, all generic Verdier quotient/triangulated references; no geometric duality theorem.
- `rg` for `finite_coefficient_verdier|FiniteVerdierSiteComparison|finiteVerdierOrdinaryExtension|FiniteCoefficientVerdierComparison`
  in both prescribed project source trees: no existing declaration.
- `rg` for the blueprint id in upstream `WeilConjectures`: no match.
- Targeted searches for scalar-extension tensorators, associators, identity comparison,
  dualizing maps and Tor intervals located the declarations listed above. Their full
  signatures and defining docstrings were read before use. The saved packet's earlier
  searches are also retained in the unchanged DAG search record.

Edge cases recomputed:

- Point, A=O/varpi^2, B=O/varpi, K=A/varpi: this is not finite Tor over A;
  invertibility is now guarded by `P n K`. The ambient natural transformation
  is allowed to fail to be an isomorphism. This addresses the H3(a) counterexample.
- Point, K=A[-1], a=b=1, d=0: its dual and both reduced duals have interval
  [-1,-1]. The repaired clauses demand that interval for the two dual objects,
  and never demand it for K_B. This addresses the H3(c) counterexample.
- n=m and level one: indexing by n+1 includes both; the unit equation is explicit.
- Three equal levels and either adjacent equality: all non-strict inequalities are
  allowed, and the canonical scalar associators appear in the equation.
- Zero complex and empty scheme: no nonempty/positive-dimension assumption was added.
- Nonflat quotient B/A: all tensor normalizations use derived counits and K-flat
  computation; no flatness hypothesis was introduced.
- Site universes remain objects `u+1`, morphisms `u`, coefficients/modules `u+1`.
  No equality of site-object and morphism universes is imposed.

## Second reading by NH

This is the author's second reading, not an independent review. I reopened the source,
node, recorded dependency signatures and repaired Lean module. The following checks
were made against the actual expressions above.

| Check | Finding and repair |
| --- | --- |
| Field datum / ell / E | Exact `D,l,Fact l.Prime,hl,E,Field,Algebra,FiniteDimensional` binders; none dropped or added. |
| Scheme / separated / finite type | `X.Over`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`; no properness requirement. |
| Positive levels and quotient | Existing `finiteDualizingCoeff` and `finiteDualizingQuotient`; n+1 indexes all positive levels. A single universally quantified family is needed to express the source cocycle. |
| Ambient objects | Etale exceptional dualizing object at the regular constant complex, pro-etale literal comparison pullback, internal Hom of those objects. |
| Finite-Tor domain | Both `P` predicates are the recorded ones. `IsIso` is under `P n K`; removed the false whole-category isomorphisms. |
| Naturality | Each family entry is a natural transformation on the ambient opposite category, hence restricts naturally to the full finite-Tor subcategory. |
| Evaluation | Read both sides' domains and codomains: tensor(S D_AK,S K) -> omega_B, using the prescribed tensor inverse then S(ev) and canonical u. Added on both sites. |
| Biduality | Both paths start at S K and end at D_B(S D_AK). The right path uses contravariance on d_K. Added on both sites. |
| Cocycle | Both paths start at S_BC S_AB D_AK and end at D_C(S_AC K). The inverse scalar associator in the contravariant argument is necessary and present. |
| Identity | Formula uses scalar-unit hom on D_AK and hom on K under the contravariant D_A; equality quotients are included. |
| Tor conclusion | Both S(D_AK) and D_B(K_B) occur in both site specializations. Rechecked point and shifted-free counterexamples. |
| No extra site theorem | Removed both `FiniteDualitySiteComparison` conjuncts. The source uses that result in the proof. |
| Canonicity / no hollow data | Ordinary extension, scalar adjunction and representative comparison are concrete. Tensor normalization fixes balancing; evaluation fixes d by transposition. Pairings are the recorded normalized ones. |
| Searches | Repeated LeanFinder, Loogle and Mathlib grep, then searched both upstream/project source trees and read the scalar/duality interfaces. No exact duplicate theorem or helper names was found. |
| Proof documentation | Replaced the single-paragraph sketch with seven numbered mathematical steps tied to the node's proof inputs. |

No statement fault remains in the DAG statement itself; the faults were in its previous
Lean rendering. No `STATEMENT-DISPUTED` is retained.

The helpers share the canonical structures before specializing coefficients.
`FiniteVerdierCoherentComparison` shares tensor and Hom as explicit parameters;
`FiniteVerdierSiteComparison` fixes actual scalar extension, its unit/associator,
and the representative normalization. `FiniteVerdierEtaleComparison` and
`FiniteVerdierProEtaleComparison` specialize this interface separately.
`FiniteVerdierTwoSitesComparison` conjoins those complete comparisons.
The final definition fixes every argument to the recorded finite quotient tower,
its exceptional dualizing objects and canonical maps; no generic helper argument
becomes an extra hypothesis of the theorem.

The `finiteVerdierEtale*At` and `finiteVerdierProEtale*At` definitions specialize
exactly the published tensor, Hom and normalized pairing, and project its evaluation
and transpose. They keep the same module structures shared during kernel checking.
The generic evaluation/biduality helpers and `finiteVerdierScalarRepresentativeAux`
likewise only project specified maps or construct the actual adjoint of a localized
unit. The tensor normalization uses heterogeneous equality of full natural
isomorphisms, as the dependency's `siteTensorIso_existsUnique` does.
A final `rg` search for all fixed-ring wrappers and both-site specialization names
in both prescribed source trees returned no matches.

### Validation

The final module compiles through the prescribed `scompile.py` with default
heartbeats and the unchanged 60-second per-file limit. The sandbox check took
7.7 seconds and the library-path check 8.4 seconds; both produced no errors or
warnings. All temporary `#eval` commands and diagnostic options were removed.
`autoImplicit false` remains enabled. The file has one `sorry`, the final theorem,
with the seven-step source proof docstring. All 26 declarations are listed in
`lean.declarations`; `lean.statement` is the theorem signature verbatim.
The node was compared again with current shared JSON: only `lean` differs.

## Worker report

The delivery states `lem-coef-integral-exceptional-mapping-system` in
`Sheaf.SixFunctors.IntegralExceptionalMappingSystem`. Only the item's `lean`
record changes. No new nodes, dependency repairs, or statement corrections.
All four theorems have `sorry` proofs and complete proof plans. Definitions are
actual functors, whiskered counits, inverses of specified isomorphisms, or
composites; there is no arbitrary choice of a mapping-system lift.

Hypothesis and clause correspondence:

- The global field is `D : FiniteFieldDatum.{u}`; the coefficient data are
  `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`, `E : Type u`, `[Field E]`,
  `[Algebra ℚ_[l] E]`, and `[FiniteDimensional ℚ_[l] E]`. The valuation ring,
  uniformizer and quotient rings are the recorded Padic constructions, used
  by the imported coefficient calculus. Index `n : ℕ` means exponent `n+1`.
- Small pro-etale module categories and their completed coefficient ring are
  `scalarReductionSource`, `coefficientSequenceDerived`, and
  `coefficientSequenceLimit` from the recorded dependencies. These are
  ordinary derived categories, not an alternative localization category.
- The category of inputs is `sfIntegralConstructibleCategory l E W`, whose
  defining predicate requires Roos completeness, constructible reductions,
  and a single common cohomological interval. `K` and `L` have exactly these
  types. No finite-Tor assumption is added: `reduction_domain` derives it
  using the residue-Tor theorem and normalized quotient comparisons.
- The schemes have `Over (Spec (.of D.k))` structures, finite type expressed
  by `LocallyOfFiniteType` and `QuasiCompact` on both structure morphisms,
  and separated structure morphisms. The morphism `f` is over the same
  field, separated, locally of finite type and quasi-compact. The fixed
  factorization is `c : Compactification f` with its open and proper maps.
- The specified system calculus is `SX`, `SZ`, `SY`; the specified finite
  operations are `r : FiniteAdjunctionDiagram.Realization ...`. The enriched
  adjunction is `a : Enriched r g s βX βY`. These are the realization data
  already introduced in the node, not an integral adjunction hypothesis.
  The dualizing systems and dual-formula normalization are provided by the
  same dependency realization theorem; this node's displayed composite
  uses its enriched adjunction `a.iso` directly.
- `R` is the existing reduction functor restricted to integral constructible
  inputs. `F r` is literally `R_X ⋙ r.F ⋙ inclusion ⋙ L_Y`;
  `J r` is literally `R_Y ⋙ r.G ⋙ inclusion ⋙ L_X`.
- `support_and_counits` states constructibility of every `F r K` and
  invertibility of both actual counit components. `supportCounit` and
  `exceptionalCounit` are whiskerings of `SY.adjunction.counit` and
  `SX.adjunction.counit`; `supportIso` and `exceptionalIso` package them
  as natural isomorphisms using `asIso`. Their forward maps are the actual
  counits, and their inverse data are determined by the inverse equations.
- `supportCoefficientComparison` explicitly identifies the finite evaluated
  counit with `sfCompactSupportFiniteReductionIso`, using the specified
  `IntegralSupport.iso` and the calculus's `reductionEvaluation`.
- `mappingSource` and `mappingTarget` are exactly the two displayed
  integral reduction mapping bifunctors. `psi` is a natural isomorphism
  defined by `H_Y(c_K inverse,1)`, the whiskered `a.iso`, then
  `H_X(1,c_L inverse)`, in that order. `NatIso.op` implements the required
  contravariance, and `NatIso.prod` is the product of natural isomorphisms.
- `finitePsi` evaluates this actual composite, conjugating with the fixed
  `globalEvaluation` identifications. The first conjunct of
  `integralExceptionalMappingSystem` identifies it with the finite enriched
  adjunction conjugated by `finiteSupport` and `finiteExceptional`.
  This is an equality in `D(Ab)`, before taking cohomology, and therefore
  specifies the map in every shifted Hom degree as well as degree zero.
- The second conjunct gives the explicit degree-zero action using
  `coefficientFiniteHomEquiv` and the recorded
  `FiniteExceptional.adjunction.homEquiv`: precompose by the inverse
  support comparison, apply the finite adjunction, then postcompose by
  the inverse exceptional comparison. The endpoint evaluation comparisons
  are included in `finiteSupport` and `finiteExceptional`.
- The finite unit, counit and coefficient-transition compatibilities are
  the unchanged `Realization.unit`, `.counit`, `.supportTransition` and
  `.exceptionalTransition` fields. The middle finite enriched comparison
  is pinned by `Enriched.component`, `.finiteEvaluation` and `.finiteHom`.
  Thus its ordinary-etale origin and simultaneous-system normalization
  are inherited from the specified realization. The composite is already
  a natural transformation of derived systems; evaluations do not choose it.

Dependency declarations used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: the coefficient
  ring constructions and `Padic.finite_coefficientExtensionRing`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`: the recorded
  completed integral coefficient sheaf and constant quotient maps.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.DerivedCompleteOnSlices`: `IntegralOnSlice.IsComplete`,
  retaining the recorded global Roos-complete predicate on the global site.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension` (also used by the calculus).
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `coefficientSequenceGlobalHom`,
  `coefficientMappingEvaluation`, `coefficientFiniteHomEquiv`.
- `WeilConjectures.Compactification.Defs`: `AlgebraicGeometry.Compactification`.
- `Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization`: `Realization`,
  `Enriched`, `IntegralSupport`, `reducedConstructible`, and `evaluation`.
- `Sheaf.Paper.QcqsCompactSupportRealization`: the recorded compact-support
  identification, including the same finite projections.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the recorded
  exceptional coefficient system; its finite operation is used through
  `Sheaf.SixFunctors.FiniteExceptional`, `FiniteExceptional.adjunction`.
- Proof imports are `IntegralResidueTor`, `NormalizedDVREffectivity`,
  `SfIntegralCompactSupportConstructible`, and
  `SuccessiveDerivedQuotientNormalization`, precisely the stated proof deps.

Edge checks: `K=0`, `L=0`, empty X (and empty Y), identity f and its identity
compactification, first reduction (n=0), equal quotient indices and triple
quotients, and ramified E. The zero objects and empty schemes are admitted;
no maximum over an empty cover or dimension of the empty scheme appears.
The formula has the correct contravariance: its first map uses c_K inverse.
There is no restriction on which integral inputs are allowed and no integral
exceptional adjunction is assumed. All universes and variables are bound;
`autoImplicit false` enforces this. The fixed dependency convention uses
`Scheme.{u}`, coefficients `Type u`, and coefficient/module sheaves of size
u+1 on the genuine small pro-etale site (objects u+1, arrows u).

Searches performed via the prescribed `msearch.py`:

- LeanFinder, "Finite exceptional enriched adjunction on derived coefficient
  systems transferred by reduction limit counits": 8 abstract derived
  adjunction hits including `CategoryTheory.Adjunction.derivedε`; none is
  the sheaf coefficient-system statement.
- Loogle, "CategoryTheory.Adjunction, CategoryTheory.NatIso": 0 hits (unknown
  NatIso in the query); corrected query "CategoryTheory.Adjunction,
  CategoryTheory.Functor": 12 hits, all abstract adjunction constructions.
- Mathlib grep, "exceptionalMapping|integralExceptional|coefficientSequenceGlobalHom":
  0 hits.
- Direct rg over `lean/WeilConjectures` and `lean/Sheaf` for the node id and
  `exceptionalMapping|integralExceptional`: existing exceptional constructions
  found, but no statement of this reduction-system counit-conjugation formula.
  Existing notions were reused rather than defined again.

The current blueprint's finite exceptional statement and proof were read in
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/`.
The older parent filename in the DAG source is absent from latest; the item's
reviewed five-step proof and the current finite exceptional source agree on
coefficient transitions and the transported finite adjunction used here.
No statement correction and no STATEMENT-DISPUTED finding.

## Second reading by Q97

Independent second reading by the maintainer review (NT-cc reviewer for Q97, 2026-10-25).
It replaces the author's self-pass, which is kept verbatim at the end of this section.
The Lean module and the node record are unchanged.

Node clauses and their Lean:

- Setup. k = D.k (`FiniteFieldDatum.{u}`), l prime with `hl : l ≠ D.p`, E finite over Q_l
  (`[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`), A_n via the recorded Padic
  rings; index n means A_{n+1}, so all n ≥ 1 are covered. Correct.
- Schemes. X, Y are `Over (Spec D.k)` with locally finite type, quasi-compact and separated
  structure maps; f is over k, separated, locally finite type and quasi-compact;
  `c : Compactification f`. These are exactly the node's hypotheses (the hypotheses on f even
  follow from the ones on X and Y). Nothing stronger is assumed.
- D^b_c(W,R) = `sfIntegralConstructibleCategory l E W` (def-weil-derived-complete-integral-
  detailed: Roos complete, constructible reductions, common interval). K and L have exactly
  this type. No finite-Tor or uniform bound is assumed. `reduction_domain` derives
  R_W K ∈ N_W (step 1).
- S_W, R_W ⊣ L_W, u, e, H_W: `CoefficientDerivedSystemCalculus` (`S.reduction`,
  `S.adjunction`, `coefficientSequenceLimit`, `coefficientSequenceGlobalHom`). SX and SY are
  arbitrary calculi with no Coherence. This is the same harmless generalisation as in the
  landed sibling lem-coef-integral-dual-exceptional-system.
- F_f, E_f: the fields `r.F`, `r.G` of `r : Realization` (pinned by `supportIso`,
  `supportEvaluation(_canonical)`, `exceptionalEvaluation`, `unit`, `counit` and the
  transitions). The specified enriched adjunction A is `a : Enriched r g s βX βY`, pinned by
  `component`, `finiteEvaluation` and `finiteHom`. These are the data of the cited
  lem-coef-finite-adjunction-diagram-realization, not an integral adjunction.
- F_f = L_Y F_f R_X: `F r` is literally `R ⋙ r.F ⋙ ι ⋙ coefficientSequenceLimit`.
  J_f = `J r` is literally `L_X E_f R_Y`. Correct.
- F_f K ∈ D^b_c(Y,R): `support_and_counits`, clause 1, for every K.
- c_K = e_{F_f R_X K} and c_L = e_{E_f R_Y L} are natural isomorphisms.
  `supportCounit`/`exceptionalCounit` are whiskerings of the actual `adjunction.counit`.
  Clauses 2–3 state that their components are invertible, and `supportIso`/`exceptionalIso`
  are `asIso` of them. The forward maps are the actual counits. Correct.
- The evaluations of c_K are the canonical compact-support coefficient comparisons:
  `supportCoefficientComparison`, for every `i : IntegralSupport r`. The composite
  (F K)⊗A_n → eval_n R_Y F K → f_{!,n}(eval_n R_X K) → f_{!,n}(K⊗A_n) equals
  (i.iso)⊗A_n followed by `sfCompactSupportFiniteReductionIso`. The directions were checked.
- Ψ = H_X(1,c_L^{-1}) ∘ A ∘ H_Y(c_K^{-1},1): `psi` is the three-factor composite of natural
  isomorphisms of bifunctors on (K,L), with the first variable contravariant (`NatIso.op`),
  and with `a.iso` whiskered by `(R_X).op.prod R_Y`. Its source and target are exactly
  `mappingSource`/`mappingTarget` = H_Y(R_Y F K, R_Y L) and H_X(R_X K, R_X J L). The map is
  not lifted from its evaluations.
- The level-n formula on every shifted Hom: first conjunct of
  `integralExceptionalMappingSystem`. It is an equality in D(Ab) between `finitePsi` (Ψ
  evaluated and conjugated by `globalEvaluation`) and H(c_{K,n}^{-1},1) ≫ `a.finiteIso n` ≫
  H(1,c_{L,n}^{-1}), where `finiteSupport`/`finiteExceptional` are the evaluated counits
  followed by `r.supportEvaluation`/`r.exceptionalEvaluation`. The variance was checked:
  `.op` of the inverse precomposes.
- Degree zero: the second conjunct gives u ↦ c_{L,n}^{-1} ∘ adj_n(u ∘ c_{K,n}^{-1}) with
  adj_n = `FiniteExceptional.adjunction ... |>.homEquiv`, the finite exceptional adjunction
  of lem-coef-finite-exceptional. The order of composition matches the node.
- Étale origin, units/counits and coefficient transitions are inherited from the fields of
  `r` and `a`. Ψ is a system transformation, so it respects transitions. No integral
  adjunction is assumed anywhere.

Edge cases: K = 0 and L = 0 (objects of the category); empty X or Y (nothing excludes them);
f = id with the trivial compactification; n = 0 (meaning A_1); ramified E (only finiteness
over Q_l is assumed). Universes: one u throughout, with Ab at u+1 as in the cited
dependencies. No variable is unbound (`autoImplicit false`).

Gates: no hollow definition (all defs are functor composites, whiskerings, `asIso` of
counits named by a separate sorried theorem, or composites of isomorphisms). Every theorem
proof is `sorry`. The module and each declaration have docstrings with the source place and
`(blueprint: lem-coef-integral-exceptional-mapping-system)`. The theorem docstrings carry
the node's steps. The lean.statement is verbatim. The 17 listed declarations equal the
file's declarations. No line is over 100 characters. The pro-étale site is the genuine
`Scheme.ProEt`. Only the item's `lean` field differs from live.

Searches: I grepped the side-live lean/ tree for `IntegralExceptionalMapping`,
`Realization l E D hl f c` and `Enriched r g s`. The only users are the dependency modules
and the sibling IntegralDualExceptionalSystem. No existing statement of this result was
found, and there is no duplicate notion. The worker's LeanFinder/LeanSearch/Loogle/grep
records are in the node.

Advisory, not changed: Realization/Geometry/SectionsPush/domain/evaluation are owned by
def-coef-finite-adjunction-system-data, and CoefficientDerivedSystemCalculus by
def-coef-derived-system-calculus-data. Neither is in this item's stmt_deps. Both are
stmt_deps of the cited lem-coef-finite-adjunction-diagram-realization, whose Lean statement
quantifies over these very structures. The landed sibling uses the same citation pattern.

Change made by this reading: only this report section, because the previous section was
the author's self-pass.

### Author's self-pass (verbatim, superseded)

A separate rereading pass by the same dispatcher worker compared the complete
node with the final module; no second agent was launched, as instructed.
The initial draft's product-isomorphism elaboration was repaired by explicitly
using `NatIso.prod` and `NatIso.op`; the actual three-factor composite is retained.
The finite Hom target was made explicit to ensure it is L_n, rather than an
unresolved full-subcategory metavariable. A final rereading added the explicit
`supportCoefficientComparison` equation for the canonical coefficient comparison.
The finite evaluation equality is stated in D(Ab) itself, so it is stronger than
merely a degree-zero formula without adding mathematical content: it is exactly
the mapping-complex compatibility already asserted in the node. The definitions
use no choice from existence of an unconstrained map, and all theorem proofs
are `sorry`. The hypothesis/clause correspondence above was checked against the
final source, including the actual counits, canonical finite comparisons and
absence of an integral adjunction premise. No node statement changes were needed.

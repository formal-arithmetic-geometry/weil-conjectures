## Worker report

The module `Sheaf.Paper.FixedStalkIdentificationReduction` states
`WeilConjectures.fixedStalkIdentification_finite_reduction`. It defines the
stalk-sections functor, fixed-point identification, and the item-side canonical
quotient-presentation bridge. Its three theorems have proof `sorry`. There is no
statement correction and no new node. NO's landed point-sections dependency record
and its 27-declaration module are retained unchanged. A transitive finite-coefficient
Hom dependency retains the previously accepted compilation-only repair. The current library supplies the sequence-site and evaluation-calculus prerequisites;
the superseded sandbox repairs of those modules are removed from this delivery.

Hypotheses and clauses, matched to Lean:

- The primes, positive finite-field exponent, cardinality and algebraic closure are
  `D : FiniteFieldDatum`; its fields are `p`, `prime`, `a`, `exponent_pos`, `q`,
  `cardinality_eq`, `k₀`, `card_base`, `k`, and `isAlgClosure`.
  The other prime is `l : ℕ` with `[Fact l.Prime]` and `hl : l ≠ D.p`.
- The finite extension is `E : Type u`, `[Field E]`, `[Algebra ℚ_[l] E]`, and
  `[FiniteDimensional ℚ_[l] E]`. Its integer ring, chosen uniformizer and quotient
  are the recorded `Padic.coefficientExtensionIntegers`,
  `Padic.coefficientExtensionUniformizer` and `Padic.coefficientExtensionRing`.
  No second coefficient ring is defined.
- Every pair `N ≥ j ≥ 1` is represented as `N = m + 1`, `j = n + 1`,
  `hnm : n ≤ m`. Both inequalities of positivity are `Nat.succ_le_succ (Nat.zero_le _)`.
  `coefficientFiniteQuotientDerived l E W hnm` is sheaf coefficient reduction;
  `pointFiniteReductionModuleTensor l E (m+1) (n+1) (Nat.succ_le_succ hnm)` is
  ordinary coefficient-complex reduction, both actual derived change of rings.
- The separated finite-type base scheme is `X₀ : Over (Spec (.of D.k₀))` with
  `[IsSeparated X₀.hom]`, `[LocallyOfFiniteType X₀.hom]`, `[QuasiCompact X₀.hom]`.
  Its geometric base change is exactly `(D.geometricFiber X₀).left`.
  `D.geometricFiber X₀` retains its structure map to `Spec D.k`.
  These are the same data used by `TraceFormulaCoefficientConventions`, not a
  replacement notion of geometric fibre or trace-formula coefficients.
- A k-endomorphism is `h : D.geometricFiber X₀ ⟶ D.geometricFiber X₀` in the
  over category. There is no properness, finiteness or flatness assumption on h.
- The arbitrary geometric point is `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]`,
  `y : Spec (.of Ω) ⟶ (D.geometricFiber X₀).left`. It is not restricted to Ω = k.
  Fixedness is precisely `hy : y ≫ h.left = y`.
- The ambient categories are the recorded `proEtaleDerivedCategory` and ordinary
  `DerivedCategory (ModuleCat (ULift ...))`. The `ULift` is only the published
  coefficient-universe convention. Site objects and morphisms keep their existing
  distinct universes. All data live in one sufficiently large ambient scheme universe;
  this imposes no equality between site-object and site-morphism universes.
- Objects K vary over the full subcategory of
  `finiteTorConstructible l E (m+1) ... (D.geometricFiber X₀).left`, exactly
  D^b_ctf(X,A), with no perfectness or Weil structure assumed.
- `finiteDerivedPullback l E m h.left` and its n-level analogue are H_A and H_B.
  `pullbackTensorQuotient l E h.left hnm` is the published canonical μ_h, with
  its ordinary unit and K-flat-counit normalization, not a supplied comparison.
- `fixedStalkSections l E Ω y m` is S_A: the recorded finite pullback at y followed
  by `pointFiniteReductionSections Ω l E (m+1)`. Likewise at level n for S_B.
  These sections are the exact point-sections derived functor with the canonical
  constant-section coefficient action.
- `fixedStalkIdentification` uses the existing `sfIntrinsicDerivedPullbackComp`
  from `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`, also used by
  `canonicalFinitePullbackTensor_composition`. It first uses
  `eqToIso (congrArg ... hy.symm)` and then that exact published comparison,
  finally applying exact point sections. Thus its component is
  precisely iota : S_R(M) ≅ S_R(H_R M), in the direction specified by the node.
- The theorem supplies `hlΩ : IsUnit (l : Ω)` as a consequence, not a new
  assumption: Ω receives the residue field of a point on the characteristic-p
  geometric fibre. This is the proof needed to instantiate the point-sections theorem.
- The existential σ is a natural isomorphism from r S_A to S_B r_X, restricted
  to the full D^b_ctf category. Its first clause fixes every component: the
  published normalized `pointFiniteReductionCanonical`, followed by sections of
  the unique counit-compatible quotient-presentation identification, followed by
  sections of `pullbackTensorQuotient l E y hnm`. This is exactly σ of the node.
  In particular σ is not merely an arbitrary isomorphism satisfying the final square.
- For each K the conclusion supplies `hP`, the bounded-above property of P_A K,
  so that the published τ can be evaluated. It also supplies `hHK`, the finite-Tor
  constructibility of H_A K, to evaluate σ at that object. Both are consequences,
  not additional input hypotheses. The latter follows from clause (i) of the
  recorded finite-Tor stability theorem and the graph factorization of h.
- The last equation reads, in Lean's left-to-right composition order,
  `r.map iota_A ≫ σ_(H_A K) ≫ S_B.map μ_h = σ_K ≫ iota_B`.
  Hence its left-hand last two maps are exactly tilde-sigma, and the equation is
  the node's identity in D(B), with the B-linear structure retained.
- Naturality in K is encoded by σ being an isomorphism of functors on the full
  finite-Tor constructible category and iota being an ambient natural isomorphism.
  The other factors are maps of recorded functors and natural comparisons.
  No coefficient endomorphism, Weil structure, lift, or properness is supplied.

Dependency declarations used (all signatures and source docstrings read):

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `TraceFormulaCoefficientConventions` and its coefficient/geometric/finite-Tor conventions;
  the underlying `FiniteFieldDatum.geometricFiber` is used directly.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel` and
  `SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`; the published quotient
  realizations retain the universal derived counit rather than an arbitrary tensor map.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteDerivedPullback`, `finiteCoefficientRing`.
- `Sheaf.Paper.BasicOperationsCoefficientReduction`: `basicOperationsCoefficientReduction`,
  using its canonical finite comparison `pullbackTensorQuotient`, whose complete
  ordinary and derived normalization is in `CompletedPullbackTensorComparison`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points are inline
  as prescribed by `def-weil-geometric-point`. The interpretation agrees with
  `Scheme.SpecToEquivOfField` in `Mathlib.AlgebraicGeometry.ResidueField`.
- `Sheaf.Paper.PointProEtaleSectionsExact`: `point_proEtale_sections_exact`,
  `pointModuleSections`, specialized by `pointFiniteReductionSections`.
- `Sheaf.Paper.IntegralFinitePullbackComposition`:
  `integralTowerGeneralPullbackComposition`, `integralFiniteCanonicalPullbackComposition`;
  these retain the canonical composition in the ring-sheaf presentation. The exact
  intrinsic presentation uses `AlgebraicGeometry.Scheme.sfIntrinsicDerivedPullbackComp`
  from `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange` directly.
- `Sheaf.Paper.PointSectionsFiniteReduction`:
  `point_sections_finite_reduction`, its bounded-above domain, sections and two
  actual derived reduction functors; the item-side bridge only aligns presentations.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`,
  with its representative characterization. Its constant-coefficient specialization
  gives the canonical comparison used here.
- `Sheaf.Paper.FiniteTorStability`: clause (i) of `finiteTor_stability`.
- Proof-only `Sheaf.Paper.DerivedPullbackTensorIso`: `derivedPullbackTensorIso`,
  specifically the composition compatibility on tensor representatives.

Edge cases checked before and after writing:

- N = j, including N = j = 1: both quotient presentations include identity maps;
  the published τ has its identity normalization. No strict inequality is used.
- Non-flat A → B: all reductions are derived, with K-flat universal counits;
  neither the statement nor the presentation adapter assumes flatness of B.
- K = 0: all maps are isomorphisms of the zero complex; no nonzero-object condition.
- h = identity: the source equality is reflexive, with the canonical unit/composition
  coherence. Arbitrary endomorphisms remain permitted, including nonproper ones.
- Empty X: there is no geometric point into X; no contradictory universal existence
  of a point is asserted. The universally quantified implication remains valid.
- Ω larger than k: only a geometric map from Spec Ω is used, not identification
  with the fixed geometric base point or an algebraicity assumption on Ω/k.
- Pullback of a bounded complex is bounded above by exact finite inverse image;
  h*K remains D^b_ctf by graph factorization and finite-Tor stability.
- Naturality of τ is used on the point-complex map d_A itself; it is not assumed
  that d_A is the pullback of a morphism on X.

Searches (2026-10-18):

- `msearch.py ... leanfinder`: "The canonical identification of a stalk with pullback
  at a fixed geometric point commutes with finite coefficient reduction".
  Eight results on ordinary structure-sheaf stalk maps and fibres, including
  `stalkMap_toStalk_apply` and `stalkToFiberRingHom_germ`; no derived comparison square.
- `msearch.py ... loogle`: `DerivedCategory, "pullback"`: zero hits.
- `msearch.py ... leansearch`: "Composition comparison for derived inverse image at
  a fixed point compatible with extension of scalar coefficients". Eight results
  including `ModuleCat.extendScalarsComp`, polynomial laws and scalar restriction;
  none is this derived geometric-point identity.
- `msearch.py ... grep`: `stalk.*(pullback|tensor)|pullback.*stalk`. Twenty-five
  ordinary stalk/tensor hits, no constant-coefficient derived reduction identity.
- Source and side-library `rg`: `fixedStalkIdentification|pointFiniteReductionQuotient|
  fixedStalkSections` had no pre-existing declarations. Source `rg` for
  `stalk.*[Rr]eduction|[Rr]eduction.*stalk` found only unrelated comments.
  The exact blueprint item id was absent from upstream source. The upstream-name
  index also had no `FixedStalk|fixedStalk` declaration.
- Side-library conceptual searches found the existing Frobenius-specific local rho
  in `TraceFormulaLocalFrobeniusOperator` and the canonical finite quotient/pullback
  comparison. The former requires a strict Weil complex and a Frobenius iterate,
  so cannot express the present arbitrary-h, arbitrary-K identity. Their recorded
  constituent constructions are reused; no duplicate statement was found.

All universes and variables are explicitly bound. Definitions contain real data;
the newly postponed statements are the main identity and the two canonical
presentation-identification lemmas, each with a source and complete proof docstring.
The transitive Hom repair retains all of its existing named postponed statements unchanged.
There is no STATEMENT-DISPUTED issue or node correction.

## Dependency modules

The dependency modules in this packet belong to
`def-sf-etale-finite-coefficient-hom-arrow`,
`def-pur-integral-compact-support-coefficient-data`, and
`def-weil-derived-pullback-tensor-hom`. Detailed readings appear below.

`def-sf-etale-finite-coefficient-hom-arrow` is a transitive prerequisite of the recorded
operation-reduction dependency. Its existing module
`Sheaf.Paper.EtaleFiniteCoefficientHomArrow` repeatedly exceeded the 60-second per-file
limit, both in the overlay and in server confirmation, preventing the main module from
loading. The sandbox repair retains all declaration names, binders, definition bodies,
canonical normalizations and proof docstrings. It makes the two backward transparency
options explicit and omits redundant result annotations on `finiteHomEtaleTotalSection`
and `finiteHomEtaleTensorModel`. Their result types are inferred from the already typed
`generator` and `model` fields of the same canonical representative record, and are
definitionally the previous types. The primary `etaleFiniteHomCanonical` signature is
unchanged. No file is split, no timeout is raised, and no linter is disabled.

This transitive node still expresses exactly its original statement: finite positive
quotient levels over a finite l-adic coefficient extension on an arbitrary scheme;
the published etale Hom and tensor; the evaluation-defined closed transpose;
the canonical quotient associator; the intrinsic pro-etale arrow and associator;
and the actual pure-tensor generators, signed-total inclusions and localization
tensorator. No hypotheses, maps, units, normalizations or universes are changed.
The seven retained theorem sorries are `finiteHomEvaluation_naturality`,
`finiteHomDerivedBraiding_existsUnique`, `finiteHomEtaleClosed_existsUnique`,
`finiteHomEtaleData_existsUnique`, `finiteHomQuotient_comp`, `finiteHomEtaleHasTensor`,
and `finiteHomEtaleRepresentativeData_existsUnique`. Their original complete proof
docstrings remain unchanged. Only the dependency's `lean` record changes in its node.

## Second reading by NQ

No second reading by another worker: this dispatcher brief prohibits starting agents.
The worker delivers directly for the maintainer's independent review. The clause-by-clause
reading above was checked again against the node and the delivered modules. In particular,
it checks the direction of the composition map, all five vertices of the coefficient
square, both boundedness/domain witnesses, the canonical normalization of σ, the full
naturality type, the identity quotient, and the absence of properness/Weil hypotheses.
The returned H13/H4 issues were checked against the saved packet and current main:
all seven bridge declarations now belong to the item's module and lean.declarations;
NO's dependency node is absent from the delivery, so its landed record is unchanged;
the alias module and alias declaration are removed; and iota now applies the existing
sfIntrinsicDerivedPullbackComp with the same coefficient ring and maps y, h.


## Repair of return 646996ee7ab7

H13/H4 (point-sections ownership): removed
`PointSectionsFiniteReductionQuotientModel.lean`, the theorem alias, and the
`lem-trf-point-sections-finite-reduction` node override. The original
`Sheaf.Paper.PointSectionsFiniteReduction.point_sections_finite_reduction`
remains owned by NO's original record, with all 27 declarations and all importers
retained. The presentation mismatch is handled inside the item module by
`pointFiniteReductionQuotientExtension_eq`, `pointFiniteReductionQuotientExtensionIso`,
`pointFiniteReductionQuotientExtensionAdditive`, `pointFiniteReductionQuotientComplexIso`,
`pointFiniteReductionQuotientTensorIso_existsUnique`,
`pointFiniteReductionQuotientTensorIso`, and `pointFiniteReductionCanonical`.
All seven are listed in the item's `lean.declarations` and their blueprint docstrings
name this item. Their mathematical types and canonical counit normalization are retained.

H4 (duplicate composition): removed `fixedStalkPullbackComposition` entirely.
`fixedStalkIdentification` uses the existing
`AlgebraicGeometry.Scheme.sfIntrinsicDerivedPullbackComp` at the finite coefficient
ring. Its source, target, direction and termwise-descended comparison are the same;
the local finite-ring instance is supplied by the recorded coefficient-ring theorem.
The main theorem's signature remains verbatim unchanged.

The accepted transitive Hom-arrow repair is unchanged from the returned head.
Comparison with current main shows it still differs only by the two transparency
options and removal of the two redundant result annotations. No other dependency
record is replaced. The saved packet's initial required dry run was attempted before
editing: server confirmation reached `DerivedPullbackTensorHom.lean` but timed out
at 60 seconds; the local pass had reported a missing RationalizationKaroubi artifact.
The repaired packet is validated again through the prescribed wrappers below.


### Dependency module: def-pur-integral-compact-support-coefficient-data

`Sheaf.Paper.IntegralCompactSupportCoefficientData` was moved into its own module
by the maintainer on 2026-10-18. Current-source compilation reported two overlong
prose lines, of lengths 116 and 102. This delivery wraps those lines, retaining
all prose, imports, declarations, signatures and bodies. Its dependency node
changes only in `lean`, retaining the same declaration names and file ownership.
The coefficient ring sheaves and pullback identifications are still `Coefficients`;
compatible coefficient maps are `Change`; exact open extension, its adjunction and
restriction mate are `openExtension`, `openAdjunction` and `openRestrictionMap`;
the separately derived proper image after exact open extension is `image`; the
actual change-of-rings comparison is `comparison`; projection is `projectionMap`
with its existing canonical comparison data. `completed` retains the completed
coefficient sheaf and actual pullback maps, and `finite` retains the finite
quotient system. All original postponed theorems and their source/proof docstrings
remain intact. This is a whitespace repair, with no change to hypotheses, clauses,
universes, empty-scheme cases, identity maps or non-flat coefficient reductions.


### Dependency module: def-weil-derived-pullback-tensor-hom

The retained sandbox repair of `Sheaf.Paper.DerivedPullbackTensorHom` differs from
current main only by `backward.isDefEq.respectTransparency false`,
`backward.isDefEq.respectTransparency.types false`,
`synthInstance.maxSize 2048`, and a final blank line. This permits the existing
composite-instance search and avoids expensive transparent comparisons while
elaborating the same canonical operations. Every declaration, definition body,
theorem statement and source/proof docstring is unchanged. Its node record now
copies the main signature with the source newlines verbatim, rather than the
inherited single-line rendering.

Clause-by-clause: `finiteDerivedPullback` remains exact intrinsic inverse image;
`finiteIntrinsicDerivedTensor`, `finiteIntrinsicDerivedInternalHom`,
`finiteIntrinsicTensorModels`, `finiteIntrinsicEvaluation`,
`finiteIntrinsicTranspose` and `finiteIntrinsicReductionHom` retain the actual
finite operations and their K-flat/closed normalization. The integral operations
remain the recorded ambient constructions restricted to the constructible domain.
Rational operations retain their uniquely determined linear or bilinear action,
and common-stage operations retain the compositum objects and conjugated
representative maps. No hypothesis or universe changes, and no resolution,
comparison, evaluation or quotient map is replaced. All twelve named postponed
theorems retain their complete proof docstrings. Identity pullback, zero objects,
positive-level identity quotients, non-flat reductions and common-stage identity
and tower cases remain covered.


## Repair of return 5f0862896f26

The first resumed dry run used the retained packet unchanged. It passed compilation
and reported three preflight record/report faults. The compact-support declaration
list now omits `WeilConjectures.PurCompactSupport.maps`, which is a prose fragment,
not a declaration. The Dependency modules section now names all three dependency
nodes. Non-Lean node fields are rebased on the current shared DAG, preserving the
maintainer's intervening reviewed_lean record. The compact-support source retains
all current public imports, with only the two prose-line wraps from the saved
repair. No statement or definition body is changed by these repairs.

Validation: the repaired packet passes `deliver2.py ... --no-push` (commit
57d73496f6). A separate prescribed `scompile.py` invocation checked all four
modules in dependency order with exit 0 and no warnings. Library-file timings:
DerivedPullbackTensorHom 39.5 s, IntegralCompactSupportCoefficientData 9.0 s,
EtaleFiniteCoefficientHomArrow 29.1 s, FixedStalkIdentificationReduction 5.1 s.
The returned PbcScalarExtension timeout does not recur against the current
published dependencies; this packet does not override that module. All four
recorded signatures occur verbatim in their sources, every Lean line is at most
100 characters, and every node differs from the current DAG only in `lean`.

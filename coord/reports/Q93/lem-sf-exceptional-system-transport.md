## Worker report

Q93 states `AlgebraicGeometry.exceptionalSystemTransport` in
`Sheaf.Paper.ExceptionalSystemTransport`. The sole postponed proof is this theorem.
Every definition has its full data. The auxiliary records are the conclusion of this
node, not assumptions in the theorem. They package the actual geometric image
adjunctions, localization on complexes, normalized mate maps, and the restricted
system adjunction. These are helpers belonging to the item's own notion, as allowed
by brief-stage2 §1 (Missing helpers); no independent new notion or dependency repair
is introduced. Only `lean` changes in the node copy.

The formalization uses the existing `SheafOfModules.CoefficientSystem`,
`CoefficientSystemOrdinaryImage`, `CoefficientSystemDerivedImage`,
`CoefficientEvaluationDerivedPackage`, and `IsNormalizedCoefficientSystem`.
It does not introduce another category of coefficient systems or a second tensor
operation. The pro-etale specializations use the actual small pro-etale site:
object universe u+1, morphism universe u, coefficients u+1, derived Hom universe
u+2. The standard derived localizations and existing sheafification instances are
exposed at those sizes; no equality of site universes is assumed.

### Hypotheses, one by one

| Node hypothesis | Lean rendering |
| --- | --- |
| Finite-field datum, including the chosen algebraic closure | `(D : WeilConjectures.FiniteFieldDatum.{u})`; the schemes are over `Spec (.of D.k)` |
| Prime l different from p | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)` |
| Finite extension E of Q_l | `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]` |
| Valuation ring and chosen uniformizer | `Padic.coefficientExtensionIntegers l E`, `Padic.coefficientExtensionUniformizer l E` |
| Positive quotients A_n | Existing `coefficientLevelModules` with ring `O ⧸ (Ideal.span {ell}) ^ (n + 1)`. Lean index zero is the residue quotient, not the zero ring. |
| X and Y finite type over k | `X.Over`, `Y.Over`, and `LocallyOfFiniteType` plus `QuasiCompact` on each structure morphism |
| f is a k-morphism | `(f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]` |
| f separated and finite type | `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` |
| No absolute separatedness | No `IsSeparated` instance on either structure morphism is requested. |
| Chosen compactification c | `(c : Compactification f)`, with `c.i` the open factor and `c.g` the proper factor |

The coefficient universe agrees with the recorded etale-system adjoint and allows
all smaller coefficient fields by cumulativity. There is no additional regularity,
completeness, flatness, cohomological-bound, or abstract-equivalence hypothesis:
those facts are construction conclusions for the specified coefficient ring.

### Conclusions, clause by clause

1. **Ordinary derived strict systems, levelwise exactness.**
   `ExceptionalProEvaluation` specializes the recorded derived evaluation package.
   `ExceptionalProOrdinaryImage` specializes the ordinary-image package to
   `Scheme.proEtaleSheafAdjunction`. `ExceptionalProCompactSupportData` supplies
   the open extension as the left adjoint of geometric restriction and the proper
   derived image through `CoefficientSystemDerivedImage`. Its coherence fixes
   the open localization and transpose on complex representatives. Consequently
   `exceptionalProSupport P` is literally `P.val.derivedOpen ⋙
   P.val.properDerived.system.direct`, the stated Rp_* j_! before any evaluation.
2. **The etale F and G.** The existential `S : StrictEtaleCompactSupport ... c`
   and `G : StrictEtaleExceptionalAdjoint ... c S` reuse the recorded ordinary
   etale system construction, including its finite adjunctions, scalar actions,
   counit-normalized quotient comparisons and bound. They are conclusions, not
   extra supplied data.
3. **C_T and V_T with actual unit and counit.**
   `ExceptionalSystemSiteComparison` uses `Scheme.proEtaleSiteComparison T`
   and the full recorded ordinary and derived coefficient-image packages.
   `image.system.inverse` is C_T and `image.system.direct` is V_T.
   `ExceptionalSystemSiteEquivalence.unit` and `.counit` assert invertibility
   of these packages' own unit and counit; `.inverseOrigin`, `.inverseBound`
   and `.directBound` give the restrictions. The input class `.origin` is
   bounded below uniformly as a whole system, with every finite level in the
   bounded-below etale essential image. `.inverseNormalized` and
   `.directNormalized` give preservation of the dependency's existing
   transition-adjoint normalization predicate.
4. **Canonical proper/open comparison.**
   `ExceptionalSystemPullbackSquareCoherence` fixes the ordinary square on
   underlying sheaves to `ProEtale.comparisonCoefficientPullbackIso`, and fixes
   its derived square on complex representatives. Its evaluation equation
   identifies the finite square. `exceptionalSystemComparison R` is explicitly
   the `mateEquiv` of that proper square followed by `R.openComparison`.
   `ExceptionalSystemCompactificationComparisonCoherence` fixes the latter by
   its open mate, also at finite levels. `exceptionalSystemOriginComparison R`
   then composes the actual source comparison counit. These are the node's J
   and kappa. `ExceptionalSystemTransportCoherence` asserts their invertibility
   on D+ and the origin class respectively. No arbitrary proper comparison
   arrow or arbitrary isomorphism replaces the canonical map.
5. **Transported adjunction on the specified class.**
   `exceptionalSystemRight G CX CY` is literally
   `CY.image.system.direct ⋙ G.right ⋙ CX.image.system.inverse`.
   `ExceptionalOriginAdjunction` contains stability on both classes and an
   actual adjunction of the corresponding `ObjectProperty` full subcategories.
   Its `transpose` equation is the whole-system forward Hom-chain formula,
   multiplied by the actual source site counit. This determines the transported
   transpose, hence both its unit and counit, on the origin class; it does not
   merely assert existence of an unspecified adjunction.
6. **Exact R_E-linearity.** The data provide the additive and shift structures;
   the coherence's `leftExact` and `rightExact` clauses require
   `Functor.IsTriangulated` for both actual functors. `ExceptionalProScalarAction`
   fixes multiplication by the ordinary constant-sheaf scalar and its derived
   representative. The `leftLinear` and `rightLinear` equations commute these
   specified scalar actions with the two functors. By naturality and additivity
   this gives the asserted R_E-linearity on Hom groups.
7. **Finite operations and evaluated unit/counit.**
   `exceptionalProSupportEvaluation` is the composite of the proper/open
   evaluation isomorphisms; `exceptionalSystemRightEvaluation` is the composite
   for V_Y, G and C_X. `finiteAdjunction n` is the same Hom-chain transport at
   that finite level. `evaluationOriginX/Y` ensure evaluation lands in the
   finite classes. The `comparisonEvaluation`, `unitEvaluation` and
   `counitEvaluation` equations identify the actual system maps with the finite
   ones, under exactly those evaluation isomorphisms.
8. **Quotient transitions and counit normalization.** The `quotientTransition`
   equation is stated for every `h : n ≤ m` and every whole system N. It uses
   the actual derived transition adjoints, `G.quotientComparison h` (already
   normalized by the recorded etale adjunction counits), the input transition,
   and `CX.image.derivedTensor h`. It is formed on the unbounded etale side
   before applying C_X; no flatness of A_m → A_n, or boundedness of its tensor,
   is assumed. `exceptionalSystemRightEtaleEvaluation` retains precisely that
   intermediate etale target, so no replacement transition on V_Y N is used.
9. **Normalization and uniform bound.** The final two coherence clauses say
   that H preserves `IsNormalizedCoefficientSystem` on `CY.origin` and that
   `∃ c_f : ℕ, ∀ (a : ℤ) N, CY.origin N → N.IsGE a →
   (H.obj N).IsGE (a - c_f)`. The bound is on the whole system and therefore
   is independent of the finite index. `rightStable` also gives bounded-below
   etale origin of H N.
10. **Before evaluation.** All functors, the proper mate, the open map, kappa,
    and the restricted adjunction are declarations on derived system categories.
    Evaluations describe their properties. No clause asserts evaluation is
    faithful on derived morphisms, or infers equality of system maps merely
    from equality at finite levels.

### Dependency declarations used

Statement dependencies were read in their node records and source, including the
complete signatures and docstrings:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, reexporting the actual
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer`
  and `Padic.coefficientExtensionRing` constructions.
- `def-weil-scheme-morphism-properties` is explicitly a convention with no
  declaration. Its recorded Mathlib meanings are used: `IsSeparated`,
  `LocallyOfFiniteType`, `QuasiCompact`, and `Scheme.Over` / `Scheme.Hom.IsOver`.
- `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement` and `.category`, reexporting
  the actual `Compactification` used here.
- `Sheaf.Paper.CoefficientSystemDerivedComparison`:
  `SheafOfModules.coefficientSystemDerivedComparison`, and its reexported
  `CoefficientSystemOrdinaryImage`, `CoefficientSystemDerivedImage`,
  `CoefficientEvaluationDerivedPackage`, `CoefficientSystem`, evaluation and
  `IsNormalizedCoefficientSystem` interfaces. These are specialized, not copied.

The proof-dependency modules are imported explicitly. The proof docstring follows
all nine assembly steps. Its named inputs are:

- `Sheaf.Paper.EtaleSystemBrownConstruction`:
  `AlgebraicGeometry.etaleSystemBrownConstruction`.
- `Sheaf.Paper.EtaleCoefficientSystemAdjoint`:
  `AlgebraicGeometry.etaleCoefficientSystemAdjoint`,
  `StrictEtaleCompactSupport`, `StrictEtaleExceptionalAdjoint`.
- `Sheaf.CategoryTheory.ExactDerivedAdjunctionBounds`:
  `CategoryTheory.exactDerivedAdjunction_isGE` and the origin-counit clauses.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `WeilConjectures.SemilinearSections.semilinearDerivedSections`.
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`:
  `AlgebraicGeometry.ProEtale.isIso_compactSupportComparisonUnit`.
- `Sheaf.CategoryTheory.SystemDerivedEvaluation`:
  `SheafOfModules.systemDerivedEvaluation_bounds_iff` and
  `systemDerivedEvaluation_isIso_iff`.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `AlgebraicGeometry.ProEtale.supportSiteComparison_pullback_coherent`;
  its underlying canonical `comparisonCoefficientPullbackIso` comes from the
  publicly imported `ComparisonPullbackCoherence` module.
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison`:
  `AlgebraicGeometry.ProEtale.openImmersionLowerShriekComparison_coherence`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `AlgebraicGeometry.ProEtale.fixedComparisonDirectImageMatePlus` and
  `isIso_fixedComparisonDirectImageMatePlus`.
- `Sheaf.Paper.EtaleSystemEvaluationBound`:
  `AlgebraicGeometry.etaleSystemEvaluationBound` and its quotient-mate data.
- `Sheaf.Paper.EtaleProEtaleScalarPullbackCube`:
  `AlgebraicGeometry.ProEtale.etaleProEtale_scalar_pullback_cube`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and `.FiniteType`:
  `IsProper`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`.
- `Mathlib.CategoryTheory.Adjunction.Basic`:
  `CategoryTheory.Adjunction.mkOfHomEquiv`.
- `Mathlib.CategoryTheory.Adjunction.Mates`:
  `CategoryTheory.mateEquiv`, `mateEquiv_vcomp`, `mateEquiv_hcomp`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `CategoryTheory.Functor.mapDerivedCategory` with its triangulated instance.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`:
  `CategoryTheory.Functor.instCommShiftDerivedCategoryRightDerivedFunctorInt`
  and `instIsTriangulatedDerivedCategoryRightDerivedFunctor`.

### Edge cases and source checks

The residue level is retained by n+1 indexing. The identity quotient h is included;
nonflat positive quotients are handled by derived tensor on unbounded categories.
For the identity compactification the mate and Hom-chain formulas reduce to the
site triangle identities; the actual site counit is retained. Empty source gives
the zero compact-support functor and a zero right functor, with c_f = 0. Empty
Y forces empty X. No nonemptiness, absolute separatedness or positive dimension
assumption is present. The bound is uniform and the origin condition includes
uniform whole-system boundedness, not only individual bounds that can vary with n.

Source read: Zheng's Construction 4.1, Lemma 4.10, Lemma 5.22 and Proposition 5.24,
in the supplied literature PDF (the latter material on printed pp. 36–37), and
the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md`. The latest blueprint's
integral condensed construction is distinct from this node's strict finite
quotient-system transport; this delivery does not redefine integral Rf!.
The requested returned steps 8–9 are preserved verbatim below.

No statement correction, new independent node, dependency-record repair, or
STATEMENT-DISPUTED issue is claimed.

### Searches for an existing statement

The prescribed msearch calls were run as Q93 / this item:

| Tool | Query | Result |
| --- | --- | --- |
| LeanFinder | Transport an adjunction on derived strict coefficient systems from etale to proetale by the site comparison equivalence | 8 generic hits, including `Equivalence.transportSheafificationAdjunction` and `Adjunction.derived`; none includes this system statement or its normalized maps. |
| Loogle | CategoryTheory.Adjunction, CategoryTheory.Equivalence | 6 generic adjunction/equivalence declarations; no strict-system transport theorem. |
| Mathlib grep | ExceptionalSystem\|strictProEtale\|coefficientSystemDerived | No hits. |
| LeanSearch | transport exact linear adjunction derived coefficient systems etale proetale comparison | 8 generic derived-adjunction hits; no matching statement. |

`rg` over `lean/WeilConjectures` and `lean/Sheaf` for
`exceptionalSystemTransport|ExceptionalSystem|strictProEtale|StrictProEtale|lem-sf-exceptional-system-transport`
found existing specialized integral/clopen frameworks, not this statement.
The direct upstream node-id search had no hit. The existing clopen comparison
record is coefficient/universe specific and includes a sequence realization;
it does not state transport with these actual strict-system operations and
quotient adjoints. Existing generic adjunction/mate definitions are used directly.
The search log is in the sandbox's `searches.jsonl`.

### Validation

All Lean compilation is through the prescribed `scompile.py`, in module mode,
against the live server build with the ordinary 60-second per-file limit.
The final import-complete version compiled cleanly in both sandbox and library
module names (scompile exit 0). The delivery dry run also compiles it. No global build or direct shared-repository mutation is used.
Data and coherence are grouped separately so elaboration remains under the file
limit; this is a representation choice, not a change in mathematical clauses.
All universes and variables are explicitly bound; no diagnostic commands remain.

## Second reading by Q93

The dispatcher explicitly prohibits starting another agent. Accordingly this is
an additional self-reading, not a claim of independent review; the maintainer's
independent review remains the delivery review. I reopened the node and full
module, checked each row and clause above, and checked that every construction
record is existential in the conclusion, not an added assumption.

The review retained the whole-system Hom-chain equation to fix the transported
unit/counit, retained the source-site counit in kappa, used the intermediate
etale evaluation in the quotient-transition formula, and passed the recorded
shift structure explicitly to both `IsTriangulated` clauses. The explicit
compactification import was corrected to its recorded `WeilConjectures` module.
The first dry run found that its declaration scanner did not recognize seven
instance names placed after a line break following the priority attribute. These
headers now place the instance keyword, priority and name together, with unchanged
types and bodies. No mathematical mismatch with the unchanged node was found in
this reading.

## Preserved returned construction steps 8–9

### lem-sf-exceptional-system-transport

Old step 8: Form the actual strict systems with coefficients $A_n=R_E/\varpi_E^n$ on the etale site. The coefficient-system adjunction theorem gives an $R_E$-linear exact adjunction $\mathsf F^{et}=Rp_{c,A,*}j_{!,A}\dashv\mathsf G^{et}$ on their ordinary derived categories. Its conclusion supplies $e_n\mathsf G^{et}\cong f^\times_{c,A_n}e_n$, including evaluated units, counits and quotient transitions, a uniform lower bound and preservation of bounded-below normalization. These assertions are not inferred merely from evaluation of the left functor. Schemes have trivial inertia, and our geometric hypotheses are precisely those of that node; in particular $Y$ may be nonseparated. All further operations use this actual derived-system adjunction.

Cited nodes: lem-pur-etale-coefficient-system-adjoint, lem-pur-coefficient-system-derived-comparison.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Construction 5.15, Lemmas 5.13, 5.16 and 5.22, and Proposition 5.24 (pp. 34–36)."}

Old step 9: Write $C_T=\nu^*_{T,A}$ and $V_T=R\nu_{T,A,*}$. The system comparison theorem supplies an actual adjunction with the stated evaluation isomorphisms. On bounded-below systems of etale-origin levels its counit is invertible; its unit is invertible because it evaluates to the finite site-comparison unit and evaluations jointly detect isomorphisms. These are equivalences on this class and preserve normalization. Construct the system compact-support comparison by the derived direct-image mate for the proper factor and the termwise open comparison. Evaluation gives the canonical proper and open comparisons, so joint conservativity proves that this actual system map is invertible. The system Hom chain is therefore
$$\operatorname{Hom}(\mathsf F^{pro}M,N)\cong\operatorname{Hom}(\mathsf F^{et}V_XM,V_YN)\cong\operatorname{Hom}(V_XM,\mathsf G^{et}V_YN)\cong\operatorname{Hom}(M,C_X\mathsf G^{et}V_YN).$$
Use its unit and counit to transport the adjunction and its finite coefficient transposes. No faithfulness of finite evaluations on morphisms is used.

Cited nodes: lem-pur-coefficient-system-derived-comparison, thm-weil-pbc-site-comparison, lem-pur-system-level-left-extension, lem-weil-pbc-ringed-topoi-derived-pushforward-composition, lem-weil-pbc-comparison-direct-image-canonical-mate, lem-cbc-proetale-extension-zero-comparison, lem-weil-pbc-adjunction-of-natural-bijection.

Source: {"document": "literature/zheng-six-operations-lefschetz-verdier-DM-stacks_arXiv-1006.3810.pdf", "place": "Zheng Lemma 5.22 transported using system comparison; finite comparison is Stacks Tag 09B1."}

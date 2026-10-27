## Worker report

The item is stated in `Sheaf.Paper.CompactSupportSystemTransposeNormalization`, with
main declaration `WeilConjectures.compactSupportSystemTransposeNormalization`. Every
theorem has `sorry`; all definitions have real data. The item's mathematical text,
statement dependencies, proof, and proof dependencies are unchanged. All 32 declarations
are owned by this item and listed in its lean.declarations. The three dependency node
files are byte-identical to sheaf-dag; their original modules are public imports.

Hypothesis and clause correspondence:

- `l : ℕ` and `[Fact l.Prime]` give the prime; `K₀ : Type u`, `[Field K₀]`, and
  `hl : IsUnit (l : K₀)` give the ground field and invertibility. No finite-field
  assumption occurs. Residue invertibility needed by the operation API is derived
  inside the two wrappers using the existing `sfCompactSupportScalarResidueUnit`;
  it is not an extra hypothesis.
- `E L : Type u`, their `Field`, `Algebra ℚ_[l]`, and `FiniteDimensional ℚ_[l]`
  instances, and `ι : E →ₐ[ℚ_[l]] L` represent the finite coefficient extensions
  and their inclusion. Field embeddings represent inclusions without making an
  irrelevant choice of ambient algebraic closure. The existing small coefficient
  models cover subextensions of a closure in an independent universe. The identity
  embedding is allowed. The actual quotient sheaf maps are
  `integralComparisonSequenceScalarMap`, using the existing uniformizers and n+1.
- `X Y : Scheme.{u}`, their `Over (Spec (.of K₀))` instances, the two pairs
  `LocallyOfFiniteType`/`QuasiCompact` for the structure morphisms, `f.IsOver`, and
  `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` render exactly the
  finite-type schemes and separated finite-type ground-field morphism.
  `c : Compactification f` contains the fixed open immersion `c.i`, proper `c.g`,
  intermediate scheme `c.Z`, and factorization. Neither structure map is assumed
  separated.
- `coefficientSequenceDerived` is the existing ordinary unbounded derived category
  of module sheaves over the actual ring sheaf on the small pro-etale sequence
  site. Its objects retain coherent strict semilinear quotient transitions. No
  replacement by a sequence of derived categories occurs. The generic sequence-site
  equivalence and semilinear calculus are imported publicly.
- `FrobeniusExchange.reduction`, `(models l E).system W` and its `adjunction`, and
  `coefficientSequenceLimit` are the fixed R, its reduction/limit adjunction, and L.
  `integralComparisonDerivedSequenceScalar` is S. `systemScalarRestriction` and its
  `mapDerivedCategory` are exact U. `systemScalarAdjunction` is normalized using the
  same universal cochain counit and the ordinary section unit; its unit is zeta.
- `systemDerivedOpen ... c.i ⋙ systemDirect ... c.g` is H. The item-owned
  `realizedSystemCompactRestriction` is d in these very operation coordinates; its
  ordinary push square is identity on sections, its proper comparison has the full
  K-injective-resolution equation, and its open part uses the original open unit.
- The fixed integral F is `sfCompactSupportFiniteIntegralFunctor`; completed C is
  `integralScalarExtension` (the retained equal-universe form of the recorded
  `integralScalarExtensionOfUniverses`). The b in the equations is precisely
  `sfCompactSupportScalarSystemMap`, the existing prescribed proper/open whole-system
  word conjugated by the fixed projection-normalized realizations. The dependency
  `sfCompactSupportNormalizedScalarIsomorphisms` identifies it with the normalized
  integral natural isomorphism. It is never a parameter or an arbitrary lift.
- `compactSupportTransposeReduction` is r: it is literally
  `compactOperationReduction` with residue units derived from hl. The helper
  `compactSupportSystemScalarReduction` is s: it is literally
  `integralComparisonScalarCounit` for the fixed models, their scalar realization,
  and the fixed Roos model. Its isomorphism clause is asserted for all ambient H
  on each of X, c.Z, Y. Thus it is not silently restricted to constructible inputs.
- The first conjunct gives eta followed by U(s) equal to zeta, on each of
  X, c.Z, Y and every ambient H. Eta is `wholeMixedCompletedReductionUnit`, the
  strict-chain mixed unit followed by reduction/restriction of the prescribed
  `scalarCompletion`. The item-owned helper records its section formula and a
  whole-system cochain square, not only its separate derived evaluations.
- `compactSupportSystemTranspose` defines q by the inverse of the actual scalar
  `homEquiv`, applied to H_A(zeta) followed by d. The all-M/all-Z bijectivity
  conjunct expresses its characterization for every derived target. The next
  conjunct is exactly its stated transpose equation, in Lean's left-to-right
  composition order. No boundedness or constructibility occurs here.
- The next two conjuncts assert that r_B is invertible on every B-constructible
  input and r_A on every A-constructible input, also explicitly at C_X K. The
  equation then reads R_B(b), followed by r_B and H_B(s_X), equal to s_Y followed
  by S_Y(r_A) and q. All are arrows of the entire B-system derived category.
- `compactSupportTransposeSource` is xi_s: scalar realization followed by L S(r_A).
  `compactSupportTransposeTarget` is xi_t: operation realization followed by
  L H_B(s_X). Both are asserted invertible. The last conjunct includes their
  actual counit squares `R_B(xi_s) ≫ epsilon = s_Y ≫ S_Y(r_A)` and
  `R_B(xi_t) ≫ epsilon = r_B ≫ H_B(s_X)`, then `b ≫ xi_t = xi_s ≫ L(q)`.
  The fixed scalar/operation realizations carry the recorded normalized Roos
  bridges, whose `computes` equation uses the limit tuple and zero shifted
  coordinate. Thus these are the same coordinates and cochain counit squares
  throughout, without choosing a new comparison. No family composition/unit
  equation for b, quotient-flatness assumption, Tor bound, or faithfulness of
  separate evaluations has been added.

Dependency declarations read and used (the convention node fixes no declaration):

- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `sfQcqsCompactSupportRealization` and its projection-normalized specification.
- `Sheaf.Paper.SemilinearDerivedSections`:
  `SemilinearSections.semilinearDerivedSections` and its system, scalar and
  geometric interfaces.
- `Sheaf.CategoryTheory.SystemRingedSequenceSite`:
  `SheafOfModules.strictSystemSequenceEquivalence`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `CoefficientDerivedSystemCalculus`, `CoefficientReductionPresentation`, and
  `coefficientDerivedSystemEvaluationCalculus` (including its reduction and counit).
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction`; the item-owned cochain specialization uses
  the identical universal-pair normalization.
- `Sheaf.Paper.SystemCompactSupportRestrictionCocycle`:
  `AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction.compactSupportRestrictionCocycle`,
  `Comparison`, `ProperComparison`, `OpenComparison`, and their signatures.
- `Sheaf.Paper.CompactSupportFiniteAction`:
  `sfCompactSupportFiniteIntegralFunctor`, `sfCompactSupportFiniteReductionIso`.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `integralScalarExtensionOfUniverses` and its retained original interface.
- `Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms`:
  `sfCompactSupportScalarSystemMap`, `sfCompactSupportNormalizedScalarIsomorphisms`,
  `sfCompactSupportScalarResidueUnit`.
- `Sheaf.Paper.SystemOperationExchangeRealization`:
  `FrobeniusExchange.models`, `scalarModels`, `reduction`, `systemDerivedOpen`,
  `systemDirect`, `systemCompactScalar`, `compactRealization`, `compactOperationReduction`.
- `Sheaf.Paper.CoefficientExtensionReductionModel`:
  `coefficientExtensionReductionModel` and `coefficientExtensionCounit`, with their
  association/strict-quotient/representative normalizations.
- `Sheaf.Paper.MixedReductionUnit`:
  `sfMixedReductionUnit`, `sfMixedReductionUnitHomotopy`,
  `sfMixedReductionDerivedUnit_existsUnique`, `sfMixedCompletedReductionUnit`.

The main docstring transcribes all eight proof steps. Stated proof dependencies are
imported plainly, including K-flat resolution/change of rings, quotient scalar
comparison descent, strict Roos comparison, exact countable pro-etale products,
open normalization, mates, the strict Roos homotopy functor, and augmented scalar
Roos resolution. Statement dependencies are public imports, directly or through
the original dependency modules. The three specialized interfaces are declarations
of the item module, not replacement dependency declarations.

Sources: the item's recorded old finite-field-independence source path no longer
exists under `literature/blueprint/latest/`; I did not substitute an older snapshot.
I read the current `sec-six-functors-basics/sk-prop-sf-pf-reduction/lem-fix-operation-reduction.md`
and its proof. Its last paragraph specifies actual scalar comparisons preserving
units, counits, evaluations and associators. The node explicitly labels the more
detailed system identification as agent-supplied, and the existing realization
interfaces encode that detail. No mathematical node correction was needed.

Edge cases checked before writing and on the final reading: E=L with identity
embedding; zero complexes; empty X or Y; level n=0 (exponent 1); arbitrary and
ramified coefficient embeddings, where quotient maps can fail flatness; arbitrary
unbounded M and arbitrary derived targets Z; finite-type schemes whose structure
maps need not be separated; no finite-field restriction. The index is all ℕ with
positive exponent n+1, so no zero quotient-level collapse or missing initial level.
The site keeps objects in u+1 and morphisms in u with coefficients in u+1, as in
the existing sequence-site encoding. No new equality of site universes is assumed.

Searches actually run:

- `msearch.py ... leanfinder`: "Compact support scalar comparison on whole derived
  coefficient systems is the scalar adjunction transpose and its derived limit realization".
  Eight unrelated distribution/test-function or local-cohomology hits; no match.
- `msearch.py ... loogle`: `CategoryTheory.Adjunction.homEquiv`. Twelve hits on
  generic adjunction Hom bijections and their unit/counit formulas; no compact-support
  or mixed-unit normalization statement.
- `msearch.py ... grep`: `compactSupport.*(scalar|transpose)|scalar.*compactSupport`.
  No Mathlib hits.
- `msearch.py ... leansearch`: "normalized derived tensor restriction adjunction on
  whole inverse coefficient systems mixed reduction unit". Eight generic derived
  adjunction/unit hits; no match to the item's prescribed maps.
- `rg` and the requested node-id grep in `lean/WeilConjectures`: no declaration for
  the item, or a whole-system mixed-unit normalization. `rg` in `lean/Sheaf/Paper`
  located `CompactSupportSystemRealizationNormalization` (finite ground field and
  Frobenius, different statement), the prescribed scalar-system map, the finite
  mixed units, and the varying-ring restriction data. All were read before adding
  the cochain/coordinate interfaces. None states this arbitrary-ground-field item.

No new definition nodes are introduced. No STATEMENT-DISPUTED finding remains.

## Repair of H13

The returned immutable head was cdbce34cf1e3. This repair changes declaration ownership
only; the accepted item mathematics and the main theorem signature are unchanged.

1. `lem-pur-sheaf-ring-derived-coefficient-adjunction.json` is byte-identical to the
   current sheaf-dag copy. It still records NO's general-site theorem
   `SheafOfModules.sheafRingDerivedCoefficientAdjunction` in its original module.
   The seven system-specific declarations formerly in SystemCoefficientAdjunction
   are now in this item's module and its lean.declarations. Their source docstrings
   carry this item's blueprint id. The original general theorem is publicly imported.
2. `def-weil-mixed-reduction-unit.json` is byte-identical to sheaf-dag. It still
   records Q103's six per-level declarations in `Sheaf.Paper.MixedReductionUnit`.
   The seven simultaneous strict-chain and whole-system mixed-unit declarations
   formerly in WholeMixedReductionUnit now belong to this item. They still use the
   recorded finite `sfMixedReductionUnit`, and completion is still the prescribed
   `scalarCompletion`; no normalization equation or construction changed.
3. `lem-weil-system-compact-support-restriction-cocycle.json` is byte-identical to
   sheaf-dag. Q51's general `compactSupportRestrictionCocycle` remains its recorded
   declaration, including cocycle, unit and finite clauses. The eleven fixed-coordinate
   restriction declarations formerly in RealizedSystemCompactSupportRestriction now
   belong to this item and carry its blueprint id. Their proper K-injective equation
   and original open-unit square are unchanged. The general cocycle is publicly imported.

The three former helper files are removed from the delivery sandbox: their declarations
are moved into scoped sections of CompactSupportSystemTransposeNormalization.lean.
The sections preserve the previous elaboration settings without leaking them into
other sections. There are no new nodes or dependency interface replacements. The
item's lean.declarations lists all 32 owned declarations, including its main theorem.
All three restored JSON files are retained in the sandbox byte-for-byte for review;
they produce no dependency-node delta in the delivery.

## Second reading by Q88

This is a second structured pass by the same dispatched worker; no other agents
were started, as required by the brief. The maintainer supplies the independent
review. I reopened the item, the three original dependency records, and the final
consolidated module. For this repair I verified that the original dependency ownership
is restored, all moved declarations are listed under the item, and each moved docstring
has the item blueprint id. The main theorem signature is byte-for-byte unchanged.
I checked the binders and every displayed equation against the correspondence above.
The pass added the explicit source/target whole-system counit squares and the scalar
comparison's isomorphism clause on all ambient H. It also ensured r_B is asserted
invertible on all B-constructible inputs, not only on scalar-extended A-inputs.
Residue-unit API requirements were discharged inside wrappers from hl, rather than
added as assumptions. A compile error from an initially swapped inverse-image mate
orientation was corrected by ordering the two geometric adjunctions B then A.
Section transports in the mixed presentation are explicit and use the existing
coefficientSequenceEvaluationAb_eq; they do not assert faithfulness of derived
evaluation. The fixed comparison b is the prescribed existing system construction,
not a parameter with finite-level constraints. No remaining statement mismatch was
found in this pass.

Validation: the consolidated item module is compiled using scompile.py. Only the expected sorry warnings are allowed. The prescribed deliver2.py
no-push preflight and final delivery are run after this report is complete.

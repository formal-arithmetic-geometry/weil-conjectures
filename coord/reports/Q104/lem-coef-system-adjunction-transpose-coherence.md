## Worker report

Item: `lem-coef-system-adjunction-transpose-coherence`; group Q104, stage 2.
Module: `Sheaf.Paper.SystemAdjunctionTransposeCoherence`.
Main declaration: `WeilConjectures.systemAdjunctionTransposeCoherence`.
Its proof is exactly `by sorry`. All other declarations contain real data or explicit
proposition formulas. No theorem has been proved in this delivery.

The source is the final paragraph of
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`,
together with the accepted node's ordinary-system refinement and six proof steps.
The module docstring identifies that source; the theorem docstring retains all six
steps, including the small ringed sequence site, simultaneous K-flat resolutions,
normalized Hom evaluation, actual mate words, both pastings, counit-compatible
uniqueness, and uncurrying before any inverse limit.

### Hypotheses and objects

- The finite-field datum is `D₀ : FiniteFieldDatum.{t}`. Its prime, finite field,
  algebraic closure and structural algebra are the recorded dependency's data.
  `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D₀.p` give the coefficient prime condition.
- `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]` and
  `[FiniteDimensional (Padic l) E]` give precisely the finite coefficient extension.
  The coefficient rings and quotient maps are the existing
  `Padic.coefficientExtensionRing` and `Padic.coefficientExtensionTransition`.
  These already use the recorded valuation ring and its chosen uniformizer.
  A natural index `n` always means the positive exponent `n + 1`; this includes
  the first coefficient ring and all equality-index reduction maps.
- `X Y : Over (Spec (CommRingCat.of D₀.k))` are the two schemes over k.
  Their three instances state finite type (locally finite type and quasi-compact)
  and separatedness. `f : X ⟶ Y` is a morphism over k with those same properties.
  `compactification : Compactification f.left` supplies the actual open immersion,
  proper morphism and factorization; its ambient scheme is `compactification.Z`.
- Each `W` is restricted by `W = X.left ∨ W = Y.left ∨ W = compactification.Z`.
  `adjunctionSystemSiteCategory` and `adjunctionSystemSite` select the existing
  `W.Etale`/`W.smallEtaleTopology` or `W.ProEt`/`Scheme.ProEt.topology W`.
  The Boolean values false and true denote etale and proetale respectively.
  These helpers select existing sites and do not define another topology.
- `adjunctionSystemRings` is the actual constant sheaf of the finite coefficient
  ring, lifted to `max u (t+1)`; its transition is the constant-sheaf image of the
  actual quotient map, with `RingHom.ulift`. No arbitrary transition is assumed.
  The site retains object universe `t+1` and morphism universe `t`.
- `adjunctionSystemDerived` abbreviates the recorded `SemilinearSections.DS`,
  the ordinary unbounded derived category of modules on the ringed sequence site.
  `Systems`, `systemRing`, `e`, `reduction`, and `Normalized` are the existing
  ordinary-system constructions, not a diagram category of derived objects.
  Reduction is the scalar-adjunction transpose of the actual derived transition.
- `adjunctionSystemData` abbreviates `SemilinearSections.Data`. It carries the
  specified closed structures, canonical scalar models, pure-tensor-normalized
  tensor evaluation, and normalized-input Hom evaluation preserving evaluation.
  The theorem quantifies over EVERY such `A`, rather than choosing a favorable
  calculus. Its extra foundational fields assert properties already belonging to
  these same operations, not extra geometric hypotheses on the theorem's inputs.
- `SystemAdjunctionCoherenceAt` quantifies over `ObjectProperty` and uses its
  existing `FullSubcategory` and inclusion `P.ι`. Thus each adjunction is an actual
  `Adjunction` of functors between full system subcategories. Operations used in
  a formula have their sources and targets in those subcategories by their types;
  no additional closure restriction or boundedness condition is imposed.
- `SemilinearSections.AdjunctionEvaluation` provides the specified left/right
  evaluation isomorphisms and BOTH unit and counit equations. In
  `SystemMateCoherence`, compatibility of `αn` with `α` is the displayed square,
  not a mere family of unrelated finite transformations.

### Conclusions, clause by clause

The main theorem has three conjuncts.

1. On each selected ringed system site, `SystemTensorTransposeCoherence` states:
   (a) evaluation of the actual closed transpose equals the finite transpose,
   using `tensorEvaluation.inv` and `homEvaluation.hom` in their correct directions;
   (b) both inverse identities of the system closed bijection;
   (c) the reduction square for every actual derived-system morphism and every
   `n ≤ m`, using `A.scalar h` and the actual `reduction`;
   (d) the natural square comparing the total tensor of any four flat-term K-flat
   representatives and any two chain maps with the derived tensor map, via the
   existing `tensorModelIso`;
   (e) the corresponding naturality equation for closed transposes under changes
   of both tensor inputs (contravariance in the Hom input is `g.op`).
   The representative square applies in particular to quasi-isomorphisms and
   hence to changes through common resolutions and their localized roofs.
   `A.tensorModels.uncurry_model` fixes tensor evaluation and its transpose on
   those representatives; `A.tensorEvaluationModel` fixes finite evaluation on
   the same representatives and `tensorEvaluationModel_ordinary` fixes it on
   pure tensors. No arbitrary comparison or chain-map choice is substituted.
   The ONLY Hom-evaluation restriction is `hL : Normalized ... A.scalar L`:
   L is the first internal-Hom argument, though it is the second tensor factor.
   Tensor evaluation itself has no normalization or quotient-flatness condition.
2. For every pair of the specified system categories, every full subcategory pair,
   every level and every actual adjunction pair, `SystemMateCoherence` states
   finite evaluation of the right mate `conjugateEquiv a' a α`, both inverse-mate
   identities, reversal of vertical composition, and invariance under the canonical
   `rightAdjointUniq` identifications on BOTH right adjoints. The direction is
   `α : L ⟶ L'` and mate `R' ⟶ R`. The uniqueness identifications are exactly
   Mathlib's counit-compatible ones, not arbitrary isomorphisms.
3. For any six selected full system subcategories, `SystemMatePasting` spells out
   both `mateEquiv_vcomp` and `mateEquiv_hcomp` equations for actual squares and
   composite adjunctions. Thus the equality occurs on systems. Specified actual
   geometric composition identifications are inserted in these squares; replacing
   right adjoints uses the preceding counit-compatible uniqueness equation.

The tensor and transpose clauses quantify over every actual system arrow `h`.
They therefore include tensor evaluation maps and their composites with the
actual units and counits, whenever the displayed objects have the required types.
Functorial evaluation preserves those composites; the tensor-evaluation and
uncurrying equations give exactly their finite constructions. This formulation
requires no new chosen family of maps and makes no finite-level lifting assertion.
All inverse identities and transition equations are in `DS` itself; no equality
is inferred from componentwise equality and no total inverse limit occurs.

### Dependency declarations used

The original statement dependencies are imported at their recorded modules.
The convention node `def-weil-scheme-morphism-properties` has no module and is
rendered using Mathlib's property classes named in its record.

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` (and its public import
  `CoefficientExtension`): the recorded coefficient integers, uniformizer,
  `Padic.coefficientExtensionRing`, and `Padic.coefficientExtensionTransition`.
- `WeilConjectures.Compactification.RefinementCategory`: the existing
  `AlgebraicGeometry.Compactification` and its refinement category.
- `Sheaf.Paper.CoefficientSystemDerivedComparison`: the recorded ordinary strict
  systems and exact evaluation interface, also realized on the sequence site by
  `SheafOfModules.strictSystemSequenceEquivalence` in
  `Sheaf.CategoryTheory.SystemRingedSequenceSite`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory` and
  `HasDerivedCategory`, via the recorded `SemilinearSections.DS` abbreviation.
- `Sheaf.Paper.NormalizedDVRTower`: the recorded finite coefficient conventions;
  normalization of the actual semilinear system is the equivalent adjoint-reduction
  condition `SemilinearSections.Normalized`, already explicitly recorded below.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom` publicly retains
  `CategoryTheory.derivedInternalHomOfUniverses`; that is the generic ringed-site
  construction used by `SemilinearSections.internalHom`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor` retains
  the recorded finite tensor presentation. System tensors and scalar tensors use
  the existing generic closed and K-flat models, not a new tensor operation.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`, used by existing `flatTerms`.
- `Mathlib.AlgebraicGeometry.Sites.Etale` and `.Proetale`: the recorded small sites.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `conjugateEquiv`,
  `mateEquiv_vcomp`, and `mateEquiv_hcomp`.
- `Mathlib.CategoryTheory.Adjunction.Unique`: `Adjunction.rightAdjointUniq`.
- The proof-only ringed-site modules are imported without `public`:
  `SystemRingedSequenceSite`, `KFlatResolutionIndependentCoefficients`,
  `KFlatTotalTensorModel`, and `RingedDerivedClosedSymmetricMonoidal`.
  Their recorded declarations supply exactly the six-step docstring proof plan.

The item's `stmt_deps` additionally cites these TWO ALREADY LANDED nodes,
per brief §5's permission to add landed statement interfaces:
`def-coef-semilinear-system-models` (`Sheaf.Paper.SemilinearSystemModels`,
`Systems`, `DS`, `e`, `reduction`, `Normalized`, `totalTensor`, `tensorModelIso`);
`def-coef-semilinear-derived-calculus` (`Sheaf.Paper.SemilinearDerivedCalculus`,
`Data` and its tensor/Hom evaluation and representative-model fields);
`def-coef-adjunction-evaluation` binds the existing
`WeilConjectures.SemilinearSections.AdjunctionEvaluation` structure in
`Sheaf.Paper.SemilinearDerivedSections`. It supplies the definition-node owner
for the two evaluation isomorphisms and the unit/counit equations. The theorem node
`lem-coef-semilinear-derived-sections` remains only a proof dependency. The public
import of its module exposes the existing structure bound by the new definition
node; no theorem conclusion is used to state the item.

### Edge cases and searches

Checked the first positive exponent, `m = n` (normalization and reduction include
it), zero objects and zero maps, identity transformations, coincident schemes,
the empty scheme and empty full subcategories. Both sites are covered, including
the small proetale universe pair `(t+1,t)`. Coefficient extensions may be ramified;
no quotient-map flatness is assumed. Non-normalized Hom source objects are excluded
only from Hom evaluation, exactly as the node says. Arbitrary unbounded system
objects remain allowed elsewhere. There is no constructibility, boundedness,
finite Tor amplitude, or independently postulated lifting hypothesis.

Searches (recorded by msearch.py in this sandbox's searches.jsonl):

- LeanFinder: “Mates of derived strict coefficient system adjunctions commute with
  evaluation and closed tensor Hom transposes independently of K-flat representatives”.
  Eight hits: ordinary mates, Frobenius mate, and tensor unit/counit identities;
  none states the complete system and representative assertion.
- Loogle: `CategoryTheory.conjugateEquiv, CategoryTheory.mateEquiv_vcomp,
  CategoryTheory.Adjunction.rightAdjointUniq`; zero combined hits. The individual
  Mathlib declarations were read directly and are used, rather than redeclared.
- msearch grep: `conjugateEquiv|mateEquiv_vcomp|transpose` in
  `CategoryTheory/Adjunction`; twelve ingredient hits in Mates, Unique and
  CompositionIso, no complete match.
- LeanSearch: “Derived coefficient system mates and closed tensor Hom transposes
  commute with evaluation and are independent of K flat representatives”;
  eight hits about ordinary module currying, dual tensor and evaluations;
  none about derived coefficient systems.
- `rg` in `lean/WeilConjectures` found existing general projection-mate operations,
  not this statement; `grep -rn` for the exact node id there found none.
  `rg` in `lean/Sheaf`, Mathlib, and `dag/lean_names_upstream.json` found no
  `systemAdjunctionTransposeCoherence`, `SystemMateCoherence`,
  `SystemAdjunctionPastingAt`, `SystemTensorTransposeCoherence`, or
  `adjunctionSystemRings` declaration. The relevant SemilinearDerivedSections
  theorem `evaluation_mate` is only the categorical evaluation ingredient;
  its full signature and docstring were read and reused through its interface.

No statement correction, disputed statement, or dependency-module repair.
One new definition-node binding is described below. The inherited mathematical
statement, proof and proof dependencies are unchanged.

## Second reading by Q104

Reopened the accepted node and the entire final module and compared the objects,
binders and all three conjuncts. This is a separate reading by the dispatched
worker; the dispatch expressly forbids starting another agent, and the maintainer
will perform the independent review.

The reading caught an existential quantifier for the calculus in an intermediate
draft. Replaced it by `∀ A : adjunctionSystemData ...`: the assertion must hold
for the specified comparisons, not merely for some favorable choice. Added the
two existing interface nodes and the new definition owner to `stmt_deps` and public imports to expose every
non-Mathlib notion in the signature. Made universe arguments explicit in the
coherence formulas, preserving separate site universes. Wrapped all lines to the
100-character limit. No change to the accepted natural-language statement was needed.

Checked the mate orientation against the actual definition of `conjugateEquiv`
(`a'` first, `a` second), the order of both pasted squares against Mathlib, and
both right-adjoint uniqueness isomorphisms against their counit equation.
Checked the Hom evaluation direction and the normalization of L against
`Data.homEvaluation_evaluation`. Checked that all map comparisons are equations
in the actual ordinary derived-system category and that representative changes
use the existing canonical model comparisons. The supplied closure assumptions
are expressed by operations and adjunctions whose typed sources and targets
belong to the selected full subcategories. No extra geometric hypothesis or
finite-level lifting conclusion was found.


## New nodes

`def-coef-adjunction-evaluation` gives definition-node ownership to the existing
plain structure `WeilConjectures.SemilinearSections.AdjunctionEvaluation` in
`Sheaf.Paper.SemilinearDerivedSections`, lines 93–108. This is an `existing: true`
binding, as required by brief-stage2 §1(A) and §5 when a project definition already
exists without its own definition node. It adds no Lean declaration or duplicate
module. The source is the final paragraph of the current blueprint proof of
`prop-coef-integral-exceptional-adjoint`, and the existing declaration cites Zheng
Lemma 4.10 and Mathlib's adjunction mates. Its only statement dependency is the
existing adjunction/mate definition node `def-weil-pbc-adjunction-mate`.

Hypotheses: the four categories, evaluation functors E and F, system adjunction
`adj : L ⊣ R` and level adjunction `level : l ⊣ r` are exactly the structure's
parameters (all type/category variables explicitly bound by its module context).
The natural isomorphism λ is field `left : L ⋙ F ≅ E ⋙ l`; ρ is field
`right : R ⋙ E ≅ F ⋙ r`. The unit equation is field `unit`, with composition in
Lean's left-to-right order. The counit equation is field `counit`, using
`left.inv.app (R.obj B)` on its right-hand side. These are all four fields; the
node asserts no existence or theorem. Empty categories, identity evaluation,
identity adjunctions, and nonfaithful evaluations are allowed. No equality of
arbitrary morphisms is inferred from evaluation.

New searches actually run during repair: LeanSearch query “Evaluation comparisons
of adjoint functors preserving the unit and counit as natural isomorphisms” returned
eight ordinary adjunction ingredients; LeanFinder query “Adjunction evaluation
comparison isomorphisms compatible with both unit and counit” returned eight mate
and transpose ingredients; msearch grep
`AdjunctionEvaluation|evaluation.*adjunction|adjunction.*evaluation` in
`CategoryTheory/Adjunction` returned five hits about adjoints to evaluation, a
different notion. `rg` in Mathlib, WeilConjectures and Sheaf located precisely the
existing Sheaf structure. `rg` in DAG nodes found theorem consumers and the old
theorem owner, with no definition-node owner; blueprint_refs search returned zero
blueprint matches. The node records the raw search-log results, including names
and digests, and the direct source/DAG search result.

## Repair of return L (head 79ff73e782d4)

H2: removed `lem-coef-semilinear-derived-sections` from the added statement
interfaces and cited `def-coef-adjunction-evaluation` instead. The new definition
node owns the existing structure through its exact published module and declaration
binding, with its signature copied verbatim. The theorem stays in `proof_deps`.
This repairs the ownership issue without redeclaring an existing notion. The
saved packet's initial dry run passed mechanically at commit `2c99afd7337`;
that did not resolve the independent review finding, so the binding and report
were repaired before the final dry run and delivery.

The shared main node still has no Lean record; its statement, proof, proof_deps,
source and every field except the authorized `lean` and `stmt_deps` match this
packet. The source of `Sheaf.Paper.SemilinearDerivedSections` was also checked
through `scompile.py --source`; the four-field structure is still the published
one. The wrapper rebases the delivery onto current main.

### Second reading of the repair by Q104

Reopened the new node, the four-field structure (including its docstring and full
signature), the item node and `SystemMateCoherence`. Both structure parameters
`A` and `A'` in the latter use precisely the new node's bound declaration. The
unit formula and counit formula in the new node match the fields in direction,
components and inverses. The natural isomorphisms, and not just their component
maps, are retained. The structure has no existence assertion and no proof is
needed to construct its type. The corrected DAG statement path reaches this
definition rather than the semilinear-derived-sections theorem conclusion.
Checked that the new definition node's sole dependency is an existing Mathlib
leaf, so the added path introduces no dependency cycle. The item's other
hypotheses and clauses retain the independently checked formulation. No second
agent was started, as the dispatch forbids it.

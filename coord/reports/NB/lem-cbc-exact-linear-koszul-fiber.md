## Worker report

The item is stated by `CategoryTheory.exists_exactLinear_signedKoszulFibre` in
`Sheaf.CategoryTheory.ExactLinearKoszulFibre`. Its only proof is `sorry`. The helper
structure `SignedKoszulFibreComparison`, specialized by the transparent alias
`ExactLinearSignedKoszulFibreComparison`, packages the fully specified conclusion;
the theorem asserts it is inhabited for every pair of normalized models. Its fields
are conclusion data and equations, not extra assumptions.
The new definition module `Sheaf.CategoryTheory.SignedKoszulCompletionModel` contains
real constructions of the negative two-term Koszul factors, their ordered total tensors,
and the canonical pure-tensor inclusions. Its model structures specify the remaining
product and fibre by coordinates and universal properties. No definition has postponed data,
and no helper theorem or axiom was introduced. The item statement is unchanged.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Two small ringed sites with commutative sheaves | `C : Type u`, `D : Type v`, separate `SmallCategory` instances, topologies `J,L`, `R : Sheaf J CommRingCat.{u}`, `S : Sheaf L CommRingCat.{v}` |
| Commutative A acting through global sections | `A : Type z`, `[CommRing A]`, ring homomorphisms `ρR,ρS` to `RingCat.sectionsSubring` |
| Module-sheaf categories | Existing `ringedSiteModules`, transparently Mathlib `SheafOfModules` |
| F additive and exact | `[F.Additive]`, `[PreservesFiniteLimits F]`, `[PreservesFiniteColimits F]` |
| F(a f)=a F(f) for all a and maps | `hlinear`, with every object, scalar and morphism quantified; `ringedKoszulCoefficientSMul` transparently uses the recorded global-sections Hom-module action |
| Canonical countable-product comparison invertible | `hproduct : ∀ M : ℕ → ..., IsIso (piComparison F M)`; `piComparison` is Mathlib's projection-characterized comparison |
| Exact countable products on both sides | Separate `[HasCountableProducts ...]` and `[CountableAB4Star ...]`; the first supplies the products whose exactness is asserted by the second |
| Any finite ordered list, including r=0 | `r : ℕ`, `a : Fin r → A`, with no positivity hypothesis |
| Q_m in degrees [-r,0] with a_i^m | `ringedNegativeKoszulFactor` uses `HomologicalComplex.double` at `(-1,0)` and exponent `m+1`; `ringedNegativeKoszul` tensors factors recursively in increasing Fin order, using `ringedKoszulTensor` and its recorded total tensor; index `m : ℕ` enumerates precisely the positive exponents |
| Specified transition, a_i in degree -1 and identity in degree 0 | `step_coordinates` is diagonal with scalar `∏ i ∈ I, a i`, exactly the tensor of these factor maps |
| T_m(C)=C tensor Q_m | `ringedNegativeKoszulTensor`, literally the existing total tensor bifunctor with the constructed Q_m |
| Canonical finite expansion, same factor order and signs | `coordinates`, `differential`, `map_coordinates`; `RingedSignedKoszulCompletionModel.normalization` pins inverse coordinate inclusions to `ringedNegativeKoszulSummand`. That map uses actual tensor inclusions, inverse unitors, and the recursively constructed pure tensors of ones. In particular there is no freedom to replace the coordinates or the unit by a sign twist. |
| B=product of T_m | `product`, `projection`, `isProduct : IsLimit (Fan.mk ...)`; a product in complexes has the indicated termwise product and its projection-defined differential |
| Transition shift | `shift`, `shift_projection` |
| H^q=B^q direct sum B^(q-1) | `fibreCoordinates` |
| d(x,y)=(dx,(1-s)x-dy) | `fibre_differential`, a literal binary-biproduct matrix; the only transport is q=(q+1)-1 |
| Unit c maps to ((c tensor 1)_m,0) | `inclusion_coordinates`, pure-tensor `normalization`, `diagonal_projection`, `unit_coordinates` |
| Natural chain isomorphism h | Existential `h : MR.model.fibre ⋙ F.mapHomologicalComplex ... ≅ ... ⋙ MS.model.fibre` |
| Canonical finite-biproduct, countable-product and binary-biproduct comparisons | `alpha` equation specifies each finite projection as F of that projection; `beta` equation specifies every countable projection; the two equations for `h` specify precisely its first and second fibre projections. These characterize the comparisons uniquely. |
| h F(eta)=eta | `unit_compatibility`, equality of actual chain maps |
| Defined models, no assumed choice of cone | Both model types are asserted `Nonempty`, and the comparison is then asserted for every such normalized model; a model is fully characterized by its finite tensor inclusions, universal product and exact signed fibre coordinates. No arbitrary cone morphism is used or chosen. |
| Descent to ordinary unbounded derived categories | The chosen `HasDerivedCategory.{wR/wS}` instances and existing `ringedSiteDerived`; functors `HR,HS`, natural factorization isomorphisms `eR,eS`, units `etaR,etaS` and their displayed localization equations; `F.mapDerivedCategory` is the existing exact-functor descent. The factorization isomorphisms also imply preservation of quasi-isomorphisms. |
| The comparison descends, with same unit | `hd` and its representative equation with `F.mapDerivedCategoryFactors`, followed by the derived-unit equality for every derived object |
| Invertibility of source unit implies target unit invertibility | `preserves_unit_isIso` quantifies over every `X : ringedSiteDerived R` |

All universes are explicitly bound. The site/coefficient universes on the two sides and
the two localization morphism universes are independent. There are no file-local instances,
notations, private definitions, `let` or `show ... from` in the theorem signature. The `letI`
in definitions only installs existing tensor, Hom-module and finite-biproduct structures.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the recorded general-site module category.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and its total-complex docstring; used through the existing `ringedKoszulTensor`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`, `DerivedCategory`, `DerivedCategory.Q`.
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`, and their exactness hypotheses.
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`: `CategoryTheory.Functor.Additive`.
- `Mathlib.CategoryTheory.Limits.Shapes.Products` and `Shapes.Countable`: product objects, projections, `piComparison`, `HasCountableProducts`.
- `Sheaf.CategoryTheory.RingedKoszulSystem`: `ringedKoszulScalar`, `ringedKoszulTensor`; the previously recorded positive/dual system is reused for these operations, not silently identified with the newly specified negative tensor system.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule`: `SheafOfModules.homModule`, the coefficient scalar action. The wrapper explicitly supplies this instance so synthesis does not search through unrelated sheaf structures.
- The already stated proof dependencies are imported through these modules and `Mathlib.CategoryTheory.Localization.Predicate` (`Localization.liftNatIso`, `natTrans_ext` infrastructure). `lem-sbc-koszul-fibre-linear-descent` has no recorded Lean declaration; it is cited in the complete proof plan, not replaced by a new assumption or an unstated Lean helper.

Sources read: the entire item's statement and nine proof steps; every statement-dependency
node and its full recorded declaration/docstring; the current blueprint proof of
`lem-cbc-completed-extension-zero-comparison`; Stacks `algebraization.tex`,
`lemma-derived-completion-koszul` (0A0E), including its proof and the positive/negative
Koszul distinction. This item's exact-linear refinement is explicitly agent-written in
its source record, so the matrix comparison follows its nine-step proof, rather than
claiming that 0A0E states that additional functor comparison.

Edge cases checked before and after writing:

- r=0: `Fin 0` has the single subset empty; the negative tensor is the ring complex,
  the coordinate shift is q+0, the transition empty product is one, and the unit is the diagonal.
- r=1: on I={0}, the coefficient is (-1)^(q+1) a_0^(m+1); the transition is a_0.
- r=2: the I={0,1} boundary has opposite signs on erasing 0 and 1, as does the ordered total tensor.
- Zero scalars, unit scalars, zero rings/modules, empty site: no division, nontriviality,
  nonempty-site or regular-sequence hypothesis appears. All identity/zero expressions remain typed.
- Arbitrarily negative and positive cochain degrees: the sign is parity of the integer
  q+|I|, not a natural truncation; degree equalities are checked before equality transport.
- The fibre square cancels the two cross terms because shift is a chain map; its lower
  diagonal is -d. The second coordinate of the unit is exactly zero.
- Unbounded complexes: no boundedness or infinite-coproduct preservation assumption on F;
  the finite tensor and exact countable-product hypotheses are exactly those in the node.

Searches: prescribed `msearch.py` LeanFinder, Loogle, LeanSearch and Mathlib grep queries
were run. The exact outputs for the new notion are in its `mathlib_searches`. The query
for an exact linear product-preserving Koszul comparison returned Dold--Kan comparisons;
`Functor.mapBiproduct, Functor.piComparison, CochainComplex` had no Loogle hit, and
`Koszul|koszul|signedFibre` in Mathlib Algebra/Homology found only a future-work comment
in LocalCohomology. Direct `rg` searches covered both `lean/WeilConjectures` and
`lean/Sheaf`; the item id has no upstream declaration. `tools/blueprint_refs.py search
"signed Koszul"` returned zero blueprint definitions. Relevant existing positive
Koszul systems, generic signed Ab-valued fibres and global-section actions were read
and reused where applicable; none supplies this negative-factor, tensor-normalized model.

No statement correction, dependency-interface repair, or statement dispute is needed.

## New nodes

`def-cbc-signed-koszul-completion-model` introduces the explicit normalized negative Koszul
tensor/product/fibre model needed to type this item's comparison. It is in the item's
chapter and unit, with the correct blueprint ancestor and via edge. Its source is the
item's explicit signed-model construction and Stacks 0A0E. The actual factors and pure
tensor inclusions are definitions with real data; the product and fibre are specified
by universal properties and complete differential, map and unit equations. Its generic
coordinate structure is only an implementation helper; its primary ringed specialization
uses exactly the recorded global-section Hom action. The three required search kinds,
project/DAG grep and blueprint search are recorded with their exact results. The existing
positive-factor/dual tower has a different strict chain model and does not give these
negative-factor pure-tensor normalizations or the signed fibre, so it cannot serve as an
existing match.

## Second reading by NB

The dispatcher explicitly forbids starting other agents and assigns the independent
reading to the maintainer. No independent reader is claimed here. The worker's own final
re-reading checked the node and the two modules together: all hypotheses and clauses are
matched in the table above. The main subtlety found during that reading was that arbitrary
finite-coordinate isomorphisms would not specify the actual unit. It was repaired by the
explicit pure-tensor basis, summand inclusions, and `normalization` field. The source and
target use separate universes; the negative degrees and all parity signs were checked.
The independent maintainer review remains the independent reading of this delivery.

Compilation design: the comparison equations are checked over abstract complexes, and
the transparent ringed alias specializes them to the actual constructed sheaf tensors.
This avoids repeatedly unfolding the tensor implementation during elaboration; the
definitions remain unfoldable and no timeout limit is raised.

Validation: both supplied modules compile through `scompile.py` within the unchanged
60-second per-file limit. The final compile performed by `deliver2.py --no-push` was
clean. Its first preflight found only signature-record delimiters: the records included
the terminating `:=`/`where`, while the gate stores the preceding signature. Those
record strings were corrected to the exact signature format required by the gate.

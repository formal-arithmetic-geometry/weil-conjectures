## Worker report

Repair of the maintainer return on immutable head `40835f0780d5`.
The retained packet initially passed `deliver2.py --no-push` (dry-run commit
`22f5ef8c02`). Its mathematical self-check nevertheless confirmed the return:
a functor with the right source and target is not necessarily direct image.
The revised module is `Sheaf.SecSmoothPurity.ClosedUnitAllStages`.
Its sole postponed theorem is `WeilConjectures.closedUnitAllStages`.
The node's natural statement and all its other non-`lean` fields are unchanged.

The theorem now asserts existence of presentations of the restricted direct images,
then asserts full faithfulness and the unit statements for **every** such presentation.
This universal assertion is about functors constrained to the recorded direct image;
it is not a claim about arbitrary functors between the coefficient categories.
The two helper structures just package functors and their comparison squares.
They do not define a new coefficient category, replace a dependency, or choose a
functor from an undetermined existence assertion. Their data contain no `sorry`.
In particular, existence of the restrictions, and hence their constructibility
preservation, is a conclusion, not an added hypothesis.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node/source phrase | Lean rendering |
| --- | --- |
| The base field k and the coefficient convention ell different from char k | `(k : Type u) [Field k]`, `(l : ℕ) [Fact l.Prime]`, `(hℓ : IsUnit (l : k))` |
| Z and X are k-schemes | `{Z X : Scheme.{u}}`, `[Z.Over (Spec (.of k))]` and `[X.Over (Spec (.of k))]` |
| Separated k-schemes | `IsSeparated` of each structure morphism |
| Finite type over k | `LocallyOfFiniteType` and `QuasiCompact` of each structure morphism, the recorded conjunction defining finite type |
| A closed immersion i:Z to X | `(i : Z ⟶ X) [i.IsOver (Spec (.of k))] [IsClosedImmersion i]`; the over-instance spells out that this is a morphism of the stated k-schemes |
| A finite coefficient extension E/Q_l | The quantified `(E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`, in the family of restrictions and the assertions; every fixed E is included |
| Every finite stage A_(E,n), n at least 1 | `(n : ℕ) (hn : 1 ≤ n)`; the coefficient ring is `Padic.coefficientExtensionRing l E n` |
| The finite constructible categories | `(Scheme.intrinsicFiniteTorsionConstructible l E n hn Z).FullSubcategory` and its X analogue |
| Finite i_* is the recorded Ri_* along i | `ClosedDirectImageCoefficientStages.finiteComparison`: the restricted functor followed by the full-subcategory inclusion is naturally isomorphic to the source inclusion followed by `Scheme.proEtaleConstantDerivedDirectImage i (Padic.coefficientExtensionRing l E n)` |
| Integral D^b_c(-,O_E) | `sfIntegralConstructibleCategory l E Z` and `sfIntegralConstructibleCategory l E X`; these include derived completeness, constructible reductions and one uniform interval |
| Integral i_* is the specified direct image | `integralComparison`: inclusion after `integralStar` is naturally isomorphic to inclusion followed by `sfCompletedDerivedDirectImage l E i`. The node's proof identifies this canonical completed image with its projection-normalized strict finite-image tower. This is an identification of the recorded operations, not a new arbitrary tower or cone. |
| Rational D^b_c(-,E) | The exact raw categories `sfRationalConstructibleCategory l E Z` and its X analogue; no Karoubi completion |
| Rational i_* is rationalization of integral i_* | `rationalComparison` identifies localization followed by `rationalStar` with `integralStar` followed by localization. `rationalAdditive` and `rationalLinear` fix the localized scalar factor; together these specify the image of every sum of pure tensors, not just integral maps. |
| Algebraically closed coefficients | `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]` and the exact `generalAlgebraicallyClosedConstructibleCategory` on each scheme |
| Common-stage i_* comes from the finite E-stage direct images | `ClosedDirectImageStages.inclusionComparison`, a natural isomorphism on every `GeneralAlgebraicallyClosedCoefficients.inclusion E`, between that inclusion followed by `algebraicallyClosedStar` and the rational direct image at `Coefficient.{u} l Ω E` followed by the target inclusion. The `scalarComparison` fields compare the rational images with the recorded scalar transitions, `scalarCoherence` is their two-extension cocycle, and `inclusionCoherence` intertwines these comparisons with the canonical `stageSystem.transIso` arrows. Thus the image of every common-stage representative, including the changes of its endpoints, is constrained. |
| These restricted direct images are defined on the stated categories | The first conclusion, `Nonempty (ClosedDirectImageStages l Ω i)`, supplies all the restrictions and comparison squares. There is no preservation hypothesis and no chosen definition made from this existence assertion. |
| i_* is fully faithful at all four stages | For every presentation `S`, the conclusion has `.Full ∧ .Faithful` for `(S.coefficient E).finiteStar n hn`, `.integralStar`, `.rationalStar`, and `S.algebraicallyClosedStar`. Finite and integral comparisons tie these presentations to i; the two subsequent squares supply their scalar realizations. |
| Whenever i_* has a right adjoint on a constructible stage | Each of the four clauses quantifies over a functor `G` in the reverse direction and an actual adjunction `adj : F ⊣ G`. It asserts no general existence of that G at integral, rational or algebraically closed coefficients. |
| The unit Q to Ri^! i_* Q is an isomorphism for every constructible Q | In each such clause the conclusion is `∀ Q, IsIso (adj.unit.app Q)`. The former `.Full` and `.Faithful` premises are removed from every unit clause. |
| At finite coefficients a right adjoint exists on the ambient categories | For every `E`, positive `n`, the conclusion contains `∃ G : Scheme.proEtaleDerivedCategory X A ⥤ Scheme.proEtaleDerivedCategory Z A, ∃ adj : Scheme.proEtaleConstantDerivedDirectImage i A ⊣ G, ∀ Q, IsIso (adj.unit.app Q)`, with `A = Padic.coefficientExtensionRing l E n`. This is an existence claim for the actual recorded ambient functor. The Q is completely ambient, with no constructibility or boundedness condition. |
| i_* = Ri_* = Ri_! | This is the source's identification of the operation being restricted. The finite/integral comparisons use Ri_*; the proof docstring explains closed exactness and the identity/proper compactification identifying it with i_* and Ri_!, and the inherited scalar versions. No new compactification or arbitrary functor is supplied as an assumption. |

The presentation quantifier is needed only because restrictions and derived functors
can be represented by naturally isomorphic functors. It does not add a geometric
hypothesis: the first conjunct asserts that presentations exist, and the second
asserts the results for all presentations of these same operations. Uniform
quantification over finite E also provides the stages needed to state the
algebraically closed coefficient clause.

Dependency declarations read and used:

- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory` (the completed coefficient category, every
  constructible reduction and its uniform amplitude).
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`, reexported by the above:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible` and its full
  subcategory inclusions.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, and its inherited localized-ring linear
  category. The full signature and tensor-Hom description were read.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`,
  `GeneralAlgebraicallyClosedCoefficients.inclusion`, and
  `AlgebraicallyClosedCoefficients.Index` / `Coefficient`. The inclusion parameters
  l, Ω and Y are implicit, so the delivered signature uses named arguments.
- `Sheaf.Paper.SfDerivedDirectImage`: `sfCompletedDerivedDirectImage`, its
  completed coefficient structural map, and `SfIntegralDirectImage` / its
  `sfDirectImageReductionComparison` for the tower identification explained in the
  proof. The finite ambient map is the reexported
  `AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage` from
  `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`.
- The recorded exceptional definition was read in
  `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`: it defines the
  constructible exceptional functor and does not assert an unrestricted ambient
  adjunction. The theorem's conditional unit clauses quantify over actual right
  adjoints. The unused import of this module has therefore been removed.
- The recorded `prop-sf-closed-immersion-unit` declarations were read via
  `scompile.py --source WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek`.
  Its ambient statement is reexported from `Derived.ClosedImmersion`; the
  constructible statement is
  `AlgebraicGeometry.ProEtale.isIso_rightDerivedUpperShriekHomEquiv_id_of_isClosedImmersion`.
  The new ambient conjunct states its existence/unit content in the intrinsic
  constant-ring coordinates already used by the finite direct-image dependency.
- Mathlib: `AlgebraicGeometry.IsClosedImmersion`, `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact`. Their recorded class signatures were
  read. `Morphisms.Separated` replaces the unused `Morphisms.Proper` import.

Edge cases checked before finalizing:

- n=1 is allowed in every finite clause; n=0 is excluded by exactly `1 ≤ n`.
  Integral reduction indexing already uses n+1 inside the recorded definition.
- Empty schemes and zero objects remain allowed. No choice of a nonempty
  stratification, nonzero object or dimension is imposed on the statement.
- Identity closed immersions remain allowed. In the nonzero point example from
  the return, a constant functor cannot satisfy `finiteComparison` or
  `integralComparison` with the identity ambient direct image: it would have to
  be naturally isomorphic to the identity. The previous counterexample is thus
  excluded by an actual map identification, not by assuming faithfulness.
- The rational comparison is additive and linear over the localized scalar ring;
  it cannot silently change the scalar factor while agreeing on integral names.
- Every finite coefficient field is included in the common-stage comparison,
  including the bottom field and identity coefficient maps. Ω has its independent
  universe v; finite fields use the recorded `Coefficient.{u}` small model.
- At higher stages no right adjoint is presumed to exist. At finite level its
  ambient existence is explicitly asserted, with the unit at arbitrary ambient Q.
- The helper structures have real functor/comparison data. The only `sorry` is
  the named main theorem. No definition chooses data from a bare `Nonempty`.

Searches retained and repeated for this repair:

- Original `msearch.py ... leanfinder "closed immersion direct image fully
  faithful at every coefficient stage"`: generic pushforward infrastructure,
  no exact proposition in the four recorded categories.
- Repeated `msearch.py Q96 prop-sf-closed-unit-all-stages leanfinder
  "canonical closed immersion direct image fully faithful on constructible
  finite integral rational common stage coefficients"`: eight hits, including
  closed-immersion integrality, proper affine global sections and constructible
  subsets; no exact four-stage proposition.
- Original Loogle search for `Functor.Full`, `Functor.Faithful` and the generic
  adjunction unit theorem found categorical infrastructure only. Repair query
  `CategoryTheory.Functor.Linear, CategoryTheory.Functor.Full,
  CategoryTheory.Adjunction.unit_isIso_of_L_fully_faithful` returned zero hits.
- `msearch.py ... grep "closed immersion.*fully faithful|isIso_unit_app"
  CategoryTheory`: five generic adjunction/reflective-subcategory hits; no
  geometric four-stage declaration.
- `rg` in the read-only source and project found
  `WeilConjectures/SixFunctors/ClosedImmersionStages.lean`. Its full signatures
  were read. Its integral category is the old derived-complete étale category,
  its rational bounded category has a Karoubi envelope, and its algebraically
  closed category is the adic-sheaf category rather than the recorded pair
  category. It cannot be recorded as an exact existing match for this node.
- `rg -n 'ClosedDirectImageCoefficientStages|ClosedDirectImageStages|closedUnitAllStages'`
  over the read-only project `lean/Sheaf` and upstream `WeilConjectures` found no
  conflicting declaration. The finite and integral direct-image constructions
  already exist and are reused via comparison squares.

No natural-statement fault or `STATEMENT-DISPUTED` remains. No new DAG node and
no dependency-node repair is needed: the structures only package the restriction
and realization assertions of this very proposition.

## Second reading by Q96

This is the worker's own second reading, as required for this dispatcher workflow;
no separate agent was started. I reopened the current node and the final module.

1. Base and geometry: the field, invertible prime, two over-structures,
   separatedness and finite type are the first binders of `closedUnitAllStages`;
   i is a bound closed immersion and `[i.IsOver (Spec (.of k))]` makes it
   a morphism of those k-schemes, as in the source. No scheme, coefficient, or object is inferred
   by an auto-bound implicit. Universes u and v are explicitly declared.
2. Finite clause: `finiteComparison` mentions the actual
   `proEtaleConstantDerivedDirectImage i`, and has source/target the exact
   intrinsic finite constructible full subcategories. The result quantifies over
   every positive exponent and asserts both Full and Faithful. This repairs the
   first H3 point for the finite stage.
3. Integral clause: `integralComparison` mentions the actual
   `sfCompletedDerivedDirectImage l E i`, with inclusions of exactly the recorded
   integral constructible subcategories. The node's projection-normalized tower
   comparison identifies this with its integral direct image. Full and Faithful
   are conclusions. This repairs the first H3 point at integral coefficients.
4. Rational clause: `rationalComparison`, additivity and localized linearity tie
   its functor to scalar localization of that integral functor, on tensor Hom
   groups as well as objects. Full and Faithful are conclusions. There is no
   Karoubi category. This repairs the rational part of the first H3 point.
5. Algebraically closed clause: `inclusionComparison` is a natural isomorphism
   for every finite-field inclusion and that field's rational direct image.
   The added `scalarCoherence` and `inclusionCoherence` equations constrain
   its action on the canonical change-of-stage arrows as well as on finite-stage
   generators and their morphisms. Full and Faithful are conclusions. Ω is general
   and its universe remains independent. This repairs the last coefficient part
   of the first H3 point.
6. Existence/preservation: `Nonempty (ClosedDirectImageStages l Ω i)` precedes
   the universal assertion. Therefore none of the comparison squares is an
   extra existence hypothesis on i. The result applies to every presentation
   constrained to i, not just to some arbitrarily selected fully faithful functor.
7. Units: all four restricted clauses have only G and an adjunction as their
   additional inputs. Each concludes `∀ Q, IsIso (adj.unit.app Q)` with no Full
   or Faithful premise. This addresses the advisory explicitly.
8. Finite ambient clause: it independently quantifies over every positive n and
   asserts `∃ G, ∃ adj : proEtaleConstantDerivedDirectImage i A ⊣ G`, followed by
   invertibility at every ambient Q. Its categories are ambient, not full
   constructible subcategories. This repairs the second H3 point.
9. Imports: `SfDerivedDirectImage` is now used in actual type expressions;
   `SfFiniteExceptionalInverseImage` and `Morphisms.Proper` are removed;
   `Morphisms.Separated` supplies the separatedness predicate. The remaining
   imports supply declarations in the statement/structure signatures. This
   addresses H9.
10. The preceding table explicitly matches every hypothesis, coefficient stage,
    full-faithfulness clause, conditional unit, and finite ambient existence/unit
    clause. Unlike the returned report, it checks the equations that connect
    functors to i, rather than interpreting unconstrained binder names as maps.
    This addresses H11. Only the Lean formalization and its record/report change;
    the node statement itself needs no correction.

Validation is performed with the prescribed `scompile.py` and `deliver2.py`
wrappers; no direct Git mutation or live-library build is performed.

Final file verification: `scompile.py Q96 prop-sf-closed-unit-all-stages
<absolute sandbox module path>` completed successfully for both the sandbox check
and the library module, with no errors or warnings. The earlier library-file check took
17.6 seconds; the final coherence-enhanced file is checked again below. The first repair compile identified implicit inclusion arguments;
the final module supplies l, Ω and Y explicitly by name. A local metadata check
confirmed that only `lean` differs from the current shared node, the recorded
signature is verbatim, there is exactly one `sorry`, and every Lean line is at
most 100 characters.

Additional common-stage audit: merely listing natural isomorphisms on separate
finite inclusions does not express their compatibility with changes of stage.
The final record therefore also retains `scalarComparison`, its exact associator
cocycle `scalarCoherence`, and `inclusionCoherence`. The latter equation says that
applying the common-stage image to `transIso_Z(h)`, then the E-inclusion comparison,
is the same as the L-inclusion comparison followed by the inverse scalar comparison
and `transIso_X(h)`. Together with naturality this prescribes the image of an arrow
represented at L by the L-stage rational image, conjugated by the endpoint scalar
comparisons. The cocycle makes this independent of enlargement of L. These are
compatibility properties in the conclusion's existence assertion, not assumptions
on the closed immersion. Their formulas use the already recorded `stageSystem`,
its associators, and the canonical upstream `StageSystem.transIso`; no second
pair category, colimit, or change-of-stage arrow is introduced.

The final coherence-enhanced file passed `scompile.py`: sandbox check 24.8 s,
library-file check 57.1 s, no errors or warnings. Both checks used the unchanged
60-second per-file limit. The final signature agrees verbatim with `lean.statement`. The explicit
k-morphism instance spells out the source phrase "of k-schemes"; it imposes
no new geometric condition beyond that source convention.

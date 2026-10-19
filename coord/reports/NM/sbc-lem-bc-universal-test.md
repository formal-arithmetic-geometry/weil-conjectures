## Worker report

The module `Sheaf.AlgebraicGeometry.UniversalBaseChangeFailureDatum` states
`AlgebraicGeometry.Etale.exists_universalBaseChangeFailure_cyclic_datum`, with its whole
proof `sorry`. No definition, helper theorem, new node, or statement correction is added.
The original statement and every other node field are retained.

The source was read in the local Stacks source, `etale-cohomology.tex`,
`lemma-base-change-does-not-hold` (Tag 0F08), and in the blueprint node
`sec-smooth-base-change/sk-lem-universal-datum/sbc-lem-bc-universal-test.md`.
The DAG's already repaired horizontal `h` orientation is used: `h : Y ⟶ X'`,
whereas `e : Y ⟶ Spec K`. The statement imposes no smoothness, relative dimension,
finiteness, or affineness hypothesis on the original morphism.

Clause-by-clause rendering:

- The schemes and morphism are `{X S : Scheme.{u}} (f : X ⟶ S)`.
- The positive integer invertible on S is `(n : ℕ) (hn : 0 < n)` and
  `(hinv : IsUnit (n : Γ(S, ⊤)))`. Positivity lets natural numbers encode exactly
  the coefficient domain of the dependency. Naturals also index the nonnegative degrees.
- The degree is `(q : ℕ) (hq : 1 ≤ q)`.
- Universal validity for every nonnegative degree at most q-1 is precisely
  `CumulativeUniversalBaseChangeProperty f n hn hinv (q - 1)`.
  Its definition expands to the bounded forall of the existing
  `UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n))`.
- Failure universally in degree q is
  `¬ UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (q : ℤ)`.
  Thus the coefficient ring in the hypothesis is fixed by n, rather than arbitrary.
- The first base-change diagram is the existential data `S' X' a b f'` and
  `ChosenCartesianSquare b f' f a`. Its inherited commutative-square equation is
  `b ≫ f = f' ≫ a`; its identification with the pullback respects both projections.
- The affine and integral clauses are the existential witnesses `IsAffine S'` and
  `IsIntegral S'`.
- Normality is `∀ x : S', IsIntegrallyClosed (S'.presheaf.stalk x)`.
  Each stalk is already a domain because S' is integral. On affine opens, these
  stalks are the prime localizations of the affine coordinate ring. This is exactly
  the dependency's normal-ring condition, with no extra global normality notion.
- Algebraic closedness of the function field is `IsAlgClosed S'.functionField`.
  This uses the dependency's arbitrary integral-scheme clause, not a curve hypothesis
  or the component-product function field.
- The algebraically closed field is `(K : Type u) (_ : Field K) (_ : IsAlgClosed K)`.
- Its extension of the function field is `(i : S'.functionField ⟶ CommRingCat.of K)`.
  Such a map of fields is injective. The induced map to S' is explicitly
  `Spec.map i ≫ S'.fromSpecStalk (genericPoint S')`, whose image is the generic point.
  This encodes exactly the stated dominance, including transcendental field extensions;
  K is not required to be algebraic over this function field.
- The fibre diagram has `Y`, `e : Y ⟶ Spec (.of K)`, `h : Y ⟶ X'`, and
  `ChosenCartesianSquare h e f' (Spec.map i ≫ S'.fromSpecStalk (genericPoint S'))`.
  This supplies the second Cartesian identification and commutativity equation.
- The cyclic order is `(d : ℕ)` with `d ∣ n`. A divisor of positive n is positive;
  allowing d=0 syntactically adds no witness. Negative integer divisors give the same
  cyclic group as their absolute values, so natural d covers the integer formulation.
- The coefficient object is exactly `AddCommGrpCat.of (ULift.{u + 1} (ZMod d))`.
  Applying `(constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj`
  gives its constant abelian sheaf. No arbitrary coefficient quotient is substituted.
- The last clause `¬ IsZero (...)` applies `singleFunctor` in degree zero, the existing
  `(Etale.lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus`, then
  `DerivedCategory.Plus.homologyFunctor _ (q : ℤ)`. This is exactly the abelian sheaf
  R^q h_* of the preceding cyclic constant sheaf. The ULift implements the same small-site
  coefficient universe as the recorded base-change interfaces.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.CumulativeUniversalBaseChangeProperty`:
  `AlgebraicGeometry.Etale.CumulativeUniversalBaseChangeProperty`, including its full body;
  its upstream fixed-degree `BaseChangeProperty` and `UniversalBaseChangeProperty` in
  `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs` were read with their map definitions.
- `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`:
  `AlgebraicGeometry.Etale.derivedBaseChangeMap` and its square-iso mate formula.
  The imported predicate uses the dependency record's existing bounded-below
  `Etale.baseChangeHomologyMap` presentation. No second map is introduced.
- `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso`:
  `AlgebraicGeometry.ChosenCartesianSquare.baseChangeInverseImageIso`; its parent module
  `Sheaf.AlgebraicGeometry.ChosenCartesianSquare` supplies `ChosenCartesianSquare`.
  Both source modules and the full square structure were read.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Sheaf.AlgebraicGeometry.FunctionField`: the full declaration and integral-scheme note;
  `Mathlib.AlgebraicGeometry.FunctionField`: `Scheme.functionField`, the generic stalk,
  and its field instance. The unused component-product construction is not duplicated.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`, used on
  each stalk; normal domains are domains integrally closed in their fraction field.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the recorded algebraic-closure
  module is imported and its closure construction is used in the proof plan.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`, whose
  body is the constant presheaf followed by sheafification.

The proof docstring follows all six DAG steps: field failure, algebraic closure,
normalization and integral pushforward compatibility, injectivity and nonzero target,
prime cyclic detection, and passage to the underlying cyclic abelian group. Recorded
proof-dependency modules are imported without `public`, including normalization in
upstream `CurveTestDatum`, coefficient restriction, prime detection, integral arrow
comparison, and the Mathlib finite/affine/qcqs interfaces. The three proof-only nodes
`sbc-lem-bc-failure-field`, `sbc-lem-bc-injectivity`, `sbc-lem-bc-integral-surjective`
have no recorded Lean modules in the base snapshot; they are named in the docstring,
not re-created. They are not missing statement prerequisites.

Edge cases checked: q=1 gives precisely the cumulative degree-zero hypothesis; q=0
is excluded by the node. n=1 gives a zero coefficient category, so failure is impossible,
without excluding this case by an added n>1 assumption. The empty base and empty total
space cannot exhibit the assumed failure; neither is excluded by an added hypothesis.
The constructed base is nonempty because IsIntegral supplies Nonempty. d=0 cannot divide
positive n; d=1 has zero cyclic group and cannot satisfy the nonzero conclusion. No
assumption forces the original schemes to be integral or affine. Field extensions need
not be finite or algebraic. All variables and the universe u are explicitly bound, and
scheme and field universes agree with the dependency's site convention. A chosen
Cartesian identification adds data that every Cartesian square canonically admits;
it does not narrow the existence assertion.

Searches for an existing exact statement:

- `msearch.py ... leanfinder`: "Failure of universal etale base change gives affine
  integral normal base with algebraically closed function field and nonzero higher
  direct image of constant cyclic sheaf". Eight hits, on affine-space nonintegrality,
  normalization properties and etale maps; no matching theorem.
- `msearch.py ... loogle`: `AlgebraicGeometry.Etale.UniversalBaseChangeProperty`.
  Zero hits; identifier unknown to the Mathlib search service.
- `msearch.py ... grep`: `exists_isPullback_not_isZero_higherDirectImage|UniversalBaseChangeProperty`
  in Mathlib AlgebraicGeometry. Zero hits.
- `msearch.py ... leansearch`: "Failure of universal etale base change detected by
  nonzero higher direct image of cyclic constant sheaf over geometric generic point".
  Service unavailable: Internal Server Error; no search verdict inferred.
- `rg` on the upstream smooth-base-change directory for universal/nonzero, and for
  the exact node id in WeilConjectures, found `CurveTestDatum.lean` and its
  `Etale.exists_isPullback_not_isZero_higherDirectImage`. Its full signature, docstring,
  and coefficient definition were read. That theorem quantifies over arbitrary Λ and
  concludes with Λ/dΛ; it is not the exact cyclic abelian-sheaf statement of this node.
  Its `exists_curveTestDatum` additionally requires an affine smooth relative curve,
  so it is not this node either. Only the required specialization is stated here.
- `rg` in `lean/Sheaf` for the upstream theorem name, universal-test names and
  higher-direct-image/constant-ZMod patterns found no existing exact statement;
  the existing abelian higher-direct-image map confirms the same abelian derived API.

Validation: the delivered module compiled cleanly via the mandated server `scompile.py`
(only a whole-theorem sorry). The final dry-run result is recorded below after running it.
No STATEMENT-DISPUTED flag or node fault remains.

Delivery dry run: `deliver2.py NM sbc-lem-bc-universal-test --no-push` printed
`OK (dry run)` and confirmed clean server compilation and preflight, with only the
independent second-reading section pending as expected for a worker. Nothing was pushed.

## Second reading by NM

I independently read the delivered node and Lean file against Stacks
`etale-cohomology.tex`, `lemma-base-change-does-not-hold` (0F08), including
`remark-base-change-holds` (0F02), and the blueprint's universal-datum page.
The Stacks remark already quantifies over arbitrary base changes and means a
cumulative degree bound; the DAG makes those quantifiers explicit and uses the
positive invertible coefficient domain of `sbc-def-base-change-property`.
The old blueprint diagram labels the vertical map h, but the reviewed DAG and
Stacks correctly label the horizontal map h. The Lean follows the reviewed DAG.

My statement inventory and clause-by-clause verdicts:

1. Arbitrary schemes X,S and a morphism f, with no geometric conditions:
   `{X S : Scheme.{u}} (f : X ⟶ S)`. Exact; no smoothness, finite type,
   Noetherian, affineness, separatedness, or field-base hypothesis is added.
2. Positive integer n invertible on S, inherited from the coefficient definition:
   `(n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(S, ⊤)))`. Exact for that
   node's stated domain. Invertibility of a constant section is equivalent to
   invertibility in every local ring. Stacks itself permits arbitrary integers;
   the present DAG explicitly specializes its coefficient domain, rather than
   silently obtaining that restriction from this theorem.
3. Positive degree q: `(q : ℕ) (hq : 1 ≤ q)`. Exact; all nonnegative
   cohomological degrees are represented and q=0 is explicitly excluded by the node.
4. Universal base change in all degrees 0 through q-1:
   `hprev : CumulativeUniversalBaseChangeProperty f n hn hinv (q - 1)`.
   I opened its full definition: it is exactly `∀ r : ℕ, r ≤ q - 1 →
   UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (r : ℤ)`.
   I also read upstream `BaseChangeProperty`, `UniversalBaseChangeProperty`,
   and `baseChangeHomologyMap` in SmoothBaseChange/Defs. They quantify over
   arbitrary base changes, all qcqs horizontal maps, and every module sheaf;
   modules over Z/nZ encode precisely abelian sheaves annihilated by n. Exact.
5. Failure universally in degree q:
   `hfail : ¬ UniversalBaseChangeProperty (ULift.{u + 1} (ZMod n)) f (q : ℤ)`.
   Exact, with the same coefficients, maps and quantifiers as item 4. Given item 4,
   this is also exactly the failure of the cumulative bound q in Stacks.
6. First base-change diagram, with its two arrows to the original diagram:
   existential `S' X' a b f'` and `ChosenCartesianSquare b f' f a`.
   I read ChosenCartesianSquare and BaseChangeInverseImageIso: the structure
   contains the commutativity equation, an isomorphism with `pullback f a`,
   and both projection equations. This is exactly a chosen Cartesian square;
   it neither permits an arbitrary scheme isomorphism nor restricts the existence.
7. Affine integral normal base S': witnesses `IsAffine S'`, `IsIntegral S'`,
   and `∀ x : S', IsIntegrallyClosed (S'.presheaf.stalk x)`.
   I read Mathlib's IsIntegral and its stalk-domain instance in FunctionField.
   Thus every stalk is a normal domain, exactly normality of the scheme;
   no Noetherian assumption is needed. Exact.
8. Algebraically closed function field: `IsAlgClosed S'.functionField`.
   I read the recorded FunctionField module and Mathlib's generic-stalk definition
   and integral-scheme field instance. The dependency explicitly supplies this
   arbitrary integral-scheme clause, not merely its separate component-product
   construction for curves. IsAlgClosed means all polynomials split, equivalently
   the root condition in the dependency. Exact.
9. Algebraically closed extension K and dominant point of S': existential
   `(K : Type u) (_ : Field K) (_ : IsAlgClosed K)` and
   `(i : S'.functionField ⟶ CommRingCat.of K)`; the point is
   `Spec.map i ≫ S'.fromSpecStalk (genericPoint S')`.
   A unital homomorphism between these fields is injective. Its spectrum lands
   at the generic point; conversely every dominant field-valued point has this
   factorization. K need not be algebraic over the function field. Exact.
10. Second square and its designated maps: existential `Y`, `e : Y ⟶ Spec (.of K)`,
    `h : Y ⟶ X'`, and `ChosenCartesianSquare h e f'` with the point of item 9.
    Projection order, commutativity, and horizontal h all match the node. Exact.
11. Cyclic divisor d and nonzero higher direct image: existential `(d : ℕ)`,
    `d ∣ n ∧ ¬ IsZero (...)`, with the constant sheaf obtained from
    `AddCommGrpCat.of (ULift.{u + 1} (ZMod d))`.
    A natural divisor represents every integer divisor up to sign, which leaves
    the cyclic group unchanged. The inner `singleFunctor _ 0`, derived
    `Etale.lowerStar AddCommGrpCat.{u + 1} h`, and outer degree-q homology
    are exactly R^q h_* of this abelian sheaf. I read constantSheaf's body:
    the constant presheaf followed by sheafification. Exact; no arbitrary-ring
    quotient or module-valued nonvanishing has replaced the abelian conclusion.

Edge cases: q=1 gives precisely degree zero in hprev; q=0 is excluded as in the
node. n=1 is admitted, with an impossible failure hypothesis, not removed by an
extra n>1 assumption. n=0 is outside the inherited coefficient domain. For positive
n, d=0 cannot divide n; d=1 gives the zero sheaf and cannot satisfy nonvanishing.
Empty X or S are not excluded by hidden instances; their failure hypotheses cannot
hold. The constructed S' is nonempty exactly because the conclusion requires it
integral. No index family occurs. No characteristic condition beyond invertibility
of n is added. Every scheme and K has the same arbitrary bound u used by the
recorded universal predicate; the coefficient lift to u+1 implements the small-site
convention, without identifying site object and morphism universes or restricting
field extensions. All variables and u are explicitly bound.

Independent H4 searches used different descriptions from the worker:

- LeanFinder through msearch: "A nonisomorphism of etale base change is detected
  by a nonvanishing cyclic constant abelian sheaf at a geometric generic point of
  a normal affine integral scheme". Eight hits about etale loci, formal unramifiedness
  and algebra base change; none states this result.
- Loogle through msearch: `"higherDirectImage"`. Zero hits.
- LeanSearch through msearch: "Nonvanishing higher direct image of a constant
  cyclic sheaf detects failure of smooth base change". Service unavailable with
  Internal Server Error; no conclusion inferred from its unavailability.
- Direct rg of Mathlib AlgebraicGeometry for base-change failure and nonzero
  higher direct images found no theorem. Direct rg of the upstream project and
  this project's lean/Sheaf for `IsAlgClosed.*functionField`, higherDirectImage
  with ZMod, and failure/nonzero theorem names located CurveTestDatum, Vanishing,
  PrimeCyclicDetection and coefficient-comparison modules. I opened the full
  upstream `exists_isPullback_not_isZero_higherDirectImage` signature and the
  definitions of higherDirectImage and constantModSheaf. That theorem's conclusion
  is a constant Λ/dΛ module sheaf for arbitrary Λ; even its Λ=Z/nZ specialization
  requires the cyclic-coefficient and underlying-abelian identifications to reach
  this exact statement. It is not an exact existing declaration of the node.

H5/H6/H8/H9: there are no definitions or helper declarations in this delivery and
one whole-theorem sorry. Its docstring gives the source and blueprint id and all
six DAG proof steps in order, including normalization before cyclic detection and
the coefficient restriction step. All recorded statement dependency modules are
used, and the recorded proof dependencies' modules are imported; the three
unrecorded proof-only prerequisites are correctly named rather than duplicated.
There are no new nodes, dependency repairs, statement corrections or citer-audit
obligations. No mathematical mismatch was found, so I retained the Lean and node
verbatim and added only this independent reading. The node's lean.statement was
checked programmatically equal to the theorem signature verbatim; lines are at
most 100 characters.

Validation: I compiled the delivered module again using the required server
scompile.py command. Both its sandbox and library checks passed (3.5 s and 3.8 s),
with no errors or warnings. No local compiler or lake build was invoked.

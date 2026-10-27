## Worker report

The module `Sheaf.Paper.DualityPullback` states
`WeilConjectures.SixFunctorDatum.duality_pullback`, with one postponed proof and
no other theorem. Its helper definitions expand this statement's restrictions,
identity comparison, and logical clauses. They introduce no independent
mathematical notion and choose no replacement operation or isomorphism.

Hypothesis and clause correspondence:

- The fixed global finite-field datum is the section parameter
  `D : FiniteFieldDatum.{u}`. Its coefficient datum `C : D.CoefficientDatum`
  contains the prime ell, its distinction from the characteristic, and the
  algebraic closure of the coefficient field. The base field of D is the
  fixed algebraic closure of the finite field. `E : Type u`, `[Field E]`,
  `[Algebra (Padic C.l) E]`, and `[FiniteDimensional (Padic C.l) E]` are the
  finite coefficient extension. The finite level is `n+1` with
  `Nat.succ_le_succ (Nat.zero_le n)`; every positive level occurs.
- `S : SixFunctorDatum D C E (n+1) ...` is exactly the supplied A1--A6
  datum, with its completed integral, rational and common-stage operations.
  No ambient admissibility assumption is added.
- `X Y : SixFunctorSpace D` are the existing full over-category of finite-type
  k-schemes. `[IsSeparated X.obj.hom]` and `[IsSeparated Y.obj.hom]` give
  the domain of absolute duality. A map `f : X ⟶ Y` is a k-morphism and
  `[IsSeparated f.hom.left]` imposes separatedness. Such a morphism between
  finite-type k-schemes is of finite type. Compactifications `cX`, `cY`,
  and `cf` are universally quantified construction coordinates, not extra
  restrictions on these maps: the separated finite-type maps admit them.
- The four `SfDualityPullbackStage` conjuncts use respectively `S.finite`,
  `S.higher.integral`, `S.higher.rational`, and `S.closure.commonStage`.
  The corresponding domains are the recorded finite-Tor predicates; at
  field coefficients these are top, exactly as in the datum.
- `sfDualityVerdierRestriction` is the existing
  `sixFunctorDomainHom`, curried and evaluated at the existing dualizing
  object. The four `...VerdierOnFiniteTor` wrappers use exactly
  `S.finiteDuality`, `S.higher.integralDuality`,
  `S.higher.rationalDuality`, and `S.closure.commonStageDuality`.
  Their `dualizing` is exceptional inverse image of the coefficient unit;
  its membership proof is the corresponding A6 `omegaDomain`. Thus these
  are the Verdier functors of def-sf-pf, including their morphism action.
- The witness `chi` in `SfDualityPullbackStage` is a family of natural
  isomorphisms `(pull restriction).op ⋙ V X cX ≅ V Y cY ⋙ exceptional
  restriction`. Both sides have source the **opposite** finite-Tor
  category on Y and target the finite-Tor category on X. Naturality in
  the input is the `NatIso` type, including all morphisms.
- The first coherence conjunct supplies the identity inverse-image unit
  identification `e`, normalized by the left unit equation for the
  supplied `pullComposition`. It then says that `chi_id`, followed by
  `sfDualityExceptionalId`, is `V(e.inv.op)`. The latter helper is built
  solely from compactification comparison, proper identification,
  the pull/direct adjunction and uniqueness of the exceptional right
  adjoint. Hence this is identity after the actual unit identifications,
  with their normalization stated explicitly rather than a vacuous
  implication about a hypothetical unit.
- The second coherence conjunct says in components
  `V(pullComposition.hom.op) ≫ chi_fg ≫ exceptionalComposition.hom =
  chi_f(pull_g K) ≫ exceptional_f.map(chi_g K)`.
  The contravariance explains the first arrow's direction. All arrows
  in this equation are the supplied comparisons, with no substitute
  compositor. Full-subcategory morphisms are displayed by their `.hom`.
- The last conjunct quantifies `O : SfOrientationDatum S` and gives
  `SfDualityPullbackSmooth` at each stage. That predicate imposes
  `[SmoothOfRelativeDimension d f.hom.left]`, with `d : ℕ`, and gives
  a natural isomorphism `D_X f* ≅ (f* D_Y) tensor T_X,d`.
  The lines are `sfOrientationReducedLine`,
  `sfOrientationIntegralLineOn`, its rationalization, and its common-stage
  inclusion, respectively. These are precisely Lambda(d)[2d]. Finite
  coefficients are displayed through the existing fully faithful
  inclusion into the ambient pro-etale derived category because the
  existing ambient tensor is defined there. This is equivalent to the
  isomorphism in the finite-Tor full subcategory: both values are the
  finite-Tor operations from the datum and the shifted invertible line.
  For the other stages the additional inclusion is the identity.

Dependencies read and used:

- `Sheaf.Paper.SixFunctorDatum`: `WeilConjectures.SixFunctorDatum`,
  `SixFunctorCoherentStage`, `SixFunctorClosedDomain`,
  `SixFunctorVerdierAxioms`, `sixFunctorDomainHom`,
  `sixFunctorExceptionalComposition`. Read their full signatures,
  docstrings, and the inherited `SixFunctorOperationDatum` and
  `SixFunctorPushStage` interfaces.
- `Sheaf.Paper.SixFunctorDualNotation` (def-sf-pf): its module documents
  and re-exports the four existing Verdier functors and dualizing objects.
  Its coefficient-dual declarations have a different second argument
  (the unit); these are deliberately not substituted for Verdier duality.
- `Sheaf.Paper.SixFunctorOrientationFamily`:
  `WeilConjectures.SfOrientationDatum`. Read its full structure, its
  higher, finite and primary families, and the actual line constructions
  in `OrientationCoefficientTwists` and
  `SixFunctorOrientationFiniteFamily`. Only the condition that an
  orientation is fixed and its existing lines appear in the statement;
  functorial purity remains an input to the postponed proof.
- The recorded proof dependency `Sheaf.Paper.VerdierExchange` is a plain
  proof import. The Mathlib proof dependencies use `Coyoneda.fullyFaithful`
  and `mateEquiv_vcomp`, `mateEquiv_hcomp`, and `conjugateEquiv_id` from
  `Mathlib.CategoryTheory.Yoneda` and `Mathlib.CategoryTheory.Adjunction.Mates`.
  The package and purity-transport proof nodes have no recorded Lean
  modules; no missing proof theorem is silently asserted by a helper.

Searches for existing statements:

- `msearch.py ... leanfinder "Verdier duality of pullback is exceptional
  inverse image of Verdier dual"`: eight hits, mainly ordinary sheaf
  pullback adjunctions and `conjugateEquiv_pullbackComp_inv`; no match.
- `msearch.py ... loogle "CategoryTheory.Adjunction,
  CategoryTheory.Equivalence"`: six generic adjunction/equivalence hits;
  no geometric four-stage statement.
- `msearch.py ... leansearch "Verdier dual of pullback is exceptional
  inverse image of Verdier dual"`: eight ordinary pullback/adjunction
  hits; no matching theorem.
- `msearch.py ... grep "verdierDual|dualityPullback|dualizingComplex"
  CategoryTheory`: generic Verdier localization/duality material; no
  geometric pullback statement.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `dualityPullback|duality_pullback|VerdierPull|verdierPull|
  cor-sf-duality-pullback|DualityPullback` found the upstream
  `WeilConjectures.SixFunctors.Etale.Derived.DualityPullback` module.
  Read that entire module. Its
  `AlgebraicGeometry.Etale.nonempty_iso_verdierDual_leftDerivedUpperStar`
  is finite-coefficient etale only and explicitly says that naturality in
  f is not recorded. Its oriented theorem is objectwise and finite only.
  They therefore do not state this node (four stages plus coherence).
  The only other Sheaf hits were distinct duality/evaluation results.

Edge cases checked: f identity; composable maps including identities;
empty schemes; zero input; d=0 (etale maps); finite level 1; arbitrary
finite E/Q_ell; and common-stage coefficients. No maximum dimension,
nonempty scheme, nonzero input, properness of f, or field-to-finite
reduction is assumed. Universes are explicit; the auxiliary generic stage
allows separate object/morphism universes. The source's informal covariant
functor notation is read contravariantly, as the DAG already specifies.
The latest blueprint and its proof were read at `literature/blueprint/latest/`;
its formal adjoint-transform route and smooth substitution are retained.

No statement correction, dependency repair, or new node is needed.
The module has one sorry, the whole proof of `duality_pullback`.

## Second reading by Q76

Author self-check, not an independent review (the dispatcher forbids spawning
agents; independent review belongs to the maintainer). Reopened the node and
module and checked each stage, variance, scheme hypotheses and conclusion.
The initial compositor direction was reversed; corrected to
`pullComposition.hom` before taking the opposite, so D maps iterated pullback
to composite pullback. The initial identity expression needed an explicit
morphism type, now supplied. Identity is stated using an existing normalized
unit, including its existence, so it cannot become vacuous. The finite smooth
clause initially tried to put the ambient tensor in a bounded category;
corrected to display both sides through the same existing fully faithful
ambient inclusion. No object or coefficient stage was replaced. A6's existing
triangulation fields are used locally inside definition bodies, without any
new triangulation or extra typeclass assumption in the statement.

Validation: scompile.py passed both sandbox and library compilation on the server,
with no errors or unexpected warnings. The prescribed deliver2.py --no-push
dry run passed the server preflight and compilation (commit 81e9ae26681).

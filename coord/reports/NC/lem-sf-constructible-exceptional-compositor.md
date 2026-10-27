## Worker report

Group NC; stage 2; item `lem-sf-constructible-exceptional-compositor`.
Source read: main-20261015, sec-six-functors/sk-thm-sf-verdier-exchange,
proof Step 1, together with the node's expanded proof. The item statement is unchanged.

`Sheaf.Paper.ConstructibleExceptionalCompositor` states
`WeilConjectures.ConstructibleExceptionalCompositor.constructibleExceptionalCompositor`.
The only postponed proofs in this delivery are that theorem and the named integral
presentation identification in the compositor module; both have full proof docstrings.
All comparison objects are actual Lean constructions. In particular `exceptionalIso`
is literally `conjugateIsoEquiv (A.adjunction.comp G.adjunction) H.adjunction alpha.symm`.
No functor, natural transformation or isomorphism is defined by `sorry` or chosen from
a bare existence proposition.

Hypothesis and clause correspondence:

* The fixed finite-field datum is `D : FiniteFieldDatum`; `B : D.CoefficientDatum`
  supplies the prime `B.l`, `B.different`, the algebraic closure `B.Qbar` and its
  coefficient structure. `FieldStage B.l` uses the existing finite extensions of
  `Padic B.l`; their valuation rings, uniformizers and quotients are the existing
  coefficient-extension constructions. `n : ℕ+` enforces exactly `n ≥ 1`.
* `X Y Z : SixFunctorSpace D` are the existing full subcategory of the over category
  of `Spec D.k` with locally finite-type and quasi-compact structure morphisms.
  The three `IsSeparated X.obj.hom` instances assert separatedness over the base.
  `f : X ⟶ Y` and `g : Y ⟶ Z` are base morphisms; their respective `IsSeparated`,
  `LocallyOfFiniteType` and `QuasiCompact` instances assert the stated conditions.
  `f ≫ g` is exactly x, with the same underlying scheme composite. The three
  elementary composition instances merely expose the existing Mathlib instances.
* `S E n : SixFunctorOperationDatum D B E.carrier n n.pos` is the specified
  operations datum, not an ambient exceptional-adjoint assumption. Its finite
  compositor is normalized by `finiteCompositionNormalization` to the recorded
  `originComposition`; its higher operations retain completed integral and raw
  rational normalization. This is one family because the assertion covers all
  positive levels and all target finite extensions, as well as common stages.
* `C B.l B.Qbar T s` is exactly the dependency's category: finite constructible
  finite-Tor, derived-complete integral with one common Tor interval over all
  reductions, raw rationalization, or the existing common finite-stage category.
  We do not replace these by arbitrary triangulated categories.
* The existential joint output `P Q R : System ...` is the three actual adjunction
  systems supplied by `exists_system`, enriched here with their simultaneous
  compositor assertions. Their ring, rational and common realization fields pin
  the actual specified functors; their adjunctions, shifts, unit/counit compatibility,
  coefficient maps and refinements are retained. We do not select a new exceptional
  operation on an unrestricted ambient category. This follows the output-data
  convention of the recorded exceptional-adjunction dependency rather than
  postulating the adjunctions or their coefficient compatibilities as premises.
* `A : LeftCompositors ... S` has a natural isomorphism `alpha cf cg cx s` in the
  requested direction `F_f ⋙ F_g ≅ F_x`. `A.finite` equates it to `finiteAlpha`,
  the unique fully faithful lift of `S.finite.composition ... .symm` through
  the existing finite-Tor inclusions and normalized realization comparisons.
  It is not an unconstrained left-adjoint isomorphism.
* `A.integral` similarly fixes `integralAlpha`, using `S.higher.integral.composition`
  and the specified completed realization. `A.rational` and `A.common` spell out
  `LeftCoefficientEquation` using the dependency's actual rationalization and
  common-inclusion q maps. They are component equations for the rationalized
  and common-stage forms of that same alpha. All finite extensions appear as
  `E : FieldStage B.l`, including any target E'; `Stage.closed` is the specified
  common category, not a replacement coefficient ring.
* `exceptionalIso` has type `G_g ⋙ G_f ≅ G_x`, i.e. the stated `G_f G_g` in
  function notation. Its definition uses inverse alpha and exactly the composite
  and direct constructible adjunctions. A `NatIso` includes both invertibility
  and naturality in every L. No further representability hypothesis appears.
* The first conjunct of `MateProperties` quantifies over every K, L and
  `u : K ⟶ (G_g ⋙ G_f).obj L`. Postcomposition by c equals
  `H.adjunction.homEquiv K L (alpha.inv.app K ≫ compositeHomEquiv.symm u)`.
  This is the displayed Hom-chain, in Lean's left-to-right composition convention.
* The second conjunct is the pasted counit formula
  `alpha.hom.app (G_f G_g L) ≫ F_x.map c_L ≫ epsilon_x =
  F_g.map epsilon_f ≫ epsilon_g`, exactly the equation in the node.
* The third conjunct quantifies over each component t, with no assumed naturality,
  and asserts the displayed equation iff `t = c_L`. This includes existence and
  the requested componentwise uniqueness.
* The last two conjuncts are `alpha.hom.CommShift ℤ` and
  `exceptionalIso.hom.CommShift ℤ`, with the actual `Operation.leftShift` and
  `Operation.rightShift` instances. Thus every integer, including negative and
  zero shifts, is covered; no replacement shift on a right adjoint is selected.
* `RefinementIndependent` quantifies over all three independent refinement arrows,
  all stages, and all L. It states equality of the path using right refinement
  for f and g followed by the old c with the path using new c followed by the
  refinement for x. These are precisely the existing counit-compatible right
  comparisons, in their contravariant directions. The dependency retains their
  identity/composition coherence, so this is independence under the stated
  identifications rather than literal equality of differently presented functors.

Dependency declarations used (the recorded declaration signatures/docstrings were read):

* `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`: the coefficient and
  constructible vocabulary of `sk-def-sf-setting`, with the datum and positive
  quotient definitions already publicly used by the following interfaces.
* `Sheaf.Paper.SixFunctorOperationDatum`: `WeilConjectures.SixFunctorOperationDatum`,
  `SixFunctorSpace`, finite support normalization and higher integral/rational stages.
* `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and its public Data
  interface: `ConstructibleExceptionalCoefficients.C`, `FieldStage`, `Stage`,
  `Operation`, `System`, `exists_system`, actual realization, coefficient and
  refinement comparison records. The original module is imported directly; its live node record is untouched.
* `Sheaf.Paper.CanonicalOriginCompactSupportComposition`:
  `AlgebraicGeometry.ProEtale.originComposition`, whose actual origin normalization
  is retained in the specified operation datum's finiteCompositionNormalization.
* `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.conjugateIsoEquiv`,
  `conjugateEquiv` and their counit characterization; `Adjunction.comp` is used
  for the composite adjunction, and `.homEquiv` for the displayed Hom-chain.
* `ObjectProperty.fullyFaithfulι`, `fullyFaithfulιOfLE` and
  `Functor.FullyFaithful.preimageIso` give canonical full-subcategory lifts.
  `Functor.associator` is retained explicitly; no strict associativity is assumed.
* Proof imports are exactly the recorded compactified-tower, finite structural
  shift, integral realization-shift, rational-transport and coherent-pair descent
  modules: `Sheaf.Paper.CompactifiedTowerComparisons`,
  `Sheaf.Paper.FiniteStructuralMapsCommShift`,
  `Sheaf.SixFunctors.IntegralRealizationShiftCoherence`,
  `Sheaf.Paper.PbcRationalTransport`, and
  `Sheaf.CategoryTheory.StageSystemFunctorDescent`. Mathlib's shift-adjunction and
  composition/whiskering compatibility infrastructure is already publicly available.

Edge cases checked before/during writing: n = 1 is included and n = 0 excluded;
identity f or g needs no extra nonidentity hypothesis; empty schemes and zero
objects are allowed; no smoothness, properness, flat coefficient-change or
unrestricted ambient exceptional adjunction was added. Negative, zero and positive
integer shifts are all quantified by `CommShift ℤ`. Independent compactification
refinements and identity refinements have correctly typed directions. The integral
proof docstrings specifically use actual strict-tower maps and common bounds,
never faithfulness of finite evaluation. The finite coefficient identification is
transported through its unit-normalized ordinary pullback, not identified by an
unchecked definitional equality.

Searches for an existing exact statement:

* `msearch.py ... leanfinder "Composition of constructible exceptional inverse images
  is conjugate to inverse compact support composition at all coefficient stages"`:
  eight unrelated results (including `Composition.invEmbedding_comp`,
  `PrimeSpectrum.ConstructibleSetData.map_comp`); none is this theorem.
* `msearch.py ... leansearch "Exceptional pullback composition on constructible finite
  Tor sheaves is adjunction conjugate to inverse compact support composition"`:
  eight results, chiefly `SheafOfModules.conjugateEquiv_pullbackComp_inv`,
  `SheafOfModules.pullbackComp` and ordinary pullback adjunctions. These concern
  ordinary sheaves/modules, not the stated finite-Tor four-stage exceptional functors.
* `msearch.py ... loogle "CategoryTheory.conjugateIsoEquiv"`: that declaration and
  its four hom/inv variants; this is the exact generic conjugation infrastructure
  used, not a geometric all-coefficient composition statement.
* `msearch.py ... grep "exceptional.*[Cc]ompos|constructible.*[Cc]ompos"`:
  no Mathlib hits.
* `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for exceptional/constructible
  composition and the item id: no existing declaration of this node. Existing
  `StandingExceptionalComposition`/finite exceptional composition results have
  different data or only finite coefficients. The existing origin compact-support
  compositor and actual constructible coefficient adjunctions are reused instead.

The repaired single module is compiled against published live sources by `scompile.py`;
final compilation/delivery status is recorded by the required delivery wrapper.
No global build or direct repository Git operation was run.

## Returned delivery repair

The independent review of returned head `bd9326bea167` identified H13: the adapter
rebound `lem-sf-constructible-exceptional-adjunction-coefficients` to a theorem that
did not state that dependency. The repaired packet omits that dependency node file,
so delivery retains the live record byte for byte, including its original module
`Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients` and main declaration
`WeilConjectures.ConstructibleExceptionalCoefficients.exists_system`.

The three helpers `WeilConjectures.constructibleFinitePullIso`,
`WeilConjectures.constructibleFiniteImageIso`, and
`WeilConjectures.constructibleIntegralSupport_eq` now belong to the item's sole
module `Sheaf.Paper.ConstructibleExceptionalCompositor` and are listed in its
`lean.declarations`. Their source/blueprint docstrings name this item. The adapter
module is removed; the original dependency and the helpers' supporting modules are
imported directly. No dependency interface is replaced and no statement is changed.

The advisory on equality is addressed in the integral helper's proof docstring:
object normalizations agree; naturality and the fixed Roos projections identify
the images of every morphism; the Milnor kernel is lim^1 of finite constructible
Ext groups. Finite inverse systems are Mittag-Leffler, so that kernel vanishes.
The faithful full-subcategory inclusion and functor extensionality then give the
stated functor equality. This is restricted to the actual constructible setting,
not an assertion that finite evaluation is faithful on arbitrary derived towers.
The shift assertion remains existential in P, Q, R, exactly as accepted in the
return: it is not a claim for every free choice of Operation.leftShift.

## Self-check by NC

The node and final module were read together after the ownership repair. The
finite and integral alpha fields are still pinned to the full-subcategory lifts
of S.finite.composition and S.higher.integral.composition. Rational and common
normalizations still use the recorded q maps. exceptionalIso remains the literal
conjugateIsoEquiv of alpha.symm under the composite/direct adjunctions. The Hom
chain, pasted counit, componentwise iff uniqueness, integer shifts, and the square
for three independent refinements are unchanged. The main theorem's signature
remains verbatim in lean.statement; every helper is in lean.declarations. All
variables and universe u are explicit under autoImplicit false. Positive level
n = 1, identities, empty schemes and arbitrary integer shifts remain included.
The sole found mismatch was helper ownership and the replaced dependency record;
the changes above repair it. This is the worker's self-check; the maintainer's
independent review is the separate second reading for this dispatcher assignment.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

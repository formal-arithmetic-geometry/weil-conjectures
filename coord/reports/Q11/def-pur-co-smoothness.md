## Worker report

The delivery defines `AlgebraicGeometry.ProEtale.IsCohomologicallySmooth` in
`lean/Sheaf/Paper/CohomologicalSmoothness.lean`. It is a definition with real data,
not a theorem and not a smoothness assumption. Its helpers belong to the same
notion and are all listed in `lean.declarations`.

Hypothesis-by-hypothesis rendering:

* `P : WeilConjectures.PurityFiniteSetting` supplies the finite-field datum
  `p,a,q,k0,k`, the prime ell different from p, Qbar, finite intermediate
  extension E, its finite-dimensionality, and `level_pos : 1 ≤ level`.
  `P.Ring` is the actual valuation-ring quotient and `P.Coefficient` its
  universe lift. `Padic.finite_coefficientExtensionRing` supplies finiteness.
  No coefficient field, quotient, or uniformizer is replaced by arbitrary data.
* `X,Y : Scheme.{u}` with `Over (Spec (.of P.field.k))` are the k-schemes.
  `LocallyOfFiniteType` and `QuasiCompact` on each structure map mean finite type.
* `f : X ⟶ Y`, `f.IsOver ...`, `IsSeparated f`, `LocallyOfFiniteType f`, and
  `QuasiCompact f` give exactly the separated finite-type k-morphism.
  Compactness and local Noetherianness of Y are derived in the body, and Nagata
  supplies its compactification. Neither is an additional user hypothesis.
* All operations act on `DerivedCategory (Sheaf (Scheme.ProEt.topology T)
  (ModuleCat.{u+1} P.Coefficient))`, the small pro-etale, constant discrete
  module-sheaf presentation used by the published six-functor framework.
  The original intrinsic `SheafOfModules` presentation is related by the
  canonical `finiteCoefficientIntrinsicRealization`, read in
  `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`.

Clause-by-clause rendering:

1. `dualizingComplex ... f` is literally `rightDerivedUpperShriek ... f`
   applied to the monoidal unit, namely the constant coefficient sheaf in
   degree zero. `cohomologicalInvertibilityClause` quantifies an inverse M,
   requires `DerivedCategory.constructibleFiniteTor ... X M`, and requires
   both `omega tensor M ≅ unit` and `M tensor omega ≅ unit`. Both sides and
   the finite-Tor condition are retained.
2. `cohomologicalTensorClause` quantifies every K satisfying the same Dctf
   predicate on Y. Its isomorphism sigma has source `omega tensor Lf*K`.
   The displayed equation is
   `PF ≫ Rf! sigma.hom ≫ counit_K = (counit_unit tensor id) ≫ leftUnitor`.
   Multiplication by the inverse of PF says exactly that sigma is the counit
   transpose specified in the node before inserting symmetry. The node's
   theta is symmetry `Lf*K tensor omega → omega tensor Lf*K` followed by
   sigma. Symmetry is a canonical isomorphism, so requiring sigma to be an
   isomorphism is equivalent to requiring the specified theta to be one.
   No arbitrary isomorphism of the endpoints suffices: it must satisfy this
   equation. `hK.plus` supplies only the already implied bounded-below fact.
3. `cohomologicalBaseChangeClause` quantifies finite-type k-schemes X',Y',
   all three k-morphisms, and `ChosenCartesianSquare g' f' f g`. Its recorded
   chosen fibre-product identification is converted by
   `IsPullback.of_iso_pullback`; it is not an unrelated square. There is
   no separatedness or smoothness condition on g. Compactification and
   finite-type/separated properties of f' are obtained by base change.
   The equation for the isomorphism beta is
   `Ex_c(omega) ≫ Rf'!_c' beta.hom ≫ counit'_unit = Lg*(counit_unit) ≫ unitIso`.
   Because the canonical compact-support exchange is invertible on these
   etale-origin objects, this is exactly its inverse followed by pullback
   of the counit and the unit comparison, transposed under f'! dashv f'^!.
   The primed counit is computed using `c.ofIsPullback sq`; the published
   etale compactification comparison transports it to the default etale
   adjunction. This retains the canonical comparison, including the unit
   normalization, without imposing equality of compactification choices.

No Tate identification, dimension, orientation, geometric smoothness, ambient
pro-etale right adjoint, global exceptional boundedness axiom, or chosen
etale-origin witness is an extra hypothesis of the main predicate.

Dependency declarations used (module, name):

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`,
  `.Ring`, `.Coefficient`; imports `FiniteFieldDatum` and `.CoefficientDatum`.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`.
* `WeilConjectures.SixFunctors.ProEtale.Derived.Tensor`:
  `AlgebraicGeometry.ProEtale.derivedTensor`, the published K-flat tensor.
* `...ProEtale.Derived.TorAmplitude`: `DerivedCategory.constructibleFiniteTor`
  and its `.plus` consequence, bounded constructibility intersect finite Tor.
* `...ProEtale.Derived.UpperShriek`: `rightDerivedUpperShriek`,
  `rightDerivedUpperShriekCounit`, `plus_etaleRightDerivedUpperShriek_obj`;
  `...Derived.Duality`: `dualizingComplex`.
* `...ProEtale.Derived.LowerShriek`: `rightDerivedLowerShriek` and
  `rightDerivedLowerShriekOfCompactification`.
* `...ProEtale.Derived.LowerShriekComparison`:
  `rightDerivedLowerShriekOfCompactificationComparisonIso`.
* `...ProEtale.Derived.LowerShriekProjection`: `projectionMap` and
  `projectionMapOfCompactification`, using the specified proper and open
  projection composites. `...Derived.ProjectionFormula` supplies their
  finite-Tor invertibility on the domain in question.
* `...ProEtale.Derived.LowerShriekBaseChange`:
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap` and its
  etale-origin invertibility theorem. This is the compactification-relative
  transported pro-etale map, so g remains arbitrary. The more general
  Zariski-local arbitrary-base extension in thm-cbc-finite-level-proetale
  is unnecessary in this field-base compactifiable setting.
* `...Etale.Derived.LowerShriekIndependence`:
  `rightDerivedLowerShriekOfCompactificationPlusιIso`, canonical comparison.
* `...ProEtale.Derived.UpperStarMonoidal`: `leftDerivedUpperStarUnitIso`.
* `...ProEtale.UpperLowerStar`: `upperStar`, its `leftDerivedFunctor`;
  `...ProEtale.Comparison.Derived`: `derivedComparisonAdjunction`.
* `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`: `ChosenCartesianSquare`;
  `WeilConjectures.Compactification.BaseChange`: `Compactification.ofIsPullback`;
  `...NagataCompactification`: its unconditional `HasCompactification` instance.
* Mathlib `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `Scheme.Over`,
  `Scheme.Hom.IsOver`, `IsPullback.of_iso_pullback`, and
  `MorphismProperty.of_isPullback` keep the recorded scheme conventions.

Edge cases checked: n=0 is excluded exactly by P.level_pos; n=1 is allowed;
ell=p is excluded by P's coefficient datum. Empty X, empty Y, and zero complexes
are permitted: the predicates use zero objects and actual scheme morphisms,
not nonempty hypotheses. Identity squares and isomorphism squares are included.
Base changes g need not be separated. Nonregular finite quotient rings are
allowed: the finite-Tor requirement is explicit, not replaced by ordinary
bounded constructibility or vector-space coefficients. No dimension bound is
added, including for empty schemes. All scheme and coefficient universes are
explicit; u+1 module coefficients do not collapse the pro-etale site universes.

Searches performed:

* `msearch.py ... leanfinder`: "A separated finite type morphism is
  cohomologically smooth when its exceptional inverse image of the tensor
  unit is invertible and the canonical tensor and base change counit mates
  are isomorphisms". Eight morphism-property matches, none this definition.
* `msearch.py ... loogle "CohomologicallySmooth"`: no Mathlib match.
* `msearch.py ... leansearch "cohomologically smooth exceptional inverse
  image invertible dualizing complex"`: service returned Internal Server Error;
  compensated by source searches and LeanFinder.
* `msearch.py ... grep "cohomolog.{0,30}smooth|CohomologicallySmooth|dualizingComplex"`:
  no exact Mathlib definition. `rg` in both source trees and `lean/Sheaf`
  found the existing etale `AlgebraicGeometry.Etale.IsCohomologicallySmooth`
  in `WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth`.
  It is an etale predicate with a different interface; it is not silently
  substituted for the required pro-etale predicate with inverse in Dctf.
* `rg` and the blueprint references located all existing operation nodes.
  Current `scompile.py --source` reads were used for the compact-support
  comparison, exchange, and related modules missing from the older checkout.
  The newer shared WeilConjectures framework supplies the actual finite-level
  exchange and compactification independence; no copies of those maps are made.
* Target id source search found the etale purity discussion but no existing
  pro-etale declaration giving all three finite-level clauses as stated.

There is no statement correction or disputed mathematical clause.

## Dependency modules

`def-weil-exceptional-inverse-image` is supplied in
`Sheaf.Paper.FiniteTypeExceptionalInverseImage`. The previously missing finite
field-base interface is essential: the current upstream exceptional definition
requires mapwise bounded-below preservation, whereas the global
`Etale.HasBoundedBelowUpperShrieks` would be an unjustified stronger assumption.
The named theorem `finiteTypeHasBoundedBelowUpperShriek` postpones exactly the
D+ preservation assertion already made in the dependency node, with its source
and full proof route in its docstring. The real definition
`finiteTypeExceptionalInverseImage` uses this proof to instantiate the existing
comparison-transport construction. No arbitrary functor is chosen. This delivery
uses only the dependency's finite coefficient stage, as does the item.

The finite-stage records of `def-weil-derived-pullback-tensor-hom` and
`def-exchange-projection` point to the existing canonical upstream operations.
`def-weil-derived-tensor` exposes the existing descended tensor used by those
operations. The finite-level `def-weil-finite-tor-amplitude` record points to
the existing upstream `constructibleFiniteTor`: bounded constructibility
intersect finite Tor amplitude, in the same fixed-module presentation as the
six functors. Its older intrinsic realization module imports the retired
FiniteCoefficient.UpperLowerStar definitions and cannot be imported alongside
the published derived exceptional/compact-support API (duplicate notation
and declarations). The repair therefore selects the existing upstream
predicate, rather than redefining a transport or a second Tor condition.
The original integral/field declarations remain available and unchanged in
Sheaf.Paper.FiniteTorAmplitude. This finite-level consumer uses no higher
coefficient stage.
No new definition node is introduced and no existing dependency statement changes.

Validation: file-only scompile.py runs compile both delivered files under the
unchanged 60-second limit, in sandbox and library modes. No proof is supplied;
the dependency preservation theorem has a named sorry with its full
natural-language proof and the matching D+ assertion of its definition node. The required deliver2.py --no-push dry run returned OK: commit 8683ab2080
compiles and passes server preflight except for the second reading, which
the second reader supplies. Nothing was pushed.

## Second reading by Q11

I independently read the node and both delivered Lean modules. The source of this
item is the blueprint definition at order 1896, not a Stacks tag. The literature
files are absent from this read-only local mirror, so I read the actual master
`sec-smooth-purity/sk-def-purity-conv/def-pur-co-smoothness.md` and its enclosing
`_section.md` from the project server. I also read the local unit record and the
statements of every direct dependency. The source gives the same three conditions
and uses finite coefficients and the constructible exceptional inverse image.
There is no `statement_change` to audit, and the node needs no source correction.

The following is my object/hypothesis/conclusion checklist, with the actual Lean
rendering and verdict for each entry.

1. Fixed finite-field data: `P.field : FiniteFieldDatum` has `p`, `a`, `q`,
   primality, positive exponent, `q = p ^ a`, the finite field of that cardinality,
   and its fixed algebraic closure `P.field.k`. I opened `FiniteFieldFiber.lean`
   and checked the structure fields. PASS.
2. Coefficient prime and finite extension: `P.coefficients` contains the prime
   distinct from the characteristic and its fixed algebraic closure;
   `P.extension : IntermediateField ...` with `P.finiteExtension` specifies the
   finite extension inside that closure. `P.level` and `P.level_pos` give exactly
   n >= 1. `P.Ring` is the existing valuation-ring quotient, and `P.Coefficient`
   is its `ULift`, with the inherited commutative-ring structure. I read
   `PurityFiniteSetting.lean` and `Padic.finite_coefficientExtensionRing` rather
   than assuming the bundled names describe the right coefficient ring. PASS.
3. The objects X and Y: `X Y : Scheme.{u}`, their `Over (Spec (.of P.field.k))`
   structures and `LocallyOfFiniteType`/`QuasiCompact` instances on their
   structure maps are precisely finite-type k-schemes. Neither scheme is
   assumed separated, smooth, proper, connected or nonempty. The noetherian and
   compact-space instances used in the body follow from these hypotheses over
   the field; they are not additional binders. PASS.
4. The morphism: `f : X ⟶ Y`, `f.IsOver ...`, `IsSeparated f`,
   `LocallyOfFiniteType f`, and `QuasiCompact f` render the separated finite-type
   k-morphism. I checked the actual finite-type and separatedness definitions
   named by the collector `def-weil-scheme-morphism-properties`. Nagata obtains
   a compactification from this context. PASS.
5. The category and operations: the displayed types are the derived categories
   of `Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u+1} P.Coefficient)`.
   `derivedTensor` is the existing K-flat-derived tensor;
   `upperStar ... |>.leftDerivedFunctor` is the existing derived inverse image;
   `rightDerivedLowerShriek` is derived proper direct image after extension by
   zero. I opened the corresponding `Tensor`, `UpperLowerStar/Defs`,
   `Derived/UpperLowerStar`, `Hom`, and `LowerShriek` interfaces and the
   canonical `finiteCoefficientIntrinsicRealization` comparison with the
   intrinsic constant-ring module presentation. This is a presentation change
   of the same finite discrete coefficients, not a new coefficient system or
   an ambient pro-etale adjoint. PASS.
6. The exceptional object and counit: `dualizingComplex A f` unfolds to
   `(rightDerivedUpperShriek A f).obj (𝟙_ _)`. The latter is literally
   `Rν_* ⋙ Etale.rightDerivedUpperShriek ⋙ Dν^*`. The monoidal unit is the
   constant coefficient sheaf in degree zero. I read
   `rightDerivedUpperShriekCounit`, its Hom-equivalence interface, and
   `plus_etaleRightDerivedUpperShriek_obj`. These supply the specified
   constructible adjunction and an etale-origin representative for omega.
   No assumption of a right adjoint to ambient pro-etale Rf_! is made. PASS.
7. Clause 1: `cohomologicalInvertibilityClause` is the existential over M,
   `constructibleFiniteTor ... X M`, and both tensor-to-unit isomorphisms.
   The source's two sides and the restriction that the inverse lies in
   D^b_ctf are all present. I opened `constructibleFiniteTor`: it is bounded
   constructibility intersected with finite Tor amplitude, not ordinary
   constructibility alone. PASS.
8. Clause 2: `cohomologicalTensorClause` quantifies every K with exactly that
   D^b_ctf predicate on Y. The supplied `hC` is `hK.plus`, an existing
   consequence of the same predicate. Its existential isomorphism has source
   `omega tensor Lf*K` and target `Rf!K`, with equation
   `PF ≫ Rf! sigma.hom ≫ counit_K = (counit_unit tensor id) ≫ leftUnitor`.
   I checked the direction and component of `projectionMap` against its proper
   projection/open-extension/composition formula. Since PF is invertible on
   this domain, the equation says that sigma is its prescribed counit mate.
   Precomposing sigma with tensor symmetry gives exactly the source's theta
   with source `Lf*K tensor omega`. This is equivalent to its invertibility;
   an arbitrary endpoint isomorphism would not satisfy the required equation.
   No naturality assumption or extra conclusion is inserted. PASS.
9. Clause 3, square and quantifiers: `cohomologicalBaseChangeClause` quantifies
   X', Y', their finite-type k-structures, g', f', g and their k-linearity, then
   `ChosenCartesianSquare g' f' f g`. Its `isoPullback` and the two projection
   equations give an actual pullback square via `IsPullback.of_iso_pullback`.
   The instances for compactification, finite type and separatedness of f'
   are obtained by base change, rather than imposed on g. No separatedness,
   smoothness, properness or flatness condition on g is present. PASS.
10. Clause 3, map: the isomorphism beta has source `Lg'^* omega_f` and target
    `dualizingComplex A f'`. Its equation is
    `Ex_!(omega) ≫ Rf'! beta.hom ≫ counit'_unit = Lg*(counit_unit) ≫ unitIso`.
    I read `rightDerivedLowerShriekOfCompactificationBaseChangeMap` and its
    etale-origin isomorphism theorem: the exchange arrow runs from
    `Lg* Rf! omega` to `Rf'! Lg'* omega`. Consequently this equation is precisely
    the transpose with inverse exchange in the node. The unit comparison is
    the existing `leftDerivedUpperStarUnitIso`. The supplied compactification
    comparison is the canonical
    `Etale.rightDerivedLowerShriekOfCompactificationPlusιIso`, not arbitrary
    user data. `cohomologicalUnitCounit` first applies the compactification-level
    pro-etale/etale comparison, then the canonical etale compactification
    comparison and etale counit, then the comparison-adjunction counit. Thus
    the primed counit is computed with the actual base-changed compactification
    and transported to the default exceptional functor. PASS.
11. The main predicate is the conjunction of precisely the preceding three
    clauses. It asserts no smoothness, dimension, orientation, or Tate
    identification. PASS.

Dependency-delivery reading: there are no new definition nodes. I read all five
initial dependency-record overrides as well as the separate exceptional module.
`def-weil-derived-tensor`, `def-weil-derived-pullback-tensor-hom` and
`def-weil-finite-tor-amplitude` name actual existing operations in the fixed-scalar
finite-level presentation. The exchange/projection override was removed after
the concurrent-landing check below. I opened the
signatures and bodies: derived tensor and closed Hom are the published derived
operations, and finite Tor is tested against arbitrary sheaves and intersected
with bounded constructibility. Their
notes explain the unusable earlier interfaces and explicitly delimit the finite
coefficient stage used here. No higher coefficient claim is consumed by this item.

For `def-weil-exceptional-inverse-image`, I read the source node's displayed D+
transport and `FiniteTypeExceptionalInverseImage.lean`. The named postponed
`finiteTypeHasBoundedBelowUpperShriek` provides the D+ preservation assertion of
that node for finite-type schemes over a field. Its docstring gives the complete
route: Nagata, a global fibre-dimension bound, the torsion proper cohomological
bound, exact extension by zero, the finite-width hypercohomology argument, and
t-structure orthogonality under the etale adjunction. The definition takes the
published exceptional functor with this proof instance. Its data are determined
by that adjunction, not chosen from a bare existence theorem. The main predicate
uses the same `rightDerivedUpperShriek` with this same proof instance. No global
`HasBoundedBelowUpperShrieks` hypothesis leaks into the main signature. PASS.

Edge cases: the empty source and empty target are admitted whenever the stated
morphism exists; no nonemptiness instance is present. On an empty source the
derived category has its zero object as unit, so the invertibility condition is
meaningful. K=0 remains in the universal tensor clause. Identity and isomorphism
base changes are among the quantified chosen squares. There is no index family
or dimension parameter to restrict. n=1 and ramified/nonregular coefficient
quotients are allowed; n=0 and ell=p are excluded exactly by the source. No
ramification-divisibility hypothesis, coefficient-field assumption or dimension
bound is introduced. `u` is arbitrary, schemes live in u, the small pro-etale site
keeps object universe u+1 and morphism universe u, and coefficient modules use the
required u+1 lift. The generic helpers also bind `u'`; no unbound variables,
universe equalities or independent smaller test universes were found.

Independent H4 searches (actually executed through msearch.py):

- LeanFinder query: "A morphism is cohomologically smooth when its exceptional
  pullback of the unit is an invertible complex and extraordinary pullback
  satisfies the canonical tensor and base change formulas". Eight hits about
  homological kernels and K-projective/derived-category fractions; no match.
- Loogle query: `"dualizingComplex"`. Zero hits.
- Mathlib grep query:
  `IsCohomologicallySmooth|tensor.?invertible|extraordinary.?pullback`. Zero hits.
- Independent `rg` over Mathlib, the slopmaster2 source, shared `lean/WeilConjectures`
  and shared `lean/Sheaf` also used cohomological-smoothness, dualizing, exceptional
  and bounded-below keywords. I opened the nearby
  `EtaleCohomology/Purity/Smooth/CohomologicallySmooth.lean` declaration.
  `AlgebraicGeometry.Etale.IsCohomologicallySmooth` is an etale predicate whose
  tensor-invertibility field does not require its inverse in D^b_ctf and whose
  base-change quantifier has another ambient domain. It is not an exact existing
  declaration of this finite-level pro-etale node. The upstream pro-etale
  dualizing object and canonical PF/exchange maps are reused rather than copied.
  No exact existing pro-etale three-clause predicate or unconditional field-base
  bounded-below helper was found.

H5/H6/H8/H9: all new definitions have real expressions and no internal sorry.
The only postponed theorem in these two files is the named bounded-below
preservation theorem above. Every declaration has a source/blueprint docstring;
that theorem carries its proof route. The item is a definition with `proof=[]`,
so no omitted theorem proof steps are required in its docstring. All lines fit
100 characters, no local notation/private definition/local instance is introduced,
and names have the proper namespaces. Each nonexisting `lean.statement` is a
verbatim signature substring of its module (beginning at `def`, excluding the
`noncomputable` modifier). Nothing is proved in this delivery.

Mismatches and changes: no mathematical mismatch was found. The initial dry run
passed at 692bc6e0b5, but disclosed a newly reviewed exchange/projection delivery.
I read the now-landed `Sheaf.Paper.ExchangeProjection` module and the live node
record. Its `finiteExchangeProjection` is exactly the triple of the published
direct exchange, compact-support exchange and projection maps already used here;
it accepts arbitrary base change and our lifted coefficient ring. The stronger
context of its `coefficientExtensionExchangeProjection` specialization is not
needed because the same node also records `finiteExchangeProjection`. I removed
the sandbox override of `def-exchange-projection` and replaced the main module
import of `Derived.LowerShriekBaseChange` by `Sheaf.Paper.ExchangeProjection`,
which publicly imports that module and the projection interface. The existing
formulas are exactly the second and third components of its finite wrapper.
Thus the landed dependency record and all its higher-stage declarations are
preserved. No canonical map, hypothesis, conclusion, signature, or definition
body was changed. The other dependency repairs remain necessary. The worker
report remains in place; its exchange-record paragraph is superseded here. The worker's shorthand module reference
`...ProEtale.UpperLowerStar` refers concretely to `UpperLowerStar/Defs.lean` and
`Derived/UpperLowerStar.lean`, as checked above.

Validation: I reran the prescribed scompile.py with both sibling files. Both
compiled in sandbox and library modes with no errors or warnings; library runs
were 3.6 s for `FiniteTypeExceptionalInverseImage` and 15.0 s for
`CohomologicalSmoothness`, under the unchanged 60-second limit. No global build
or direct git mutation was run.

After this import repair, both modules and the prescribed delivery checks are
rerun below; the earlier clean compilation is not used as evidence for an
unchecked changed import.
The post-repair scompile.py run also passed cleanly for both siblings in sandbox
and library modes: library times 5.0 s and 19.3 s respectively, with no warnings.
The final post-repair `deliver2.py --no-push` passed compilation and server
preflight at 8206ac4fd3. It no longer delivers an exchange/projection node override.

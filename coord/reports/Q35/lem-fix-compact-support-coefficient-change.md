## Worker report

Item: `lem-fix-compact-support-coefficient-change`, group Q35, stage 2.
The delivery states the B-linear compact-support coefficient comparison, its invertibility
for the actual finite quotient rings, and all three requested compatibilities. All postponed
proofs are named theorems with `sorry` and source/proof docstrings. No definition contains
`sorry`. No assertion is made that scalar restriction on derived morphisms is faithful.

The source checked is the blueprint node, order 1824, at
`sec-smooth-purity/sk-prop-sf-trace-perfectness/lem-fix-compact-support-coefficient-change.md`.
The available full blueprint text was read in `/home/ubuntu/work-bp/sheaf/literature/blueprint/master/blueprint/`.
The current DAG's nine-step proof fixes the B-linear normalization more explicitly than the
original short blueprint proof. This delivery follows that normalization. There is no statement
correction and no disputed mathematical statement.

### Hypotheses and clauses

- The finite-field datum is `(D : WeilConjectures.FiniteFieldDatum.{u})`. The distinct
  coefficient prime is `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`.
- The finite extension is `(E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]`. The existing `Padic.coefficientExtensionRing l E n`
  is precisely the quotient of the valuation ring by the nth power of its uniformizer ideal.
- `(m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)` are exactly the allowed indices. The map is
  `Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)`, lifted by `RingHom.ulift`.
  The source quotient is exponent n and the target exponent m. Finiteness of both rings
  is obtained from `Padic.finite_coefficientExtensionRing`, not assumed additionally.
- X and Y are schemes of universe u with `.Over (Spec (CommRingCat.of D.k))` and
  `[f.IsOver ...]`. Their structure morphisms have `LocallyOfFiniteType` and `QuasiCompact`,
  expressing the finite-type schemes of the finite-field context. The morphism f has
  `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`.
- `(c : Compactification f)` fixes the same compactification used by the recorded
  definition of compact support. `Rf_!(c)[ModuleCat ...]` is exactly the recorded
  `rightDerivedLowerShriekOfCompactification`: D(j!) followed by Rp*. All comparisons
  are for every such c, so no special compactification or functor is postulated.
- K belongs to the actual unbounded derived category of sheaves of A-modules on the
  small pro-etale site. `_hK : DerivedCategory.constructibleFiniteTor ... X K` combines
  bounded constructibility with finite Tor amplitude. The coefficient ring is
  `ULift.{u+1} A_{E,n}`, so the category fits the fixed-scalar presentation's module
  universe u+1 without identifying site object and morphism universes. A ring-equivalence
  lift changes no coefficients mathematically.
- `CoefficientTensorModel φ T K` packages an object, its map from K after scalar
  restriction, and the published `Sheaf.IsDerivedBaseChange` universal property.
  It therefore represents the actual tensor K tensor_A^L B, including its B action
  and canonical unit. It is not an unspecified map or an object with an arbitrary
  isomorphism to a tensor. The existing universal property determines it up to unique
  compatible isomorphism. `nonempty_coefficientTensorModel` explicitly states existence
  for every K and arbitrary ring map, so M and N do not add an existence hypothesis.
- M is this tensor on X. N is the same tensor of `Rf! K` on Y. The canonical arrow
  `compactSupportCoefficientComparison c M N` is the inverse universal-arrow bijection
  applied to `Rf!` of M.unit followed by the canonical scalar-restriction comparison.
  Its type is `N.obj ⟶ (Rf!_B).obj M.obj`, in D(B), as required.
- `finiteReductionCompactSupportComparison` substitutes the actual quotient map;
  `finiteReductionCompactSupportComparison_isIso` states `IsIso` of this very arrow.
  No flatness, freeness, or perfection of B over A is assumed.
- Successive reductions are `compactSupportCoefficientComparison_comp`. The model
  `.comp` is constructed from the two units using the published scalar-restriction
  composition isomorphism and `IsDerivedBaseChange.comp`. The equation compares the
  composite with the direct comparison as actual C-linear arrows, including identity
  reductions. Generic finite-ring notation permits substitution of every tower of the
  specified coefficient quotients.
- Pullback compatibility is `compactSupportCoefficientComparison_pullback` for every
  `IsPullback g' f' f g`. It uses the recorded actual compactification exchange map and
  `c.ofIsPullback sq`, not a supplied square-commutativity hypothesis. `.pullback`
  includes the canonical inverse-image/scalar-restriction square, with its universality
  as a named theorem. The equality is in D(B) on Y'.
- Counit compatibility is `directImageCoefficientComparison_counit`, which equates
  Lf*_B of the actual proper-factor comparison followed by the B-counit to scalar
  extension of the A-counit. The open unit equation is `openCoefficientComparison_unit`.
  `compactSupportCoefficientComparison_factorization` identifies the full comparison
  with the direct-image comparison followed by Rp*_B of the open comparison. Together
  these give exactly the proper counit/open unit compatibility defining the compactified
  projection transformation of `def-exchange-projection`.

### Existing notions and dependency declarations

The primitive mathematical notions are reused, rather than privately redefined:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its coefficient-definition
  import: `Padic.coefficientExtensionRing`, `Padic.coefficientExtensionIdeal`,
  `Padic.finite_coefficientExtensionRing`.
- Mathlib: `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `IsProper`,
  `IsOpenImmersion`, `Compactification`, `IsPullback`, `Ideal.Quotient.factor`,
  `Ideal.pow_le_pow_right`, `ULift`, `RingHom.ulift`.
- `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek`:
  `rightDerivedLowerShriekOfCompactification`, the recorded compact-support declaration.
- `Sheaf.Paper.ExchangeProjection` and the smaller upstream modules it imports:
  `rightDerivedLowerShriekOfCompactificationBaseChangeMap`,
  `projectionMapOfCompactification`, the actual functors and their adjunctions.
- `WeilConjectures.SixFunctors.ProEtale.Derived.RestrictScalars`:
  `leftDerivedUpperStarRestrictScalarsIso`, `Sheaf.derivedRestrictScalars`,
  `Sheaf.derivedRestrictScalarsCompIso`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange` (transitive import):
  `Sheaf.IsDerivedBaseChange`, its actual definition by a bijection of morphisms, and
  `.comp`. `CoefficientTensorModel` only packages this existing notion with its object
  and unit for readable types; no second tensor operation is defined.
- `WeilConjectures.SixFunctors.ProEtale.Derived.TorAmplitude`:
  `DerivedCategory.constructibleFiniteTor`, the bounded constructible/finite Tor
  intersection in this fixed-scalar presentation. Its bounded-constructible component
  is the published finite-coefficient etale-origin presentation.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`:
  `Functor.rightDerivedFunctorObjQIso`, used in the full normalization equation.
- The two dependency modules described below supply the canonical compact-support and
  direct-image restriction interfaces.

The finite Tor node previously recorded `Sheaf.Paper.FiniteTorAmplitude` in the intrinsic
constant-ring-sheaf presentation, while the recorded compact-support and exchange nodes
use the fixed-scalar presentation. Its current record now exposes the existing upstream
`DerivedCategory.constructibleFiniteTor`, exactly as this delivery already uses. Importing the two pro-etale frameworks together
fails with duplicate `AlgebraicGeometry.ProEtale.lowerStarComp` declarations. Accordingly
this file uses the smaller published fixed-scalar predicates and operations. The upstream
`Derived.Constructible` docstring explicitly identifies its finite-coefficient predicate
with intrinsic constructibility by `lem-sf-proetale-constructible-origin` (already a proof
dependency of this item). This does not replace finite Tor amplitude by boundedness or
by perfection. It does not use etale origin at integral or rational coefficients.

The umbrella `def-weil-derived-pullback-tensor-hom` now has an existing upstream record
exposing its finite-level operations. Only that finite-level clause is involved here:
its actual inverse-image and tensor operations are the published operations just named,
and scalar extension is the existing universal notion above. No integral, rational, algebraically closed, or internal-Hom operation is
needed to type this finite-level lemma; this delivery does not attach a misleading partial
record to that all-stage umbrella node.

The stated proof-plan imports include `DerivedChangeOfRingsIndependentCoefficients`,
`KFlatResolutionIndependentCoefficients`, `ChangeOfRingsTensorComparison`,
`ProjectionMateExact`, `RingedExchangeTensorCoherence`, and the upstream etale
`Derived.ProjectionFormula`. Other recorded proof interfaces that import the incompatible
new constant-ring pro-etale framework cannot be imported alongside the recorded compact
support functor; their precise mathematical uses remain named in the theorem's nine-step
proof docstring. No downstream theorem is used to define its own canonical map.

### Edge cases checked

- m=n is allowed. The quotient map is the canonical identity quotient map; none of the
  definitions requires a strict reduction. Successive composition includes identity maps.
- m=1 is allowed, and n is positive by hm.trans hmn. The excluded exponent zero is not
  inadvertently used to obtain a finiteness instance.
- For Z/l^2 to Z/l the quotient is nonflat. Neither the universal model nor any comparison
  assumes it flat; the finite-free scalar-extension API was specifically rejected here.
- Zero K, empty X, and an empty compactification cause no undefined choice or nonempty
  restriction. Every tensor model still has its universal arrow; every functor is the
  actual derived functor. No connectedness or nonempty scheme is assumed.
- Pullback g is arbitrary, including an identity or an empty base change. The equation
  uses the canonical exchange map, not an assumed isomorphism or a smooth-only square.
- Equality statements are in the reduced-coefficient category. Exact scalar restriction
  reflects isomorphisms but is never used as a faithful functor on derived morphisms.
- All variables and universes are explicit; `autoImplicit` is false. The small pro-etale
  site and its u+1 coefficient convention are retained.

### Searches

1. `msearch.py ... leanfinder` with query "Derived compactly supported direct image
   commutes with derived extension of finite coefficients for bounded constructible
   complexes of finite Tor amplitude": eight unrelated derived/Ext/fraction results;
   no statement of this map with the requested coherences.
2. `msearch.py ... loogle` with `"changeOfRings", "rightDerived"`: no results.
3. `msearch.py ... grep` with
   `lowerShriek.*[Ss]calar|[Cc]oefficient.*[Cc]hange|[Cc]ompact[Ss]upport.*[Tt]ensor`:
   seven unrelated ordinary elliptic-curve coefficient-change hits.
4. `rg` of old upstream, current `lean/WeilConjectures`, and `lean/Sheaf`, including
   the exact item id, scalar-extension, compact-support, tensor, restriction, and
   coefficient-reduction names: no full general-f theorem with the three clauses.
   Adic-system occurrences concern compactly supported global cohomology, a specialization.
5. Read the full relevant upstream scalar-extension interface: its flat/finite-free
   hypotheses exclude the quotient reduction. Read `DerivedBaseChange` instead; its
   universal property works for the actual nonflat derived extension.
6. Read `FiniteCoefficientReductionFlatModel` and the integral coefficient maps:
   the actual quotient homomorphism already is `Ideal.Quotient.factor`, with ULift.
   This delivery uses that primitive map directly, without duplicating a named reduction.
7. Read both direct-image/restriction encodings, the exact compact-support declaration,
   the actual inverse-image/restriction isomorphism and the open adjunction. They provide
   canonical mates, but no usable full compact-support restriction/coherence record.

## Dependency modules

`lem-sf-compact-support-restriction-of-scalars` is an existing genuine prerequisite.
Since the worker draft, Q43 recorded its intrinsic constant-ring presentation; this
packet supplies the fixed-scalar interface repair required by the recorded Rf! imports. Its module `Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars`
defines the actual open restriction comparison as the adjunction mate of the inverse-image
comparison, names its invertibility obligation, and forms the specified proper/open composite.
It states transitivity with the actual restriction composition isomorphisms. Finiteness is
explicit. A chosen compactification contains its open/proper factors; no separate arbitrary
comparison data is assumed. The construction also works without the coefficient-invertibility
restriction, so it applies in particular in the stated invertible finite-torsion setting.

`lem-weil-proetale-direct-image-restriction-of-scalars` has an intrinsic constant-ring record
that cannot coexist with the fixed-scalar compact-support imports, due to the duplicated
`AlgebraicGeometry.ProEtale.lowerStarComp`. Its replacement module
`Sheaf.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage` is a section 1(B)
interface repair. It uses the mathematically equivalent fixed-scalar presentation of the
same modules and the same canonical inverse-image mate. It gives an actual normalized
natural isomorphism and the complete K-injective resolution formula, including the
quasi-isomorphism of the pushed-forward resolution. In this presentation the ordinary
pushforward/restriction square is definitionally the identity, so its extra comparison
factor disappears. It never assumes that restriction preserves K-injectives. Only this
node's `lean` field changes; its original statement and dependencies stay unchanged.

Both existing prerequisite ids are added to this item's statement dependencies, and their
node records and modules are included in the packet. There are no new independent nodes.

### Validation

All delivered files are compiled separately, in dependency order, using the prescribed
`scompile.py` wrapper. The final dry run is `deliver2.py Q35
lem-fix-compact-support-coefficient-change --no-push`. The independent second reader
will add their own second-reading section and deliver; this report does not claim it.

## Earlier second reading (a previous round; superseded)

I did not author these modules. I read the item's node and its original blueprint
file (order 1824), the operation-unit conventions, all eleven statement-dependency
records, the two delivered dependency nodes and their modules, and the actual
signatures/definitions used in the main module. I also read Stacks
`more-etale.tex`, labels `lemma-projection-formula-Rf-lower-shriek` and
`remark-Rf-lower-shriek-change-of-rings` (0GL5/0GL6), and
`sites-cohomology.tex`, labels `lemma-derived-pushforward-composition`,
`lemma-modules-abelian-unbounded`, and `lemma-j-shriek-and-tensor`
(0D6E/0D6J/0GL1), in `/home/ubuntu/work-bp/sheaf/literature/stacks-project/`.
The Stacks projection formula assumes qcqs schemes and separated finite-type f;
the finite-type schemes over the field in this item are Noetherian, hence qcqs.
The ringed-topos direct-image composition and open tensor statements impose no
flatness assumption on the coefficient reduction.

The statement checklist, made before checking the Lean, and its rendering are:

1. Global finite-field datum, coefficient prime distinct from p, and a finite
   extension E/Q_l: `D : WeilConjectures.FiniteFieldDatum`, `l : ℕ`,
   `[Fact l.Prime]`, `_hl : l ≠ D.p`, `E : Type u`, `[Field E]`,
   `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`. I opened
   `FiniteFieldFiber.lean`: D contains p, positive a, q=p^a, the finite base
   field and its algebraic closure, with the specified field/algebra instances.
   The finite-type geometric-field setting is the one used by this unit. Verdict:
   same datum; no replacement of a coefficient ring by a field.
2. Separated finite-type f:X→Y between finite-type schemes in that setting:
   `.Over (Spec (CommRingCat.of D.k))` for X and Y, finite-type structure
   morphisms rendered by `LocallyOfFiniteType` and `QuasiCompact`, and
   `(f : X ⟶ Y) [f.IsOver ...] [IsSeparated f] [LocallyOfFiniteType f]
   [QuasiCompact f]`. I opened the Mathlib property declarations: these are
   precisely the locally finite-type, quasi-compact and separated conditions.
   There is no smoothness, properness of f, connectedness, or extra explicit
   Noetherian assumption. Verdict: matches.
3. A=A_{E,n}, B=A_{E,m}, 1≤m≤n, and the canonical reduction A→B:
   `(m n : ℕ) (hm : 1 ≤ m) (hmn : m ≤ n)` and
   `Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)`, for the two
   `Padic.coefficientExtensionIdeal`s, followed by `RingHom.ulift`. I read
   `CoefficientExtension.lean`: the ideal is `(span {uniformizer})^n`, and
   the ring is its quotient in the actual valuation ring. The direction is
   exponent n to exponent m. `finite_coefficientExtensionRing`, which I also
   read, supplies finiteness using hm and hm.trans hmn. Verdict: actual quotient
   coefficients and map, with no flatness or finite-projective hypothesis.
4. K is bounded constructible and has finite Tor amplitude:
   `K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
   (ModuleCat (ULift (Padic.coefficientExtensionRing l E n))))` and
   `_hK : DerivedCategory.constructibleFiniteTor ... X K`. I opened the upstream
   `Derived.TorAmplitude`, `Derived.Constructible` and the underlying
   `DerivedCategory.TorAmplitude` definitions. The predicate is the intersection
   of bounded constructibility and existence of an interval testing tensor with
   every degree-zero module sheaf. It does not assert that boundedness implies
   finite Tor amplitude. I compared the recorded `FiniteTorAmplitude.lean`
   finite-level predicate as well: it expresses the same intersection in the
   intrinsic constant-ring-sheaf presentation. The upstream finite-coefficient
   constructible predicate uses the equivalent etale-origin reading; its
   docstring explicitly cites `lem-sf-proetale-constructible-origin`. That
   node's clause (ii), which I read, identifies the two classes of objects.
   This finite-level use does not import its invalid integral analogue. Verdict:
   same mathematical input in the fixed-scalar presentation required by Rf!.
5. The chosen compactification and compact-support functor: `(c : Compactification f)`
   and `Rf_!(c)[ModuleCat ...]`. I opened the recorded `Derived.LowerShriek`
   declaration: it is exactly `D((c.i)_!open) ⋙ R((c.g)_*)`, on the unbounded
   derived categories. Quantification is over every c, including the chosen
   compactification used by the definition node. No ambient exceptional right
   adjoint or finite cohomological dimension on all pro-etale sheaves is assumed.
   Verdict: the recorded compact-support candidate, with its correct domain.
6. Source and target of the comparison are `(Rf!_A K) tensor_A^L B` and
   `Rf!_B (K tensor_A^L B)` respectively. `M` models the input tensor on X,
   `N` the output tensor on Y; the map is
   `finiteReductionCompactSupportComparison ... c M N :
   N.obj ⟶ (Rf!_B).obj M.obj`. I retrieved the current published
   `Sheaf.DerivedBaseChange` source with `scompile.py --source` and read
   `Sheaf.IsDerivedBaseChange`: it is bijectivity of the map induced by the
   specified unit into scalar restriction, for every B-derived object. Thus the
   model packages the existing scalar-extension universal property, rather than
   an arbitrary tensor-like object. `nonempty_coefficientTensorModel` states
   existence for every input; the units make the model unique up to unique
   compatible isomorphism. The comparison is constructed by this bijection and
   the actual proper/open restriction isomorphism. Verdict: a canonical B-linear
   map, not an A-linear map with an unspecified lift. The main theorem states
   `IsIso` of this exact map.
7. Compatibility with successive reductions: `compactSupportCoefficientComparison_comp`.
   Its first route is scalar extension of the A→B comparison using `.map`, then
   the B→C comparison; its second route is the A→C comparison using `.comp`
   at both endpoints. I checked `.comp` uses the published restriction
   associator and `IsDerivedBaseChange.comp`, not an arbitrary identification.
   The generic finite rings include every requested quotient tower. Verdict:
   the equality is in D(C), with the canonical associativity identifications.
8. Pullback compatibility: `compactSupportCoefficientComparison_pullback`.
   Its square is `IsPullback g' f' f g`; its compactifications are c and
   `c.ofIsPullback sq`. Both geometric exchange arrows are the recorded actual
   `rightDerivedLowerShriekOfCompactificationBaseChangeMap`, one for each
   coefficient ring. `.pullback` retains the published restriction/pullback
   isomorphism in its unit, whose universality is separately stated. Both
   routes have the same B-derived endpoints on Y'. Verdict: the requested
   coefficient/geometric exchange square, without assuming it commutes.
9. Compatibility with the counits defining projection:
   `directImageCoefficientComparison_counit` equates B-pullback of the proper
   comparison followed by the B-counit with scalar extension of the A-counit.
   `openCoefficientComparison_unit` gives the corresponding open unit equation;
   `compactSupportCoefficientComparison_factorization` ties these factors to
   the full coefficient comparison. I read `ExchangeProjection.lean` and the
   upstream `Derived.LowerShriekProjection` definition: the projection map is
   precisely the proper counit mate followed by the open projection comparison.
   The displayed equations therefore fix the counits/units defining that map,
   as requested, and do not merely identify its endpoints. Verdict: matches.

Dependency packet reading: there are no new definition nodes. For
`lem-sf-compact-support-restriction-of-scalars`, I checked the node's specified
proper/open composite and transitivity against `compactSupportRestrictionIso`
and `_comp`. `fixedScalarRestrictionOpenMap` is the inverse mate of the inverse
canonical pullback square, in the correct direction, with its invertibility a
named postponed theorem. For
`lem-weil-proetale-direct-image-restriction-of-scalars`, I opened the earlier
intrinsic module as well as this replacement. The earlier one uses constant-ring
module sheaves and the finite-coefficient upper/lower-star framework; the packet
uses the fixed-scalar framework required by the recorded Rf!. The replacement's
mate uses the actual derived adjunctions and canonical pullback square.
`fixedScalarRestrictionDirectImage_kInjective` includes both that f_*(j) is a
quasi-isomorphism and the normalized equation: after canonical exact-functor and
K-injective identifications, the forward comparison is the inverse of f_*(j).
This is exactly the dependency's extra normalization clause; restriction need
not preserve K-injectives. The construction and transitivity of the compact-support
isomorphism use these maps, not choices from an unidentified Nonempty isomorphism.
The two lean.note entries describe why these dependency interfaces are supplied.

Edge cases: m=n is permitted by hmn (and included in successive composition),
m=1 is permitted, and n=0 cannot satisfy hm.trans hmn, exactly as in the node.
There is no excluded empty scheme, zero K, empty stratum, identity pullback, or
empty base change. No index set, cardinality, or nonemptiness assumption occurs.
The reduction Z/l²→Z/l is allowed despite its nonflatness. The characteristic
condition is explicitly l≠D.p; the field's characteristic makes l invertible
on these schemes. Universe u is declared explicitly; the small pro-etale site
keeps object universe u+1 and morphism universe u, while module values and lifted
coefficients are in u+1. ULift changes the presentation by a ring equivalence,
not the coefficients or their quotient exponents. No equality of site object
and morphism universes was introduced. All theorem variables are bound under
`autoImplicit false`.

Independent searches (different wording from the worker):

- LeanFinder: “Derived extension of scalars commutes with compactly supported
  pushforward and reduction modulo a power of a uniformizer”. Eight hits about
  adic completion and BDeRham; none states this result.
- Loogle: `"lowerShriek", "tensor"`. No hits.
- LeanSearch: “Derived pushforward with proper support commutes with extension
  of finite torsion coefficients”. Service returned Internal Server Error;
  recorded as unavailable, with no inferred negative result.
- Tool grep: `([Ee]xtend[Ss]calars|[Bb]ase[Cc]hange|[Rr]estrict[Ss]calars).*(lowerShriek|[Cc]ompact)`.
  Six unrelated compact-neighborhood/base-change-property hits.
- Direct rg in Mathlib, upstream WeilConjectures, and project lean/Sheaf for
  coefficient comparison/change, scalar restriction, lowerShriek and compact
  support. I opened `SfDerivedDirectImage`, the recorded intrinsic direct-image
  restriction module, `ExchangeProjection`, the upstream restriction/pullback
  source (retrieved with `scompile.py --source`), and the universal derived
  base-change source. They provide the reused primitives or specialized/incompatible
  presentations, not an existing full declaration of this node. Exact searches
  for the packet's new public names found no existing duplicate.

No mathematical mismatch was found, so I preserved the Lean modules and the node
statements/signatures. The independent search coverage and this clause-by-clause
reading are added to the report. Every postponed theorem has only `sorry`, every
definition has actual data or data uniquely determined by a named theorem, and
all public declarations have source/blueprint docstrings. The main proof docstring
covers the nine DAG proof steps in five grouped paragraphs (scalar adjunction,
etale origin and Tor bounds, proper transport, open factor, three coherences).
All three files satisfy the 100-column convention; there are no file-local
notations/instances, private definitions, unbound universes, or proved theorems.
The three recorded primary signatures were compared with their file signatures
with whitespace normalized; they agree. No statement_change or citer audit is
needed because no mathematical statement was corrected.

Validation and delivery-tool failure: the explicit `scompile.py Q35
lem-fix-compact-support-coefficient-change` invocation with all three sibling files
completed successfully, with no errors or warnings. The subsequent prescribed
`deliver2.py ... --no-push` also passed compilation (its local shared-overlay cache
lost ProjectionMateExact.olean, so the wrapper automatically confirmed against the
current server sources). It then failed preflight before pushing anything:

- The supplied `lem-sf-compact-support-restriction-of-scalars` was classified as
  outside the item's prerequisite closure.
- Its addition to stmt_deps was consequently rejected, and its module was
  consequently classified as having no owning node.

This classification is a tool fault, not a missing mathematical prerequisite:
the dependency is explicitly in the item's proof_deps on the base and as delivered,
and the human's 2026-10-16 instruction authorizes stating it in this delivery.
Read-only inspection of both current local and server `tools/stage2_delivery.py`
shows `_dep_closure` begins with all direct prerequisites but stops its depth-first
scan at `len(seen) < 3000`. A read-only full traversal of the shared DAG from this
item's statement/proof prerequisites, including the two delivered prerequisites,
contains 10,817 nodes. Since descendants are added to the same stack as the
remaining roots, that cutoff can leave a direct root unvisited. The reported
failure rejects precisely such an explicit direct prerequisite. The later two
preflight failures are consequences of that failed classification.

I did not alter coordinator tools, change the mathematical statement to evade
preflight, remove the required dependency, or bypass the preflight. No delivery
was pushed. This packet is mathematically reviewed and compiles, but requires the
maintainer/launcher to repair the dependency-closure scan before the prescribed
dry run can print OK and delivery can proceed. The only changes from the worker
packet are the independent search records and this review/validation report.

## Retry validation by Q35

At 2026-10-16T02:15:27+00:00, reran the prescribed
`python3 /home/ubuntu/weil-launcher-nt/deliver2.py Q35 lem-fix-compact-support-coefficient-change --no-push`.
All three module compiles passed with no reported errors or unexpected warnings.
Preflight again failed with the same three reasons quoted above: it excludes
`lem-sf-compact-support-restriction-of-scalars` from the prerequisite closure, then
rejects its addition to stmt_deps and its owning module as consequences. Nothing
was pushed.

Read-only reinspection confirmed that `tools/stage2_delivery.py` still terminates
`_dep_closure` at `len(seen) < 3000` (line 738). An uncapped traversal of the
current shared DAG from the item's statement/proof prerequisites again gives
10,817 nodes. The rejected node is a direct proof prerequisite on the base and
a direct statement prerequisite as delivered. The rejection is therefore a
reproduced tool failure. The contract reserves coordinator-tool changes to the
maintainer; no tools or read-only repository files were modified or bypassed.

Rechecked the three primary signature records and full declaration lists against
their files: they agree. Every theorem body is exactly `by sorry`, and every Lean
line is at most 100 characters. The actual quotient map, nonflat reductions,
identity reduction, pullback square and proper/open unit-counit normalizations
remain as reviewed above. No mathematical or Lean-source repair was needed.

## Retry validation by Q35 (third tool-failure attempt)

At 2026-10-16T02:25:30+00:00, the prescribed `deliver2.py Q35
lem-fix-compact-support-coefficient-change --no-push` retry again compiled all
three delivered modules, one file at a time under the 60-second limits. No Lean
error or unexpected warning was reported. Server preflight again rejected the
compact-support restriction dependency, its addition to stmt_deps, and its owning
module. Nothing was pushed.

Read-only inspection of `tools/stage2_delivery.py`, lines 729–756, confirms that
`_dep_closure` starts with both dependency fields on the base and as delivered,
but stops at `len(seen) < 3000`. The rejected
`lem-sf-compact-support-restriction-of-scalars` is explicitly present in the
item's base proof_deps (and in its delivered stmt_deps). An uncapped traversal
of the current shared DAG reaches 10,817 nodes and includes this prerequisite;
a bounded traversal reaches 3,000 and misses it. Lines 934–936 accept supplied
prerequisites in stmt_deps only after the earlier dependency classification,
so the other two failures follow from the closure-cap rejection.

The sandbox item differs from the shared node only in lean and stmt_deps; each
dependency node differs only in lean. No mathematical statement was changed,
no required prerequisite was removed, and no preflight was bypassed. This is
an actual coordinator-tool refusal of the authorized same-delivery prerequisite.
`tools/README.md` reserves coordinator-tool repair to the maintainer. The three
compiling modules and the earlier independent second reading are preserved.


## Retry validation by Q35 (fourth tool-failure attempt)

At 2026-10-16T02:42:20.967390+00:00, reran the prescribed
`python3 /home/ubuntu/weil-launcher-nt/deliver2.py Q35
lem-fix-compact-support-coefficient-change --no-push`. All three delivered Lean
modules again compiled successfully, one file at a time with the wrapper's
60-second limit. Server preflight still rejected the direct prerequisite
`lem-sf-compact-support-restriction-of-scalars`, its addition to stmt_deps,
and its owning module. Nothing was pushed.

Read-only checks found that the current shared base still has no lean record
for that restriction node, and `scompile.py --source
Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars` reports
`Module source unavailable`. The base item's proof_deps explicitly contains
the rejected node. Its current source still has the closure limit
`while todo and len(seen) < 3000` in tools/stage2_delivery.py line 738.
The other supplied prerequisite, the direct-image restriction interface repair,
is accepted by preflight and is not the source of this failure.

An investigation of the closure ordering showed that the capped depth-first
traversal can visit this direct prerequisite with some Python hash seeds and
miss it with others. A second full dry-run invocation with local
`PYTHONHASHSEED=2` again passed every compile but produced the same three
server-preflight errors; it did not resolve the refusal. No coordinator tool
was modified, no preflight was bypassed, and no mathematical statement or
required dependency was changed. The unchanged, compiling packet remains in
the sandbox for a coordinator-tool repair by the maintainer.


## Retry checks by Q35 (fifth attempt, successful)

Reopened the main node, all statement-dependency statements and records, all three
Lean modules, the original blueprint statement, and the relevant published
universal-base-change, inverse-image comparison, compact-support, Tor-amplitude,
exchange and projection definitions. The actual original blueprint file was
read from the available literature mirror. Rechecked Mathlib's finite-type,
quasi-compact, separated and proper class declarations. No Lean repair was
needed. Updated the two report passages whose dependency records had changed:
the finite-Tor and finite-stage operation nodes now record the existing upstream
interfaces already used by this packet.

Repeated Loogle (`"lowerShriek", "tensor"`: zero results), LeanFinder
(`Derived compactly supported pushforward commutes with extension of finite
torsion coefficients and successive coefficient reduction`: eight unrelated
results), tool grep (`lowerShriek.*[Ss]calar|[Cc]oefficient.*[Cc]hange|[Cc]ompact[Ss]upport.*[Tt]ensor`: seven unrelated results),
and direct upstream/project searches for the new comparison names and item id
(no existing matches). The search wrapper preserved its raw results in
`searches.jsonl`. `scompile.py --source
Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars` still reports
`Module source unavailable`; the missing prerequisite must remain in this delivery.

Using the project's declaration parser, confirmed all three primary signatures
and their complete declaration lists against their node records. All three
JSON files use the required format; all Lean lines satisfy the 100-column limit.
The item differs only in lean and the two added statement prerequisites; each
prerequisite node differs only in lean. A fresh uncapped prerequisite traversal
reaches 10,817 nodes, and the compact-support restriction node remains an explicit
direct proof prerequisite on the base. The local coordinator source still has
`while todo and len(seen) < 3000` in `_dep_closure`.


At 2026-10-16T02:54 UTC, the prescribed `deliver2.py Q35
lem-fix-compact-support-coefficient-change --no-push` completed with exit code 0:
`OK (dry run): commit 8c7848bcde passes the preflight and compiles; nothing pushed`.
All three files passed compilation with no errors or unexpected warnings, and
server preflight accepted both prerequisite nodes and their owning modules.
The earlier closure-cap rejection is resolved in the current server tool.
The historical failure notes above describe earlier attempts, not a remaining
blocker. The current local coordinator copy still has the old cap, but it is
not the server preflight used by this wrapper. No coordinator code was edited.

## Second reading by Q35

I am a fresh second reader and did not write these declarations. I read the three
sandbox modules and node records, the source blueprint file at order 1824 in the
work-bp literature mirror, the statement-dependency records, and their actual
interfaces. I also read Stacks more-etale.tex, labels
lemma-projection-formula-Rf-lower-shriek and
remark-Rf-lower-shriek-change-of-rings (0GL5/0GL6), and
sites-cohomology.tex, labels lemma-derived-pushforward-composition,
lemma-modules-abelian-unbounded, and lemma-j-shriek-and-tensor
(0D6E/0D6J/0GL1). The Stacks compact-support setting is qcqs with separated
finite-type morphisms and torsion coefficients; finite-type schemes over the
field here satisfy these geometric conditions. The coefficient map need not be flat.

My statement checklist and comparison with Lean are:

1. The finite-field datum and coefficient extension: `D : FiniteFieldDatum.{u}`,
   `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p`, and the field, algebra and
   finite-dimensional instances on `E`. I opened FiniteFieldFiber.lean and the
   actual coefficient-extension definitions. Verdict: the specified datum,
   prime and finite extension, not field coefficients substituted for A or B.
2. Finite-type schemes and separated finite-type f: X and Y have `Over` the
   spectrum of D.k, their structure maps have `LocallyOfFiniteType` and
   `QuasiCompact`, and f has `IsOver`, `IsSeparated`, `LocallyOfFiniteType`,
   `QuasiCompact`. I read the Mathlib property signatures. Verdict: the node's
   field-base hypotheses, without smoothness, properness of f or nonemptiness.
3. A=A_{E,n}, B=A_{E,m}, 1≤m≤n: `Padic.coefficientExtensionRing`, `hm`, `hmn`;
   the scalar map is `Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)`.
   The ideal is the nth power of the chosen uniformizer ideal. `RingHom.ulift`
   only transports the coefficients to the module universe. Finiteness comes
   from `finite_coefficientExtensionRing`. Verdict: correct quotient and direction.
4. Bounded constructible K of finite Tor amplitude: K is in the unbounded
   derived category of pro-etale A-module sheaves and `_hK` is
   `DerivedCategory.constructibleFiniteTor`. I read TorAmplitude.lean,
   Constructible.lean and the site-independent torAmplitudeIn definition:
   this is bounded constructibility intersected with a uniform interval tested
   on every degree-zero sheaf. The finite-coefficient etale-origin presentation
   agrees with the intrinsic predicate at these coefficients, as documented
   with lem-sf-proetale-constructible-origin. Verdict: exact finite-stage input.
5. Compact support: `c : Compactification f` and `Rf_!(c)[ModuleCat ...]`.
   I opened Derived.LowerShriek: this is D(j!) followed by Rp*, not the right
   derived functor of the underived composite. Verdict: the recorded candidate,
   quantified over every chosen compactification.
6. Canonical comparison and invertibility: `CoefficientTensorModel` packages
   the existing `Sheaf.IsDerivedBaseChange` universal arrow, which I opened in
   DerivedBaseChange.lean. `nonempty_coefficientTensorModel` states existence
   for all inputs, including nonflat maps. The inverse universal bijection
   defines `compactSupportCoefficientComparison`; its specialized version has
   source N.obj=(Rf! K) tensor_A^L B and target Rf!_B M.obj. The main theorem
   asserts `IsIso` of this exact B-linear map. Verdict: canonical tensor map
   and isomorphism, with no arbitrary lift or faithful-restriction hypothesis.
7. Successive reductions: `compactSupportCoefficientComparison_comp` equates
   scalar extension of the first comparison followed by the second with the
   direct comparison, using `.comp` and the actual restriction associator.
   Verdict: equality in the final coefficient category, including identities.
8. Pullback: `compactSupportCoefficientComparison_pullback` uses `IsPullback`,
   `c.ofIsPullback`, and the actual coefficientwise
   `rightDerivedLowerShriekOfCompactificationBaseChangeMap`. Model.pullback
   uses the published inverse-image/restriction square. Verdict: the two
   geometric/coefficient routes agree, without assuming their commutativity.
9. Counits defining projection: `directImageCoefficientComparison_counit`
   identifies the B-counit transpose with extension of the A-counit;
   `openCoefficientComparison_unit` identifies the open unit and
   `compactSupportCoefficientComparison_factorization` fixes their composite.
   I read finiteExchangeProjection and its actual proper/open construction in
   ExchangeProjection.lean. Verdict: the specified counit/unit normalization,
   rather than an equality of endpoints alone.

I independently read both dependency modules. There are no new definition nodes.
The direct-image module gives the actual inverse-image mate, its invertibility,
and the full K-injective normalization including QuasiIso of f_*(j); it does not
assume scalar restriction preserves K-injectives. The compact-support module
forms the actual open mate followed by this proper comparison and states the
restriction composition equation. Each corresponds to its dependency node.
The current shared DAG now records Q43's intrinsic compact-support restriction
module. I opened it: its derived functor is sfAmbientCompactSupportCandidate on
intrinsic modules, whereas this item's recorded Rf! is on fixed-scalar sheaves.
The incompatible framework imports still require the section 1(B) interface
repair. I corrected the dependency's lean.note and the worker-report passage
that incorrectly called it unstated. No Lean statement or mathematical node
statement changed; no statement_change or citer audit is needed.

Edge cases: m=n and m=1 are allowed; n=0 is excluded by 1≤m≤n exactly as in the
node. Nonflat reductions such as Z/l²→Z/l are allowed. Zero K, empty X or Y,
identity and empty pullbacks are not excluded. There is no index-set or
connectedness assumption. The prime is distinct from the field characteristic.
Universe u is bound, site object/morphism universes remain u+1/u, and module
values and lifted coefficients are in u+1. No equality of those site universes
or additional coefficient flatness is imposed.

Independent searches in this reading:

- LeanFinder, “Change of coefficient ring for derived pushforward with proper
  support”: eight pushforward/sheaf-operation hits, no full theorem or coherences.
- Loogle, `"derivedRestrictScalars"`: no hits.
- Tool grep, `([Cc]oefficient|[Ss]calar).*(LowerShriek|lowerShriek|[Cc]ompactSupport)`:
  no hits.
- LeanSearch, “Base change of coefficients for compact support of constructible
  torsion sheaves”: unavailable (Internal Server Error), not a negative result.
- Direct rg across Mathlib, slopmaster2 WeilConjectures and project lean/Sheaf
  for coefficient, scalar, lowerShriek and compactSupport combinations. I also
  opened the newer Q43 compact-support and intrinsic direct-image modules,
  the existing tensor universal property, Tor predicate, actual compact-support
  functor and restriction/pullback comparison. These give the reused primitives
  or the incompatible intrinsic presentation, not a usable existing declaration
  of the full item. No module is dropped as an exact existing match.

All three primary signatures match their recorded signatures through the project's
signature reader. Every variable/universe is bound under autoImplicit false;
all lines meet the 100-column limit. Definitions have actual data; the instances
needed for isomorphism data come from named invertibility theorems. Each postponed
proof is a named theorem with source, blueprint and proof docstrings; the main
proof covers the nine DAG steps. No theorem was proved in this stage.

Validation in this reading: scompile.py compiled all three delivered siblings
separately with exit code 0 and no Lean errors or unexpected warnings. The
prescribed deliver2.py --no-push then returned exit code 0 and
`OK (dry run): commit 713da3c5de passes the preflight and compiles; nothing pushed`.
The earlier dependency-closure failures are resolved. The only second-reading
changes are the updated section 1(B) dependency justification and this report;
the three Lean modules and mathematical statements are preserved.

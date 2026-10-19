## Worker report

Repair of the return at immutable head b787e37159cc, point H3. The arbitrary
`ExceptionalCoefficientSquare` and `IsExceptionalAdjointAdmissibleAtCoefficientDiagram`
have been removed. There are no caller-supplied categories, support comparisons,
coefficient functors, or reduction/scalar index types in their replacement.

I read the ORIGINAL source Markdown on the server, in addition to the expanded DAG
statement and the two units `sk-def-sf-operations` and `sk-def-sf-admissible`.
Order 1474 defines higher admissibility by tests at every finite stage. Unit
sk-def-sf-operations (vi) specifies the maps between positive finite quotients
before passing to normalized systems, rationalization and common stages. The DAG
expansion had instead identified the criterion with unspecified integral-to-finite
and higher-category squares. I corrected that expansion under brief-stage2 §1(C),
with the full source and citer record in `statement_change`. The delivery defines
the finite-system criterion itself; it does not choose arbitrary functors on the
integral, rational or common-stage categories and call them canonical.

The unchanged finite-stage definition and the accepted interval repair remain.
The new coefficient maps have actual data:

* `exceptionalCoefficientExtension φ T` is the left adjoint to the recorded exact
  coefficient restriction on the ordinary unbounded intrinsic module-derived
  category. Its defining theorem is the K-flat derived tensor universal property,
  including nonflat quotient maps. This determines the functor together with its
  unit up to unique compatible isomorphism, rather than choosing from a bare
  Nonempty functor type.
* `exceptionalFiniteSupportExtensionMap` is the inverse scalar-adjunction mate of
  `sfCompactRestriction φ c`. The latter is an explicit composite: the unit mate
  for open extension by zero and the direct-image comparison normalized on every
  K-injective resolution. Its construction and normalization are supplied in the
  same delivery. There is no arbitrary support coefficient map parameter.
* `exceptionalFiniteRightCoefficientMap` transports the SAME chosen ambient
  adjunctions `DA.adjunction c` and `DB.adjunction c` to the fixed support
  presentation, inverts the actual left coefficient comparison, and applies
  `mateEquiv` across those two adjunctions. The left comparison is invertible when
  support has an ambient right adjoint: support then preserves coproducts, so the
  free coefficient resolution computes the tensor comparison on unbounded inputs.
  Invertibility of its further right mate is a separate requirement.
* Presentation isomorphisms are coordinate transports of the same Rp* j!, never
  coefficient maps. No presentation is selected from a bare Nonempty statement:
  `ExceptionalFiniteCoefficientCompatible` quantifies over all of them. Their
  types are inhabited by `exceptionalSupportPresentation_nonempty`. Changing a
  presentation changes the right mate by the conjugate isomorphism of adjoints,
  so its invertibility is unchanged. This universal quantifier cannot be vacuous.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* The prime is `l : ℕ` with `[Fact l.Prime]`. The coefficient field is `E : Type u`
  with `Field`, `Algebra (Padic l)` and `FiniteDimensional` instances. The finite
  ring is exactly `Padic.coefficientExtensionRing l E n`; `hn : 1 ≤ n` excludes
  exponent zero in the finite definition. Systems use `n+1`, covering every
  positive exponent without an optional exponent index.
* `S X Y : Scheme`, `[X.Over S]`, `[Y.Over S]`, and
  `hS : ∀ s : S, IsUnit (l : S.presheaf.stalk s)` render the base and invertible
  prime. `LocallyOfFiniteType` and `QuasiCompact` on both structure maps render
  finite type. The same classes and `IsSeparated` on f render its morphism
  conditions; `[f.IsOver S]` supplies the commutative triangle. No base field,
  absolute separatedness, Noetherian hypothesis, or characteristic is added.
* `c : Compactification f` is the chosen open/proper factorization.
  `SfAmbientExceptionalRightAdjointDatum` supplies clause (1), with FullCD,
  genuine ambient adjunctions, the chosen adjunction at c, all refinement
  comparisons, their unit/counit equations, and identity/composition coherence.
* `ExceptionalAdjointPreserves` supplies clause (2) with signed `cMinus cPlus : ℤ`,
  independent of `a b`, input `a ≤ b`, and output endpoints `a+cMinus`,
  `b+cPlus`. It supplies clause (3) using exactly `finiteTorConstructible` for
  input and output, with no additional Tor bound hypothesis.
* `HasUniformFiniteExceptionalAdjoints` quantifies the nonnegative FullCD bound
  and both signed amplitude constants before the exponent and field indices.
  An integral E-family uses the inhabited singleton `PUnit`, never a caller's
  potentially empty type. Each target scalar field has bounds uniform in its
  exponent. For the algebraic closure there is one bound across all fields and
  exponents.
* `ExceptionalFiniteReductionsCompatible` tests EVERY `m ≤ n`, including equality,
  using `Ideal.Quotient.factor` for the actual map from exponent n+1 to m+1 and
  the right-adjoint coefficient mate just defined. Tensor is derived even when
  this quotient is nonflat.
* `ExceptionalFiniteScalarsCompatible` tests EVERY exponent, using the recorded
  `integralScalarQuotientMap`, the finite projection of the valuation-ring
  inclusion. `IsExceptionalAdjointAdmissibleAtIntegral` quantifies over ALL finite
  coefficient extensions L and Q_l-algebra embeddings E → L, including identity,
  and ties source and target maps to the actual DE and DL families. There is no
  scalar-extension square function that can ignore them.
* `IsExceptionalAdjointAdmissibleAtRational` uses the same finite obligations
  BEFORE raw rationalization, exactly as the original defining paragraph does.
  No Karoubi completion or unspecified rational comparison is introduced.
* `IsExceptionalAdjointAdmissibleAtAlgebraicallyClosed` uses the ACTUAL finite
  intermediate fields of its fixed algebraic closure and their actual inclusions.
  The base intermediate field witnesses nonemptiness. Closure and scheme
  universes are independent: each finite field is transported with Mathlib's
  `Shrink.algEquiv`; the inclusion is conjugated through those algebra
  equivalences. This is precisely the finite system used before common stages.

Dependency declarations read and used:

* `AlgebraicGeometry.Scheme.SfAmbientExceptionalRightAdjointDatum` and
  `sfAmbientCompactSupportCandidate`, from AmbientExceptionalRightAdjoint.
* IntrinsicFiniteTorsionConstructibility: `intrinsicFiniteTorsionConstructible`;
  FiniteTorAmplitude: `finiteTorConstructible`;
  ConstructibleIntervalsUnordered: `constructibleInterval`.
* `AlgebraicGeometry.Scheme.proEtaleCoefficientRestrictScalars`, from
  ProEtaleDirectImageRestrictionOfScalars, and the exact derived descent.
* FiniteCompactSupport: `sfFiniteCompactSupport`, `sfConstantModuleRealization`,
  `sfConstantDerivedRealization` and their canonical realization equivalences.
* CompactSupportRestriction: `sfOpenRestrictionMate`,
  `sfSheafDerivedDirectRestriction`, `sfSheafCompactRestriction`,
  `sfRealizationRestriction`, `sfInverseRealizationRestriction`,
  `sfCompactRestriction` and their defining normalization equations.
* IntegralScalarExtensionWellDefined: `integralScalarQuotientMap`, its actual
  valuation-ring inclusion and quotient construction, and transition coherence.
* FiniteCoefficientFields: `Padic.FiniteCoefficientFields`, its finite-dimensional
  instance, bottom coefficient field and directed inclusions.
* Mathlib: `mateEquiv`, `Adjunction.ofNatIsoLeft`, `Adjunction.ofIsRightAdjoint`,
  `Ideal.Quotient.factor`, `Shrink`, `Shrink.algEquiv`, and finite-basis smallness.

Edge cases checked: exponent zero is not included; exponent one is included;
identity quotients and identity coefficient embeddings are included; nonflat
quotients are treated by derived tensor; the empty scheme is allowed; the
singleton field family is inhabited; the common-stage field index has the
bottom field; uniform bounds precede their indices; opposite signed amplitude
bounds are permitted; a reversed shifted interval is the zero-cohomology
subcategory through `Set.Icc`; arbitrary choices of new right coefficient maps
are impossible. Neither FullCD nor ambient adjunction existence is asserted for
general separated finite-type morphisms. The elliptic-curve warning is retained.

Searches: the original packet's LeanFinder, Loogle and Mathlib/source/project grep
searches were reread. The repair additionally searched LeanFinder for "derived
scalar extension adjunction mates compact support finite coefficient reduction"
(eight ordinary ModuleCat scalar adjunction hits, no admissibility definition),
Loogle for `CategoryTheory.mateEquiv` (the generic Mathlib mates API), and Mathlib
CategoryTheory grep for `ExceptionalAdjointAdmissible|exceptionalFiniteRightCoefficientMap`
(no hits). Project/upstream grep for the new declaration names returned no hits.
Live-source checks found the two finite support prerequisite modules absent, so
both are supplied from the already written Q23 stage-2 packet, rather than
replacing their canonical constructions by arbitrary maps.

STATEMENT-DISPUTED: citer `lem-weil-smooth-proper-purity-hypotheses` unconditionally
claims strong ambient admissibility for every smooth proper structure morphism.
The elliptic-curve counterexample already contradicts that claim. It is named
with holds:false in the citer audit and is not edited. The optional definition
itself does not assert that false existence claim.

## Dependency modules

`def-weil-constructible-intervals`: the accepted interval repair is unchanged.
The recorded interface requires an ordered endpoint proof and cannot express the
reversed output endpoints explicitly required by the item. The delivered
`constructibleInterval` uses actual cohomological support contained in `Set.Icc a b`,
with the recorded intrinsic bounded constructibility predicate. Its full subcategory
inherits every ambient morphism. This is the only dependency module delivered.

`def-weil-finite-tor-amplitude`: a record-only §1(B) repair uses the published
`WeilConjectures.finiteTorConstructible` in `Sheaf.Paper.FiniteTorAmplitude`.
The former fixed-scalar category is not the intrinsic constant-ring module-derived
category needed by the item. The existing intrinsic interface gives exactly bounded
constructibility and finite Tor amplitude, and the module also supplies the integral
uniform-Tor definition and field aliases. No copy of that module is delivered.

The former two copied support dependency modules were removed during the second
reading, because `Sheaf.Paper.SfCompactSupportRestrictionOfScalars` is now published
and its canonical comparison directly uses the required ambient support candidate.
Its landed node record and the exact existing compact-support record are reused.

## Statement corrected

The old statement is retained verbatim in `statement_change.old_statement`.
The finite-stage clauses and warning are unchanged. The corrected higher-stage
paragraph makes the original source's finite-system criterion explicit and
removes its mistaken expansion into unspecified higher-category squares. Its
quotient arrows, coefficient inclusions, adjunctions and mate direction are all
specified. It neither changes a blueprint unit nor replaces an optional ambient
adjoint by the unconditional constructible one. Source: original order-1474
Markdown, final defining paragraph; unit sk-def-sf-operations (vi), normalized
finite systems before rationalization and common stages.

All 25 direct statement/proof citers were found and read. Their individual
results follow (no citer was edited).

* `fix-cor-verdier-exchange`: holds:true. The citation uses the unchanged finite-stage clauses, or assumes the optional higher admissibility with its uniform coefficient compatibility; the concrete finite-system criterion preserves that use.

* `lem-fix-weil-operations`: holds:true. The citation uses the unchanged finite-stage clauses, or assumes the optional higher admissibility with its uniform coefficient compatibility; the concrete finite-system criterion preserves that use.

* `def-pod-conventions`: holds:true. The citation uses the unchanged finite-stage clauses, or assumes the optional higher admissibility with its uniform coefficient compatibility; the concrete finite-system criterion preserves that use.

* `cor-pur-smooth-admissibility`: holds:true. It cites only the unchanged preservation or bounded-class interpretations of finite-stage clauses (1)-(3); no arbitrary higher comparison diagram is used.

* `fix-lem-tensor-adjunction`: holds:true. The citation uses the unchanged finite-stage clauses, or assumes the optional higher admissibility with its uniform coefficient compatibility; the concrete finite-system criterion preserves that use.

* `thm-sf-preservation-class`: holds:true. It cites only the unchanged preservation or bounded-class interpretations of finite-stage clauses (1)-(3); no arbitrary higher comparison diagram is used.

* `cor-pur-general-admissibility-datum`: holds:true. It cites only the unchanged preservation or bounded-class interpretations of finite-stage clauses (1)-(3); no arbitrary higher comparison diagram is used.

* `lem-weil-smooth-proper-purity-hypotheses`: holds:false. Its unconditional assertion of strong ambient admissibility for every smooth proper structure morphism already contradicts the elliptic-curve warning; the present finite-system clarification does not repair that assertion.

* `cor-zl-purity-smooth-proper`: holds:true. It explicitly uses the unconditional constructible exceptional adjoint and excludes the optional ambient datum; the finite-system clarification leaves that distinction intact.

* `prop-weight-purity`: holds:true. The citation uses the unchanged finite-stage clauses, or assumes the optional higher admissibility with its uniform coefficient compatibility; the concrete finite-system criterion preserves that use.

* `thm-weil-deligne-purity`: holds:true. The citation uses the unchanged finite-stage clauses, or assumes the optional higher admissibility with its uniform coefficient compatibility; the concrete finite-system criterion preserves that use.

* `lem-trf-global-operator-perfect`: holds:true. The citation uses the unchanged finite-stage clauses, or assumes the optional higher admissibility with its uniform coefficient compatibility; the concrete finite-system criterion preserves that use.

* `def-weil-complex-weights`: holds:true. It explicitly uses the unconditional constructible exceptional adjoint and excludes the optional ambient datum; the finite-system clarification leaves that distinction intact.

* `fix-prop-adjunctions`: holds:true. The citation uses the unchanged finite-stage clauses, or assumes the optional higher admissibility with its uniform coefficient compatibility; the concrete finite-system criterion preserves that use.

* `def-fix-six-functor-datum`: holds:true. It explicitly uses the unconditional constructible exceptional adjoint and excludes the optional ambient datum; the finite-system clarification leaves that distinction intact.

* `thm-pur-td-criterion`: holds:true. The citation uses the unchanged finite-stage clauses, or assumes the optional higher admissibility with its uniform coefficient compatibility; the concrete finite-system criterion preserves that use.

* `cor-sf-ambient-adjoint-discharge`: holds:true. It cites only the unchanged preservation or bounded-class interpretations of finite-stage clauses (1)-(3); no arbitrary higher comparison diagram is used.

* `lem-sf-mate`: holds:true. The citation uses the unchanged finite-stage clauses, or assumes the optional higher admissibility with its uniform coefficient compatibility; the concrete finite-system criterion preserves that use.

* `lem-fix-operation-reduction`: holds:true. Its conditional exceptional-adjoint assertion uses exactly the canonical finite quotient and scalar mates required here; integral compatibility is expressed through the normalized finite system before rationalization/common stages.

* `def-pur-smooth-trace`: holds:true. The citation uses the unchanged finite-stage clauses, or assumes the optional higher admissibility with its uniform coefficient compatibility; the concrete finite-system criterion preserves that use.

* `def-weil-exceptional-inverse-image`: holds:true. It explicitly uses the unconditional constructible exceptional adjoint and excludes the optional ambient datum; the finite-system clarification leaves that distinction intact.

* `def-trf-admissibility`: holds:true. It explicitly uses the unconditional constructible exceptional adjoint and excludes the optional ambient datum; the finite-system clarification leaves that distinction intact.

* `def-weil-poincare-trace-cup`: holds:true. It explicitly uses the unconditional constructible exceptional adjoint and excludes the optional ambient datum; the finite-system clarification leaves that distinction intact.

* `thm-weil-poincare-duality`: holds:true. It explicitly uses the unconditional constructible exceptional adjoint and excludes the optional ambient datum; the finite-system clarification leaves that distinction intact.

* `prop-weil-operations`: holds:true. It explicitly uses the unconditional constructible exceptional adjoint and excludes the optional ambient datum; the finite-system clarification leaves that distinction intact.


## Repair validation

H3 is repaired by the concrete finite-system declarations above. In particular the
coefficient extension is universally determined by the fixed restriction functor,
the support square is its normalized open/proper comparison, and the exceptional
square is its mate under the actual chosen `DA.adjunction c` and `DB.adjunction c`.
The universal presentation test ranges over inhabited isomorphism types and changes
only coordinates on these same support functors. The definitions for integral,
rational and algebraically closed coefficients expose no category or arrow parameter
and no reduction or scalar-extension index set that a caller can make empty.

I reread order 1474 and the complete source sections `sk-def-sf-operations` and
`sk-def-sf-admissible`. The source's last defining paragraph explicitly says “every
finite coefficient stage”; section (vi) explicitly supplies the positive quotient
maps and passage through normalized systems, raw rationalization and common stages.
The correction specifies that criterion and does not change either unit's statement.
All 25 current direct citers have been checked against the recorded audit; none is
missing. Each delivered Lean signature has been copied verbatim into its node record.


Final search pass: LeanFinder query “Canonical derived coefficient extension and
compact-support adjunction mates compatible at every positive finite quotient”
returned eight unrelated analysis/distribution and functional-equation declarations;
none is a match. Loogle `CategoryTheory.mateEquiv` again found the generic mates API.
Exact-name searches in upstream `WeilConjectures` and published `lean/Sheaf` returned
no competing admissibility, finite-family or finite-right-coefficient-map definition.
The live `--source` checks still report both support prerequisite modules unavailable;
the corresponding same-delivery dependency modules are therefore required.


Compilation repair: the internal singleton type is explicitly `PUnit.{1}`
(`Type 0`). This resolves inferred singleton-index universe metavariables;
coefficient fields remain in `Type u`, schemes in `Scheme.{u}`, and the fixed
algebraic closure in independent `Type v` with finite fields canonically shrunk.

## Second reading by NW

I am the second reader, not the author of the packet. I read the corrected
node first against the original order-1474 Markdown retrieved read-only from
`/home/ubuntu/weil-newtargets/literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/def-weil-exceptional-adjoint-admissibility.md`
on the server. I also read both unit records `sk-def-sf-operations` and
`sk-def-sf-admissible`, especially (iv), (v), and (vi). The original final
paragraph explicitly imposes the three conditions at every finite stage with
uniform bounds and coefficient isomorphisms. Unit (vi) spells out the positive
quotient maps before normalization, rationalization, and common stages.
Consequently the finite-system clarification in `statement_change` follows the
source and leaves the units unchanged; it does not manufacture an unconditional
ambient exceptional adjoint. The warnings and the finite-stage clauses agree
with the original source.

My object/hypothesis/conclusion checklist, with the final Lean rendering:

1. A prime ell: `l : ℕ`, `[Fact l.Prime]`. A finite extension of Q_l:
   `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
   `[FiniteDimensional (Padic l) E]`. The chosen valuation-ring uniformizer and
   quotient are those of `Padic.coefficientExtensionRing l E n`, not another
   finite coefficient algebra. `n : ℕ`, `hn : 1 ≤ n` is exactly a positive
   exponent. Verdict: exact.
2. S, X, Y and their structure maps: `(S X Y : Scheme.{u})`, `[X.Over S]`,
   `[Y.Over S]`. Invertibility is `_hS : ∀ s : S, IsUnit
   (l : S.presheaf.stalk s)`. Finite type is `LocallyOfFiniteType` and
   `QuasiCompact` on each structure map. The morphism `f : X ⟶ Y` has
   `[f.IsOver S]`, `[IsSeparated f]`, `[LocallyOfFiniteType f]`,
   `[QuasiCompact f]`. There is no field base, Noetherian condition, absolute
   separatedness, extra characteristic restriction, or compactification-existence
   assertion. Verdict: exact context.
3. The chosen factorization: `c : Compactification f`; its `i` is open and
   its `g` proper, with their composite f. `sfAmbientCompactSupportCandidate A c`
   is the actual termwise exact intrinsic extension by zero followed by
   `proEtaleConstantDerivedDirectImage c.g A` on the ordinary unbounded
   `proEtaleDerivedCategory`. I opened these dependencies. This is the same
   Rp_* j_!, without an ambient independence assertion. Verdict: exact.
4. Clause (1): the existential `D : SfAmbientExceptionalRightAdjointDatum A f c`
   contains `fullCD : ∃ c_cd : ℕ, sfFullCohomologicalDimension c.g A c_cd`,
   `rightAdjoint d`, `adjunction d` for every compactification, `theta`, `rho`,
   both unit/counit equations, both identity laws, and both composition laws.
   `adjunction c` is the chosen adjunction, not a separate unrelated one.
   `Adjunction.homEquiv` gives the all-K/all-L natural bijections. FullCD is
   exactly its recorded source definition: every original-source module sheaf,
   and its restriction on each specified pro-etale base change, not only
   etale-origin sheaves. No bound on other proper parts is added. Verdict: exact.
5. Clause (2): `∃ cMinus cPlus : ℤ` outside the interval quantifiers, followed
   by `∀ (a b : ℤ), a ≤ b → ∀ L` in `ExceptionalAdjointPreserves`. Input is
   `constructibleInterval ... Y a b L`; output is the same intrinsic notion
   on X, at `(a+cMinus,b+cPlus)`, for `(D.rightAdjoint c).obj L`.
   Signed constants are independent, and output ordering is not assumed.
   Verdict: exact.
6. Clause (3): the second conjunct in `ExceptionalAdjointPreserves` is
   `∀ L, finiteTorConstructible ... Y L → finiteTorConstructible ... X (G.obj L)`.
   Its predicate is intrinsic bounded constructibility intersected with finite
   Tor amplitude, not an imposed common Tor interval for all inputs. Verdict:
   exact; the dependency attachment is repaired below.
7. At a general coefficient map phi, `exceptionalCoefficientExtension phi Z`
   is the left adjoint to the fixed exact
   `(proEtaleCoefficientRestrictScalars Z phi).mapDerivedCategory`.
   The defining existence theorem states that universal property, rather than
   existence of an unconstrained functor. Tensor and its unit are determined
   up to the unique unit-compatible isomorphism; this is sufficient for the
   invariant invertibility test. Nonflat maps are included. Verdict: exact.
8. The support comparison is now the PUBLISHED
   `AlgebraicGeometry.Scheme.sfCompactSupportRestriction c phi`, read both in
   the shared checkout and through `scompile.py --source`. It uses the same
   `sfAmbientCompactSupportCandidate` as D. Its open part is normalized by
   adjunction units; its proper part uses the recorded K-injective equation.
   `exceptionalFiniteSupportExtensionMap` is its inverse scalar-adjunction
   mate. `exceptionalFiniteSupportExtensionMap_isIso` states the consequence
   of the actual ambient adjunction. `exceptionalFiniteRightCoefficientMap`
   is `mateEquiv (DA.adjunction c) (DB.adjunction c)` of this inverse map.
   These are the SAME chosen adjunctions as in the preservation conditions.
   `ExceptionalFiniteCoefficientCompatible` tests precisely its `IsIso`.
   Verdict: exact canonical maps; no comparison or presentation parameters.
9. Uniform finite-stage data: `FiniteExceptionalAdjunctionFamily` quantifies
   every n with exponent n+1. `HasUniformFiniteExceptionalAdjoints` quantifies
   `∃ cCD : ℕ, ∃ cMinus cPlus : ℤ` before all field and exponent indices,
   and imposes FullCD and both preservation conditions. Verdict: uniformity
   and quantifier order are correct.
10. All finite reductions: `ExceptionalFiniteReductionsCompatible` quantifies
    `∀ (m n : ℕ) (h : m ≤ n)` and uses `Ideal.Quotient.factor` for the
    corresponding powers of the same uniformizer ideal. D at n and D at m
    are passed to the SAME canonical mate. Verdict: every positive quotient,
    including identity; no arbitrary reduction index or underived tensor.
11. Integral stage: `IsExceptionalAdjointAdmissibleAtIntegral` existentially
    chooses DE on the inhabited singleton `PUnit.{1}`, with its uniform bounds
    and every reduction. It then quantifies every finite Q_l-coefficient field
    L and embedding `ι : E →ₐ[Padic l] L`, chooses DL with its own exponent-
    uniform bounds and reductions, and uses
    `ExceptionalFiniteScalarsCompatible ... ι ... DE DL` at every n.
    Its ring map is exactly `integralScalarQuotientMap l E L ι n`.
    I opened that definition: it is the actual valuation-ring restriction of
    ι descended through the positive-power quotient. Verdict: exact, including
    identity embeddings; no freely selected square can ignore DE or DL.
12. Rational stage: `IsExceptionalAdjointAdmissibleAtRational` abbreviates the
    same finite-system obligations before raw rationalization. It introduces
    neither Karoubi completion nor an independently chosen rational diagram.
    Verdict: matches the corrected source-based finite-system criterion.
13. Algebraically closed stage: the index is the actual
    `Padic.FiniteCoefficientFields l Ω` of the fixed algebraic closure Ω.
    D is one family at ALL its fields and exponents; uniform bounds precede
    both indices. Each field has every quotient test. Every `E ≤ L`,
    including equality, has the scalar test through the actual
    `IntermediateField.inclusion h`, conjugated by `Shrink.algEquiv`.
    The finite fields are canonically represented in the scheme universe;
    Ω remains in independent universe v. Verdict: exact common-stage input,
    with no optional field index or equality of closure and scheme universes.
14. The warning is a scope warning, not an existence conjunct. None of these
    predicates proves FullCD or an ambient adjunction for general f. Verdict:
    preserved, and distinct from the unconditional constructible exceptional
    inverse image.

Edge cases: n=0 is excluded only in the positive finite-stage definition;
n=1 is included, and n+1 enumerates every positive exponent. The zero object
and empty schemes are not excluded. The interval uses actual cohomological
support in `Set.Icc`; when its endpoints reverse all cohomology must vanish.
Negative amplitude constants and shifts in either direction are allowed.
Identity quotient arrows, identity field embeddings, and same-field inclusions
are included by non-strict inequalities/unrestricted embeddings. Nonflat
quotients use a left derived tensor adjunction. The singleton index is inhabited;
the finite-subfield index contains the base field `Padic.finiteCoefficientBase`.
The algebraic closure's universe is independent, and finite-dimensionality gives
the smallness used to Shrink each intermediate field. No additional universe
equality, finiteness of the scheme site, or characteristic hypothesis appears.

Searches independently repeated: LeanFinder query "Uniform amplitude and finite
Tor preservation for a coherent family of ambient right adjoints to pro-etale
compact support, compatible with quotient coefficients" returned eight condensed
module/free tensor hits, none the criterion. Loogle
`"IsExceptionalAdjointAdmissible"` returned no hits. LeanSearch query
"Exceptional adjoint admissibility of a separated scheme morphism with coefficient
reduction compatibility" was unavailable (Internal Server Error), not counted as
negative evidence. Launcher grep for admissibility/coefficient/support names had
no Mathlib match. I also ran direct rg for `admissib`, `ExceptionalAdjoint`,
`constructibleInterval`, `exceptionalCoefficientExtension`, and the right-coefficient
map in Mathlib, upstream WeilConjectures, and project Sheaf. Mathlib's admissible
maps concern elliptic-curve variable changes or triangulated subcategories.
Upstream `AlgebraicGeometry.ProEtale.IsExceptionalAdjointAdmissible` was opened:
it works in fixed-scalar sheaves, assumes a chosen global compactification, and
omits the refinement datum and higher-stage coefficient requirements. It is not
an exact attachment. Mathlib's generic `mateEquiv` IS the exact mates dependency,
and is now used directly without a second generic wrapper.

Mismatches found and changes:

* The report's assertion that the support prerequisites are unavailable is now
  stale. `lem-sf-compact-support-restriction-of-scalars` is landed as
  `Sheaf.Paper.SfCompactSupportRestrictionOfScalars`, and its actual comparison
  already has the ambient ring-sheaf support functors needed here. I removed
  the two copied modules `FiniteCompactSupport` and `CompactSupportRestriction`
  and their two dependency node copies. Thus this delivery does not overwrite
  the landed Q43 record or the exact existing compact-support definition.
* With that actual comparison available, the two arbitrary presentation
  isomorphisms and the universal quantifier over presentations are unnecessary.
  I removed them and `exceptionalSupportPresentation_nonempty`. The coefficient
  mate now uses DA.adjunction c and DB.adjunction c directly. There is no
  presentation nonemptiness theorem needed to prevent vacuity.
* The generic `exceptionalAdjointCoefficientMate` repeated the recorded Mathlib
  mates notion. I removed the wrapper and used `mateEquiv` directly.
* The finite-Tor dependency's old recorded fixed-scalar category cannot type
  this intrinsic predicate. I repaired its record under §1(B) to the already
  published `WeilConjectures.finiteTorConstructible` and its sibling definitions
  in `Sheaf.Paper.FiniteTorAmplitude`, with `existing: true` and an explanatory
  `lean.note`. No second definition or new module is supplied for it.
* I explicitly added the landed ambient-datum node to stmt_deps, since the
  formulation uses its exact structure. The source-based correction and its
  old statement remain recorded; no unit or target statement was changed.

Dependency reading: the only remaining dependency MODULE of the delivery is
`def-weil-constructible-intervals`, `ConstructibleIntervalsUnordered`. I opened
both its node and recorded `ConstructibleIntervals` source. The old predicate
requires a proof a≤b and a prime-invertibility witness in every call, so cannot
express the item's explicitly reversed output endpoints. The supplied
`constructibleInterval` is precisely the same intrinsic bounded-constructibility
predicate and inclusive vanishing condition, using the recorded
`proEtaleCohomologicalSupport`. Its full subcategory has all inherited morphisms.
The conservative extension to unordered endpoints introduces no new mathematical
notion and no theorem; the module and its lean.note are retained unchanged.
The finite-Tor RECORD repair above reuses the published module, and its definition
and Tor test were opened: a single finite interval works against every degree-zero
module sheaf, via K-flat derived tensor. No new nodes are needed.

Citer audit: an independent scan finds exactly the same 25 direct statement/proof
citers as `statement_change.citers` (no missing or stale IDs). I opened
`lem-fix-operation-reduction`: its exceptional-adjoint clause is conditional on
exactly the coefficient comparisons in the admissibility datum, so holds:true is
correct. I opened `lem-weil-smooth-proper-purity-hypotheses`: its item (1) really
asserts strong ambient admissibility for every smooth proper structure morphism,
contradicting the elliptic-curve warning; holds:false is correct. I also read the
constructible-only use in `prop-weil-operations`. No citer was edited. The
STATEMENT-DISPUTED in the worker report concerns the false citer, not this
optional definition.

No definition contains sorry data. The two remaining postponed theorems in the
main module are named and state the universal coefficient adjunction existence
and invertibility of its support mate, both explicitly present in the corrected
node. Their source/blueprint docstrings give the K-flat/free-resolution arguments.
All theorem proofs remain sorry, as stage 2 requires. The main signature is
unchanged and matches lean.statement verbatim up to whitespace; all new helper
signatures have explicitly bound variables and universes. Lines are at most
100 columns. Final compilation and delivery validation are recorded below.

Final validation: the required scompile wrapper compiled both delivered modules,
and deliver2's existing-declaration probe checked the published finite-Tor
attachment. `deliver2.py NW def-weil-exceptional-adjoint-admissibility --no-push`
printed `OK (dry run)` at c55f1cf86d: all files compile without warnings and the
server preflight passes. The final delivery contains two Lean modules, three
node records, and this report. The wrapper correctly preserved the base's
maintainer-owned `reviewed_lean` field on the finite-Tor dependency; only its
lean attachment is delivered.

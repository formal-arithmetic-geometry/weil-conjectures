## Worker report

The module `Sheaf.SixFunctors.QbarDualRecollement` states
`WeilConjectures.QbarDualRecollement.qbar_dual_recollement`, with sorry.
It uses the actual intrinsic finite-field pair category, completed pullback,
ordinary adic right adjoint, compact-support coefficient actions, and relative
internal-Hom duality. It adds no Karoubi completion or discrete-coefficient category.
All helper declarations belong to this node and are listed in lean.declarations.
The theorem existentially supplies the relative-duality data B and their properties P;
the helpers accept these data explicitly and do not choose a freely unspecified
Datum from a postponed existence theorem.
The only other postponed theorem is the standard-t-structure helper
`sfArbitraryBaseStandard_existsUnique`, now owned and recorded by this item.
The live adic-heart dependency record and module are untouched.

Hypothesis correspondence:

- The arbitrary field is `{k : Type u} [Field k]`; the coefficient prime is
  `(l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]`.
- The chosen algebraic closure is `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]`. Its universe v is independent of u.
- `X : PerAdic.Base k` bundles exactly the structure morphism, its separatedness,
  locally-finite-type and quasi-compact properties. `Z U : PerAdic.Base k` expose
  the inherited structures on the closed and complementary open subschemes.
  These impose no additional mathematical restriction: finite type over a field
  makes X Noetherian; Z is finite type, and U is a quasi-compact Noetherian open.
  Both inherit separatedness. Empty schemes are included.
- `i`, `[IsClosedImmersion i]`, `j`, `[IsOpenImmersion j]`, their `IsOver` instances,
  and `hc : Set.range j = (Set.range i)ᶜ` are precisely the closed subscheme and
  its complementary open subscheme, with their induced k-structures.

Clause correspondence:

- All category expressions are `generalAlgebraicallyClosedConstructibleCategory`.
  This is the literal carrier of the recorded `intrinsicPbcQbarCategory` alias,
  with its common-stage shifts and triangles. The source domain conditions follow
  from finite type over the field; they are not new assumptions.
- `B W` is the existing `Datum` for the identity on each base, and the conclusion
  also supplies its existing `Properties` witness `P W`. Its structure-map
  adjunction determines omega up to the canonical adjunction isomorphism.
  `dual` is exactly `(B W).dualY`, namely the recorded common-stage internal Hom
  into that omega. The base normalization, evaluation bidual arrows, signed dual
  shifts, and coefficient comparisons are retained by `P W`. These are output
  witnesses, never additional hypotheses on the theorem.
- `exceptional` is the actual composite `D_X.rightOp ⋙ (i*).op ⋙ D_Z`, hence
  literally `D_Z i* D_X` on objects and morphisms, with the variances correct.
- `Conclusion.exactOpenExtension`, `exactOpenPull`, `exactOpenPush`,
  `exactClosedPull`, `exactClosedPush`, and `exactExceptional` assert additivity
  and a shift structure under which each functor is triangulated. Their source
  and target are already the bounded constructible categories, so preservation
  of those categories is built into their types.
- The existing `openAdjunction` is j! adjoint to j*, and `ordinaryAdjunction`
  supplies j* adjoint to Rj* and i* adjoint to Ri*. The new
  `exceptionalAdjunction` is Ri* adjoint to the literally defined i!.
- `compactOpen` identifies the open functor with the specified coefficient action
  for `(j,id_X)`; `compactClosed` identifies Ri* with that action for `(id_Z,i)`.
  These are the canonical open/proper compactifications already defined upstream,
  rather than arbitrary unrecorded pushforwards. The coefficient action includes
  the integral Roos construction and its rational and common-stage arrow action.
- `openUnit`, `openCounit`, `closedCounit`, and `exceptionalUnit` assert that the
  actual corresponding adjunction maps are isomorphisms, giving respectively
  j*j!=id, j*Rj*=id, i*Ri*=id, i!Ri*=id.
- `openClosedZero`, `closedOpenZero`, and `exceptionalOpenZero` assert that every
  value of j*Ri*, i*j!, and i!Rj* is a zero object, respectively.
- `firstTriangle` existentially supplies only the connecting arrow. Its first
  arrow is `openAdjunction.counit.app K`, and its second arrow is
  `ordinaryAdjunction i .unit.app K`. The membership is in the existing distTriang.
- `secondTriangle` likewise supplies only its connecting arrow, retaining
  `exceptionalAdjunction.counit.app K` and `ordinaryAdjunction j .unit.app K`.
- `dualRestrictions.openIso` is the natural isomorphism j*D_X ≅ D_U j*;
  `closedIso` is i*D_X ≅ D_Z i!. The use of opposite functors renders the
  contravariant naturality on the actual categories.
- `shifts` gives the two explicit signed commutative squares with `dualShift`.
  `restrictionShift` is the existing representative-normalized completed pullback
  shift. The closed square uses the explicit `exceptionalShift` composite, built
  from `dualShift` on X, `restrictionShift i` at -n, contravariant application
  of D_Z to their inverse composite, and `dualShift` on Z at -n, followed only
  by the equality -(-n)=n. There is no freely quantified exceptional shift.
- `openScalars` and `closedScalars` give explicit commuting squares at EVERY finite
  coefficient field, using the prescribed pullback inclusion and trace-normalized
  dual inclusion. `rationalExceptional` is the same literal dual-pull-dual composite;
  `exceptionalInclusion` is constructed by composing those three prescribed maps.
  These squares identify each finite-stage comparison with the common-stage one.
  Thus, by the existing coherent inclusion/transition comparisons, they retain
  identity extensions and successive coefficient extensions as well.
- `closedRestriction` and `openRestriction` assert for every integer n the natural
  commutation with `PerAdic.cohomology (sfArbitraryBaseStandard ...) n`, namely
  standard truncation cohomology placed in degree zero. For every geometric point
  they give naturally isomorphic restricted fibre functors. Both fibre functors
  satisfy `SfAdicCommonFiberSpec`, so their values and rational fraction maps are
  normalized by the actual completed geometric point sections at every finite
  coefficient stage followed by the recorded coefficient inclusion into Ω.

Dependency declarations read and used:

- Scheme properties: Mathlib `IsClosedImmersion` (closed embedding and surjective
  stalk maps), `IsOpenImmersion` (locally-ringed-space open immersion),
  `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` (closed diagonal).
  The collecting convention node defines no separate notion.
- `Sheaf.Paper.IntrinsicQbarCategory`: `intrinsicPbcQbarCategory`, its literal
  `generalAlgebraicallyClosedConstructibleCategory` carrier and existing triangles.
- `Sheaf.Paper.AdicHeartIntrinsicFibres`: `sfAdicIntegralFiber`,
  `sfAdicRationalFiber`, `SfAdicCommonFiberSpec`, and the preserved
  `sfAdicHeartPullbackFibres`; `PerAdic.Base` and `PerAdic.cohomology` in its imports.
- `Sheaf.SixFunctors.ArbitraryFieldVerdier`: `arbitrary_field_verdier_duality`,
  `Datum`, `Properties`, `Datum.dualY`, `dualShift`, `Rational.Datum.dualY`,
  `dualYInclusion`, `pullInclusion`, `openExtension`, `openAdjunction`,
  `ordinaryAdjunction`, `arbitraryFieldDerivedPushWithUnit`, and `pull`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `commonStageDerivedPullback` and its
  uniquely specified finite-stage object and conjugated representative-map formula;
  the above `pull` is this exact construction with the actual residue inverses.
- `Sheaf.Paper.SfCommonStageDirectImage` exposes a finite-field model interface,
  unusable as a direct arbitrary-field morphism input. The already stated
  arbitrary-field direct image in the duality dependency supplies the equivalent
  right-adjoint interface for exactly the given completed pullback. No new choice
  of an unnormalized direct-image functor is introduced here.
- `Sheaf.Paper.QcqsCompactSupportRealization`:
  `sfQcqsCompactSupportRealization`; its public coefficient actions
  `SfCompactSupportCoefficientAction` and finite integral/rational/common-stage
  constructions enter `compactOpen` and `compactClosed` explicitly.

The module imports all recorded proof-dependency modules as non-public imports;
statement-dependency interfaces are exported through its public imports. No cycle
is introduced. The item publicly imports the unchanged intrinsic-fibre dependency
and `SfConstructibleHeart`, and owns the two standard-t-structure helpers.

Edge cases checked before and during writing: empty X, empty Z (U=X), empty U
(Z=X), and zero K. The range-complement hypothesis, actual unit/counit triangles,
and zero-object clauses cover all of these. No nonemptiness, connectedness,
reducedness, smoothness, finite-field descent, perfectness, or Galois-cohomological
bound is imposed on k. Arbitrary shifts n, zero shift, the identity coefficient
extension, and successive extensions are included. The geometric-point universe
matches schemes; the coefficient closure universe remains independent.

Source inspection: read Bhatt--Scholze Lemmas 6.7.19 and 6.7.20,
Proposition 6.8.14 and Remark 6.8.15 directly in the local PDF. In particular
Remark 6.8.15 identifies open/closed pullback with naive inverse image and
closed compact support with ordinary image, and supplies the supported-sections
right adjoint. The relative arbitrary-field normalization is exactly the cited
node's refinement. No statement correction and no disputed statement are needed.

Searches actually run with msearch.py:

- leanfinder: `Open closed recollement of constructible adic derived categories
  with Verdier duality`: eight hits (localCohomology.diagram, derived-category
  truncation and standard-localization facts), no statement on these adic pairs.
- loogle: `"recollement"`: no hits.
- grep in Mathlib CategoryTheory: `recollement|Recollement|Verdier|exceptionalPullback`:
  nineteen bibliographic Verdier hits, no matching construction.
- leansearch: `Verdier compatible open closed recollement common stage constructible
  ell adic categories`: generic constructible sets, adhesive sheaves, t-structure
  recursors and Adjunction.Quadruple, no match.
- rg in upstream WeilConjectures for recollement, Verdier, and the item id:
  only finite/discrete étale or abstract six-operation packages and related Verdier
  constructions; the item id has no hit. Read the candidate Package.lean duality
  signatures: they use the finite-coefficient étale category, not these adic pairs.
- rg in lean/Sheaf: finite/open-closed, condensed bounded-below and integral
  common-stage triangle helpers exist, but no combined arbitrary-field adic dual
  recollement theorem. Those helpers lack exceptional dual restriction and/or use
  another coefficient category. The arbitrary-field Verdier module supplies the
  reusable actual operations used here.
- rg in Mathlib, upstream WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json
  for the new full-name fragments `qbar_dual_recollement`, `QbarDualRecollement`,
  `sfArbitraryBaseStandard`: no existing declarations.

The relative-duality data are explicit existential output witnesses rather than
definitions extracting an entire Datum from the postponed existence result.

## Repair of returned head e891ba5a4387

H13: followed the maintainer's first repair option. Moved
`WeilConjectures.sfArbitraryBaseStandard_existsUnique` and
`WeilConjectures.sfArbitraryBaseStandard` into the item module, retaining their
signatures and real-data definition. Their source/blueprint docstrings now name
this item, and both are listed in this item's `lean.declarations`. Removed the
sandbox dependency-node replacement and `AdicHeartArbitraryBase.lean` entirely.
Consequently the delivery changes neither the live
`lem-per-adic-heart-pullback-fibres` JSON nor `AdicHeartIntrinsicFibres.lean`.
Q72's seven-declaration record, its main `sfAdicHeartPullbackFibres` theorem,
three stage-3 sorries, and all live importers remain in place.

The helpers construct standard cohomology from the existing
`sfCommonStageStandardClass` in `SfConstructibleHeart`; that API previously
provided its t-structure only with finite-field model data. The uniquely specified
bounded t-structure on an arbitrary separated finite-type base is now an auxiliary
statement of this recollement node, as explicitly authorized in the return.
It has a complete proof docstring; its t-structure definition chooses from a
uniqueness theorem, not from unconstrained existence.

H3: removed `∃ sE : (exceptional i).CommShift ℤ` from `ShiftCompatible`.
Added the real-data object isomorphism `exceptionalShift K n`:
first apply i* to the prescribed signed dual shift on X, then apply the
prescribed restriction shift at -n; apply D_Z contravariantly to the inverse
of that composite; finally use the prescribed signed dual shift on Z at -n
and the index equality -(-n)=n. Thus its endpoints are literally
`i!(K[n]) ≅ (i!K)[n]`. The closed square uses the inverse of this very
isomorphism inside D_Z. Its comparison can no longer be selected from the
closed restriction isomorphism e to force the square to hold.
The open square and all other conclusion fields are retained verbatim.
The item statement, its dependencies, and proof plan have not changed.

## Second reading by Q141

Repair self-check with the node and final module open: the field, prime,
invertibility, independently sized coefficient closure, separated finite-type
bases, closed/open immersion instances, and complementary-image hypothesis are
unchanged. `Conclusion` still supplies the compact-support identifications,
six exact functors, exceptional adjunction, four invertible adjunction maps,
three zero composites, both triangles with actual unit/counit arrows, both dual
restriction isomorphisms, the two finite-stage scalar squares, and both standard
cohomology/geometric-fibre restrictions. These correspond to the node clauses
listed above. Re-read the new exceptional shift at both endpoints: its two
contravariant dual shifts reverse n twice; applying D_Z to the inverse inner
comparison gives the required forward isomorphism. The square now fixes this
composite for every integer n, including zero and negative indices.
The empty-base and zero-object cases impose no additional hypotheses.
The two mismatches identified in the return are precisely the record replacement
and freely chosen shift; both are repaired as detailed above. No statement
correction, new node, disputed statement, or dependency-module replacement is needed.

Validation: the initial saved-packet dry run passed preflight and compilation
(commit c5c457a87b, not pushed), but the explicit returned findings still required
repair. After both repairs, `scompile.py Q141 lem-per-qbar-dual-recollement` on
the sole delivered module passed its sandbox check in 11.3 s and its actual
module-name check in 10.7 s, with no errors or warnings. The checks cover the
canonical shift endpoints, standard cohomology on the intrinsic carrier, all
six functor endpoints, both scalar squares, both triangles and both fibre clauses.

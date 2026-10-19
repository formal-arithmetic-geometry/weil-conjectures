## Worker report

Repair of the returned immutable head `88356d25136c`. The prescribed initial
`deliver2.py --no-push` passed on the saved packet (temporary commit
`7e35089aaf`), but the required semantic self-check reproduced both H3 faults.
The packet is substantively repaired, rather than re-pushed unchanged.

`lean/Sheaf/Paper/BoundaryHomVanishing.lean` states
`WeilConjectures.boundaryHomVanishing`, with its sole proof `sorry`.
All four Hom sets now use the actual finite-coefficient-field common-stage
category or its recorded Frobenius fixed-pair category. In both reverse clauses
the SOURCE is shifted by one. There is no derived category of unrestricted
coefficient sheaves and no derived category of Weil sheaves in the signature.

Hypothesis-by-hypothesis correspondence:

* The finite field, chosen geometric algebraic closure, and characteristic are
  `D : FiniteFieldDatum.{u}`. Its geometric fibers are `D.geometricFiber`.
* The coefficient prime and its characteristic condition are `l : ℕ`,
  `[Fact l.Prime]`, and `hl : l ≠ D.p`. The former redundant
  `[Fact (ringChar D.k₀ ≠ l)]` is removed. `sfWeilPrimeInvertible` derives
  invertibility on the geometric fibers; it is not an extra hypothesis.
* The chosen coefficient algebraic closure is `Ω : Type v`, `[Field Ω]`,
  `[Algebra ℚ_[l] Ω]`, `[IsAlgClosure ℚ_[l] Ω]`. Universes `u` and `v` are
  independent, as in the recorded heart and coefficient definitions.
* `c : MiddleExtensionCurve D` bundles the separated finite-type curve,
  smoothness, pure dimension one, dense open source and immersion `c.j`.
  `[GeometricallyConnected c.C.hom]` is the additional connectedness in this node.
* `Z₀`, `i₀ : Z₀ ⟶ c.C`, `[IsClosedImmersion i₀.left]`, and
  `[IsReduced Z₀.left]` specify the reduced closed boundary.
  `hcomp : IsCompl (Set.range c.j.left.base) (Set.range i₀.left.base)`
  says its underlying closed subset is exactly the complement of the open.
  The finite-type instances on `Z₀.hom` make explicit the domain of the
  recorded geometric-fiber construction; they follow for the closed boundary
  of the stated finite-type curve and exclude no boundary of the node.
* `F₀ : sfCommonStageWeilSheaf D l hl c.U Ω` is the constructible Weil
  sheaf in the recorded common-stage fixed-pair category. Its geometric
  carrier is `F₀.obj.carrier`, with heart membership `F₀.property`.
  `hF₀ : HasCommonStageLisseLattice ... F₀.obj.carrier` is the landed
  finite-stage integral-lattice criterion for being lisse; it requires no
  Frobenius-stable lattice and permits the zero sheaf.

Clause-by-clause correspondence:

1. Arbitrary geometric constructible `E` is quantified as
   `E : sfCommonStageHeart l (D.geometricFiber Z₀).left Ω`.
   There is no Weil structure on this binder. Write B for the `.obj` of
   `(boundaryClosedPushforward ... i₀).obj E` and A for the `.obj` of
   `(qbarCurveOrdinaryPushforward ... c).obj ⟨F₀.obj.carrier, F₀.property⟩`.
   The first `Subsingleton` is literally `B ⟶ A⟦(1 : ℤ)⟧` and the second
   literally `A⟦(1 : ℤ)⟧ ⟶ B`. The Hom is inherited from the actual
   common-stage pair category. These hearts already consist of degree-zero
   complexes; another `DerivedCategory.singleFunctor` is neither needed nor used.
2. `E₀ : sfCommonStageWeilSheaf D l hl Z₀ Ω` is exactly the
   constructible Weil boundary sheaf. `boundaryOrdinaryWeilImage` uses the
   ordinary closed/open adjunctions and their canonical inverse-image
   Frobenius square, not arbitrary chosen arrows. Its carrier is literally
   the respective ordinary heart image. Its structure is the counit-normalized
   adjunction mate defined in `boundaryImageFrobeniusMap`.
3. `boundaryWeilShift ... c.C sΦ` puts the ordinary open image in shift one
   and transports its structure by `Φ(K[1]) ≅ Φ(K)[1] ≅ K[1]`.
   The existential `sΦ : Φ.CommShift ℤ` supplies the structural cohomological
   pullback/shift comparison, as in the landed parent
   `qbarCurveIntermediateExtension`. It is an asserted structural witness,
   not an added hypothesis, an arbitrary morphism, or a triangulation on pairs.
   It can be supplied by the usual finite-stage complex shift and descent.
   Both pair Hom sets use `sfCommonStageWeilComplex ... c.C Ω`: the first
   goes from closed image to shifted open image, and the second from shifted
   open image to closed image. Forgetting them gives exactly the two geometric
   Hom sets in clause 1. Vanishing is expressed by `Subsingleton`, so it says
   every morphism is zero in each of these additive categories.

The proof docstring now names the source and reproduces all six DAG steps:
ordinary heart/adjunction, heart extension triangle, adjunction retraction,
consecutive-arrow identity, negative-degree orthogonality, and faithfulness of
forgetting fixed pairs. It also explains the structural shift comparison.

Dependency declarations read and used (including their complete signatures):

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `FiniteFieldDatum.geometricFiber`.
* `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  `Sheaf.AlgebraicGeometry.PureDimension`: `Scheme.IsPureDimension`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
  These occur in the imported recorded curve data or the explicit boundary.
* `Sheaf.Paper.QbarCurveOrdinaryImage` (current server source also read with
  `scompile.py --source`): `qbarCurveOrdinaryPushforward`,
  `qbarCurveOrdinaryAdjunction`, on the recorded common-stage hearts.
  The older `CurveWeilMiddleExtension` interface is reexported there but is
  not used as a substitute for the current carrier category.
* `Sheaf.Paper.LisseIntegralSmallCoefficients`:
  `Scheme.LisseIntegralSheafOfUniverses`, read as the recorded integral
  inverse-system convention. The landed `Sheaf.Paper.CommonStageLisse`:
  `HasCommonStageLisseLattice` supplies its actual degree-zero integral
  lattice criterion in the intrinsic common-stage carrier.
* `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeart`,
  `sfCommonStageHeartProperty`;
  `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, its actual finite
  stages, literal pairs, Hom colimits and shifts.
* `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilSheaf`,
  `sfCommonStageWeilComplex`, `sfCommonStageWeilFrobeniusPullback`.
* `Sheaf.Paper.WeilIndSheafCategory`: `zlHeartPull`, `zlHeartFrobenius`,
  `zlHeartSquare`. The last is the unique heart lift of the normalized
  finite-stage inverse-image composition/Frobenius square. Only those
  geometric heart declarations are used; no ind-sheaf category replaces a
  Hom category of the item.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`
  was read for the cohomological convention; actual common-stage shifts
  are the imported finite-stage coefficient shifts.
* Proof imports, since they have statements already:
  `WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology`
  (abstract heart/short-exact triangle infrastructure), and
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
  (consecutive-arrow-zero). The open-closed cohomology proof prerequisite
  currently has no recorded Lean declaration; the statement does not
  assume its conclusions as hypotheses.

Edge cases checked: `Z = ∅`, `E = 0`, `F₀ = 0`, and `j = id` give zero Hom
sets, with no nonzero/rank/nonemptiness assumption. For constant F on
`G_m ⊂ A¹`, ordinary `Hom(j_*F,i_*E)` can be nonzero (the map to the
nonzero boundary stalk); this explicitly detects the returned missing-shift
fault. With source `(j_*F)[1]`, the reverse Hom is a negative Ext and vanishes.
Nontrivial local inertia is allowed: no boundary stalk is assumed zero, only
the lisse hypothesis on the open. There is no properness assumption and no
Frobenius structure on arbitrary geometric E.

Searches (original findings retained and malformed query explicitly corrected):

* Original `leanfinder` query "boundary Hom vanishing for a middle extension
  on a curve": eight general homological-complex extension hits, no match.
* Original Loogle query `DerivedCategory Hom Subsingleton IsAdicConstructibleSheaf`
  reported unknown identifier `Hom`; this malformed query was not evidence
  of absence. Repair Loogle query `"IsoAlgebra"` succeeded with three
  ordinary AlgCat algebra-equivalence hits, none concerning Frobenius pairs.
* Repair `leanfinder` query "ordinary direct image constructible common stage
  sheaves Frobenius fixed pairs right adjoint": eight general sheaf/module
  right-adjoint hits. `Scheme.Modules.pushforward` is for structure-sheaf
  modules, not this finite-stage coefficient heart.
* Repair `leansearch` query "Constructible l adic sheaves ordinary direct
  image closed immersion with Frobenius structure induced by adjunction":
  eight hits including `SheafOfModules.pushforwardPushforwardAdj`,
  `Scheme.Modules.restrictAdjunction`, and closed-immersion definitions.
  None supplies the present common-stage fixed-pair operation.
* Original Mathlib grep `middleExtension|boundaryHom|boundary.*Hom` in
  AlgebraicGeometry: zero hits. Repair Mathlib grep
  `Frobenius|ordinary.*direct.*image` in AlgebraicGeometry: zero hits.
* `rg` in Mathlib, upstream `WeilConjectures`, and shared `lean/Sheaf` for
  `boundaryHomVanishing|boundaryClosedPushforward|boundaryOrdinaryWeilImage|boundaryWeilShift`:
  no name matches. `grep -rn` for this item in upstream: no match.
* `tools/blueprint_refs.py search 'ordinary direct image'`: thirteen blueprint
  matches, including the existing ordinary open middle extension and generic
  module direct-image notions; none is this missing common-stage boundary
  image/normalized mate definition. A more specific search for
  `ordinary closed direct image` returned zero blueprint matches. Read the
  relevant generic operations and open-closed cohomology nodes as well.
* `tools/blueprint_refs.py ancestor` identifies `rem-dl-a1-conventions` as
  the ancestor for the added definition node. Direct read-only dependency
  traversal found no path back to this item from either added dependency.

No mathematical node statement is changed or disputed. The source's mistaken
"Second paragraph" locator in the base node is not silently edited: the actual
blueprint source was opened and its final ordinary-image paragraph is cited in
both module and theorem docstrings.

## New nodes

`def-dl-a1-boundary-ordinary-images`, module
`lean/Sheaf/Paper/BoundaryOrdinaryImages.lean`, supplies the missing common-stage
closed ordinary image and counit-normalized induced pair construction. It uses
`zlHeartPull` and the actual heart square rather than a private inverse image.
The generic module operations node describes fixed-ring module sheaves; it does
not give this right adjoint on the intrinsic common-stage heart. The open image
is reused from its existing module. The open-closed cohomology lemma states
properties of these images but currently supplies no Lean construction.

`boundaryClosedRestriction_isLeftAdjoint` is the named postponement for existence
of the specified ordinary adjoint, which determines its data up to unique
adjunction-compatible isomorphism. `boundaryImageFrobeniusMap_isIso` is the named
postponement for invertibility of the explicit normalized mate. Both facts are
explicit clauses of the new definition node, with complete natural-language
proofs in their docstrings. All other declarations are real constructions;
there is no `Nonempty` choice of an unrelated map or isomorphism. Every helper
is listed in `lean.declarations`.

The existing, landed `def-a1-common-stage-lisse-lattice` is added to the item's
statement dependencies for the actual lisse predicate. Its module is imported;
it is not redefined or redelivered.

## Dependency modules

`def-weil-pbc-qbar-category` gets a §1(B) module repair,
`lean/Sheaf/Paper/IntrinsicQbarCategory.lean`, with the required `lean.note`.
The former `pbcQbarCategory` uses the legacy completed integral predicate,
so it is not literally the carrier of the already recorded `sfCommonStageHeart`
and `sfCommonStageWeilComplex`. The repair publicly imports both published
interfaces and uses the existing `generalAlgebraicallyClosedConstructibleCategory`:
the current intrinsic finite-stage pairs, actual Hom colimit, scalar stages,
cohomological shifts and common-stage cone triangles. The primary `intrinsicPbcQbarCategory` alias retains exactly the source domain
hypotheses (Noetherian, finite dimension, coefficient invertibility) and is
definitionally the existing pair type. It adds no carrier data.

The entire scalar-action clause of the dependency is also retained.
`intrinsicQbarStageFieldEquiv` composes the integral-normalized fraction-field
identification `sfRationalCoefficientEquiv` with the canonical small-model
`Shrink.algEquiv`. `intrinsicQbarStageLocalizedLinear` caches the already existing
localized-ring linear structure; `intrinsicQbarStageLinear` restricts it along
that explicit equivalence to the actual intermediate coefficient field.
`intrinsicQbarScalarCompatible` is the named semilinearity statement, with its
proof in the docstring. `intrinsicQbarScalarAction` then applies the existing
`StageSystem.qbarScalarHom`, using exactly the compositum and quotient formula
of the dependency. It is not an arbitrary action. The scalar laws on the
existing colimit abelian groups are stated in `intrinsicQbarLinear_existsUnique`;
`intrinsicQbarLinear` takes the uniquely prescribed structure. The formula fixes
all data fields, so only the law proofs are postponed. The existing generic
`qbarScalarHom_mkHom` is imported for the calculation at any overfield, including
equal stages. Thus the repair covers the scalar-action, pair-category and
triangulation clauses, without an envelope or an unrelated carrier.

Only this dependency node's `lean` changes. Both its new named theorem
statements are clauses of that node, and their docstrings give their natural
language proofs. The main consumer imports the repair through
`BoundaryOrdinaryImages`. It does not impose a coefficient/site universe
equality. The original PBC declarations remain publicly available.

## Second reading by NM

I read the repaired signature against the unchanged current node and opened
blueprint source after the initial saved-packet dry run. The old degree-zero
reverse clauses were false on the constant-sheaf punctured-line example; both
now have exactly the same shifted open image as their corresponding forward
clause. The old ambient sheaf and derived-of-Weil categories are replaced by
the recorded finite-stage heart and fixed-pair categories. The ordinary open
image is exactly the recorded `qbarCurveOrdinaryPushforward`; the new closed
image is fixed by its actual ordinary adjunction, and both induced Weil
structures are the specified counit mates. Forgetting them gives the same
geometric carriers in the first conjunct, and forgetting the shifted pair gives
exactly A[1]. This checks every one of the four Hom directions and both sheaf
quantifiers. The source geometric hypotheses, complement and lisse condition
are all present; no extra characteristic fact remains. I also checked the new
helper signatures, both proof docstrings, all namespace/universe binders, the
coefficient-category module repair, and the absence of a dependency
cycle. All five postponed statements have matching node clauses and explicit
proof docstrings; no proofs are completed in stage 2.

Validation: the initial repaired two-module compile passed. The complete scalar-action
repair also compiled cleanly. The first expanded dry run caught a grouped-citation
format error in the new definition node; each dependency is now cited separately
as `[id]`. Its warning about a non-verbatim existing signature belonged to the
superseded existing-record-only coefficient repair, which is now replaced by the
full dependency module. The final packet is validated by another complete dry run.

The final compiler pass also checked the restricted PBC alias successfully.
A subsequent preflight identified that an imported side-library declaration cannot
be listed in this module's `lean.declarations`. The imported general category entry
was removed; its local, source-domain alias `intrinsicPbcQbarCategory` remains the
primary declaration. No Lean source or mathematical statement changed in that fix.

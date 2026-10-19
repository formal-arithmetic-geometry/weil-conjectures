## Worker report

The delivery states `WeilConjectures.subsingleton_adicMiddleExtension_hcZero` in
`Sheaf.Paper.MiddleExtensionHcZero`. Its proof is exactly `by sorry`. It also exposes one
standard separatedness instance by `inferInstanceAs`; this is the existing pullback
instance, not a postponed geometric theorem or new assumption. No definition node,
dependency repair, or statement correction is needed. Only the item's `lean` field changes.

Hypotheses and clauses, read against the complete natural statement:

- The finite field, characteristic, cardinality, and chosen geometric algebraic closure are
  `D : FiniteFieldDatum.{u}`; its `k₀` and `k` are exactly the fields used below.
- The coefficient prime and its distinctness from the characteristic are `(l : ℕ)`,
  `[Fact l.Prime]`, and `hl : l ≠ D.p`. The chosen coefficient closure is
  `(Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`, the
  universe convention of the recorded lisse and ordinary-image interface.
- `c : AlgebraicGeometry.Scheme.MiddleExtensionCurve D` supplies `c.C`, `c.U` and
  `c.j : c.U ⟶ c.C` over `Spec k₀`. Its fields give separatedness and finite type
  (locally finite type plus quasi-compact) of both schemes, the open immersion
  `c.j.left`, and `c.dense : DenseRange c.j.left.base`. Thus density is precisely
  closure of the image equal to the entire target, not a generic-point substitute.
- Affineness is `[IsAffine c.C.left]`. Smooth relative dimension one is
  `[SmoothOfRelativeDimension 1 c.C.hom]`. Geometric connectedness is
  `[GeometricallyConnected c.C.hom]`, whose definition tests all field base changes.
  The bundle's smoothness and pure-dimension-one fields are already consequences of
  these hypotheses: the nonempty smooth curve over a field has pure dimension one.
  Its conditions on U impose no restriction: a dense open in this finite-type
  Noetherian separated curve is itself separated finite type. Conversely, forgetting
  the bundle yields exactly the stated curve and dense open. No connectedness of U
  is assumed independently.
- The underlying lisse sheaf is `F : adicMiddleExtensionLisse l Ω c hl`. This is the
  recorded finite-extension, adic lisse category on `(D.geometricFiber c.U).left`,
  with its actual finite-stage pair and lattice. An arbitrary Weil structure is the
  isomorphism `theta : (sfCommonStageWeilFrobeniusPullback ...).obj
  (adicMiddleExtensionInput ... F) ≅ adicMiddleExtensionInput ... F`.
  This is exactly the fixed-pair convention of def-weil-weil-sheaf-complex;
  theta need not preserve the input lattice. No purity, weight, ramification,
  semisimplicity, or nonzero-rank condition is present.
- Geometric base change is `D.geometricFiber c.C` (respectively `c.U`); these are
  the actual pullbacks along the chosen `k₀ → k`. The ordinary image is
  `adicMiddleExtensionWeil l Ω c hl F theta`. Its carrier is
  `adicMiddleExtensionObject`, built by applying ordinary module direct image to
  the completed input module and then placing that module in degree zero, before
  rationalization and finite-stage inclusion. It is not the full derived image.
  `adicMiddleExtension_constructible` supplies the recorded heart membership.
- Forgetting Weil structure is the literal application
  `(sfCommonStageWeilForget D l hl c.C Ω).obj (adicMiddleExtensionWeil ... theta)`.
  Its carrier is the same ordinary-image common-stage object, so theta contributes
  no extra coefficient or action assumption to the cohomology.
- `compactification : Compactification (D.geometricFiber c.C).hom` is an arbitrary
  presentation of the canonical compact-support construction. Every compactification
  is covered; existence follows from separated finite type, so this does not assume
  that C is proper. The global helper instance only exposes separatedness of its
  structure morphism by the standard `pullback.snd` base-change instance. The other
  required geometric finite-type and quasi-compact instances already synthesize.
- The conclusion is `Subsingleton (adicCompactCohomology ... compactification ... 0)`.
  The recorded operation computes completed integral compact sections at the actual
  finite coefficient stage, rationalizes, takes degree-zero cohomology, and extends
  scalars to Ω. A module has a zero element, so Subsingleton is exactly H_c^0=0.
  No additional cohomological vanishing or Frobenius assertion is included.

Dependency declarations read and used:

| Node | Module | Declarations |
| --- | --- | --- |
| def-wf-middle-extension | Sheaf.Paper.CurveWeilMiddleExtension (publicly retaining Sheaf.Paper.CurveMiddleExtension) | AlgebraicGeometry.WeilSheaf.curveWeilMiddleExtension; AlgebraicGeometry.Scheme.MiddleExtensionCurve; the finite-level ordinary-image constructions |
| def-weil-ordinary-compact-cohomology | Sheaf.Paper.CommonStageCompactWeilCohomology | WeilConjectures.adicCompactCohomology, with the retained integral/rational cohomology definitions |
| def-sbc-smooth-morphisms | Mathlib.AlgebraicGeometry.Morphisms.Smooth | AlgebraicGeometry.SmoothOfRelativeDimension (and Smooth) |
| def-weil-weil-sheaf-complex | Sheaf.Paper.SfWeilSheafComplex, public through AdicMiddleExtensionConstructible | WeilConjectures.sfCommonStageWeilFrobeniusPullback, sfCommonStageWeilForget |
| lem-a1-adic-middle-extension-constructible | Sheaf.Paper.AdicMiddleExtensionConstructible | WeilConjectures.adicMiddleExtensionLisse, adicMiddleExtensionInput, adicMiddleExtensionWeil, adicMiddleExtension_constructible |

The curveWeilMiddleExtension specialization uses the older upstream WeilSheaf encoding;
its module explicitly retains the full finite-stage CurveMiddleExtension interface.
The theorem uses the geometric ordinary image already constructed by the constructibility
dependency on precisely that retained interface. It introduces no second middle extension.

All currently recorded proof-dependency modules are imported without `public` (statement
imports take precedence when a node is also a proof dependency). These include the Mathlib
base-change, Noetherian and irreducibility modules; SmoothConnectedCurveLocalRings;
GaloisLisseRepresentations; ClosedSubsetProperOverBase; and the upstream smooth-dimension
and proper-affine-finite modules. `lem-a1-constructible-degree-zero-proper-support` has
neither a Lean record nor mathlib_match in the supplied DAG: its future module import is
omitted, and its exact role is retained in proof steps 5 and 7 of the docstring. It is only
a proof dependency; no missing object from it is needed to type this stage-2 statement.

Edge cases checked before drafting: F=0 gives zero; j=id gives ordinary lisse affine-curve
H_c^0 vanishing; a constant sheaf on A¹ and Kummer examples on G_m or with a boundary in A¹
have no nonzero proper-support sections. Arbitrary wild ramification is permitted.
Geometric connectedness uses ConnectedSpace and excludes the empty target as in the node;
density on a nonempty target excludes an empty U. The boundary may be empty (j=id).
Disconnected C₀ and dimension-zero targets are outside the stated hypotheses. The arbitrary
Weil isomorphism need not preserve a lattice. Every compactification and every finite
coefficient field/model in the recorded lisse category are quantified, including the base
coefficient field. No field embedding in ℂ or weight convention occurs.

Searches made with the prescribed wrapper (all successful tool calls, 2026-10-18):

- LeanFinder: "The degree zero compactly supported etale cohomology of the ordinary direct
  image of a lisse sheaf from a dense open in a smooth geometrically connected affine curve
  is zero". Eight hits, headed by exists_app_map_eq_zero_of_isLimit and
  exists_appTop_map_eq_zero_of_isLimit; the others concern structure sheaves, singular
  homology, or the etale locus, not this statement.
- Loogle: `"cohomology", "support"`. Zero hits.
- Mathlib grep: `compactlySupportedCohomology|compactSupport.*lisse|middleExtension`.
  Zero hits.
- LeanSearch: "A lisse adic sheaf extended by ordinary direct image to a connected nonproper
  smooth curve has no nonzero compactly supported sections". Eight hits: structure-sheaf
  section lemmas, HasCompactSupport.extend_zero, Opens.toScheme_presheaf_obj,
  Modules.restrictAdjunction, and general sheaf/condensed-category functors; no match.
- Project rg: `middleExtension|directImage_zero|HcZero|hcZero` in lean/Sheaf/Paper and
  upstream WeilSheaf/DeligneLaumon/AffineLine. Inspected the upstream general theorem
  AlgebraicGeometry.subsingleton_compactlySupportedCohomology_directImage_zero in
  WeilConjectures.DeligneLaumon.AffineLine.Endpoints, its affine-line wrapper in Upper,
  and Sheaf.Paper.AffineCurveHcZero. The latter concerns a lisse sheaf on the entire curve,
  not an ordinary middle extension from a dense open. The upstream general theorem uses
  the PadicAlgCl pro-etale module-object WeilSheaf category and cohomology of the derived
  category of Weil sheaves. Reading Adic/Module, WeilSheaf/Category and WeilSheaf/Cohomology
  confirms it is not a theorem on the required finite-extension completed/rationalized
  common-stage construction. No comparison identifies these coefficient interfaces.
- Upstream `grep -rn 'lem-a1-middle-extension-hc0'` returned no hits. Broader upstream rg
  for middle-extension/compact-support-zero located only the above older theorem and
  wrapper. No declaration of the new theorem or helper name was found.

Validation: scompile.py checked both the sandbox module and its intended library path
cleanly (3.8 s and 4.2 s for the initial clean version). An initial failed compile only
reported the missing bundled geometric separatedness instance, repaired by exposing the
actual existing pullback instance. Final wrapper compile and delivery preflight are run
again after finalizing imports and records. No STATEMENT-DISPUTED flag or node fault.

## Second reading by N3

I reopened the node and reread the complete final signature and every construction it
uses as a separate self-check; no other agent was started. The independent maintainer
review is performed on the delivered branch, as specified in the dispatch brief.

The finite-field and coefficient binders retain the chosen fields and the distinct prime.
The curve bundle expands to the dense open immersion and separated finite-type smooth
pure-dimension-one models; the explicit affine, relative-dimension-one and geometric
connectedness binders give exactly the additional hypotheses in this node. The seemingly
extra pure-dimension and finite-type-U fields are consequences of those hypotheses, as
explained above. In particular, density is an actual DenseRange field and geometric
connectedness tests every field extension. F is the geometric lisse finite-stage sheaf,
and theta is an arbitrary Frobenius isomorphism on its common-stage image. Reading
adicMiddleExtensionImageIntegral confirms that ordinary pushforward precedes the single
functor in degree zero; it does not substitute Rj_*. The conclusion explicitly forgets the
induced Weil structure before the recorded adicCompactCohomology in degree zero.
Subsingleton is exactly zero cohomology, including rank zero. The arbitrary compactification
binder is presentation data, not a new geometric condition. No clause concerning weights,
purity, or ramification has appeared. No statement mismatch was found. The compile-driven
instance repair changes only how the already inherited separatedness is made available;
it adds no hypothesis or postponed theorem. All seven proof steps of the node are retained
in the theorem docstring, and all explicit universes/variables are bound.

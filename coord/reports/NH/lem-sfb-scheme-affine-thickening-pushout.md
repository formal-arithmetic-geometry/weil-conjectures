## Worker report

The module `Sheaf.AlgebraicGeometry.SchemeAffineThickeningPushout` states
`AlgebraicGeometry.exists_scheme_affine_thickening_pushout`. Its only theorem has
`by sorry`; there are no new definitions, helper axioms, or extra hypotheses.
The node copy changes only `lean`. No statement correction or dependency repair
is needed.

Source checked: `literature/stacks-project/more-morphisms.tex`, Tag 07RT,
`lemma-pushout-along-thickening`, statement and proof, lines 4206–4273. The node
asks for pushout existence, thickening of the other leg, and cartesianness. These
are exactly the clauses stated here. The additional structure-sheaf description
in the source is used in the proof plan, rather than added to the conclusion.

Clause-by-clause correspondence:

- The schemes T, T', S are `{T T' S : Scheme.{u}}`, with an explicitly declared
  arbitrary universe `u`. The morphisms are `(i : T ⟶ T') (a : T ⟶ S)`.
- The thickening hypothesis is `(hi : IsThickening i)`. The recorded dependency
  defines it as `IsClosedImmersion i ∧ Surjective i`. A surjective closed
  embedding is a homeomorphism; this is precisely the node's closed immersion
  inducing a homeomorphism. No square-zero or nilpotence-exponent condition is used.
- Affineness is `[IsAffineHom a]`. Its Mathlib definition is exactly that for
  every affine open U in S, `a ⁻¹ᵁ U` is affine. The class binder introduces
  this mathematical hypothesis, without an assumption on S or T themselves.
- Existence of the scheme pushout and its two arrows is
  `∃ (P : Scheme.{u}) (j : S ⟶ P) (b : T' ⟶ P), ...`.
- The commutative-square equation is included in `IsPushout a i j b` through
  `CommSq.w : a ≫ j = i ≫ b`, namely j composed with a equals b composed with i.
- The universal property against every scheme Z is `IsPushout a i j b`, whose
  `isColimit'` is the colimit property of `PushoutCocone.mk j b w` in Scheme.
  `IsPushout.desc` gives the extending morphism, `inl_desc`/`inr_desc` its
  restrictions, and `hom_ext` uniqueness. Z need not be affine or separated.
- The other leg is a thickening: `IsThickening j` uses exactly the same dependency
  predicate, so includes both closed immersion and homeomorphism on point spaces.
- The square is cartesian: `IsPullback a i j b`. Its limit cone has vertex T and
  projections a and i. This gives the canonical, projection-compatible isomorphism
  `T ≅ pullback j b` through `IsPullback.isoPullback`; it is not an unrelated
  isomorphism of schemes. Scheme pullbacks are supplied by Mathlib.
- The lack of a finite-order assumption is literal: there is no exponent,
  square-zero ideal, finite-order thickening predicate, or uniform nilpotence bound
  anywhere in the theorem's hypotheses.

Recorded statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`. Read their full
  structure signatures and docstrings in Scheme.lean.
- `def-sbc-first-order-thickening`:
  `WeilConjectures.AlgebraicGeometry.Thickening`,
  `AlgebraicGeometry.IsThickening` (one of the recorded declarations, rather
  than the narrower main-record `IsFirstOrderThickening`). Read all four predicates.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`.
  The cartesian formulation uses Mathlib's `IsPullback` and its `isoPullback` API,
  with scheme pullbacks from `Mathlib.AlgebraicGeometry.Pullbacks`.

The affine hypothesis uses the existing `AlgebraicGeometry.IsAffineHom` in
`Mathlib.AlgebraicGeometry.Morphisms.Affine`; the square predicates are the existing
`CategoryTheory.IsPushout` and `CategoryTheory.IsPullback` in
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`. No duplicate notion
is introduced. All statement-dependency modules are public imports. The already
stated proof dependencies are included as plain proof imports (or are already
publicly available through the statement imports):
`WeilConjectures.AlgebraicGeometry.ThickeningAffineScheme.isAffine_of_isThickening`,
`Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout.isPushout_spec_pullbackCone_of_surjective`,
and the Mathlib modules containing the recorded closed immersion, spectrum,
localization/open immersion, principal-open basis, affine-open basis, morphism-gluing,
and spectrum fibre-product declarations. The proof-only node
`lem-sfb-ring-fibre-product-spectrum` has no recorded Lean module in the read clone,
so there is no module to import for it; its role remains explicitly documented in
steps 2 and 3 of the proof docstring. It supplies no missing object in this statement.
No import of a downstream algebraic-space or curve theorem was added.

Edge cases checked before writing:

- If S is empty, a forces T empty and the thickening forces T' empty. The empty
  scheme is a valid existential witness; neither universal property excludes it.
- If T is empty and S arbitrary, T' is empty and the pushout is S, with j identity.
- If i is identity, P = S, j identity and b = a give the expected square.
- If a is identity, P = T', j = i and b identity give the expected square.
- Zero affine coordinate rings are allowed by Scheme, IsThickening, and IsAffineHom.
- A nil ideal need not be nilpotent: for example the ideal generated by the x_n in
  k[x_1,x_2,...]/(x_n^(n+1) for n ≥ 1) is nil without a uniform nilpotence exponent.
  The quotient closed immersion is included by `IsThickening`; no stronger
  finite-order predicate appears.
- The theorem is universe-polymorphic in the ambient category Scheme.{u}, and
  tests all targets in that category; it does not quantify over an independent
  smaller universe of test schemes.

Searches (all with msearch.py under group NH and this item unless noted):

1. LeanFinder: "The pushout of a scheme thickening and an affine morphism exists,
   its other leg is a thickening, and the square is cartesian". Eight hits:
   spectra of ring pushouts give pullbacks, and other hits concern affine opens,
   affine transition limits, or base-affine pullback existence. No matching theorem.
2. LeanSearch: "A scheme thickening and an affine morphism admit a pushout that is
   a cartesian square and a thickening on the other side". Eight hits, including
   `isPullback_SpecMap_pushout`, general `IsPushout.of_hasPushout`, and an affine
   pullback instance. None asserts scheme pushout existence under these hypotheses.
3. Loogle: `IsPushout, IsAffineHom` returned zero hits and reported unknown
   unqualified identifier `IsPushout`. Follow-up `AlgebraicGeometry.IsAffineHom`
   searches the qualified existing affine predicate; it is used directly here.
4. msearch grep: `IsPushout|pushout` in AlgebraicGeometry returned 25 hits,
   including pushouts of open immersions, ring-section pushouts, and the
   contravariant Spec/pullback results. None states the node.
5. rg searches in `lean/WeilConjectures` for the node id, pushout/thickening in
   either order, and existence of pushouts found ring-sheaf pushouts, deformation
   spaces, and etale descent results, but no scheme affine-thickening theorem.
6. rg in `lean/Sheaf` found `SpaceAffineThickeningPushout`, `FerrandSchemePushout`,
   `CurveInfinitesimalPushout`, and `AffineClosedPinchingPushout`. Read the relevant
   full signatures: the space theorem has a different ambient category and no
   cartesian clause; its scheme specialization lacks the thickening/cartesian
   conclusion. Ferrand's theorem requires the affine leg to be integral and affine
   neighbourhoods of its fibres, so does not cover arbitrary affine a. The closed
   affine pinching theorem requires all three inputs affine, and is used as the
   recorded proof dependency. The curve theorem is a downstream application.
7. Name-clash rg in Mathlib, WeilConjectures, Sheaf, and
   `dag/lean_names_upstream.json` found no
   `AlgebraicGeometry.exists_scheme_affine_thickening_pushout`.

Validation: the prescribed `scompile.py` compiled both the sandbox and library
module successfully, with no error or non-sorry warning. There is no
STATEMENT-DISPUTED issue and no node fault requiring correction.

## Second reading by NH

This is the worker's separate final rereading, not a claim of an independent
agent review: the dispatcher explicitly forbids starting other agents and reserves
the independent reading for the maintainer. I reopened the node, Tag 07RT, and the
finished module and compared every clause as above. In particular I checked the
orientation `a i j b` for both square predicates: their common source is T, their
right vertex S, lower vertex T', and common target P. Thus j is the thickening
leg and T is the fibre-product vertex. The use of `IsThickening` rather than
`IsFirstOrderThickening` preserves the explicit arbitrary-thickening scope. The
pushout is in Scheme, so its colimit universal property includes nonaffine targets.
The cartesian conclusion retains the specified projections through `IsPullback`.
No missing hypothesis, extra conclusion, private definition, or statement change
was found in this rereading; no changes were required.

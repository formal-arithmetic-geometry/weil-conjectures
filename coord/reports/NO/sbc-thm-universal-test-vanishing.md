## Worker report

The module Sheaf.AlgebraicGeometry.UniversalCurveTestVanishing states
AlgebraicGeometry.Etale.isZero_universalCurveTest_higherDirectImage, with proof `sorry`.
It states the node without correction. No definitions or dependency repairs are needed.
The declaration docstring carries all seven proof steps of the node, including the
connected-component correction to the torsor argument.

Hypothesis and conclusion correspondence:

- The normal domain A is `A : Type u`, `[CommRing A]`, `[IsDomain A]`, and
  `hA : IsNormalScheme (Spec (.of A))`. The last predicate is the recorded integral-normal
  scheme predicate; for a domain A, normality of Spec A is exactly integral closedness of A.
- The base S = Spec A is substituted directly throughout, rather than introducing a scheme
  together with an isomorphism to Spec A.
- Its algebraically closed fraction field L is `[Field L]`, `[Algebra A L]`,
  `[IsFractionRing A L]`, and `[IsAlgClosed L]`. The fraction-ring condition supplies the
  specified injective inclusion of A into L, with its correct fraction-field property.
- The extension of algebraically closed fields K/L is `[Field K]`, `[Algebra L K]`,
  `[IsAlgClosed K]`. A unital homomorphism of fields is injective, so this supplies the
  inclusion L into K without an additional assumption or an arbitrary scheme map.
- The affine total space is `{X : Scheme.{u}} [IsAffine X]`.
- The affine smooth relative curve is `f : X ⟶ Spec (.of A)`, `[IsAffineHom f]`, and
  `[SmoothOfRelativeDimension 1 f]`. The latter implies Smooth and implements the
  recorded relative-dimension convention. No connectedness or nonemptiness is imposed on X.
- The other scheme and projections are `{Y : Scheme.{u}}`, `h : Y ⟶ X`, and
  `e : Y ⟶ Spec (.of K)`.
- The specified geometric generic map g is literally
  `Spec.map (CommRingCat.ofHom (algebraMap L K)) ≫
  Spec.map (CommRingCat.ofHom (algebraMap A L))`.
- The base-change square, including its chosen Cartesian identification and both projection
  equations, is `sq : ChosenCartesianSquare h e f (...)`.
- The signed integer and its invertibility on Spec A are `(d : ℤ)` and
  `(hd : IsUnit (d : A))`. The canonical global-sections isomorphism Γ(Spec A, ⊤) ≅ A
  identifies this with invertibility on the base.
- The coefficient is `Y.constantZMod d.natAbs`, which unfolds to the recorded constantSheaf
  applied to the abelian group `ULift (ZMod d.natAbs)`. Since (d) = (|d|) in ℤ, this is the
  stated ℤ/dℤ, including negative d. The ULift places values in the site's u+1 universe.
- The range q ≥ 1 is `(q : ℤ) (hq : 1 ≤ q)`.
- The conclusion is `IsZero` of the q-th `DerivedCategory.Plus.homologyFunctor` applied to
  `Etale.rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h` of the constant cyclic sheaf,
  placed in degree zero by `DerivedCategory.Plus.singleFunctor ... 0`. This is exactly
  R^q h_*(ℤ/dℤ) = 0 in the abelian category of small-etale abelian sheaves.

Dependency declarations used:

- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.SmoothOfRelativeDimension
  (and its Smooth consequence), as recorded by def-sbc-smooth-morphisms.
- Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso: uses the shared
  AlgebraicGeometry.ChosenCartesianSquare imported there from
  Sheaf.AlgebraicGeometry.ChosenCartesianSquare, as specified by sbc-def-base-change-square.
- Sheaf.AlgebraicGeometry.NormalScheme: AlgebraicGeometry.IsNormalScheme.
- The scheme-conventions dependency introduces no declaration of its own; Scheme, IsAffine,
  IsAffineHom, and Spec are the existing notions named in its convention record.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: CategoryTheory.constantSheaf, through
  AlgebraicGeometry.Scheme.constantZMod in WeilConjectures.AlgebraicGeometry.Sites.Kummer.
  Its definition was read: sheafification of the constant abelian presheaf, with ULift.
- WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence:
  AlgebraicGeometry.Etale.rightDerivedLowerStarPlus, the bounded-below right derived functor
  of Etale.lowerStar from WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs. These are
  the declarations recorded for def-weil-pbc-direct-image. Its module record names Defs,
  while its derived declaration is actually supplied by UpperLowerStarCoherence.

Every proof dependency with a recorded module is imported (without public unless also a
statement dependency). sbc-thm-cohomological-dimension-of-an-affine-curve has no recorded
module and therefore contributes no import. The presheaf computation uses the landed
abelian version Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf. The source of the
recently landed SmoothCurveAlgClosedExtension was read using `scompile.py --source` because
it is not present in the older local mirror.

Edge cases: d = 0 is excluded by IsUnit in the nonzero domain A, while d = ±1 gives the
zero cyclic coefficient. Both signs and all characteristics compatible with hd are retained.
The base cannot be empty, as A is a domain, but X and Y may be empty or disconnected.
q = 1 is included and q = 0 is excluded exactly as the node requests. No finite-type,
Noetherian, connected, section, or separability hypothesis has been added. A, L, K, X, Y
use a common arbitrary universe u; coefficients are in u+1 as required by the existing
etale derived API. There is no quantification over test schemes in a smaller universe.

Searches:

- msearch.py leanfinder, query "Higher direct images constant torsion etale sheaf geometric
  generic fibre smooth affine curve vanish": eight unrelated etale-locus, differential,
  and affine-limit hits; no match.
- msearch.py loogle, query '"higherDirectImage"': zero hits.
- msearch.py grep, query `higherDirectImage|constantZMod`: zero Mathlib hits.
- msearch.py leansearch, query "Higher direct images constant cyclic abelian etale sheaf
  geometric generic smooth affine curve vanish": service unavailable (Internal Server Error).
- rg over upstream WeilConjectures and project lean/Sheaf for
  `sbc-thm-universal-test-vanishing|universal.*[Vv]anishing|curveTest|curve_test` found
  CurveTestDatum and Vanishing in the upstream smooth-base-change folder. Opened their full
  relevant signatures, definitions, and docstrings. The upstream theorem
  Etale.CurveTestDatum.isZero_higherDirectImage_constantSheaf concludes vanishing for module
  sheaves Λ/dΛ, parameterized by Λ : Type (u+1), on its bundled datum with natural d.
  It is not the node's literal abelian constant-sheaf statement; using it as existing would
  conceal the coefficient and datum comparisons. The new statement uses the original
  canonical abelian constructions, without duplicating them.
- rg for `isZero_.*[Uu]niversal|isZero_.*[Cc]urve|universalTest` in both source trees found no
  existing statement of the proposed abelian theorem. Exact declaration-name search in
  Mathlib, WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json found no collision.

Validation: the delivered module compiled cleanly on the server using scompile.py's server
fallback, nice 19, two threads, 60 seconds per file. The supplied script currently attempts
local compilation first; sandbox/server_only.py disables that backend in memory so the
unchanged server fallback is used. No local compiler or lake build was run.

No STATEMENT-DISPUTED flag and no statement correction.


## Second reading by NO

Read independently against the complete node, its blueprint source, and Stacks
etale-cohomology.tex, theorem-smooth-base-change, second proof (Tag 0EYU),
especially the final universal curve-test reduction. The earlier source fixes an
invertible n and d dividing n; requiring d itself invertible is precisely the
resulting condition (conversely choose n = |d|). No ambient Noetherian,
connectedness, or finite-generation hypothesis is assumed there.

Object/hypothesis/conclusion checklist, in node order:

- Schemes X, Y and base S: `{X Y : Scheme.{u}}` and the explicit `Spec (.of A)`.
  Verdict: exact, with S substituted by its specified affine spectrum.
- Normal domain A: `[CommRing A] [IsDomain A]` and
  `hA : IsNormalScheme (Spec (.of A))`. Opened NormalScheme.lean: the predicate
  is integral plus domain and integrally closed stalks. On Spec of a domain this
  is equivalent to normality of A, without a Noetherian assumption. Verdict: exact.
- Algebraically closed fraction field L with given inclusion A into L:
  `[Field L] [Algebra A L] [IsFractionRing A L] [IsAlgClosed L]`.
  Fraction-ring localization is injective for a domain. Verdict: exact.
- Algebraically closed extension K/L: `[Field K] [Algebra L K] [IsAlgClosed K]`.
  The algebra map between fields is injective. Verdict: exact.
- Affine X and affine smooth relative curve f: `[IsAffine X]`,
  `(f : X ⟶ Spec (.of A))`, `[IsAffineHom f]`,
  `[SmoothOfRelativeDimension 1 f]`. Opened the Mathlib class, whose
  standard-smooth charts are the recorded dependency's notion; its Smooth
  consequence adds no assumption. Verdict: exact.
- Geometric generic map g: the composite of `Spec.map` of `algebraMap L K`
  followed by `Spec.map` of `algebraMap A L`. Verdict: the specified canonical
  map, with the correct contravariant order, not an arbitrary geometric point.
- Projections h and e: `(h : Y ⟶ X)` and `(e : Y ⟶ Spec (.of K))`.
  `sq : ChosenCartesianSquare h e f (...)` supplies the Cartesian identification.
  Opened ChosenCartesianSquare.lean and BaseChangeInverseImageIso.lean: inherited
  commutativity and `isoPullback`, `hom_fst`, `hom_snd` are exactly a chosen
  identification respecting both projections. Verdict: exact.
- Integer coefficient invertible on S: `(d : ℤ) (hd : IsUnit (d : A))`.
  The global sections isomorphism of Spec identifies this with invertibility on S.
  Verdict: exact, including signed d.
- Constant abelian etale coefficient: `Y.constantZMod d.natAbs`. Opened its
  definition in Sites/Kummer.lean: `constantSheaf` of
  `AddCommGrpCat.of (ULift (ZMod n))`. Read the constant-sheaf dependency:
  sheafification of the constant presheaf. Since (d) = (|d|), this is the
  specified cyclic abelian sheaf. Verdict: exact.
- Every positive degree: `(q : ℤ) (hq : 1 ≤ q)`. Verdict: exact quantifier range.
- Vanishing R^q h_*: `IsZero` of `Plus.homologyFunctor ... q` on
  `rightDerivedLowerStarPlus AddCommGrpCat h` of `Plus.singleFunctor ... 0`
  of that constant sheaf. Opened both upstream lowerStar and its bounded-below
  derived definition: lowerStar is sheaf pushforward by the etale base-change
  functor, and rightDerivedLowerStarPlus is its rightDerivedFunctorPlus.
  Verdict: precisely the dependency's abelian higher direct image, not a
  module-coefficient replacement or vanishing of only global sections.

Edge cases: the domain base is necessarily nonempty; empty or disconnected X
and Y remain permitted, and the smooth-chart condition is vacuous on empty X.
There is no index-set quantifier in the statement; the proof's finite empty
coproduct is explicitly handled in its docstring. Zero coefficients d = ±1
are included. d = 0 cannot be a unit in the nonzero domain, exactly as in the
source. q = 1 is included, q = 0 is excluded. Positive characteristic is
restricted only by invertibility of d. Universe u is arbitrary; A, L, K and
schemes share the scheme universe, and ULift puts the cyclic coefficient in
the u+1 universe required by the small-etale abelian derived API. No smaller
universe of test objects or extra universe equality is assumed.

Independent searches used alternative wording: msearch leanfinder
"Positive derived direct image of a constant cyclic abelian sheaf along
algebraically closed generic extension of smooth relative curve is zero"
returned eight unrelated affine-limit, smooth-locus and module-category hits;
loogle `"constantZMod"` returned no hits; msearch grep
`higherDirectImage.*constant|generic.*[Vv]anishing` returned one irrelevant
prime-spectrum topology hit. Direct rg of Mathlib and project Sheaf sources
for `universalCurveTest`, `generic.*[Vv]anish`, `CurveTestDatum` and vanishing
variants found no matching declaration. Direct upstream searches located
SixFunctors/Etale/SmoothBaseChange/CurveTestDatum.lean and Vanishing.lean;
I opened the full datum and the concluding theorem signature and proof.
`CurveTestDatum.isZero_higherDirectImage_constantSheaf` has coefficient
`constantModSheaf Λ ... d` and target `higherDirectImage Λ`, with Λ a ring in
u+1; it is not this node's abelian statement. Its use would require actual
coefficient and datum comparison results, so it is not an exact existing match.
All notions in the new signature reuse the dependency declarations; no private
copy or new definition is introduced.

H5/H6/H8/H9: one public named theorem with proof `sorry`, no definitions,
no additional axioms, no local notation or instances. Source and blueprint
markers are present; the docstring reproduces all seven node proof steps,
including the finite-monodromy-orbit correction rather than assuming the
torsor connected. Every recorded proof-dependency module is imported; the
unstated affine-curve cohomological-dimension node has no module to import.
There are no new nodes, dependency modules, or statement corrections to audit.
No mathematical or signature mismatch found; the Lean and node record were
left unchanged. The recorded lean.statement was checked verbatim against the
source signature, with no unbound variables or universes.

Validation: recompiled the sole delivered module through scompile.py's
server backend, using the existing sandbox server_only.py adapter to prevent
the tool's default local attempt. This preserves the prescribed server nice 19,
two threads and 60-second per-file limit; no local compiler was run.

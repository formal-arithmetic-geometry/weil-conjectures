## Worker report

Q105, 2026-10-17. Module `Sheaf.Paper.SupportedAffineLineHomotopy` states
`WeilConjectures.PurityFiniteSetting.supportedAffineLineHomotopy` and supplies the
canonical maps its statement names. The mathematical statement is unchanged.
The only node changes are its Lean record and two added, already landed statement
dependencies: `def-asd-finite-etale-tate-sheaf` and
`lem-weil-pbc-comparison-pullback`. No new node or dependency-record repair is needed.

The source read was main-20261015,
`sec-smooth-purity/sk-prop-an/lem-pur-frame-independence.proof.md`, the shear
paragraph, together with the item's three proof steps and Stacks Tag 09XP
(`etale-cohomology.tex`, cohomology-with-support section). The false constant-sheaf
claim in that paragraph is already repaired by the DAG item's supported homotopy
formulation. This delivery follows that formulation.

Hypotheses and clauses, in order:

- The finite datum and arbitrary positive level are `(P : PurityFiniteSetting.{u})`.
  `P.Coefficient` is the existing universe-lifted `A_{E,n}`; `P.level_pos` already
  says `1 ≤ n`. There is no new divisibility hypothesis on the level.
- An arbitrary k-scheme is `{X : Scheme.{u}} [X.Over (Spec (.of P.field.k))]`.
  The local `a := X ↘ Spec (.of P.field.k)` is its given structure map.
- The closed subscheme is `{C : Scheme.{u}} (i : C ⟶ X) [IsClosedImmersion i]`.
  The support functor is the recorded kernel of restriction to `i.openComplement`.
- The affine-line projection is the local
  `p := AffineSpace (ULift.{u} (Fin 1)) X ↘ X`. Its closed inverse-image support
  is `i₁ := pullback.snd i p`; `pullback i p` is C ×_X A¹_X, canonically the
  same inverse-image closed subscheme as the node's A¹_X ×_X C.
- All integer cohomological degrees and twists are `(q r : ℤ)`.
  `affineSupportBaseTwist` specializes the existing `Scheme.finiteEtaleTateSheaf`
  at `Spec k`, using `ringChar P.Coefficient` as a canonical annihilator and
  `CharP.cast_eq_zero` as its annihilation proof. This permits every positive
  coefficient level, including levels not divisible by the ramification index.
  Positive powers and negative dual powers are those of the existing signed
  finite Tate sheaf. `affineSupportEtaleTwist` transports it by the exact inverse
  image of a, and `affineSupportProEtaleTwist` then uses `comparisonUpperStar`.
  This is the etale-origin twist, with no choice of root or trivialization:
  roots of unity, tensor powers and the dual of this finite locally free sheaf
  commute with inverse image. The characteristic annihilator gives the usual
  coefficient Tate sheaf by extension of scalars from Z/char(A).
- `affineSupportEtaleH` derives the existing generic
  `Sheaf.supportedSectionsFunctor` specialized to `ModuleCat P.Coefficient`,
  applies it to the twist in degree zero, then takes H^q.
  It is the module-valued version of the recorded etale support cohomology;
  forgetting scalars gives its underlying abelian group by the standard
  acyclic-resolution comparison for sheaf cohomology with module coefficients.
  Injective module sheaves are acyclic for sections on X and its open complement;
  their restriction to that complement is surjective on sections. Localization
  therefore also makes them acyclic for the support kernel. One does not need
  scalar forgetting to preserve injective objects. This is a specialization of
  the existing kernel, not a second support construction.
  `affineSupportProEtaleH` uses the dependency's actual
  `ProEtale.supportHypercohomology` on the same degree-zero coefficient sheaf.
- The first two conjuncts assert `IsIso` of the actual projection pullbacks
  `affineSupportBaseChangeEtale` and `affineSupportBaseChangeProEtale`.
- The next two conjuncts assert that `affineSupportComparison` is invertible
  for `(X,C)` and `(A¹_X,C₁)`. The fifth conjunct is the commuting comparison
  square for these specific projection maps.
- The sixth conjunct quantifies every `(s : X ⟶ AffineSpace ... X)` and
  `(hs : s ≫ p = 𝟙 X)`. It gives both inverse identities for each of the etale
  and pro-etale section pullbacks, not just the existence of some inverse.
  `affineSupportSectionComplement` supplies exactly the inverse-image support C.
- The last two conjuncts equate the zero and unit section pullbacks on the
  etale and pro-etale cohomology groups separately. They use the existing
  `AffineSpace.zeroSection`, `oneSection` and their projection identities.
- No typeclass or binder assumes finite type, separatedness, smoothness,
  regularity, connectedness, Noetherianness or strict locality of X or C.

Canonical-map construction:

The etale and pro-etale `affineGlobalSectionMap` are explicit adjunction units,
evaluated on the terminal object, followed by the inverse of its base-change
projection. The two `affineSupportUnit_existsUnique` theorems require a unique
natural transformation whose composite with the support-kernel inclusion is
that precise global-section map. Thus their `.choose` definitions are determined
uniquely as actual maps; they do not select arbitrary morphisms or isomorphisms.
The comparison support unit is fixed in the same way by the ordinary site
comparison adjunction unit. Its `.choose` also has a unique value.
`Functor.rightDerivedFunctorPlusBaseChange` derives these transformations.
The pullback on twists uses `Etale.upperStarComp`; the pro-etale map additionally
uses the existing canonical
`ProEtale.supportSiteComparisonCoefficientPullbackIso`. The single-functor
comparison maps identify inverse image of a degree-zero sheaf with that sheaf's
inverse image in degree zero. These are actual canonical pullbacks and comparison,
not extra hypotheses that assume them or bare existentially supplied arrows.
The kernel-normalization helpers and complement equalities are local supporting
declarations of this same node, as authorized by the human's helper rule. All are
listed in `lean.declarations`, with source and blueprint docstrings. Every
postponed theorem has a complete natural-language proof in its own docstring.

Dependency declarations used:

- `Sheaf.Paper.PurityFiniteSetting`:
  `WeilConjectures.PurityFiniteSetting`, `.Coefficient`, `.field`, `.level_pos`.
- `Sheaf.AlgebraicGeometry.SupportCohomology`:
  `CategoryTheory.Sheaf.supportedSectionsFunctor`,
  `AlgebraicGeometry.Etale.supportRestrictionArrow`,
  `AlgebraicGeometry.ProEtale.supportRestrictionArrow`, `.supportSections`,
  `.supportHypercohomology`. Their signatures and kernel docstrings were read.
- Mathlib's recorded `AlgebraicGeometry.IsClosedImmersion` and
  `AlgebraicGeometry.AffineSpace`, plus the upstream
  `WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection` and
  `WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace` for the named sections.
- `Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf`:
  `AlgebraicGeometry.Scheme.finiteEtaleTateSheaf` (full signed signature read).
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`:
  `AlgebraicGeometry.ProEtale.supportSiteComparisonCoefficientPullbackIso`;
  its inverse is precisely f_pro* nu_X* → nu_Y* f_et*.
- The upstream etale and finite-coefficient pro-etale `UpperLowerStar.Defs`
  provide `upperStar`, `upperStarLowerStarAdjunction`, `upperStarComp`,
  `comparisonUpperStar`, and `comparisonAdjunction`.
- Upstream `Functor.rightDerivedFunctorPlusBaseChange`,
  `Functor.mapDerivedCategoryPlusSingleFunctor`,
  `Functor.mapDerivedCategoryPlusIdIso`, and Mathlib
  `DerivedCategory.Plus.singleFunctor` / `.homologyFunctor`.
- Proof dependency `thm-pur-with-support-exactness` has the recorded module
  `Sheaf.AlgebraicGeometry.SupportLongExact`, imported non-publicly.
  The ordinary affine-line and supported cup-functoriality proof nodes have no
  published Lean declarations yet; they remain the explicit stage-3 proof plan
  in the main theorem's docstring.

Edge cases checked before writing:

- Empty support gives zero kernel; full support gives ordinary cohomology. The
  construction needs neither a nonempty complement nor a nonempty scheme.
- Empty X, disconnected X, nonreduced C, and singular/non-Noetherian/non-finite-type
  schemes are allowed by the definitions and the theorem's binders.
- q < 0 is allowed by integer homology of a sheaf in degree zero; r = 0,
  positive r and negative r use the existing signed sheaf. No natural-degree
  truncation appears in the statement.
- n = 1 and all ramification/level relationships are admitted. In particular
  the existing specialized positive twist interface requiring a ramification
  divisibility hypothesis is not imposed here.
- The section is arbitrary, not just a constant-coordinate section. Its support
  equality follows from s ≫ p = id, independently of any geometry of s.
- Zero and one sections need not be assumed distinct; their equality conclusion
  is equality of maps between the same actual support cohomology objects.
- Terminal-object pullback transport is explicitly included; no definitional
  identification of the pullback terminal object with the terminal object is
  assumed. Site and coefficient universes remain u/u+1 as published.

Searches made (no exact existing declaration found):

- `msearch.py ... leanfinder` query: "pullback along the affine line projection
  is an isomorphism on etale cohomology with closed supports and finite prime to
  characteristic coefficients". Eight results, including
  `Scheme.Pullback.pullbackP1Iso`, `Scheme.instHasPullbacksEtale`,
  `AffineSpace.isPullback_map` and open-cover pullback isomorphisms. None state
  cohomological invariance with support.
- `msearch.py ... loogle` query: "AlgebraicGeometry.AffineSpace,
  CategoryTheory.IsIso". Only the empty-coordinate affine-space projection
  instance, not this theorem.
- `msearch.py ... grep` query: "support.*[Cc]ohomology|homotopy.*[Ii]nvariance"
  in `AlgebraicGeometry`: zero hits.
- `msearch.py ... leansearch` query: "homotopy invariance etale cohomology with
  closed supports affine line". Eight unrelated results about etale morphisms,
  base-change stability, affine homotopies and etale loci; no match.
- `msearch.py ... leanfinder` query: "canonical pullback map on cohomology with
  supports is obtained by deriving the kernel of restriction along a scheme
  morphism". Eight scheme-restriction and appLE results; no supported map.
- `rg` of the item id in upstream `WeilConjectures` found no declaration.
  Searches of support/affine-line/cohomology in Mathlib, upstream and
  `lean/Sheaf` found the recorded support kernels and coefficient constructions.
  `WeilConjectures.affineLine_invariance` in `Sheaf.Paper.AffineLineInvariance`
  is the distinct normalized local sheaf-gluing statement with finite-type
  separated hypotheses and specified local comparisons, not this arbitrary-base
  supported cohomology theorem. No duplicate notion is introduced.
- Exact proposed declaration-name searches in `dag/lean_names_upstream.json`,
  Mathlib, `WeilConjectures` and `lean/Sheaf` found no preexisting declarations.

Validation:

All compilation uses the prescribed `scompile.py Q105
lem-pur-supported-affine-line-homotopy` wrapper. The theorem and every definition
compile with explicit universes and `autoImplicit false`. An initial broad
support-comparison import encountered an existing duplicate inverse-image API
in the live dependency graph; the final module imports the smaller published
comparison-mate module and uses the recorded terminal-evaluation kernel, which
eliminates that conflict. The final clean file-only compilation had no errors or
warnings. All six theorem proofs are `sorry`, as required for stage 2; definitions
have concrete data, with choices only from the three uniquely determining kernel
factorization theorems. No mathematical statement fault was found.

Independent second reading is intentionally left to the second worker specified
in the brief; this is the first worker's report only.

## Second reading by Q105

I read the node statement, its Stacks/blueprint source place, every recorded
statement dependency, and the delivered signature item by item.

- The fixed finite datum is `P : PurityFiniteSetting.{u}`.  Its
  `P.Coefficient` is the recorded `A_{E,n}` and `P.level_pos` supplies the
  arbitrary positive level condition; no extra divisibility condition is
  assumed.  Verdict: rendered by the first parameter and the existing
  `PurityFiniteSetting` declaration, with no added hypothesis.
- The base is an arbitrary `k`-scheme `X : Scheme.{u}` with
  `[X.Over (Spec (.of P.field.k))]`, and `a` is its structure map.  Verdict:
  rendered by `X` and the explicit repeated term
  `(X ↘ Spec (.of P.field.k))`; no finiteness, separatedness, smoothness,
  regularity, connectedness, or locality instance is required.
- The support is a closed immersion `i : C ⟶ X` with
  `[IsClosedImmersion i]`.  Verdict: rendered exactly; the inverse-image support
  is `pullback.snd i (AffineSpace ... X ↘ X)` and the complement equalities are
  stated by the canonical helper theorems.
- The affine-line projection is the recorded
  `AffineSpace (ULift.{u} (Fin 1)) X ↘ X`, and its inverse-image closed support
  is the displayed pullback.  Verdict: exact object and orientation, with the
  node's `A¹_X ×_X C` represented by the canonical pullback.
- The integers `q r : ℤ` are unrestricted.  Verdict: both are explicit integer
  binders, so negative degrees and twists and `r = 0` remain included.
- The first two conjuncts assert `IsIso` for etale and pro-etale projection
  pullback.  The next two assert `IsIso` for comparison on `(X,C)` and on
  `(A¹_X,C₁)`.  The fifth conjunct is the displayed commuting comparison
  square.  Verdict: all four isomorphism clauses and the square occur in the
  same order with the canonical maps.
- The sixth conjunct quantifies every section `s` with `s ≫ p = 𝟙 X` and gives
  both inverse identities for etale and pro-etale pullback.  Verdict: all four
  identities and the inverse-image support condition are explicit.
- The final two conjuncts equate the zero-section and one-section maps on each
  site.  Verdict: both endpoint clauses are present separately, using the
  recorded `AffineSpace.zeroSection` and `oneSection`.
- The concluding absence of geometric hypotheses is respected by the binders;
  universes are shared (`Scheme.{u}` and coefficient `Type (u+1)`).

Edge cases checked: empty support and full support, empty or disconnected X,
nonreduced or singular C, non-Noetherian and non-finite-type schemes, `q < 0`,
`r = 0`, negative twists, `n = 1`, arbitrary ramification/level relation,
and coincident zero and unit sections.  None is excluded by the signature.
The construction does not require a nonempty complement or scheme, and no
independent index or test-algebra universe is introduced.

Searches were repeated with `msearch.py` LeanFinder/Loogle/grep queries for
supported affine-line cohomology and homotopy invariance, plus `rg` over
Mathlib, `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`.
Only generic affine-space, restriction, and support-kernel declarations were
found; no declaration states this theorem.  The existing finite Tate sheaf,
support kernels, site comparison, and affine-space sections are used directly.

The one mismatch found was the worker's use of `let a`, `let p`, and `let i₁`
inside the theorem proposition.  The stage-2 convention forbids `let` binders
in statements because they elaborate as hidden `have`s.  I replaced them with
their full canonical terms, updated `lean.statement` to the exact new
signature, and kept the mathematical node statement unchanged.  No
hypothesis, object, quantifier, or conclusion clause required any other repair.
The repaired module compiles cleanly with `scompile.py`; no new node or
dependency-module repair was needed.

Independent search details: LeanFinder query `cohomology with support invariant
under vector bundle projection etale torsion` returned eight entries headed by
`CategoryTheory.Sheaf.H`, `Sheaf.cohomologyPresheaf`, and
`Algebra.etaleLocus_eq_compl_support`; none concerns projection invariance with
support. Loogle `"homotopy", "support"` returned zero entries. The grep service
query `homotopy|affineLine|support.*[Ii]nvariance` returned general topological
homotopy declarations, and the targeted local `rg` reads found support-localization
modules and derived orientation declarations, not this theorem. I opened
`WeilConjectures.affineLine_invariance`: its hypotheses require a separated
finite-type base, a cover, and specified normalized comparisons of complexes;
it is a different sheaf-gluing statement.

I also checked the concrete dependency bodies: `supportedSectionsFunctor.obj`
is the kernel of restriction, its morphism is `kernel.map`, and
`ProEtale.supportHypercohomology` is integer homology of its bounded-below right
derived functor. `finiteEtaleTateSheaf` uses the published nonnegative twists
and internal sheaf Hom for negative twists. The `ringChar` annihilator in this
module therefore introduces no ramification-divisibility restriction; it is the
ell-power characteristic of the actual finite coefficient quotient. Pullback
from Spec k preserves this invertible finite root line and its dual. The
comparison coefficient pullback is explicitly the adjunction conjugate of the
sectionwise direct-image base-change isomorphism, so its direction in the
pro-etale coefficient transport is correct. The existing right-derived
base-change construction accepts an actual natural transformation, rather than
requiring an arbitrary isomorphism as input. The three `ExistsUnique` kernel
factorizations thus determine real canonical maps and do not hide their data.
Stacks `etale-cohomology.tex`, section `section-cohomology-support`, starts
with arbitrary schemes and closed subschemes and gives the displayed kernel
and localization sequence without finiteness assumptions. The blueprint's
shear paragraph supplies the endpoint use; the node has already replaced its
unsupported constant-sheaf inference by the localization argument.

## Maintainer fix (independent second reader, 2026-10-17)

The delivered theorem had two conjuncts that the node does not state: `IsIso` of
`affineSupportComparison` on `(X,C)` and on `(A¹_X,C₁)`. The node says only that the
projection isomorphisms on the two sites hold "compatibly with their canonical
comparison", that is, the commuting square (kept as a conjunct). Its proof steps do
not prove that the etale-to-pro-etale comparison is invertible (H3, conclusion
strengthened). The fix removes these two conjuncts and the matching sentence in proof
step 4 of the docstring. In the worker report and second reading above, the conjuncts
are therefore renumbered: the two projection `IsIso` clauses come first, then the
comparison square, the section-inverse clause, and the two zero/unit equalities.
Nothing else changed. The fixed file compiles cleanly with nt_compile.py.

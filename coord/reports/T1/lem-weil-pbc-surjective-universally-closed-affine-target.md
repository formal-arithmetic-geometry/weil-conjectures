## Worker report

The module `Sheaf.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget` states
`AlgebraicGeometry.isAffine_of_surjective_of_universallyClosed`.
It binds schemes `X Y : Scheme.{u}` and a morphism `f : X ⟶ Y`; the typeclass
`[IsAffine X]` renders the affine-source hypothesis, `[Surjective f]` renders
surjectivity on underlying topological spaces, and `[UniversallyClosed f]` renders
universal closedness of every base change. The conclusion `IsAffine Y` is exactly
affineness of the target. The parenthetical integral implication is documented in
the declaration: Mathlib's `IsIntegralHom.instUniversallyClosed` supplies universal
closedness, while the main statement itself has precisely the universally closed
hypothesis.

The statement uses Mathlib declarations `AlgebraicGeometry.Scheme` and
`AlgebraicGeometry.Scheme.Hom` (from `Mathlib.AlgebraicGeometry.Scheme`),
`AlgebraicGeometry.Surjective` (from
`Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`), and
`AlgebraicGeometry.UniversallyClosed` (from
`Mathlib.AlgebraicGeometry.Morphisms.Proper`). `IsAffine` is Mathlib's affine-scheme
predicate from `Mathlib.AlgebraicGeometry.AffineScheme`.

Edge cases checked: the universe `u` is shared by both schemes and the morphism;
no nonemptiness, finite type, Noetherian, or separatedness assumptions were added;
the empty affine source and zero scheme remain covered by the same typeclass
formulation; and the integral parenthetical is not strengthened into an extra
hypothesis.

Searches made: `msearch.py leanfinder` for “surjective universally closed morphism
from an affine scheme has affine target” found only related Mathlib predicates and
no theorem; `msearch.py loogle` for
`AlgebraicGeometry.IsAffine, AlgebraicGeometry.Surjective, AlgebraicGeometry.UniversallyClosed`
found no result; grep of Mathlib's AlgebraicGeometry morphism files found no target
affineness theorem; `rg` over `WeilConjectures/` and project `lean/Sheaf` found no
existing declaration of this statement. The existing local theorem
`isAffine_of_isFinite_surjective` concerns finite morphisms and is a different,
stronger hypothesis, so it was not reused.

Compilation with `scompile.py` succeeded with no errors or warnings other than the
expected `sorry` declaration warning.

## Earlier second reading (a previous round; superseded)

The signature and hypotheses were checked against the source statement and the
pinned Mathlib class definitions. `IsAffine X`, `Surjective f`, and
`UniversallyClosed f` are all typeclass hypotheses on the same morphism and shared
universe; the conclusion is exactly `IsAffine Y`. No additional clause is present.

## Second reading by T1

I independently opened the node copy, the delivered Lean file, all four statement
 dependency nodes and the actual Mathlib declarations they record. I read Stacks
05YU on its official page https://stacks.math.columbia.edu/tag/05YU and downloaded
https://raw.githubusercontent.com/stacks/stacks-project/master/limits.tex into the
sandbox scratchpad because the repository's literature/stacks-project/limits.tex
is absent on this machine. The section introduction (lines 2822ff) and proposition
and proof (2875ff) assume no ambient field, Noetherian hypothesis or separatedness:
separatedness and quasi-compactness of the target are deductions.

The node's objects, hypotheses and conclusions, matched individually:

- Objects: schemes X and S, and a scheme morphism f : X → S. Lean binds
  `{X Y : Scheme.{u}} (f : X ⟶ Y)`; Y renames S. PASS. Mathlib Scheme extends
  LocallyRingedSpace with local affine charts (Scheme.lean:42), and Scheme.Hom
  is a morphism of their locally ringed spaces (line 74), exactly def-pc-scheme.
- Hypothesis: X affine. `[IsAffine X]`. PASS. AffineScheme.lean:59 defines this
  by invertibility of X.toSpecΓ, and Scheme.isoSpec identifies X with Spec Γ(X).
  This is equivalent to the dependency's existence of an isomorphism with Spec A.
- Hypothesis: f surjective on underlying points. `[Surjective f]`. PASS.
  UnderlyingMap.lean:59 has `surj : Function.Surjective f`; the coercion is the
  underlying continuous map. This is the exact def-weil-surjective-morphism record,
  not surjectivity of a ring map or on stalks.
- Hypothesis: every base change of f is closed on underlying spaces.
  `[UniversallyClosed f]`. PASS. UniversallyClosed.lean:43 uses
  `universally (topologically @IsClosedMap) f`; MorphismProperty/Limits.lean:872
  quantifies over every cartesian square in Scheme.{u}. The proper-morphism
  dependency explicitly records this declaration among its declarations;
  no IsProper, finite type or separatedness instance is required here.
- Conclusion: S affine. `: IsAffine Y`. PASS. No clause is weakened or strengthened.
- Parenthetical consequence: the same conclusion for a surjective integral f
  with affine source. PASS, as a specialization of this very theorem: the
  dependency's IsIntegralHom extends IsAffineHom and requires integral maps on
  sections of affine opens (Integral.lean:35); its instance at lines 112ff
  supplies UniversallyClosed f. No second theorem or extra hypothesis is needed.
  The retained Integral import makes this specialization available to users.

Edge cases: empty schemes and Spec of the zero ring are not excluded; an empty
surjective source forces the target empty, which is affine. There is no Nonempty,
nonzero-ring, field, characteristic, finite-type, Noetherian, separatedness, or
quasi-compactness binder. There is no index set or integer n in this statement,
so empty-index and n = 0 tests do not apply. The universe u is explicitly bound
and arbitrary, and both objects are in the same Mathlib category Scheme.{u};
there is no independently smaller test-object universe. The universally closed
predicate uses all pullback squares in that category. Nothing is auto-implicit.

Independent searches (other wording than the worker's):

- `msearch.py leanfinder "affineness descends along a closed surjection stable
  under base change"`: eight hits, none equivalent. In particular
  IsClosedImmersion.isAffine_surjective_of_isAffine assumes an affine TARGET and
  concludes source affineness and surjectivity on global sections, the other direction.
- `msearch.py loogle "AlgebraicGeometry.IsAffine, AlgebraicGeometry.UniversallyClosed"`:
  only isIntegral_appTop_of_universallyClosed, requiring an affine target and
  concluding integrality on sections, not target affineness.
- `msearch.py leansearch "An affine scheme mapping onto a scheme by a universally
  closed morphism forces that scheme to be affine"`: service Internal Server Error;
  recorded as unavailable, not a negative verdict.
- `rg` on Mathlib/AlgebraicGeometry, WeilConjectures, and repository lean/Sheaf
  for `isAffine.*surjective`, the proposed declaration name, 05YU, 01ZT,
  Chevalley, and affine/target/closed variants: no equivalent existing declaration.
  The landed isAffine_of_isFinite_surjective has the stronger finite-morphism
  hypothesis; FpqcAffineDescent uses a different flat descent situation.
  Neither replaces this theorem. No notion needs a new definition.

Repairs: the signature is correct and has been preserved verbatim in lean.statement.
The old proof docstring compressed eight steps into three sentences and omitted
why the affine finite stage maps surjectively to the target. I expanded it into
all eight numbered node steps, including the qcqs checks and the factorization
argument, with the dependency node names and Stacks tags. I removed the redundant
Proper, UnderlyingMap and AffineScheme imports; Integral supplies all declarations
used by the signature and the documented integral specialization. There is still
exactly one theorem with `by sorry`, no definitions, proofs, local notation, local
instances, hidden let/show binders or extra declarations. Every line is at most
100 characters. No new node, dependency module, or statement correction is needed.

Validation: scompile.py compiled the delivered module cleanly; the only permitted
warning is the theorem's use of sorry. Delivery dry run and final push use deliver2.py.

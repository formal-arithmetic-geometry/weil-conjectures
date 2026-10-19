## Worker report

The module states constant-coefficient constructibility for a projective smooth relative
curve over an arbitrary Noetherian scheme. Its only theorem has proof `sorry`; no
new definitions or dependency repairs were needed. The item node changes only in `lean`.

Hypothesis and conclusion correspondence:

- Schemes X and S: `{X S : Scheme.{u}}`, for an explicitly declared arbitrary universe u.
- S Noetherian: `[IsNoetherian S]`, the scheme condition (locally Noetherian and compact),
  rather than merely a Noetherian underlying topological space.
- Morphism f from X to S: `(f : X ⟶ S)`.
- Projective: `[IsProjective f]`, the recorded H-projective convention.
- Smooth with geometric fibres of pure dimension one:
  `[SmoothOfRelativeDimension 1 f]`. This is precisely the relative-dimension notion
  recorded in def-sbc-smooth-morphisms; standard smooth charts of dimension one
  express smoothness and pure one-dimensional nonempty geometric fibres. It does not
  impose surjectivity, geometric connectedness, or irreducibility.
- Prime ℓ: `(ℓ : ℕ) [Fact ℓ.Prime]`. The Fact wrapper supplies the existing field
  structure on ZMod ℓ, without imposing any condition beyond primality.
- Invertible on S: `(hinv : IsUnit (ℓ : Γ(S, ⊤)))`. A global integer section is a unit
  exactly when it is a unit in every local ring, equivalently when the residue
  characteristic is different from ℓ at every point. This is also the convention in
  the upstream `Scheme.invertiblePrimes`.
- The coefficient field F_ℓ: `ULift.{u + 1} (ZMod ℓ)`. ULift changes only the size
  representation; it excludes no prime or scheme. The value of the constant sheaf is
  `ModuleCat.of (ULift (ZMod ℓ)) (ULift (ZMod ℓ))`, the field as a module over itself.
  The coefficient category is `ModuleCat.{u + 1}` as required by the small etale site.
- Constant sheaf on X: `(constantSheaf X.smallEtaleTopology ...).obj ...`.
- Every higher direct image: arbitrary `(r : ℕ)` and
  `DerivedCategory.Plus.homologyFunctor ... (r : ℤ)` applied to
  `Etale.rightDerivedLowerStarPlus ... f` of the degree-zero sheaf embedding
  `DerivedCategory.Plus.singleFunctor ... 0`. Thus the result concerns the actual
  right derived direct image, not a free variable or an assumed comparison object.
- Constructible: `Scheme.IsConstructibleEtaleModuleSheaf`, the finite locally constant
  module restriction on a finite constructible locally closed partition. This is the
  exact predicate used by the recorded bounded-constructible dependency, not the
  upstream alternative `Scheme.IsConstructibleSheaf`.

Dependencies read and used:

- def-pc-projective-morphism: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`,
  `AlgebraicGeometry.IsProjective`. The current server source was read with
  `scompile.py --source` because its extracted module is absent from the older local
  source checkout. It extends `IsHProjective` and `QuasiCompact`.
- def-sbc-smooth-morphisms: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.SmoothOfRelativeDimension` (and its smoothness implication).
- def-weil-pbc-constructible-complexes:
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible`; its underlying
  constructibility predicate is imported publicly and used for this sheaf statement.
- def-weil-pbc-direct-image: `AlgebraicGeometry.Etale.lowerStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, and the recorded
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` available in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`. The latter is the
  generic right-derived functor applied to lowerStar, as its complete signature and
  definition show.
- def-weil-pbc-scheme-conventions is explicitly a convention record without a
  declaration. The scheme and Noetherian definitions are Mathlib's.
- Constant sheaf: Mathlib `CategoryTheory.constantSheaf`, already recorded in
  def-weil-pbc-constant-sheaf; no duplicate notion is introduced.
- All four recorded proof-dependency modules are imported without `public`:
  GeometricFiberFinite, StalkConstructibilityCriterion,
  ProjectiveCurveBettiCardinalities, and upstream ProjectiveSpace. Their role is
  documented step by step in the theorem docstring.

Edge cases checked: r = 0 is included. Empty X and empty fibres are allowed, as are
empty S and disconnected fibres. Empty fibres are vacuously pure of the specified
relative dimension in the recorded smooth-relative-dimension convention. No field
base or finite-type-over-field restriction is imposed. Characteristic ℓ on any
nonempty component is excluded exactly by invertibility; characteristic zero and
all other residue characteristics are allowed. No bound on r or on the genus is
assumed. All variables and universes are explicitly bound.

Searches (2026-10-15):

- msearch.py leansearch: “Higher direct images of constant finite field sheaves under
  a smooth projective curve over a Noetherian base are constructible”. Service
  unavailable (Internal Server Error).
- msearch.py leanfinder: “Higher direct images of constant finite field sheaves under
  projective smooth curves over Noetherian schemes are constructible”. Eight results,
  including constructible images of scheme morphisms and finite scheme fibres;
  none is this etale sheaf constructibility theorem.
- msearch.py loogle: `AlgebraicGeometry.SmoothOfRelativeDimension,
  AlgebraicGeometry.IsProjective`. No hits; IsProjective is unknown to that service.
- msearch.py grep: `constructible.*projective|projective.*constructible` in Mathlib
  AlgebraicGeometry. No hits.
- rg in Mathlib Smooth and Noetherian found the exact relative-dimension and
  Noetherian classes. rg in upstream WeilConjectures and project lean/Sheaf for
  `projective_smooth_curve|smooth.*curve.*[Ff]init|[Ff]init.*smooth.*curve` found
  unrelated smooth-curve geometry and no existing version of this theorem.
- rg for this item id in upstream WeilConjectures found no declaration. Searches for
  higherDirectImage/constructibility in the project found ProjectiveCurveFiniteGroup,
  a different theorem for arbitrary finite groups on projective curves over a field;
  it does not cover the present arbitrary Noetherian base.

Validation: the module compiled cleanly using scompile.py on the server under the
standard per-file limit. No local compiler or library build was run. There are no
statement corrections, new nodes, or disputed clauses.

## Second reading by NW

I independently read the node, its blueprint source (the item has no separate
Stacks theorem source), all five statement-dependency records, and the actual
signatures and bodies used in the module. No mathematical mismatch was found;
the Lean file and its recorded signature are retained verbatim.

Object, hypothesis, and conclusion checklist:

- Objects: schemes X and S and a morphism X → S are `{X S : Scheme.{u}}`
  and `(f : X ⟶ S)`. Verdict: exact, with arbitrary explicitly bound u.
- Noetherian base: `[IsNoetherian S]`. I read the Mathlib class, which extends
  `IsLocallyNoetherian S` and `CompactSpace S`. Verdict: scheme Noetherianity,
  exactly as in the node, with no field or separated-base assumption.
- Projectivity: `[IsProjective f]`. I read the current server module via
  `scompile.py --source WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  it extends `IsHProjective f` and `QuasiCompact f`; the former is a closed
  immersion into projective space on a finite coordinate type over S.
  Verdict: precisely the dependency node's explicitly fixed H-projective
  convention. Stacks morphisms.tex, definition-projective (01W8), distinguishes
  this from its broader unqualified projectivity; no convention was substituted.
- Smoothness and pure one-dimensional geometric fibres:
  `[SmoothOfRelativeDimension 1 f]`. I read its affine-chart definition and
  `SmoothOfRelativeDimension.smooth`, and Stacks morphisms.tex,
  definition-smooth-relative-dimension (02G2), including the following paragraph:
  smooth relative dimension d means nonempty fibres equidimensional of dimension d.
  Smoothness and this dimension condition are preserved by field extension.
  Verdict: the two source hypotheses together, without surjectivity or
  geometrically connected fibres.
- Prime: `(ℓ : ℕ) [Fact ℓ.Prime]`. Verdict: exactly primality; the wrapper supplies
  the canonical prime-field instances without an extra mathematical hypothesis.
- Invertibility on S: `(hinv : IsUnit (ℓ : Γ(S, ⊤)))`. An integer section is
  invertible globally iff it is invertible in every local ring, equivalently its
  residue in each residue field is nonzero (the local inverses glue uniquely).
  Verdict: precisely invertibility on S, including the empty base.
- Coefficient and constant sheaf: `ULift.{u + 1} (ZMod ℓ)` and
  `(constantSheaf X.smallEtaleTopology ...).obj (ModuleCat.of ... ...)`.
  I read Mathlib's constantSheaf body (constant presheaf followed by
  sheafification). Verdict: the constant prime-field module sheaf, with a
  universe lift only; its value is the coefficient field acting on itself.
- Every higher direct image: `(r : ℕ)` precedes the conclusion; the term is
  `Plus.homologyFunctor ... (r : ℤ)` of `Etale.rightDerivedLowerStarPlus ... f`
  applied to `Plus.singleFunctor ... 0` of that constant sheaf. I read
  `rightDerivedLowerStarPlus` (the rightDerivedFunctorPlus of lowerStar),
  `lowerStar` (sheaf pushforward along base change on the small etale sites),
  and Mathlib's Plus single and homology functors. Verdict: actual R^r f_* of
  the specified sheaf, in every nonnegative degree; no comparison map or
  chosen arbitrary cohomology object is assumed.
- Constructible conclusion: `Scheme.IsConstructibleEtaleModuleSheaf` of this
  term. I opened BoundedConstructibleComplexes and its public dependency
  IsConstructibleEtaleModuleSheaf. The latter asks for a finite locally closed
  stratification, constructible strata, and etale-local constant finite module
  models of the canonical stratum pullbacks. Verdict: exactly the dependency's
  constructibility clause. It is not the upstream alternative predicate on
  finitely generated geometric stalks, nor a boundedness assertion.

Edge cases: r = 0 is quantified; no bound on r is imposed. Empty X, empty S,
empty fibres, and disconnected fibres are admitted. The relative dimension
condition is pointwise and hence vacuous on an empty source. The finite
stratification definition permits zero strata on an empty base. The zero sheaf
and its finite zero module models are permitted. There is no variable dimension
n in this statement: the relative dimension is exactly one, as in the source.
Primality excludes ℓ = 0 and ℓ = 1 exactly as required. Residue characteristic ℓ
is excluded precisely by hinv on nonempty loci; characteristic zero and other
characteristics remain covered. All universes are bound, coefficient/module
universes are u+1 as the recorded small-site interface requires, and no extra
universe equality or independent lower test universe is present.

Independent searches used different wording from the worker:

- msearch leansearch: "Constructible higher direct image prime field smooth
  projective relative curve"; service unavailable (Internal Server Error).
- msearch leanfinder: "Constructibility of higher etale direct images of prime
  field coefficients for proper smooth families of one dimensional schemes";
  eight results, involving standard smooth presentations and etale morphisms,
  none stating this constructibility theorem.
- msearch loogle: `AlgebraicGeometry.SmoothOfRelativeDimension`; twelve results,
  giving the definition and stability/composition API, no matching theorem.
- rg on Mathlib AlgebraicGeometry, upstream WeilConjectures and project
  lean/Sheaf: `constant.*[Cc]onstructible|[Cc]onstructible.*constant|smooth_curve|smoothCurve`.
  I opened both nearby project theorem signatures. ProjectiveCurveFiniteGroup
  requires a finite-type field base and concludes abelian constructibility;
  ProperSmoothCurvesFiniteModule requires geometrically connected fibres.
  Neither says the node's theorem. Upstream direct-image stability uses the
  alternative constructibility predicate and broader finiteness interfaces,
  not this statement. No definition or statement is duplicated here.

There are no new nodes, dependency modules, or statement corrections to audit.
The declaration and module docstrings identify the source and blueprint id;
the theorem docstring follows all four node proof steps, including coefficient
linearity at the last step. There is exactly one postponed named theorem, with
whole proof `sorry`, no definitions, hidden parameters, private copies, or
additional proved results. All required proof dependencies are imported.

Changes: appended this independent review only; no Lean or node repair was
necessary. The recorded lean.statement was checked against the file signature.
Validation: scompile.py compiled the sole delivered module on the server cleanly
(4.1 seconds for the library file), with no errors or unexpected warnings,
using the standard 60-second per-file/two-thread/nice-19 wrapper.

## Worker report

Item: `thm-trf-internal-hom-pullback`; group NN; stage 2; 2026-10-18.
Module: `Sheaf.SixFunctors.InternalHomPullback`.
Main declaration:
`WeilConjectures.TraceFormulaCoefficientConventions.internalHomPullback`.
The only postponed proof is this named theorem, whose docstring gives all six
steps of the DAG proof. Definitions contain actual data. No statement correction,
new node, dependency-module replacement, or disputed statement is submitted.

The module defines the actual canonical comparison and states its invertibility,
two-variable naturality, both integer-shift compatibilities, and its compatibility
with distinguished triangles in the second argument. It does not replace the
comparison by an unspecified isomorphism. Auxiliary abbreviations expose existing
operations and predicates, without defining a second coefficient category,
perfectness predicate, derived tensor product, or derived internal Hom.

Source read: both the theorem and the unit statement and sketch proof in
`literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-internal-hom-pullback/`,
the item's six-step DAG proof, and Stacks `sites-cohomology.tex`,
`lemma-dual-perfect-complex` (Tag 08JJ), beginning at line 13048. The latter
includes finite projective summands, and its second argument is arbitrary.
The delivery retains the item's finite-Tor constructibility restriction.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node/source datum or clause | Lean rendering |
| --- | --- |
| Global finite-field datum, prime distinct from the characteristic, chosen algebraic closure, finite coefficient subextension | `T : TraceFormulaCoefficientConventions.{u}`; its `datum`, `coefficients`, `extension`, and `coefficientField` are the dependency's recorded data. |
| Positive exponent and finite quotient `A = O_E / uniformizer^level` | `T.level` and `T.level_pos`; the existing operations index exponents as `n+1`, so all helpers use `n = T.level - 1`. Then `T.level - 1 + 1 = T.level` by positivity. `homPullbackCategory` is just the recorded `proEtaleDerivedCategory` at that exponent. |
| `X` under the global conventions | `T.geometricBaseChange`, with structure morphism `T.structureMap`; the recorded convention supplies its separated finite-type model over the finite field and geometric base change. |
| A morphism `g : Y' -> X` of finite-type schemes | `{Y : Scheme.{u}}`, `g : Y ⟶ T.geometricBaseChange`, `[LocallyOfFiniteType (g ≫ T.structureMap)]`, `[QuasiCompact (g ≫ T.structureMap)]`. These two classes mean that `Y` is of finite type over the same geometric base field. No separatedness of `Y`, properness, smoothness, or flatness is required. The composite supplies its base structure; no independently chosen structure map or extra commutativity hypothesis is needed. |
| Coefficient prime invertible on the schemes | `homPullbackUnits` transports the already recorded `finiteFieldDatumPrimeUnit` through the residue-field map of the structure morphism. Its use in the comparison definition introduces no additional hypothesis. |
| `M` in ambient `D(X,A)` | `M : T.homPullbackCategory T.geometricBaseChange`. No constructibility condition on `M` is imposed. |
| `M` site-perfect | `T.homPullbackPerfect T.geometricBaseChange M`, an abbreviation of `IsFiniteCoefficientSitePerfect`, which uses local bounded complexes of retracts of finite free module sheaves. |
| `N` belongs to `D^b_ctf(X,A)` | `T.homPullbackFiniteTor T.geometricBaseChange N`, an abbreviation of `finiteTorConstructible`. Both bounded constructibility and finite Tor amplitude are retained. |
| `Lg* RHom(M,N)` | `(T.homPullbackFunctor g).obj ((T.homPullbackHom T.geometricBaseChange).obj (op M,N))`. These abbreviate `finiteDerivedPullback` and `finiteIntrinsicDerivedInternalHom`. |
| `RHom(Lg*M,Lg*N)` | `(T.homPullbackHom Y).obj (op ((T.homPullbackFunctor g).obj M), (T.homPullbackFunctor g).obj N)`. |
| Canonical comparison | `internalHomPullbackComparison` is `finiteIntrinsicTranspose` applied to `(canonicalFinitePullbackTensor ... RHom(M,N) M).inv` followed by the pullback of `finiteIntrinsicEvaluation ... M N`. The tensor comparison is the existing K-flat-representative-normalized one. |
| The comparison is an isomorphism | First conjunct: `IsIso (T.internalHomPullbackComparison g M N)` under precisely the two object predicates. |
| Naturality in both variables | Second conjunct: the explicit square for every `a : M' ⟶ M` and `b : N ⟶ N'`, using `Prod.mkHom a.op b`; the hypotheses retain site-perfect first arguments and finite-Tor constructible second arguments. The arrows need not be isomorphisms. |
| Compatibility with shifts of `N` | Third conjunct: existential `CommShift ℤ` structures on both Hom functors, required to make those functors triangulated, and `TrfHomPullbackShiftSquare` on their composites with the fixed pullback. Its equation is `beta_(N[n]) ; shift_target = shift_source ; beta_N[n]`, for every integer `n`. |
| Compatibility with shifts of `M` | Fourth conjunct: the same square for the flipped Hom functors from the opposite derived categories, with the exact shift structures and the canonical `F.op` shift. The opposite triangulated category reverses the shift sign. This also retains the first-variable signed shift clause spelled out in DAG proof step 6. |
| Distinguished triangles in `N` | `TrfHomPullbackTriangleSquare` quantifies over every distinguished triangle whose three objects satisfy the recorded finite-Tor constructible predicate. Both images are distinguished, and there is a triangle morphism with `hom₁`, `hom₂`, `hom₃` equal to the three defined comparisons. A morphism of triangles includes the connecting-arrow square; this is not merely three unrelated isomorphisms. The same Hom shift witnesses occur in the shift and triangle clauses. |
| Size convention | Explicit `universe u`; `Scheme.{u}`, the actual small pro-etale site with objects in `u+1` and morphisms in `u`, coefficient modules in `u+1`, and the standard ambient derived category. Generic compatibility predicates explicitly bind their object and morphism universes `a b v w`. `autoImplicit false` is set. |

The Hom `CommShift` structures are existential exact-functor witnesses, as in the
recorded `ringedInternalHom_exact` interface. They are not hypotheses on the user.
The comparison itself is fixed before any such witness is quantified and never
chosen from a bare existence statement. No `let` occurs in the theorem statement;
local instance data only occur inside the actual comparison definition.

Dependency declarations used:

- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, `coefficientField`,
  `geometricBaseChange`, `structureMap` and its geometric finite-type instances.
- `Sheaf.Paper.DerivedPullbackTensorHom` (publicly reexported by the convention):
  `finiteCoefficientRing`, `finiteDerivedPullback`,
  `finiteIntrinsicDerivedInternalHom`, `finiteIntrinsicEvaluation`,
  `finiteIntrinsicTranspose`. Their actual signatures and docstrings were read.
- `Sheaf.Paper.FiniteTorAmplitude` (publicly reexported by the convention):
  `finiteTorConstructible`. This is the current recorded intrinsic interface,
  rather than its older fixed-scalar wrapper.
- `Sheaf.Paper.SitePerfectComplex`: `IsFiniteCoefficientSitePerfect`.
  Its larger-site/coefficients signature elaborates on the actual intrinsic
  category without a new universe equality or an object transport assumption.
- `Sheaf.Paper.FinitePullbackTensorComparison`:
  `canonicalFinitePullbackTensor`. Its construction is the existing prescribed
  K-flat tensor comparison and unit-normalized intrinsic realization. The already
  landed node `def-pur-finite-pullback-tensor-comparison` is added to `stmt_deps`.
- `Sheaf.Paper.DirectImagesConstructible` (already publicly reexported through
  `OrdinaryCompactCohomology`): `finiteFieldDatumPrimeUnit`. The already landed
  node `lem-weil-structure-direct-images-constructible` is added to `stmt_deps`.
- `def-weil-scheme-morphism-properties` is a convention record, not a declaration;
  its `LocallyOfFiniteType` and `QuasiCompact` classes express finite type.
  `def-weil-size-convention` likewise requires explicit universes, not a new object.
- All stated proof-dependency modules are imported without `public`:
  `RingedDerivedClosedSymmetricMonoidal` (`ringedDerived_closed_symmetric_monoidal`),
  `RingedDerivedMonoidalComparisons` (`ringedDerivedMonoidalComparisons`),
  `RingedSitePerfectDuality` (`ringedSitePerfectDuality`),
  `RingedSiteDualityMaps` (`ringedSiteDualityMaps_exists`),
  `CoefficientRingedTensorHomModel` (`CoefficientTensorModels`),
  `RingedTopoiDerivedPullback` (`SheafOfModules.ringedTopoiDerivedPullback`),
  `RingedInternalHomSignedCalculus` (including the reexported exactness interface),
  and `HomComplex` (`CategoryTheory.homComplex`).
  The Mathlib-matched proof leaf `lem-sfb-dual-tensor-adjunctions` is imported via
  `Monoidal.Rigid.Basic` and `Adjunction.Limits`, using `tensorLeftAdjunction`,
  `tensorRightAdjunction`, `leftAdjoint_preservesColimits` and
  `rightAdjoint_preservesLimits`; the full signatures/docstrings were read.

Edge cases checked before writing and on rereading:

- `M = 0`, `N = 0`, and `M = A_X`: no nonzero or positive-rank hypotheses; the
  defined transpose has the expected zero maps or unit normalization.
- `Y` empty: no `Nonempty` scheme, point, or cover-index assumption is present;
  the residue-field inverse is simply a dependent function on the empty type.
- `T.level = 1`: the operation index is zero and the coefficient exponent is one.
  Higher levels, including non-field rings such as `Z/l^2`, are included without
  a flatness assumption on a quotient coefficient change.
- Negative shifts, zero shift, and arbitrary positive shifts: the squares quantify
  over `ℤ`, not just natural degrees. The first-variable category is opposite.
- Local perfectness with finite projective summands is retained, not replaced by
  a globally bounded finite-free representative or a chosen duality structure.
- Naturality for zero maps and arbitrary noninvertible maps: both variables use
  ordinary morphisms. The theorem does not reduce naturality to isomorphisms.
- Triangles: the predicate tests all three vertices, and the morphism of triangles
  includes the connecting arrow using the same shift structures as the shift square.

Searches for an existing statement/construction:

| Tool and query | Result and decision |
| --- | --- |
| `msearch.py ... leanfinder "Derived pullback of internal Hom from a perfect complex is canonically isomorphic to internal Hom of pullbacks, naturally and compatible with shifts and triangles"` | Eight hits, chiefly ordinary module pullback and `PullbackShift.adjunction`; none gives this coefficient-site comparison with all clauses. |
| `msearch.py ... leansearch "Internal Hom commutes with derived inverse image for perfect complexes"` | Eight generic resolution/Homology comparison hits; no matching theorem. |
| `msearch.py ... loogle "CategoryTheory.expComparison, CategoryTheory.Functor.Monoidal"` | Zero hits. |
| `msearch.py ... grep "expComparison|internalHom.*[Pp]ullback|[Pp]ullback.*internalHom" CategoryTheory` | Six hits, including `Mathlib/CategoryTheory/Monoidal/Closed/Functor.lean`'s `expComparison`. It is a generic closed-category comparison, not the required finite-coefficient theorem. |
| `rg` for the item id and internal-Hom/pullback spellings in upstream `WeilConjectures` and `lean/Sheaf` | Upstream `SixFunctors/Etale/Derived/Perfect/Pullback.lean` has `AlgebraicGeometry.Etale.DerivedCategory.nonempty_iso_leftDerivedUpperStar_derivedHom`; its signature assumes an abstract dualizable object in an etale sheaf category and asserts only a `Nonempty` object isomorphism. It does not identify the intrinsic canonical map or state its naturality/shift/triangle clauses, so it is not an exact match. Scheme O_X analogues and etale generic comparison modules use different coefficients/sites. |
| Focused `rg` for finite pullback/tensor and site Hom constructions | Found and reused `canonicalFinitePullbackTensor`. `finiteHomSiteHom` is for the etale-to-pro-etale site morphism nu, so it is not the map along the scheme morphism g and is not substituted. |
| `rg` for every newly introduced full-name suffix in Mathlib, upstream and `lean/Sheaf` | No collision with the declarations in this delivery. |

Validation: the prescribed `scompile.py` compiled the initial module cleanly in
both sandbox and library-path forms (29.1 s and 19.1 s). After the second reading
added explicit exactness of the shift witnesses, the final module compiled cleanly
again through the same wrapper (27.3 s sandbox, 19.2 s library). The dependency
additions were also checked for return paths to this item; neither creates a cycle.
The prescribed delivery dry run and final delivery both run the server preflight
and per-file compilation again.

## Second reading by NN

I reopened the node and the written module and checked the table above against
both texts. The dispatcher explicitly prohibits starting another agent, so this
section records my separate second pass rather than claiming an independent
worker's review; the maintainer's independent delivery review remains applicable.

The first pass had the two integer-shift witnesses and the explicit compatibility
squares but did not require those witnesses to make the individual Hom functors
triangulated. The second pass added `IsTriangulated` for both Hom functors in both
variables, using the same witnesses in the shift and triangle clauses. I also
checked that the triangle condition specifies `hom₃` and therefore includes the
connecting-arrow square; that the first variable uses `a.op` and the opposite
integer-shift convention; that every positive coefficient level is represented;
and that no finite-Tor/constructibility assumption was accidentally imposed on M.
The declared arrow is the evaluation transpose of the prescribed tensor map,
not an arbitrary chosen isomorphism. No mathematical statement field was changed.

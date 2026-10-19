## Worker report

Repair of the independently returned head dae348d91931. The former four-conjunct
rank statement omitted substantive conclusions. The replacement states the source's
three clauses, with actual root generators and isomorphisms on a common cover,
normalized Kummer-induced A-linear maps, signed line properties, and equivalences
whose specified inverses are the negative twist functors. Its only postponed proof
is `AlgebraicGeometry.Scheme.tateTwist_locallyFree`; all helpers have real data.
The natural-language proof in this theorem's docstring now follows every node proof
step, including the common refinement of the root and integral trivializing covers.

Hypotheses and objects:

- `X : Scheme.{u}` is arbitrary, with no finite-type, Noetherian, separated,
  nonempty, connected or field-of-definition restriction.
- `ℓ : ℕ`, `[Fact ℓ.Prime]` and the residue-field invertibility instance render
  the fixed prime and its invertibility on X.
- `E : Type u`, `[Field E]`, `[Algebra (Padic ℓ) E]` and
  `[FiniteDimensional (Padic ℓ) E]` render the finite coefficient extension. Its
  valuation ring and completed coefficient sheaf are the existing
  `purTwistIntegralModule` and `completedIntegralCommRingSheafUnrestricted`
  constructions, rather than additional freely chosen coefficients.
- `Ω : Type v`, its field, algebra and `IsAlgClosure` instances render an arbitrary
  algebraic closure; `ι : E →ₐ[Padic ℓ] Ω` renders its containing E. The closure's
  universe is independent of the scheme's.
- `A : Type (u + 1)`, `[CommRing A]`, `[Finite A]` render every finite commutative
  coefficient ring at the ambient sheaf size. `r : ℕ` denotes the positive integer
  r+1, and `hA : ∀ a, ℓ^(r+1) • a = 0` is precisely the annihilation condition.
  Every finite root level n similarly denotes exponent n+1. Thus n=0 represents
  μ_ell, not μ_1; this repairs the misleading level description in the old report.

Clause (1): `∃ I U f ζ e` gives one covering family of small-site objects, compatible
sections in the actual roots modules, and unit-to-root isomorphisms over its members.
`Presieve.ofArrows U f ∈ (ProEt.precoverage X).coverings _` is the pro-etale cover.
A family is the site presentation of the source's covering X-tilde. The equation
using `proEtaleRootsOfUnityTransition` is ζ_(n+1)^ell = ζ_n in additive notation.
The component formula for `(e n i).hom.val.app V` is a ↦ a • restriction(ζ_n), over
EVERY object of the slice site. It states an isomorphism of sheaves, not bijectivity
from scalar constants on global sections (which would fail on disconnected objects).
The roots module has exactly the recorded root sheaf as its underlying group
presheaf, transported only by its canonical coefficient-ring isomorphism.

Clause (2): `∃ a : ZMod (ℓ^(r+1)) →+* A` supplies the unital quotient map forced by
annihilation; Mathlib's `ZMod.subsingleton_ringHom` makes this coefficient map unique.
`tateFiniteScalar` applies this map to the constant sheaves. `tateFiniteLine` is the
recorded mixed-universe scalar extension of `purTwistRootsModule`, i.e. precisely
μ_(ell^(r+1)) tensor_(Z/ell^(r+1)) A_X. For every `n` and `hrn : r ≤ n`, the higher
coefficient map is its composite with `ZMod.castHom` reduction. The conclusion gives
an A-linear sheaf morphism k, `IsIso k`, and its formula on EVERY local pure tensor:
`b tensor x ↦ b tensor Kummer(x)`. `tateFiniteTensor` is the actual sheafification
unit applied to a sectionwise scalar tensor (`purScalarSection`). Consequently k is
the induced Kummer map, not an arbitrary isomorphism between the same objects. The
formula determines it because pure tensors locally generate. Equal annihilating
levels n=r are included.

Clause (3), sheaf lines: `TateSignedLine X R L U` explicitly states rank one and
triviality over the SAME covering U for every integer signed twist, constructed with
`coefficientTwistLine` (zero unit, positive powers, negative internal duals). It also
states L(d) tensor L(-d) ≅ R for every d : ℕ, including d=0. It is instantiated for
the arbitrary finite A-line and for the completed integral line.

For E, `TateRationalSignedLine` explicitly requires every integer signed coefficient
line, after the canonical `rationalDerivedPullback` to EACH member of the SAME U,
to be isomorphic to the local coefficient unit. It also requires the global tensor
product of the d and -d coefficient lines, under `rationalDerivedTensor`, to be the
coefficient unit for every d : ℕ. Each coefficient line is the localization of
`intrinsicIntegralCoefficientTwist`; its zero twist is exactly the coefficient unit.
Thus these are the degree-zero rank-one lines in the node's integral-representative
interpretation, rather than a replacement by a discrete constant E sheaf.

For Ω, `TateQbarSignedLine` makes BOTH clauses explicit again in the RECORDED
common-stage category, using `intrinsicQbarCoefficientTwist`,
`commonStageDerivedPullback` and `commonStageDerivedTensor`. Its local unit is the
least-stage zero twist on the covering scheme. An isomorphism in this category is
an actual common finite-stage isomorphism, precisely the node's Ω interpretation.
The helper `tatePullbackInvertible` transports the GIVEN invertibility along each
cover member's residue-field ring homomorphism, using `Invertible.map` and
`map_natCast`; it introduces no extra assumption about the covering schemes.
In both rational interpretations, a degree-zero line locally isomorphic to the
coefficient unit states rank one; the global product clause states invertibility.

Clause (3), functors: `TateInverseTwists F G` requires an actual categorical
equivalence e with `e.functor = F` and `e.inverse = G`. Thus it records the negative
inverse, not merely an IsEquivalence instance or objectwise isomorphisms.
`tateComplexTwist` uses the existing exact ordinary tensor model's
`mapDerivedCategory` on the whole unbounded derived category of A_X-modules. Exactness
comes from the published `coefficientTwistLine_exact`; its rank premise is proved
in the conclusion, not added as an assumption. `tateIntegralTwist` is tensor with
`intrinsicIntegralCoefficientTwist` using `constructibleIntegralTensor` on the
bounded complete integral category. `tateRationalTwist` uses the localization of
that very line and `rationalDerivedTensor` on `sfRationalConstructibleCategory`.
The Ω operation is the RECORDED `intrinsicQbarComplexTwistFunctor` on
`generalAlgebraicallyClosedConstructibleCategory`. Every map in these helpers is
inherited from the published tensor bifunctor; none is an arbitrary functor datum.
The final universal D/hD binders only supply the dependency's legacy indexing of
its integral-line membership proof. They impose no finite-field structure on X;
the categories and line data are the intrinsic, datum-free ones. Both d and -d
refer to these same specified functors.

Dependencies actually used:

- `Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf`:
  `proEtaleRootsOfUnitySheaf`, `proEtaleRootsOfUnityTransition`, and the module
  structure reused through `purTwistRootsModule`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `constantSheaf`, used to form A_X
  and its scalar maps.
- The CURRENT recorded `Sheaf.Paper.IntrinsicCoefficientTwists`:
  `intrinsicIntegralCoefficientTwist`, `intrinsicQbarCoefficientTwist`,
  `intrinsicQbarComplexTwistFunctor`, and its
  public imports' `coefficientTwistLine`, `coefficientTwistLine_exact`,
  `constructibleIntegralTensor`, `rationalDerivedTensor`,
  `sfRationalConstructibleLocalization`, `rationalDerivedPullback`,
  `commonStageDerivedPullback` and `commonStageDerivedTensor`. The old legacy
  rational/common-stage
  categories are not substituted for the current recorded ones.
- `Sheaf.Paper.PurTwistSheafLocallyFree`: the concrete finite roots and completed
  integral modules and coefficient rings; also the published proof dependency.
- `Sheaf.Paper.PurInverseImageTensorHom`: `purScalarSection`, the existing canonical
  section tensor map. No second sheaf tensor or sheafification construction is made.

The two integral-limit/localization proof dependency nodes have no current Lean
record in the shared DAG. Their mathematical uses remain explicit in the theorem
proof docstring; there is no invented module import for either.

Edge cases checked by the statement and definitions: r=0 and n=0 are the positive
exponent one; n=r includes identity transitions; d=0 includes unit twists and both
inverse functors; negative integers use the published internal dual. Empty schemes
and empty covering families are allowed. Zero finite rings are allowed. Disconnected
covering members are allowed because the generator formula ranges over the actual
slice coefficient sheaf. The algebraic closure may have a different universe, and E
may be Q_ell itself. No stage condition restricts X or forces a morphism to a finite
field. All theorem and universe binders are explicit (`autoImplicit false`).

Searches retained from the first packet: `msearch.py leanfinder` with "Tate twists
are well defined and locally free of rank one on the pro-etale site" returned eight
generic condensed/local-constancy results; `loogle "Tate twist,
IsFiniteLocallyFreeOfRank, coefficientTateTwists"` returned no hit (unknown Tate);
Mathlib grep `TateTwist|coefficientTateTwists` returned none. Repair searches:
LeanFinder "Compatible roots of unity on a pro-etale cover give Tate twists
independent of annihilator and inverse tensor autoequivalences" returned eight
cyclotomic-character/Kummer-field results, none the scheme/sheaf theorem. Mathlib
and project/upstream-name grep for the new helper names found no existing match.
Project searches found and reuse the root, signed-line, mixed-universe tensor and
intrinsic tensor functors above. The helpers merely specialize these existing
notions and package clauses of this one node; no independent definition node or
dependency redefinition is needed. Search transcripts are in searches.jsonl.

## Second reading by NW

Self-check of the repair with the node, declaration and all three dependency records
open (no additional agent was started, as the launcher forbids delegation).
The returned H3 omissions were checked individually: the replacement now binds an
arbitrary Ω containing E, positive levels are n+1, one cover precedes ζ and e, ζ are
compatible, e is an isomorphism with the exact scalar-section generator formula,
and Kummer k is A-linear and normalized on every pure scalar tensor. The signed
property uses all integers and explicitly includes the tensor inverse pairing.
A final clause check found that integral triviality alone did not explicitly STATE
the rational and Ω local conclusions. It added the two signed-line predicates:
each has the canonical pullback-to-unit isomorphism on every common covering member
and the positive/negative tensor isomorphism globally, in its recorded category.
The derived equivalence predicate fixes BOTH functor and inverse, including the
finite, intrinsic integral, raw rational and intrinsic common-stage coefficient
categories. This check caught and removed two defective drafts: bijectivity from
scalar constants on global sections, and the legacy rational/common-stage category
substitution. It also removed the old report's erroneous claim that unused A/r
binders expressed its finite-coefficient conclusion. H8 is repaired by the five
proof paragraphs, with the node's common-refinement step stated explicitly.
The exact signature is copied from the final file into lean.statement; all helper
names are recorded in lean.declarations. The only sorry belongs to the owning node.

Validation: the final module compiled through the prescribed `scompile.py` wrapper
in both the sandbox and library checks, with no errors or warnings. The final
record-to-signature check, 100-character line check and one-sorry check passed.

## Maintainer review fix (cc review service, 2026-10-18)

H3, quantifier order: the delivered theorem bound `A`, `[CommRing A]`, `[Finite A]`, `r` and
`hA` before `∃ I U f ζ e`, so the cover and the root generators could depend on the finite
coefficient ring. The node fixes one cover X-tilde in clause (1) and states clause (3) for
every finite A on that same X-tilde (proof step 3: "(1) identifies A_X(1) with the constant
free rank-one A on the same cover"). The fix removes the five binders from the signature and
states, after the cover data, `∀ (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ),
(∀ a : A, (ℓ ^ (r + 1)) • a = 0) → ∃ a, (Kummer clause) ∧ (finite line clause)`, with the
integral, rational and Qbar conjuncts unchanged. No helper, docstring or other clause changed;
the fixed file compiles clean through nt_compile.py.

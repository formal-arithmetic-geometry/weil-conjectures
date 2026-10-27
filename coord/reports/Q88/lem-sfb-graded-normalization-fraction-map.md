## Worker report

This repaired stage-2 delivery states the entire accepted node in
`Sheaf.RingTheory.GradedNormalizationFractionMap`, in namespace
`GradedNormalization`. Every theorem has proof `sorry`; definitions have actual
data. No statement, split, source, or dependency edge is changed.

The repaired packet contains only the item module, the item's node JSON, and
this report. It does not deliver or modify the landed associated-graded node
`def-weil-pbc-associated-graded-ring`: the F1 record of
`WeilConjectures.RingTheory.AssociatedGradedRing`, `Ideal.associatedGraded`,
remains byte-identical to live. The sandbox node agrees with the live item in
every field except `lean`.

Hypotheses and clauses, read against the complete node:

- The local commutative ring is `[CommRing A] [IsLocalRing A]`; m is
  `IsLocalRing.maximalIdeal A`. The residue field F is the actual quotient
  `A ⧸ IsLocalRing.maximalIdeal A`, without an independently chosen field.
- The embedding A into the commutative ring B is `φ : A →+* B` with
  `hφ : Function.Injective φ`. Separate ring universes are used for the
  algebraic statements. Scheme composites use one common universe, which can
  be instantiated by the maximum of the carrier universes.
- `residueIdeal φ` is exactly `m.map φ`, so E is `B ⧸ residueIdeal φ`.
  G is the upstream `Ideal.associatedGraded m`, with its unchanged ring and
  F-algebra structure. The item module supplies the missing internal-grading interface on this same ring.
- `f : maximalIdeal A` binds f and f∈m together. `hgen` is precisely
  `m.map φ = Ideal.span {φ f.val}`, and `hreg` is injectivity of multiplication
  by φ(f) on B. No domain, Noetherian, finiteness, or reducedness hypothesis is
  used in the general construction.
- `linearForm f` is the degree-one initial form. `Chart f` abbreviates the
  recorded Mathlib `HomogeneousLocalization.Away` at that actual form.
  `fraction f n d` is its actual `Away.mk` element in_n(d)/ell^n, for
  `d : ↥(m^n)`. There is no free map standing in for a localization.
- `existsUnique_fractionMap` first concludes unique b with
  `φ(f)^n*b=φ(d)`, then unique θ on the actual chart satisfying
  `FractionFormula`: every such b maps the fraction to its actual quotient
  class. This is a total ring homomorphism defined on the quotient of all
  ordinary localization representatives, so lift independence and equalities
  involving additional powers are included. The docstring gives the extra-k
  calculation, including zero divisors of ell.
- The ring-hom formulation with the all-degree fraction formula expresses
  exactly the F-algebra map: at n=0 it sends the constant fraction of every
  a∈A to [φ(a)]. These representatives surject onto F, and the source constant
  fractions are its recorded degree-zero scalar embedding. Thus the formula
  implies the AlgHom scalar compatibility, without adding an arbitrary
  Algebra structure on E. `fractionMap` chooses only this uniquely specified
  ring homomorphism from the theorem, as permitted for uniquely determined data.
- `fractionMap_changeDenominator` takes both pairs of generator/regularity
  hypotheses and states equality of `Spec.map fractionMap ≫ Proj.awayι`
  for f and g, with the actual Proj chart immersions. Separately,
  `fractionMap_changeDenominator_formula` uses independent carrier universes
  and supplies `w : Bˣ` obeying g=f*w and f=g*w⁻¹.
  The ratio ell_g/ell_f maps to [w].
  For each n,d and their division coefficients b,c it states c=b*(w⁻¹)^n
  and θ_g(in_n(d)/ell_g^n)=θ_f(in_n(d)/ell_f^n)*[(w⁻¹)^n].
- `fractionMap_overlap` supplies the unique comparison from the g-chart to
  the localization of the f-chart at t=ell_g/ell_f. Its formula is exactly
  fraction_f(d) times invSelf(t)^n. It supplies the common map ψ to E,
  with ψ on the f-chart equal to θ_f and ψ after the comparison equal to θ_g.
  Together with the preceding unit identities this is the stated overlap
  equality and its residue formula, including n=0.
- `fractionMap_natural` binds local A,A′ and compatible ring isomorphisms
  α,β with `∀ a, β (φ a)=φ′(α a)`. It CONCLUDES that α(f) lies in m′,
  φ′ is injective, and the transported f satisfies both required conditions;
  these are not extra hypotheses. It concludes the uniquely characterized
  induced residue-field isomorphism κ, graded-ring isomorphism U, chart
  isomorphism, and E-isomorphism by their values on all representatives.
  The pair of chart and residue isomorphisms is unique solely from its two
  representative formulas. In a separate universally quantified conclusion,
  every pair satisfying those formulas obeys βbar ∘ θ_f = θ_f′ ∘ T.
  Thus uniqueness does not depend on assuming the square commutes.
  Scalar maps are induced by the same α on the degree-zero representatives.
- `normalization_extension` handles the final reduced-ring specialization.
  B and B′ are literally `integralClosure A (FractionRing A)` and its primed
  version. The unique β is characterized by the actual Mathlib
  `IsFractionRing.ringEquivOfRingEquiv α` on every total-fraction element,
  and its compatibility on A is explicit. Applying `fractionMap_natural`
  to this β is the normalization naturality clause. No injectivity or
  surjectivity of θ is claimed anywhere.

Dependencies read and used:

- `WeilConjectures.RingTheory.AssociatedGradedRing`: full file read, including
  `associatedGradedPiece`, `associatedGraded`, multiplication, ring structure,
  `associatedGradedRingHom`, and `associatedGradedAlgebra`. The new grading
  uses the ranges of these SAME `DirectSum.of` inclusions.
- `Mathlib.Algebra.Algebra.Hom`, `AlgHom`; `Mathlib.RingTheory.Ideal.Quotient.Operations`,
  `Ideal.Quotient.algebra`, `mkₐ`, and quotient operations: structural maps,
  quotient rings and the representative form of scalar compatibility.
- `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`: `Away`, `Away.mk`,
  `mk_surjective`, and `val_injective`, with the full quotient relation read.
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec` and `Spec.map` signatures/docstrings;
  `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`: `Proj`; its Basic
  interface `basicOpenIsoSpec` and `awayι` supplies the actual chart inclusion.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure` and
  `IsIntegral`, read with the monic-polynomial definition. The normalization
  clause uses these actual integral closures.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`, `mk`,
  `mk_eq`, and `mkLinearMap` were read as the module-localization dependency.
  Its unused direct import is removed: the total fraction construction and
  proof dependency already bring the relevant localization infrastructure.
- Proof-only import `WeilConjectures.Algebra.Module.GradedModuleAwayRestriction`,
  `LocalizedModule.gradedModuleAwayRestriction`, read with its overlap
  localization clause. Other proof dependencies use Mathlib localization
  (`IsLocalization.Away.lift`, ringHom_ext) and Proj Basic already imported,
  or the unchanged associated-graded upstream module now directly publicly imported.

Sources: Stacks curves.tex, remark-quadratic-extension (0CBT), read in full,
particularly constructions (2),(3) and their omitted comparison. The accepted
node makes that comparison intrinsic in the stated generality. Stacks
constructions.tex 01M4 supplies the chart-overlap interpretation; the proof
route remains exactly the accepted eight steps.

Edge cases checked mathematically: n=0 uses multiplication by one and records
all scalar classes. f=0 forces B to be the zero ring by multiplier injectivity;
the localization and E are then zero rings. f∈m² makes ell=0 and forces E=0
(the quotient mB/m²B is zero while mB=fB and f is regular). Nilpotent or
zero-divisor initial forms are allowed: the extra-k localization equality
uses cancellation only of f in B. g=f and α,β identities remain included.
A field A (m=0) has only the zero-B case. Reduced rings with several components
are allowed: FractionRing is the total ring at non-zero-divisors, not a field
or an integral-domain restriction. Arbitrary nonreduced A is allowed in every
clause except the explicit final specialization.

Searches actually performed: preserved searches.jsonl records the prior
LeanFinder query for the canonical division/residue chart map (8 homogeneous
localization hits, no match), Loogle `"HomogeneousLocalization", "map"`
(12 hits, only localization functoriality), and grep for associated-graded
fractions/normalization (0). In this continuation msearch LeanFinder
`canonical graded chart fraction map to quotient by regular principal extension
of maximal ideal natural under ring isomorphisms` returned 8 hits on
HomogeneousLocalization/Proj, none the division construction. Loogle
`"IsFractionRing.ringEquivOfRingEquiv"` returned the exact total-fraction
transport, which is reused. msearch grep
`associated[Gg]raded.*[Gg]rading|associated[Gg]raded.*fraction|[Nn]ormali.*[Gg]raded`
returned 0 Mathlib hits. rg over both WeilConjectures and Sheaf found no
associatedGradedGrading/Class or GradedNormalization declarations; fractionMap
hits belonged to unrelated coefficient and scalar-localization systems. The
node-id search in upstream found no existing statement. DAG searches found
this node and its users, no duplicate internal grading definition.

## Repair of return L, immutable head 78f0cddaaadc

H13: removed the dependency node JSON and
`Sheaf.RingTheory.AssociatedGradedInternalGrading` from the delivery. All six
helpers now belong to the item module and its `lean.declarations`:
`Ideal.associatedGradedGrading`, `associatedGradedGrading_monoid`,
`associatedGradedGrading_isInternal`, `associatedGradedGradingRing`,
`associatedGradedClass`, and `associatedGradedClassHomogeneous` (each in
namespace `Ideal`). Their docstrings now cite this item's blueprint node.
The grading is the ranges of the existing `DirectSum.of` maps, and the class
is the actual quotient class injected into that same direct sum. The two
named theorem obligations describe multiplication/unit compatibility and
unique decomposition, with complete natural-language proofs. The grading
instance uses the uniquely determined decomposition, never an arbitrary
choice of grading. No replacement associated-graded ring is introduced.

A1: `fractionMap_natural` now states `(∃! p, A ∧ B) ∧ ∀ p, A ∧ B → square`,
with A and B the representative formulas for the chart and residue maps.
A2: extracted `fractionMap_changeDenominator_formula` over independent
universes u,v; only the Spec/Proj equality uses a common scheme universe.
A3: removed the unused direct `LocalizedModule.Basic` import.

No mathematical statement, split, source, or DAG dependency is changed;
no new definition node or dependency-module repair is needed. The return
explicitly permits placing these missing internal-grading helpers in the item
module. The module and node are retained from the returned packet, with the
changes above; the original dry run was run first and passed mechanically,
but the independent-review H13 still required this substantive repair.

## Second reading by Q88

No independent worker was started: the dispatcher forbids other agents. The
maintainer performs the independent review under the direct-delivery workflow.
The repair self-review checked the preserved node and the complete module.
The representative conditions uniquely determine the chart and residue
isomorphisms before asserting naturality. The unit and denominator identities
cover arbitrary carrier universes and n=0. The scalar, localization-torsion,
overlap, graded and residue transport, and normalization clauses remain as
in the independently reviewed packet. The internal grading still uses exactly
the recorded upstream ring. All its helper declarations are now owned by the
item; the proved dependency and its 45 citers are unaffected. The main Lean
signature and every non-lean field of the item node are unchanged.

## Validation of the repaired delivery

The item module compiled cleanly through scompile.py in both sandbox and
library modes (6.4 seconds each), with no errors or warnings. Only the
prescribed wrapper was used; no local or global Lean build was run.
The repaired deliver2.py --no-push passed server preflight and compilation
at dry-run commit 1ebd3f8eafe. The staged set contains exactly this report,
the item node, and the item module; it contains no dependency node or module.
Self-checks confirmed the item JSON differs from live only in `lean`, its
recorded main signature is verbatim from the module, all 19 owned declarations
are listed, all lines satisfy the 100-character limit, and the retired helper
module and unused localization import are absent. Every universe and binder
is explicit with autoImplicit false. No mathematical statement fault or
dispute was found.

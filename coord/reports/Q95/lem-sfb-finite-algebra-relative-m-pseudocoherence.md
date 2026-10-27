## Worker report

The module `Sheaf.RingTheory.FiniteAlgebraRelativeMPseudoCoherence` states
`DerivedCategory.isMPseudoCoherentRelativeTo_restrictScalars_finite_iff`, with
`sorry` as its sole proof. The node copy changes only `lean`. No definitions,
new nodes, dependency repairs or statement corrections are needed.

Read Stacks `literature/stacks-project/more-algebra.tex`,
`lemma-finite-extension-pseudo-coherent` (Tag 0673, fixed-m clause), together with
`lemma-relatively-pseudo-coherent` and `definition-relatively-pseudo-coherent`
(Tags 065H and 065I). The source has exactly the stated equivalence. The theorem
docstring carries all six proof steps from the node: zero rings and polynomial
presentations; lifted monic equations from integrality; successive two-term
resolutions; the finite power-product basis; fixed-m scalar restriction through
those quotients and the finite free polynomial algebra; and independence of the
chosen polynomial presentation.

Hypotheses and clauses, matched to Lean:

- Commutative rings R, A, B: `(R : Type u) {A B : Type u}` and the three
  `[CommRing ...]` binders. A common universe follows the recorded relative
  predicate's interface. Rings in smaller universes can also inhabit a common
  larger universe; no special ring is selected.
- Given compatible R -> A -> B: `[Algebra R A] [Algebra R B] [Algebra A B]`
  and `[IsScalarTower R A B]`. The latter asserts compatibility of the direct
  R-action with the composite; the restriction map is `algebraMap A B`.
- A and B finitely generated as R-algebras: `[Algebra.FiniteType R A]` and
  `[Algebra.FiniteType R B]`. These are algebra finiteness, not module finiteness.
- B finitely generated as A-module: `[Module.Finite A B]`.
- Arbitrary integer m: `(m : ℤ)`, without a sign restriction.
- Arbitrary M in D(B): `(M : DerivedCategory (ModuleCat.{u} B))`.
  The independent `HasDerivedCategory.{wA}` and `.{wB}` binders specify the two
  localizations. The family at `wP` supplies the finite polynomial presentations
  used by the recorded relative definition. These are choices of derived
  category size, not boundedness or regularity conditions on M or the rings.
- M is m-pseudo-coherent relative to R: the left side is exactly
  `IsMPseudoCoherentRelativeTo R m M`, with the given `Algebra R B` instance.
- If and only if its restriction to A is relatively m-pseudo-coherent: `↔`
  and the right side `IsMPseudoCoherentRelativeTo R m
  ((RingDerivedScalarExtension.moduleDerivedRestriction (algebraMap A B)).obj M)`.
  This side uses the given `Algebra R A`, the same R, and the same m.
- The termwise restriction clause is built into the named functor. Read
  `RingDerivedScalarExtension.moduleDerivedRestriction`, its alias
  `ConstantScalarRealization.moduleDerivedRestriction`, and
  `ModuleCat.restrictScalars`: the functor is
  `(ModuleCat.restrictScalars f).mapDerivedCategory`, keeping additive groups
  and differentials and letting a act through f(a). It is not a tensor functor.
- No Noetherian, finite-presentation, flatness or cohomological boundedness
  assumption occurs in the signature.

Dependency declarations used (signatures and docstrings read):

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` (statement dependency def-weil-abstract-derived-category).
- `Sheaf.RingTheory.RelativeMPseudoCoherent`:
  `DerivedCategory.IsMPseudoCoherentRelativeTo` (statement dependency
  def-sfb-ring-relative-m-pseudocoherent), with its existential finite polynomial
  presentation and absolute `IsMPseudoCoherent` predicate used unchanged.
- The latter module publicly supplies
  `CategoryTheory.RingDerivedScalarExtension.moduleDerivedRestriction` from
  `Sheaf.AlgebraicGeometry.RingDerivedScalarExtension`, using the exact ordinary
  module functor from `Sheaf.Paper.ConstantRealizationDerivedScalarExtension`.
- Plain imports for stated proof dependencies:
  `WeilConjectures.RingTheory.MPseudoCoherent`
  (`DerivedCategory.IsMPseudoCoherent`),
  `Mathlib.Algebra.MvPolynomial.Basic` (`MvPolynomial`),
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`
  (`Algebra.IsIntegral.of_finite`),
  `WeilConjectures.RingTheory.RingPseudoCoherent`
  (`DerivedCategory.IsPseudoCoherent`), and
  `Mathlib.RingTheory.AdjoinRoot` (`AdjoinRoot.powerBasis'`).
  The fixed-m scalar-restriction and presentation-invariance proof nodes have
  no recorded modules in the read checkout and so add no imports.

Edge cases checked against the node, source and definitions:

- R = 0 implies A = B = 0; zero modules and zero finite free models are allowed.
  B = 0 with nonzero A is also allowed. No `Nontrivial` binder occurs.
- M = 0 satisfies both relative predicates at every integer, using zero models.
- Zero polynomial variables and an empty algebra generating list are permitted
  (`n : ℕ`, `Fin 0`). The proof includes the identity induction in that case.
- Identity A -> A and finite quotient A -> A/I are included; there is no
  injectivity, surjectivity or flatness binder on A -> B.
- For k -> k and any infinite-dimensional k-vector space V in degree zero,
  m = 1 satisfies both sides using the zero approximation; m = 0 fails on
  both sides because V is not finite. This checks that the statement is at
  the fixed m, not silently the all-m pseudo-coherent predicate.
- Negative m and unbounded derived objects are syntactically unrestricted.

Searches actually run (2026-10-24):

- `msearch.py ... leanfinder`: "A complex over a finite algebra is relatively m
  pseudo coherent if and only if its restriction of scalars is relatively m
  pseudo coherent". Eight hits: quasi-finite scalar restriction, ordinary
  finite presentation and base-change results; no relative derived equivalence.
- `msearch.py ... loogle`: `"PseudoCoherent"`. Zero hits.
- `msearch.py ... leansearch`: "finite algebra relative m pseudo coherence
  restriction of scalars". Eight hits, including `RestrictScalars`,
  `ModuleCat.restrictScalars` and sheaf/presheaf restriction; no target theorem.
- `msearch.py ... grep`: `finite.*[Pp]seudo.?[Cc]oher|[Pp]seudo.?[Cc]oher.*finite`.
  Zero Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the above pattern and
  `IsMPseudoCoherentRelativeTo`: found the recorded relative ring definition,
  absolute pseudo-coherent statements, the all-m polynomial-presentation theorem
  and scheme-level statements, but no ring-level fixed-m finite-map theorem.
- `grep -rn` for the item id in `lean/WeilConjectures`: no hits.
  A narrower relative/pseudo-coherent search in the two RingTheory directories
  also found no exact theorem. The scheme predicate with the same short name
  belongs to `Scheme`, a different namespace and a different object type.

Validation: the prescribed `scompile.py Q95
lem-sfb-finite-algebra-relative-m-pseudocoherence <file>` succeeded in sandbox
and library modes (6.7 s and 1.9 s); no errors or unexpected warnings were printed.
All universe variables are explicit and `autoImplicit` is disabled.
No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q95

Performed a separate reading pass of the node, the finished signature and both
statement-dependency interfaces. The three commutative rings, three algebra
structures and scalar-tower binder retain the given compatible maps; the two
finite-type binders and module-finite binder retain the exact three finiteness
hypotheses. Both sides apply the same recorded relative definition at the same
integer m and base R, with M over B on the left and canonical restriction to A
on the right. The functor unfolds to termwise exact restriction, as required.
There is no added boundedness or flatness assumption and no replacement of a
fixed-m claim by pseudo-coherence at all integers. Checked the zero-ring,
zero-object, identity-map and m = 0/1 cases above. No mismatch was found and
no statement change was made. This is the worker's own second pass; the
maintainer's independent review is still required.

## Worker report

The module states `AlgebraicGeometry.ml_cohomology_powers_ideal` in
`lean/Sheaf/Paper/MLCohomologyPowersIdeal.lean`. It binds a Noetherian commutative
ring, proper morphism, ideal, coherent module and cohomological degree, then records
cohomology objects abstractly by `H`, `M`, quotient maps `rho` and transition maps
`tau`. The conclusion is the kernel bound, stabilization of images to `rho`, and the
Mittag-Leffler stabilization clause. The proof is `sorry`, as required for stage 2.

Dependencies consulted: `IsNoetherianRing` (Mathlib.RingTheory.Noetherian.Defs),
`AlgebraicGeometry.IsProper` (Mathlib.AlgebraicGeometry.Morphisms.Proper),
`Scheme.IdealSheafData.comap` (Mathlib.AlgebraicGeometry.IdealSheaf.Functorial),
`RingedSpace.IsCoherent` (Sheaf.AlgebraicGeometry.Coherent),
`AlgebraicGeometry.CoherentFormalModule` (Sheaf.AlgebraicGeometry.CoherentFormalModule),
`sheafCohomologyAndHigherDirectImages` (Sheaf.Paper.PQFCohomology), and
`CategoryTheory.Functor.IsMittagLeffler` (Mathlib.CategoryTheory.CofilteredSystem).

Searches in Mathlib and WeilConjectures for a lemma matching the cohomology powers
Mittag-Leffler statement found no match; only local cohomology and categorical
Mittag-Leffler declarations were found. The file compiles with the server compiler.

## Earlier second reading (a previous round; superseded)

The module was compiled successfully on the server. The statement is recorded verbatim
in the node `lean.statement`; no existing declaration matched the source lemma.


## Second reading by S1

Read the node, Stacks coherent.tex at lemma-ML-cohomology-powers-ideal (02OB),
its full proof, and the signatures and implementations of all seven statement dependencies.
The local source text agrees with the node: A is Noetherian, f is proper, F coherent,
and p nonnegative. Stacks includes level zero in its natural-number system; its quotient
there is zero. The node explicitly selects the positive levels. There are no additional
ambient hypotheses to supply. The node itself needed no correction.

Object, hypothesis and conclusion checklist, with the final Lean rendering and verdict:

1. A, a commutative Noetherian ring: `{A : Type u} [CommRing A]
   [IsNoetherianRing A]`. Read Noetherian.Defs: the latter is IsNoetherian A A,
   equivalently all ideals finitely generated. Exact; no domain or field restriction.
2. X and the proper morphism to Spec A: `{X : Scheme.{u}} (f : X ⟶ Spec (.of A))
   [IsProper f]`. Read Proper and UniversallyClosed: proper is separated,
   universally closed and locally finite type; universally closed supplies quasi-compact,
   so this is finite type as in the dependency node. Exact. No extra Noetherian instance
   on X, flatness, projectivity, or finite presentation is assumed.
3. I, any ideal of A: `(I : Ideal A)`. Exact.
4. The extended ideal I O_X: `(Scheme.IdealSheafData.ofIdealTop
   (I.map (Scheme.ΓSpecIso (.of A)).inv.hom)).comap f` at every occurrence.
   Read ofIdealTop in IdealSheaf.Basic (ideal on an affine open is the map of the
   global ideal), ΓSpecIso, and comap in IdealSheaf.Functorial (kernel of the
   base-changed closed immersion). These give the ideal associated with I on Spec A
   and its pullback image ideal on X, exactly def-nagata-extended-ideal.
5. F, a coherent O_X-module: `(F : X.Modules)
   (hF : RingedSpace.IsCoherent X.toRingedSpace F)`. Read Coherent.lean: finite type
   and finite type kernels for every map from a finite free module on every open.
   Exact; no local freeness or rank assumption.
6. Powers and quotient F/(I O_X)^n F: `formalModuleQuotient` through
   `formalModuleQuotientπ` and `formalModuleQuotientMap`. Read CoherentFormalModule
   and its imported idealModuleProductι and idealSheafPower: the quotient is the
   cokernel of the multiplication-image inclusion. No arbitrary quotient or extra
   structure was retained. The definitions work for arbitrary X and F without an
   IsNoetherian X binder. Exact part (0) of the dependency.
7. p ≥ 0: `(p : ℕ)`. Exact, including p = 0.
8. H = H^p(X,F), and M_n = H^p(X,F/(I O_X)^n F): the objects of
   `RingedSpace.moduleCohomology X.toRingedSpace p`. Read PQFCohomology and
   RingedSpaceModuleCohomology: this is the p-th right derived functor of module-valued
   global sections, not arbitrary groups or abelian-sheaf Ext. Exact.
9. The A-action on H and M_n: their intrinsic Γ(X,O_X)-module action restricted by
   `ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom`.
   The kernel clause uses this exact restricted functor and Submodule A. The ranges
   in the second clause use the original module maps; restriction of scalars leaves
   the underlying functions, zeros and ranges unchanged. Exact specified action.
10. rho_n: moduleCohomology.map applied to `formalModuleQuotientπ` for that ideal,
    n and F, with restriction of scalars in the kernel clause. Exact canonical map.
11. tau_(k,n) for k ≥ n: moduleCohomology.map applied to
    `formalModuleQuotientMap` of that ideal and `𝟙 F`. The proof of n ≤ k is
    `Nat.le_trans (Nat.le_add_right n c) h`. Read the definition: cokernel.desc of
    the quotient projection; precomposition with the level-k quotient is the
    level-n quotient. Thus tau rho = rho is built into the canonical maps rather
    than an extra hypothesis. Exact.
12. One uniform nonnegative integer c: `∃ c : ℕ` outside both universal clauses.
    Exact order of quantifiers; c does not depend on n or k.
13. Kernel bound, for n ≥ 1 and n ≥ c: first conjunct has both `1 ≤ n` and `c ≤ n`,
    `LinearMap.ker` of the actual restricted cohomology projection, bounded by
    `I ^ (n - c) • (⊤ : Submodule A ...)`. This is the submodule of finite sums
    a_i h_i for a_i in I^(n-c), as read in Algebra.Algebra.Operations. Exact.
14. Image equality, for n ≥ 1 and k ≥ n+c: second conjunct binds n,k,
    `1 ≤ n`, then `h : n+c ≤ k`, and equates Set.range of the actual tau and rho.
    Equality of the underlying sets is precisely equality of the image submodules.
    Exact; no unsupported k < n transition is quantified.
15. ML consequence of the same quotient system: third conjunct is
    `(formalCompletionSystem ... F ⋙ moduleCohomology ... p ⋙ forget (ModuleCat ...))
    .IsMittagLeffler`. Read formalCompletionSystem: op m denotes level m+1 and maps
    are the same canonical reductions. Read CofilteredSystem.IsMittagLeffler:
    a stage attains the eventual image. For the decreasing images of a tower this
    is equivalent to the node's eventual equality formulation. Forgetting the
    module directly gives the same underlying sets as forgetting via abelian groups.
    Exact recorded definition, with all positive levels covered.

Edge cases: there is no variable index set to make empty: the tower is the fixed positive
natural numbers, represented by op m ↔ m+1. The empty scheme and zero module are allowed,
with no Nonempty or nonzero hypothesis. The zero ring and I = 0 or I = top are allowed.
The powers at exponent zero are genuine powers, so n = c is included; c = 0 is allowed.
The node imposes no clause at n = 0, and both bounds now explicitly require n ≥ 1.
The degree p = 0 and every characteristic are covered. Universe u is declared explicitly
and arbitrary; the ring, scheme, module sheaves and cohomology are in the established
shared scheme universe, with no independent test-object universe or smallness hypothesis.
By-eye signature audit found no unbound variable, implicit extra instance, let, local
notation, local instance, private definition, or hollow datum.

Independent searches (using different descriptions from the first worker):

- LeanSearch: "Artin Rees kernel cohomology quotient coherent module proper Noetherian
  scheme". Service returned unavailable (Internal Server Error); no verdict assigned.
- LeanFinder: "cohomology quotient sheaves by powers of ideal proper scheme Mittag
  Leffler stabilization of images". Eight hits: localCohomology and its radical/diagram
  variants, idealPowersDiagram, and affine-transition-limit section-vanishing lemmas.
  Opened source declarations relevant to these names: these are local module cohomology
  or sections of limits, not the theorem for proper coherent sheaf quotients. No match.
- Grep/rg over pinned Mathlib, WeilConjectures and project Sheaf for Mittag, ArtinRees,
  ml_cohomology and cohomology_powers, plus IdealSheaf and moduleCohomology searches.
  Found the categorical ML predicate, ideal products and powers, coherent formal-module
  quotients, module cohomology and module-level Artin-Rees. No existing declaration
  states this lemma. These existing notions are used; no new definition or dependency
  module is necessary. The primary declaration name is absent in both source libraries.

Mismatches repaired: the original H, M, rho, tau and Ipower were arbitrary and had no
connection to f, I, F or p. Even their sole compatibility hypothesis did not constrain
tau to quotient-induced maps or Ipower to an ideal action. Deleted every such binder
and used the established definitions above. The old statement also asserted both bounds
at n = 0 and used arbitrary non-additive maps: replaced by positive-index conditions
and canonical linear maps. Replaced the hand-written ML clause with the dependency's
IsMittagLeffler predicate on the canonical tower. Fixed malformed duplicate blueprint
markers, supplied the standard file header, and expanded the proof docstring to all
six node steps, with the kernel comparison, two image inclusions, and ML consequence.
The ring, properness and coherence hypotheses and module/declaration names were retained.

Validation: server single-file compilation passes with no errors or warnings. Every
binder is explicit under relaxedAutoImplicit = false. The sole theorem is
AlgebraicGeometry.ml_cohomology_powers_ideal, with proof `by sorry`; no theorem was proved
and no definition was introduced. The node lean.statement was regenerated by the
project signature reader and is verbatim equal after whitespace normalization.

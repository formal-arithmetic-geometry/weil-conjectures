## Worker report

The module `Sheaf.AlgebraicGeometry.SNCFiniteRootRegularRing` states
`AlgebraicGeometry.isRegularRing_snc_finiteRoot`, with proof `sorry`. It introduces
no new definitions, no helper theorems, and no new nodes. Only the item's `lean`
record is changed. No statement correction or disputed statement is needed.

The previous worker mistook the already completed stage-1 split for completion of
stage 2. The Q08 entry in the ledger records a stage-1 merge and the node's
`reviewed` record; its `lean` field is absent. That is consistent with its
`split_report`, which explicitly says “No new nodes and no Lean attachment.”
This delivery supplies that missing Lean statement without changing the split.

Hypothesis and conclusion correspondence:

- A commutative ring: `(A : Type u) [CommRing A]`. The explicitly bound universe
  is arbitrary; neither a field structure nor nontriviality is required.
- Regularity of X = Spec A: `hA : IsRegularScheme (Spec (.of A))`, using precisely
  the recorded scheme definition. Its conjunction includes local Noetherianity.
- A finite family t_1,...,t_r with r >= 0: `(r : ℕ) (t : Fin r → A)`.
  `Fin 0` is permitted.
- The SNC boundary: `(H : (Spec (.of A)).IdealSheafData)` and
  `hH : IsStrictNormalCrossingsBoundary H`, using the dependency's definition,
  including Cartier, radical, regular-intersection and dimension conditions.
- Its branches are precisely the closed subschemes V(t_i): `hbranches` equates
  the range of the zero loci of the t_i with the images in Spec A of the
  irreducible components of the subspace `H.support`. `PrimeSpectrum.zeroLocus`
  gives exactly the closed subset underlying the principal closed subscheme.
  `hreduced` states `IsReduced (A ⧸ Ideal.span {t i})` for every i. Together these
  say that each principal closed subscheme is the reduced closed subscheme of
  the specified irreducible component; the reduced scheme structure on a
  closed subset is unique. They exclude replacing a branch equation by a power.
  Every component is included by the equality of sets, and no extra branch is
  allowed. This uses the same subspace-component convention as the consumer
  `Sheaf.Paper.SNCRootLimitNormalCharts`.
- Pairwise distinct branches: `hdistinct` is injectivity of
  `i ↦ PrimeSpectrum.zeroLocus {t i}`. Injectivity of the equations as ring
  elements would not suffice, since associates have the same branch.
- A positive integer root degree: `(n : ℕ) (hn : 0 < n)`; n >= 1 is equivalent
  to this condition. `hnunit : IsUnit (n : A)` is exactly invertibility of
  n times 1 in A, including characteristic restrictions and the zero ring.
- The displayed ring is written directly as
  `MvPolynomial (Fin r) A ⧸ Ideal.span (Set.range (fun i ↦ X i ^ n - C (t i)))`.
  These are exactly the r given equations, with no invariants, normalization,
  localization, or further quotient.
- The conclusion `IsRegularRing` includes `IsNoetherianRing` and
  `∀ (q : Ideal C_n) [q.IsPrime], IsRegularLocalRing (Localization.AtPrime q)`
  by Mathlib's definition in `RegularLocalRing/Defs.lean:92`.
- For r = 0 this expression is the polynomial ring in no variables modulo the
  span of an empty range, hence canonically A. The node's displayed equality
  is this canonical identification, rather than literal equality of Lean types.
  There is no hypothesis r > 0. For A = 0 the presentation is zero, and the
  regular-local condition is vacuous because there are no primes.

Recorded statement dependencies read and used:

- `Sheaf.AlgebraicGeometry.IsRegularScheme`,
  `AlgebraicGeometry.IsRegularScheme`: the full definition is
  `IsLocallyNoetherian X ∧ IsRegular X`. Also read the upstream class
  `AlgebraicGeometry.IsRegular` in `WeilConjectures.AlgebraicGeometry.Regular`:
  regularity of every stalk.
- `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`,
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`: read its entire definition,
  including the finite regular integral component witnesses, injective supports,
  support union, regular intersections, and stalk-dimension equality. Its
  `Scheme.IdealSheafData.IsInvertible` means a local nonzerodivisor generator,
  as read in `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`.
- `Mathlib.Algebra.MvPolynomial.Basic`, `MvPolynomial`: read the finite-support
  monoid-algebra definition and `MvPolynomial.algHom_ext` (line 436). Read
  `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval` (line 593) and its
  docstring. The theorem needs the polynomial object, not an evaluation map.
  These are the recorded existing declarations for the polynomial-ring node.

The module also imports every available proof dependency's module, without
`public`, unless it already occurs as a public statement dependency. These are
Mathlib's affine stalk, Noetherian, finite-type, quotient-localization,
AdjoinRoot and polynomial-regularity modules, and the recorded upstream
`RegularLocalLocalization`, `RegularLocalRing.Defs`, `RootAlgebraRegularAtRoot`,
`LocalizationOfRegularRing`, and `HypersurfaceDerivationRegular` modules. The
seven numbered docstring steps reproduce the node's simultaneous induction,
including the branch-unit case as well as primes containing a root coordinate.

Sources opened: ILO IX Proposition 2.1 and its proof, printed p.133 (PDF page 139),
which displays the full simultaneous-root algebra before invariants and reduces
locally to distinct regular parameters; and `literature/stacks-project/etale.tex`,
`lemma-strict-normal-crossings`, lines 2418 onward (Tag 0BIA), giving precisely the
reduced-component/intersection criterion and its proof. The general regular-affine
case of this node is the local regularity argument supplied by its existing split.

Edge cases checked before writing: A = 0; r = 0 and H the empty divisor;
n = 1 (each variable is eliminated and the quotient is canonically A);
A = k[s,u] with branches s and u; primes on one branch, on their intersection,
or on neither branch (the corresponding equations are units locally).
Repeated branches are prohibited: the repeated-equation example
k[x,y]/(x^n-y^n) can be singular. Nonreduced equations are prohibited:
t = s^2 with n = 2 over characteristic zero gives the singular algebra
k[s,x]/(x^2-s^2). A noninvertible n is prohibited by `hnunit`; no global
finite Krull-dimension hypothesis is introduced.

Searches actually run (via the prescribed `msearch.py` wrapper where applicable):

- LeanFinder: “A finite simultaneous root algebra of distinct strict normal
  crossings branch equations over a regular ring is regular when the root
  degree is invertible”. Eight hits on standard smooth/etale presentations,
  including `Algebra.IsStandardSmoothOfRelativeDimension`, `StandardEtalePair`
  and `Algebra.instIsStandardEtaleRing`; no simultaneous ramified-root theorem.
- Loogle: `IsRegularRing, MvPolynomial`. One hit:
  `MvPolynomial.isRegularRing_of_isRegularRing`, which proves regularity of the
  polynomial ring, not of the ramified quotient. This is already a proof leaf.
- Mathlib grep via msearch: `root.*[Rr]egular|[Rr]egular.*[Rr]oot|[Nn]ormal[Cc]rossing`
  in RingTheory. Nine hits on regular-sequence congruence and root-multiplicity
  formulas; none states this theorem.
- Direct rg across `lean/WeilConjectures` and `lean/Sheaf` for root/regular and
  SNC/root variants; direct rg for the exact node id in upstream source.
  No existing statement of this node. The upstream
  `AdjoinRoot.isRegularLocalRing_atPrime_of_root_mem` handles one root at primes
  containing that root, and is a proof dependency, not a match. Other hits are
  strict henselian or one-divisor root models and consumer proof docstrings.
  The existing full root-limit consumer's hypotheses helped confirm the
  component-subspace convention; no second root algebra construction is made.

Validation: `scompile.py NQ lem-sfb-snc-finite-root-regular-ring` compiled the
single delivered file in both its sandbox and actual library module contexts
on the server, with no errors or warnings (3.8 s and 2.9 s respectively).

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

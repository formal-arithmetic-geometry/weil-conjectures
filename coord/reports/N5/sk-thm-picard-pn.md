## Worker report

The delivery states `AlgebraicGeometry.ProjectiveSpace.picard_pn` in
`Sheaf.AlgebraicGeometry.ProjectiveSpace.PicardPn`. Its only proof is `sorry`.
There are no new definitions, new nodes, dependency repairs or statement corrections.
The node copy changes only `lean`.

Read the entire target, its seven proof steps, all four statement-dependency nodes
and the recorded declarations and docstrings, the main-20261015 unit statement,
Stacks `coherent.tex`, `lemma-cohomology-projective-space-over-ring` (Tag 01XT),
its ordered-Cech proof and `equation-identify`, and the blueprint canonical-sheaf lemma.
The theorem docstring carries all seven proof steps and their named prerequisites.

For the following clause correspondence, P abbreviates the expression
`ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))` in this report only. No file-local notation
or private definition occurs in the Lean file. Each cohomology expression in the
file is written out using `RingedSpace.moduleCohomology P.toRingedSpace q`, applied
to the specified module sheaf and then `ModuleCat.restrictScalars` along
`Scheme.globalSectionsRingHom k (X := P)`. This last map is induced by the canonical
structure morphism to `Spec k` and the inverse of `Scheme.ΓSpecIso`. Thus the
cohomology objects and their isomorphisms are in `ModuleCat k`, with the required
k-linear structure, rather than bare additive-group isomorphisms.

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| k a field | `(k : Type u) [Field k]`, with `universe u` explicit |
| n a nonnegative integer; X projective n-space over k | `(n : ℕ)` and P, with exactly n+1 ordered homogeneous coordinates; the lift puts the finite coordinate type in the same universe as k |
| O(m) for every integer m | `twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m`, with `m : ℤ` |
| S^r(V), V = k^(n+1), in the ordered basis | `MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k r`; the node explicitly identifies the symmetric power with this homogeneous polynomial module |
| H^0(O(m)) = S^m(V) for m >= 0 | First conjunct, `∀ m : ℤ, 0 ≤ m → Nonempty (... ≅ ModuleCat.of k (... m.toNat))`; toNat is used only under nonnegativity |
| H^q(O(m)) = 0 for q outside {0,n} | Second conjunct, `∀ (q : ℕ) (m : ℤ), q ≠ 0 → q ≠ n → IsZero (...)` |
| H^n(O(m)) = 0 for m >= -n, n >= 1 | Third conjunct, `1 ≤ n → ∀ m : ℤ, -(n : ℤ) ≤ m → IsZero (...)`, degree n |
| H^n(O(m)) = S^(-m-n-1)(V)^dual for m <= -n-1, n >= 1 | Fourth conjunct, `1 ≤ n → ∀ m : ℤ, m ≤ -(n : ℤ) - 1 → Nonempty (... ≅ ModuleCat.of k (Module.Dual k (... (-m - n - 1).toNat)))`; the hypothesis ensures the dualized degree is nonnegative |
| At n=0, X=Spec k | Fifth conjunct starts `n = 0 → IsIso (P ↘ Spec (.of k))`; this states that the canonical structure morphism identifies X with Spec k |
| At n=0, every O(m)=O_X | Under the same implication, `∀ m : ℤ, Nonempty (twist ... m ≅ SheafOfModules.unit P.ringCatSheaf)` |
| At n=0, H^0(O(m))=k for every m | Next part of the fifth conjunct is `Nonempty (... ≅ ModuleCat.of k k)` in degree zero, without a sign restriction on m |
| At n=0, no higher cohomology | Last part of the fifth conjunct, `∀ q : ℕ, q ≠ 0 → IsZero (...)` for that same arbitrary twist |
| omega_X = Lambda^n Omega^1_(X/k) = O_X(-n-1), all n | Sixth conjunct, `Nonempty (Scheme.Modules.exteriorSheaf (P ↘ Spec (.of k)).relativeDifferentials n ≅ twist ... (-(n : ℤ) - 1))` |
| H^q(O_X)=k delta_(q,0), all n | Final two conjuncts: degree zero is `Nonempty (... ≅ ModuleCat.of k k)`; `∀ q : ℕ, q ≠ 0 → IsZero (...)` in every positive degree, using `SheafOfModules.unit P.ringCatSheaf` |

`IsZero` is used on module-category objects, where it asserts that the module
vanishes. All displayed sheaf equalities are nonempty types of isomorphisms in
P.Modules, and all displayed cohomology equalities are isomorphisms in ModuleCat k.
No finiteness, characteristic, algebraic closure, positivity of n or derived-category
existence hypothesis is imposed globally.

Dependency interfaces used:

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`,
  `AlgebraicGeometry.ProjectiveSpace.twist`, from def-pc-projective-space-twist.
  This is the live library's canonical twist on the projective space obtained from
  the integral model. Its source docstring specifies its local rank-one gluing.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`,
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`, from pqf-def-cohomology.
  Its degree functors are the imported `AlgebraicGeometry.RingedSpace.moduleCohomology`;
  these are exactly the right derived functors used in every clause here.
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`,
  `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, from
  def-sc-relative-differential-sheaf. Applied to P's specified structure morphism.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`,
  `AlgebraicGeometry.Scheme.Modules.exteriorSheaf`, from def-sc-sheaf-exterior-power.
  This is sheafification of sectionwise exterior powers, including degree zero.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`,
  `AlgebraicGeometry.Scheme.globalSectionsRingHom`, supplies the canonical scalar map.
  The upstream `.H` defined in this module is NOT substituted for the node's
  module-sheaf right derived functor. Its docstring expressly distinguishes them.
- Mathlib's `MvPolynomial.homogeneousSubmodule`, `Module.Dual`,
  `ModuleCat.restrictScalars`, `ModuleCat.of`, and `CategoryTheory.Limits.IsZero`
  supply the polynomial models, linear dual, scalar restriction and vanishing.

All recorded proof-dependency modules that have statements are imported as plain
`import`, including Serre, affine Leray, alternating Cech comparison, monomial Cech
decomposition, fixed-exponent homology, and projective-space differentials.
The general `Proj` prerequisite is already transitively imported by the twist module.
Serre's cohomology equivalences now live in
`WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceOverField`, which is
also imported for the proof plan. The existing four formulas do not alone match
the whole node: they use the abelian-sheaf `.H` encoding and omit the combined
canonical-sheaf, dimension-zero and structure-sheaf clauses. The recorded canonical
proof prerequisite points to local freeness of relative differentials; that statement
alone does not supply its full advertised canonical-bundle isomorphism. These
proof-interface observations do not affect the four usable statement dependencies
or require changing the item's mathematical statement.

Edge cases checked before writing:

- n=0: neither top-degree implication applies. Every integer twist, including
  m=-1 and arbitrary negative m, has degree-zero cohomology k. The zeroth exterior
  power is O and O(-1) is trivial. The explicit dimension-zero clause and all-n
  canonical-sheaf/structure-sheaf clauses include this case.
- n=1: at m=-1 the top group vanishes; at m=-2 it is the dual of degree-zero
  polynomials, hence k; at m=-3 it has the two dual monomials of degree one.
- n=2: m=-3 gives a one-dimensional top group, while m=-2 is in the vanishing
  range. The middle degree q=1 vanishes for every twist.
- m=0: H^0 is k and all positive groups vanish for every n. At q=n=0 the
  middle-degree implication is inapplicable, so it cannot falsely kill H^0.
- q>n is included in `q ≠ 0 → q ≠ n`; no upper bound on q was introduced.
- Arbitrary field characteristic and arbitrary universe u remain allowed.
  ULift changes no finite coordinate set or polynomial module up to isomorphism.

Searches actually run:

- msearch/leanfinder: `Cohomology of twisting sheaves on projective space over a field homogeneous polynomials dual top degree canonical sheaf`.
  Eight hits on Proj structure sheaves, basic opens and section maps; no theorem
  stating the combined node.
- msearch/loogle: `AlgebraicGeometry.ProjectiveSpace, "twist"`.
  Zero hits; the service reports unknown identifier AlgebraicGeometry.ProjectiveSpace.
- msearch/grep in Mathlib/AlgebraicGeometry:
  `nonempty_H_zero_twist_equiv|nonempty_H_twist_top_equiv_dual|canonical.*twist`.
  Zero hits.
- msearch/leansearch: `Cohomology of twisting sheaves on projective space over a field`.
  Eight hits on `CategoryTheory.Sheaf.H`, Proj structure sheaves and sections;
  no combined statement.
- rg on both live `lean/WeilConjectures` and `lean/Sheaf`:
  `sk-thm-picard-pn|nonempty_H_zero_twist_equiv|subsingleton_H_twist|nonempty_H_twist_top_equiv_dual|canonicalSheaf|projectiveSpaceCanonical`.
  Located the exact upstream formulas in Cohomology/Serre and
  Cohomology/ProjectiveSpaceOverField and their users; no whole-node declaration.
- rg on projective-space and Sheaf algebraic-geometry modules:
  `canonicalModuleIsoTwist|canonicalModule|exteriorSheaf.*relativeDifferentials|relativeDifferentials.*exteriorSheaf`.
  Located the upstream exteriorPower-based canonical module and its gluing
  isomorphism, and the explicit exteriorSheaf dependency used here. No combined
  statement using the recorded four dependency interfaces.
- rg of `picard_pn|picardPn` in Mathlib, WeilConjectures and Sheaf found no
  existing declaration with the chosen name.

No STATEMENT-DISPUTED flag: the source and node agree, and the dimension-zero
exception explicitly prevents the false n=0 top-vanishing assertion.

Validation: prescribed scompile.py compiled the sandbox and final module paths
successfully (34.9 s and 23.4 s), without errors or warnings. There is one named
postponed theorem and no postponed definition data. All variables and the sole
universe are explicit; every Lean source line is at most 100 characters.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

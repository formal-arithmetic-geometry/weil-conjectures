## Worker report

The module `Sheaf.AlgebraicGeometry.FreeQuotientFirstCohomologyEstimate` states
`AlgebraicGeometry.ProjectiveSpace.freeQuotient_firstCohomology_estimate` with proof
`sorry`. Its two concrete helpers specialize existing definitions: no independent
notion, new node, dependency repair, or statement correction is needed.

Source read: `literature/stacks-project/varieties.tex`, Tag 08AG,
`lemma-bound-quotients-free`, especially its last numerical paragraph. The assigned
node deliberately restricts to positive b, avoiding the source paragraph's erroneous
claim that sections vanish at twist zero. The assigned assertion is true as written.

Hypotheses and objects, clause by clause:

- A field k is `(k : Type u) [Field k]`, with explicit universe u.
- `n r : ℕ`, `hn : 1 ≤ n`, and `hr : 1 ≤ r` render n,r >= 1.
  `b : ℤ`, `hb : 1 ≤ b` render the positive integer twist.
- X is the actual projective space
  `ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of k))`.
  The coordinate type has n+1 elements and lies in the field's universe.
- K and F are objects of X.Modules. The middle object is the canonical
  `SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))`, the direct
  sum of r copies of O_X; i and q are the two displayed arrows.
- `w : i ≫ q = 0` packages their composite as a short complex, and
  `hseq : (ShortComplex.mk i q w).ShortExact` renders exactly the short exact
  sequence, including both endpoints. The choice of w is only a proof.
- `hK` and `hF` use the exact recorded `RingedSpace.IsCoherent` predicate:
  finite type and finite-type kernels of all maps from finite free modules
  on opens. The canonical finite free middle object is coherent on projective
  space over a field, so it needs no additional hypothesis.
- E(d) is literally `E ⊗ ProjectiveSpace.twist ... d`, with the prescribed
  E-first tensor order. `freeQuotientTwistCohomology k n E d j` is
  `(RingedSpace.moduleCohomology X.toRingedSpace j).obj (E(d))`, restricted
  to k along `Scheme.globalSectionsRingHom k`. In particular it is right-derived
  module cohomology, not the upstream underlying-abelian-sheaf Ext definition.
- `hvan : ∀ j : ℕ, 2 ≤ j → IsZero (...)` renders exactly H^j(K(b))=0
  for every j >= 2. `IsZero` is on a bundled ModuleCat object.
- `freeQuotientTwistEuler k n E d` is exactly `(E(d)).eulerChar k`, using
  the dependency's recorded Euler characteristic, including its canonical
  field structure. Its agreement with module-cohomology dimensions is the
  existing comparison between the two models, not an extra assumption.

Conclusions, in order:

- First conjunct: chi(K(b)) = r*C - chi(F(b)). Here
  `C = (n + b.toNat).choose n`; hb ensures b.toNat is precisely b viewed as
  a natural number. The entire subtraction is in Z, without truncated subtraction.
- Second: `(Module.finrank k (H^0(K(b))) : ℤ) ≤ r*C`.
- Third: `0 ≤ (Module.finrank k (H^1(K(b))) : ℤ)`.
- Fourth: `(h^1 : ℤ) = (h^0 : ℤ) - chi(K(b))`.
- Fifth: `(h^1 : ℤ) ≤ chi(F(b))`. Together these render every part of the
  displayed dimension chain; nonnegativity is included explicitly as requested.
- Final conjunct quantifies over every `P : Polynomial ℚ`, assumes
  `∀ d : ℤ, (chi(F(d)) : ℚ) = P.eval (d : ℚ)`, and concludes the three
  inequalities `0 ≤ h^1`, `h^1 ≤ P(b)`, and
  `P(b) ≤ (max 0 ⌈P(b)⌉ : ℤ)` with the integer maximum cast to Q.
  It retains all integer twists, including negative twists and zero, in the
  polynomial hypothesis, and does not assume that P has integer coefficients.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field` (commutative ring and division ring).
- Sheaf.AlgebraicGeometry.CoherentFiniteType, publicly exposing
  WeilConjectures.AlgebraicGeometry.Coherent: `RingedSpace.IsCoherent`.
  The former conjunction `IsQuasiCoherentFiniteType` is not substituted for
  the finite-type-kernel definition.
- WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist:
  `ProjectiveSpace.twist`, including its gluing/transition-unit docstring.
- WeilConjectures.AlgebraicGeometry.PQFCohomology:
  `sheafCohomologyAndHigherDirectImages`, with
  WeilConjectures.Topology.RingedSpaceModuleCohomology:
  `RingedSpace.moduleCohomology` and `RingedSpace.globalSectionsFunctor`.
- WeilConjectures.AlgebraicGeometry.Cohomology.Defs:
  `Scheme.globalSectionsRingHom`, `Scheme.Modules.eulerChar`.
- Mathlib.LinearAlgebra.Dimension.Finrank: `Module.finrank`.
- Mathlib.Algebra.Category.ModuleCat.Sheaf.Free: `SheafOfModules.free`.

The proof dependency imports are present without `public`:
FiniteLocallyFreeTensorExact (`finiteLocallyFree_tensorLeft_exact`),
ProjectiveSpace (`instIsProper`), Cohomology.EulerCharProper
(`finite_setOf_nontrivial_H_of_isProper`, `finite_support_finrankH_of_isProper`),
Cohomology.Serre (projective twist monomial cohomology/vanishing), and
Cohomology.LongExact (`eulerChar_eq_add_of_shortExact`). Statement dependencies
are public imports. The docstring carries all five proof steps, including the
finite-direct-sum basis count and the intermediate coherent partial sums.

Edge cases checked mathematically before writing: n=1 has automatic higher
vanishing, and for K=O(-1), F a rational-point quotient of O, b=1 the first
cohomology bound is 0 <= 1. For F=0, K=O^r all three formulas give h^1=0 and
h^0=chi=r*C. For K=0 and F=O^r the formulas again give h^1=0. The minimal
r=1 and b=1 are included, and no characteristic restriction is introduced.
A polynomial with negative P(b) simply cannot meet the quotient and vanishing
hypotheses, since the asserted bound forces nonnegativity. The ceiling is the
integer ceiling, not natural truncation. Universes are arbitrary u, with ULift
only placing the finite coordinate and free-generator sets in that universe.

Searches (prescribed msearch.py, Q92 and this item):

- leanfinder: "On projective space the first cohomology dimension of the twisted
  kernel of a coherent free sheaf quotient is bounded by the Euler characteristic
  of the quotient". Eight results: projective-object Ext/Tor vanishing and
  projective-dimension lemmas, none the geometric numerical estimate.
- loogle: `"eulerChar", "finrank"`. Three results, the graded-object and complex
  finite-support Euler sum formulas; none is the quotient statement.
- grep: `eulerChar|finrank.*cohomology`, Mathlib/AlgebraicGeometry. Zero hits.
- leansearch: "Euler characteristic and global sections bound the first cohomology
  of the kernel of a coherent free sheaf quotient on projective space". Eight
  results, group/cotangent cohomology and free presentations; none this estimate.
- rg in lean/WeilConjectures and lean/Sheaf for free quotient, first cohomology,
  and the proposed declaration names, plus the node-id grep in WeilConjectures.
  Found the consumer FreeQuotientKernelRegularityBound and unrelated free-quotient
  constructions, no existing instance of the requested theorem or helper names.
  The upstream-name inventory also has no proposed declaration name.

Validation: compile every delivered module with the prescribed scompile.py;
then deliver2.py --no-push and deliver2.py, repairing any failures.

## Second reading by Q92

A separate pass by this single dispatched worker compared the node, the source
paragraph, and the complete Lean signature. The dispatcher forbids other agents;
the maintainer provides the independent review. The pass checked the field,
n,r,b bounds, coherent K and F, free middle term, both exactness endpoints,
the precise tensor order, and every conclusion as matched above. It checked
that hvan concerns actual right-derived module cohomology with the canonical
k-action and that the polynomial hypothesis covers every integer d. It checked
that dimension subtraction occurs in Z and polynomial comparisons in Q.
An unnecessary explicit coherence binder for the canonical free middle object
was removed: that coherence is automatic on projective space over a field.
Compiler feedback required a type ascription on E(d), so the tensor monoidal
structure is inferred on X.Modules before its use as a ringed-space module;
it changes no mathematical object. No mismatch with the assigned statement remains.

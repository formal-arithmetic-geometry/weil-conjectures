## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.EulerTensorHomogeneity` states
`AlgebraicGeometry.IsAbelianVariety.eulerChar_tensor_integer_power` with exactly one
`sorry`, its entire proof. No definitions or other theorems are introduced. The item's
JSON changes only in `lean`. No statement correction, new node, dependency repair, or
STATEMENT-DISPUTED flag is necessary.

Hypothesis and clause correspondence:

- An algebraically closed field k is `(k : Type u) [Field k] [IsAlgClosed k]`.
  `Field` is Mathlib's commutative division-ring structure and `IsAlgClosed` is its
  polynomial-splitting property, equivalent to roots of nonconstant polynomials.
- A/k is `(A : Over (Spec (.of k))) [GrpObj A] [IsAbelianVariety A]`.
  The group object supplies the group-scheme structure; the recorded abelian-variety
  class supplies properness, smoothness, and connectedness. No extra group law or
  commutativity assumption is imposed.
- Dimension g >= 1 is `(g : ℕ) (hg : 1 ≤ g)` together with
  `(hdim : topologicalKrullDim A.left = (g : WithBot ℕ∞))`.
  The cast embeds the natural dimension into the recorded extended Krull dimension.
  It excludes precisely dimension zero and negative/infinite dimensions as the node does.
- An arbitrary invertible O_A-module is `(L : A.left.Modules) [L.IsInvertible]`.
  There is no ample, very ample, nonzero-Euler, finite-kernel, or nondegeneracy hypothesis.
- Every integer n is the unrestricted binder `(n : ℤ)`.
- For n >= 0 the object is `L.tensorPow n.toNat`; at zero the existing recursive
  definition is the tensor unit, i.e. the structure sheaf. For n < 0 it is
  `L.dual.tensorPow (-n).toNat`. The recorded invertibility module and its `Dual`
  interface identify this dual with the tensor inverse. This is the identical
  inline signed-power convention used by the recorded Snapper theorem; no new
  signed-power notion is introduced.
- Coherent Zariski Euler characteristic is the recorded `.eulerChar k`, valued in Z.
  Its `finrankH` uses the k-action from the structure morphism, and its `finsum`
  is the alternating sum in the node. The node's finite-sum explanation follows
  from properness, Noetherianity, coherence of invertible modules and the already
  recorded Euler well-definedness theorem; it adds no independent input or hypothesis.
- The conclusion is literally the integer equality
  `(if 0 ≤ n then L.tensorPow n.toNat else L.dual.tensorPow (-n).toNat).eulerChar k =
  n ^ g * L.eulerChar k`. The exponent on the integer n is the natural dimension g,
  so the sign for negative n is retained.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (available through public imports).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraically closed
  clause of `def-weil-algebraic-closure`; no algebraic closure extension is required.
- `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`:
  `AlgebraicGeometry.IsAbelianVariety`, also `IsAbelianVariety.dim` and its
  `topologicalKrullDim_eq` read to check the dimension convention.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`, publicly available
  through the abelian-variety definition module.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` and `tensorPow`, publicly
  available through `WeilConjectures.AlgebraicGeometry.Modules.Dual`.
  That latter module supplies `dual`, `nonempty_tensorObj_dual_iso_unit` and
  `exists_tensorObj_iso_unit`, so the negative-power object is the genuine inverse.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`:
  `AlgebraicGeometry.Scheme.Modules.eulerChar`, `finrankH`, and `moduleHOfField`.

Plain imports retain the stated proof dependencies: Noetherian permanence from
`Mathlib.AlgebraicGeometry.Noetherian`; coherent = quasi-coherent and finite type
from `WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`;
Euler finiteness from `WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharProper`;
`exists_mvPolynomial_eulerChar_tensorPowers` from
`Sheaf.AlgebraicGeometry.SnapperNumericalPolynomial`;
`IsAbelianVariety.exists_dual_polarization_calculus` from
`Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus`;
`isIsogeny_npow_id` and `isogenyDegree_npow_id` from
`WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny`; and
`Polynomial.eq_of_infinite_eval_eq` from `Mathlib.Algebra.Polynomial.Roots`.
The proper-morphism definition is already a public import of the abelian-variety module.
`lem-sfb-isogeny-postcomposition-degree` and `lem-sfb-abelian-euler-degree-square`
had no recorded Lean module when inspected; they are proof dependencies only, so no
missing statement object is needed. The five numbered docstring steps reproduce the
node's proof, including the zero-degree convention and the polynomial sign argument.

Sources and edge cases:

Read Milne AV, Chapter I Theorem 11.1, printed p.54 / PDF p.60 directly with
`pdftotext -f 60 -l 60 -layout`. Part (b) says chi(L(D)) = (D^g)/g! for arbitrary
invertible L; applying it to nD gives the stated formula, including n < 0.
At n=0 the left object is O_A and the right side is zero because g>=1, yielding
chi(O_A)=0. At n=1 tensorPow 1 is canonically L, so equality becomes invariance
under the unit isomorphism. At n=-1 it gives chi(L dual)=(-1)^g chi(L), consistent
with duality on an abelian variety. For chi(L)=0 the conclusion still says every
signed-power Euler characteristic is zero; no cancellation by chi(L) was assumed.
In particular the trivial and degenerate line bundles are retained. At g=1 this
is the usual degree formula on a genus-one curve. Dimension zero is excluded
explicitly by the node; the empty scheme cannot be a connected group variety.
There is no characteristic restriction, nor any restriction to positive n.
All universes and variables are explicitly bound, and auto-implicit binding is disabled.

Searches for reuse (2026-10-24):

- msearch.py / leanfinder: "On an abelian variety of dimension g the Euler
  characteristic of the nth tensor power of an invertible sheaf is n^g times its
  Euler characteristic for every integer n". Eight hits include
  `IncidenceAlgebra.eulerChar_prod`, `FDRep.char_tensor`, `CommRing.Pic.mk_tensor`,
  `CommRing.Pic.mul_eq_tensor`, `AlgebraicGeometry.Proj.pow_apply`, and
  `AddChar.zsmul_apply`; none states coherent Euler homogeneity.
- msearch.py / loogle: "AlgebraicGeometry.Scheme.Modules.eulerChar, tensorPow, zpow".
  Zero hits; service reports unknown identifier
  `AlgebraicGeometry.Scheme.Modules.eulerChar` (the project declaration was read directly).
- msearch.py / grep, AlgebraicGeometry: "eulerChar|tensorZPow|tensorIntPow|IsAbelianVariety".
  Zero Mathlib hits.
- msearch.py / leansearch: "For an abelian variety A of dimension g and every
  invertible sheaf L the Euler characteristic of the integer tensor power L^n equals
  n^g times chi(A,L)". Eight hits: linear-equivalence tensor powers, incidence Euler
  characteristics, representation tensor characters, and Proj section evaluation;
  none states the item.
- rg on `lean/WeilConjectures` and `lean/Sheaf` for tensor-power / integer-power /
  Euler homogeneity names located the existing tensorPow and dual definitions,
  the inline convention in SnapperNumericalPolynomial, and unrelated generic
  `CategoryTheory.TensorInverse.zpow`. No existing item statement was found.
- rg in `dag/lean_names_upstream.json`, WeilConjectures and Sheaf for
  `homogeneity|euler_tensor|eulerChar_tensorPow` found no matching theorem.
- grep -rn for the full item id in `lean/WeilConjectures` returned no result.
  Searches of the abelian-variety and six-functor DAG chapters locate this node
  and its distinct degree-square sibling, rather than another node for this statement.

Compilation: prescribed scompile.py compiled both its sandbox module and the final
library module on the server cleanly (2.1 s and 1.9 s respectively), under the default
60-second limit. Only the named theorem is postponed. No global build was run.

## Second reading by Q86

Author's separate self-check, not an independent review: I reopened the node statement
and the written signature. The six statement-dependency notions are their recorded
Mathlib/upstream notions. The group structure is explicit alongside the abelian-variety
class; g is a positive natural number tied to the actual topological Krull dimension;
L is any invertible module. The unrestricted integer n and conditional tensor-power
expression retain zero and negative exponents. The right hand side uses integer
exponentiation by g, rather than abs(n)^g or natural-number truncation. The dual really
is the tensor inverse; no choice of an arbitrary inverse is assumed. The Euler invariant
uses the structure morphism of the same Over object A. No mismatch was found and no
statement field was changed. The report records the finite-sum clause as the semantic
well-definedness of the existing Euler characteristic on these proper coherent inputs,
not as an extra assumption. The independent delivery review remains the maintainer's.

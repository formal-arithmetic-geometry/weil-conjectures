## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.smoothCurve_section_degree_cap`
in `Sheaf.AlgebraicGeometry.SmoothCurveSectionDegreeCap`. The theorem has the sole
postponed proof (`sorry`). Four definition helpers have real data and belong to
this same statement: `smoothCurveVanishingTwist`, `smoothCurveVanishingSections`,
`smoothCurveSectionGerm`, and `smoothCurveSectionVanishes`. They specialize existing
constructions; no independent mathematical notion or new DAG node is introduced.

Read the item, all nine statement-dependency statements and records, their source
interfaces and docstrings, the proof dependency records, and Stacks `curves.tex`
`lemma-grd-inequalities` (0CCS, lines 442 onward), together with `varieties.tex`
`lemma-degree-tensor-product` (0AYX) and
`lemma-degree-effective-Cartier-divisor` (0AYY). No repair note exists for this item.
The old example Sheaf CompactObject module is withdrawn; I also read the recorded
upstream `WeilConjectures.CategoryTheory.CompactObject` example.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
- Curve over k: `(C : Scheme.{u}) [C.Over (Spec (.of k))]`; its structure morphism
  is `C ↘ Spec (.of k)`. This packages precisely one structure morphism, without
  selecting or assuming additional maps.
- Smooth, proper, connected curve: `[IsConnectedCurve (C ↘ Spec (.of k))]`,
  `[Smooth (C ↘ Spec (.of k))]`, `[IsProper (C ↘ Spec (.of k))]`.
  IsConnectedCurve includes separatedness, finite type, connectedness, nonemptiness,
  and dimension exactly one. Integrality, regularity, and Noetherianness are not
  added as hypotheses. The generic germ helper obtains integrality from the recorded
  smooth-connected-curve theorem.
- Invertible A: `(A : C.Modules) [A.IsInvertible]`.
- Effective finite divisor B: `(B : C.Divisor)` is the existing finitely supported
  integer function on closed points; `hB : ∀ P : closedPoints C, 0 ≤ B P`
  says precisely that every coefficient is nonnegative. Its b is
  `Divisor.degree C B`, the existing sum-of-coefficients homomorphism.
- Nonnegative integers m,q: `(m q : ℕ)` includes both zero values and is equivalent
  to quantifying over integers subject to nonnegativity.
- e = deg A: every occurrence uses `A.degree k`, the recorded Euler characteristic
  difference. There is no new degree definition or free numerical parameter.
- A^{⊗m}(-qB): `smoothCurveVanishingTwist` is literally
  `A.tensorPow m ⊗ (-(q • B)).moduleOfSmoothConnectedCurve k C f`.
  Tensor powers and divisor modules are the recorded existing objects.
- The space is H⁰ of this actual module: `smoothCurveVanishingSections` applies
  `RingedSpace.moduleCohomology C.toRingedSpace 0` and restricts scalars along
  `globalSectionsRingHom k (X := C)`. Thus it uses the recorded module-sheaf
  derived functor directly, rather than identifying two definitions of higher
  cohomology without a comparison.
- Vanishing to order at least q n_P: `smoothCurveSectionVanishes` universally
  quantifies over proofs that the canonical generic germ is nonzero and requires
  `(q : ℤ) * B P ≤ rationalSectionOrder ... P` for every closed P.
  A zero generic germ satisfies this vacuously, as required for the zero section.
  On an integral curve, invertibility implies that a global section with zero
  generic germ is zero; thus this includes exactly the node's zero convention.
- Identification with the prescribed-vanishing space: the first conjunct produces
  an injective k-linear map j from that H⁰ to Γ(A^{⊗m}); membership in its image is
  equivalent to the exact order condition for every global section s. The target
  k-action is the same canonical restriction of scalars, expressed using
  RingedSpace.globalSectionsFunctor. This is an identification of vector spaces,
  not merely an equality of their dimensions. The existential map is a conclusion,
  not an assumed or arbitrarily chosen replacement for the divisor module.
- Finite dimensionality: the next conjunct is `FiniteDimensional k` of this H⁰.
- Degree equality: the next conjunct is the literal degree of the twist equal to
  `(m : ℤ) * A.degree k - (q : ℤ) * Divisor.degree C B`.
- Dimension bound: `(Module.finrank k (smoothCurveVanishingSections ...) : ℤ)`
  is at most `max ((m : ℤ) * A.degree k - (q : ℤ) * Divisor.degree C B + 1) 0`.
  The cast and the subtraction force the maximum to lie in ℤ, not ℕ.
- In particular zero in negative degree: the final implication uses the same
  integer expression `< 0` and concludes `Subsingleton` of H⁰. For this vector
  space that means it is the zero vector space, not just a finrank-zero claim
  that could hide infinite dimension.

Dependency declarations used:

- `Field` (Mathlib.Algebra.Field.Defs) and `IsAlgClosed`.
- `AlgebraicGeometry.IsConnectedCurve` / `IsCurve`
  (WeilConjectures.AlgebraicGeometry.Curve), supplied publicly by DivisorModule.
- `AlgebraicGeometry.IsProper` (Mathlib.AlgebraicGeometry.Morphisms.Proper),
  supplied by the EulerChar dependency.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible` and `tensorPow`
  (WeilConjectures.AlgebraicGeometry.Modules.Invertible); the tensor-power
  invertibility instance is in Modules.ProjectionFormula, publicly imported
  because the statement uses rationalSectionOrder for A.tensorPow m.
- `AlgebraicGeometry.Scheme.Modules.degree`
  (WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar), defined from
  `Modules.eulerChar` and `finrankH` in Cohomology.Defs.
- `AlgebraicGeometry.Scheme.Divisor`, `Divisor.degree`
  (WeilConjectures.AlgebraicGeometry.Curve.Divisor), and
  `Divisor.moduleOfSmoothConnectedCurve` (Sheaf.AlgebraicGeometry.DivisorModule).
- `AlgebraicGeometry.Scheme.Modules.rationalSection` and `rationalSectionOrder`
  (Sheaf.AlgebraicGeometry.RationalSectionDivisor). The order is exactly the
  recorded normalized DVR valuation of the coefficient in a local generator.
- `AlgebraicGeometry.RingedSpace.moduleCohomology`, `globalSectionsFunctor`
  (WeilConjectures.Topology.RingedSpaceModuleCohomology), with existing
  `ModuleCat.restrictScalars` and `Scheme.globalSectionsRingHom`.

All recorded proof-dependency modules are imported as plain imports when not already
public statement dependencies. The record for
`lem-trf-proper-field-invertible-coherent` has no Lean declaration, so no module
import is available for that proof dependency; its exact role is retained in the
seven-step theorem docstring. No unstated proof dependency is needed to type this
statement. The smooth-connected-curve local-rings module is also public transitively
through RationalSectionDivisor and supplies the helper's integral instance.

Edge cases checked before writing: B=0 gives the zero twist divisor; m=0 uses the
existing tensor unit; q=0 gives O(0) for every B. Together these give degree zero,
h⁰(O_C)=1, and bound 1. When me-qb=-1 the bound is exactly zero; for smaller
negative values the integer maximum remains zero. For degree zero, the trivial
bundle attains 1 and a nontrivial degree-zero line may have zero sections. On P¹,
A=O(e) gives h⁰=max(me-qb+1,0), so the bound is sharp even with imposed vanishing.
For an elliptic curve A=O(P), m=1 and q=0 gives 1≤2. The zero section satisfies
all conditions, including at points outside supp B. Empty curves, disconnected
curves, and dimension-zero schemes are excluded by the node's connected-curve
hypothesis itself. No characteristic restriction or projectivity hypothesis is added.

Searches (all run 2026-10-24):

- msearch LeanFinder: “Global sections of an invertible sheaf on a proper smooth
  curve have dimension bounded by max degree plus one zero”, digest
  `379f8078a743de32`, 8 hits: Weierstrass polynomial-degree bounds,
  coordinate/function fields and ranks; no match for this theorem.
- msearch Loogle: `"finrank", "degree"`, digest `42af015a5688d0f7`, 12 hits,
  about polynomial quotients, field separable degrees, residue degrees and rational
  functions; no matching line-bundle section bound.
- msearch Mathlib grep: `finrankH.*(le|degree)|degree.*finrankH|h0.*degree`,
  digest `6c367c3005496229`, 18 returned hits concerning polynomial degrees and
  field theory, none the statement.
- msearch LeanSearch: “Sections of a line bundle on a curve vanishing along an
  effective divisor are global sections of its negative twist”, digest
  `30980abda296ea40`, 8 hits about affine restrictions, Proj, and vanishing ideals;
  no existing construction or theorem with the required identification.
- Direct rg in lean/WeilConjectures and lean/Sheaf for
  `finrankH.*≤|finrankH.*degree|degree.*finrankH|degree.*[Cc]ap|section.*degree.*bound`
  and rationalSectionOrder/generic germs found the recorded section-order APIs and
  Modules.finrankH_zero_eq_zero_of_degree_neg. The latter only gives negative-degree
  vanishing, not the degree computation or dimension cap and image identification.
- Direct rg for the item id in lean/WeilConjectures returned no declaration.
  Direct rg for all five proposed declaration names found no collision.

Validation: module-mode server scompile.py passes for the delivered module, both
its sandbox probe and its actual library module name, with no errors or warnings.
The initial parser errors were missing parentheses around an H⁰ type and were
repaired. The final statement directly uses the recorded module cohomology object.
No statement correction, dependency replacement, or STATEMENT-DISPUTED issue.

## Second reading by NQ

Self-check against the node and the completed module (no separate worker was
started, as the dispatcher expressly forbids other agents): all field, curve,
properness, smoothness, invertibility and effectivity hypotheses match. Checked
that IsConnectedCurve really includes dimension one and nonemptiness, and that
natural m,q include zero. Read the helper bodies: the negative sign is outside q•B,
so the local twist is t^{q n_P}, and scalar restriction uses the structure map.
The first theorem conjunct includes both injectivity and the pointwise image iff,
so it identifies the entire vanishing section space and includes zero. The generic
germ and rational-section order come from the recorded dependency, with no new
valuation normalization. Replaced the first draft's source `Modules.H` in the
section-space clauses by the exact recorded `RingedSpace.moduleCohomology` functor;
EulerChar degree remains the recorded existing definition. Checked the dimension
cast, integer max, degree equality, and negative-degree implication separately.
No hypothesis or numerical conclusion changed. Every helper is definitionally
constructed, and the only theorem proof is sorry. The full seven-step node proof
is in its docstring. The maintainer's independent review is still required by the
remote worker delivery workflow.

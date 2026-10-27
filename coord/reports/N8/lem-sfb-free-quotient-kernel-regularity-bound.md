## Worker report

This delivery states `AlgebraicGeometry.ProjectiveSpace.exists_freeQuotient_kernel_regularity_bound` in `Sheaf.AlgebraicGeometry.FreeQuotientKernelRegularityBound`, with one whole-proof `sorry`. The natural-language node is unchanged. Its earlier Q25 review is the review of the stage-1 split; the base has no Lean record, so this is new stage-2 work, not another unchanged stage-1 submission. Source read: `literature/stacks-project/varieties.tex`, `lemma-bound-quotients-free` (08AG), including its induction proof, and `definition-regularity` (08A3).

Clause-by-clause reading:

- Integers n >= 0 and r >= 1: `(n r : ℕ) (hr : 1 ≤ r)`; arbitrary rational polynomial: `(P : Polynomial ℚ)`. These parameters precede the conclusion.
- A single integer depending only on n,r,P: `∃ a : ℤ` occurs before `∀ (k : Type u) [Field k]` and before every module and arrow. No choice of field or quotient can affect a. The universe `u` is explicitly declared and unrestricted.
- Projective n-space over k: `ℙ(ULift.{u} (Fin (n + 1)); Spec (CommRingCat.of k))`. The project's coordinate index counts n+1 homogeneous coordinates. ULift changes only size, not the coordinate set.
- Kernel and quotient: `K F` are modules on exactly this scheme. The middle term of the two morphisms `i` and `q` is `SheafOfModules.free (R := ...ringCatSheaf) (ULift.{u} (Fin r))`, the coproduct of r copies of the structure sheaf.
- Short exact sequence: `w : i ≫ q = 0` and `(CategoryTheory.ShortComplex.mk i q w).ShortExact`, whose fields say exactness, mono i, and epi q. No extra splitting or condition on sections is assumed.
- Coherence of K and F: the two hypotheses `Scheme.Modules.IsQuasiCoherentFiniteType K` and `... F` use the dependency's recorded declaration. Projective space over a field is locally noetherian, where quasi-coherent finite type is precisely coherent; see the existing `Scheme.Modules.isFiniteTypeWithFiniteTypeKernels_iff` in `WeilConjectures.AlgebraicGeometry.Cohomology.FiniteFibre`. The canonical finite free middle term is automatically coherent and needs no additional premise. No altered general definition of coherence is introduced.
- Every integral twist: `(∀ d : ℤ, ((F ⊗ twist ... d).eulerChar k : ℚ) = P.eval (d : ℚ))`. This includes negative d and uses the recorded Euler characteristic. Its integer value is cast to Q to compare with the rational polynomial. For coherent modules here, projective finiteness and higher vanishing ensure this is the finite alternating sum stipulated by the node, not an infinite or infinite-dimensional surrogate.
- Regularity: `∀ j : ℕ, 1 ≤ j → j ≤ n → Subsingleton ((K ⊗ twist ... (a - (j : ℤ))).H j)`. In an additive group, Subsingleton is exactly vanishing. All and only the degrees 1 through n are required. There is no nonnegativity condition on a.
- The tensor products with the recorded `ProjectiveSpace.twist` are exactly G(d) = G tensor O(d); no new twist or regularity predicate is defined.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType` (quasi-coherent and finite type); the locally noetherian specialization above accounts for coherence.
- `def-pc-euler-characteristic`: `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`, `AlgebraicGeometry.Scheme.Modules.eulerChar` (finsum of signed `finrankH k q`), and its `H` and `finrankH` definitions.
- `def-pc-projective-space-twist`: `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`, `AlgebraicGeometry.ProjectiveSpace.twist`, the canonical pullback of the integral model's twisting sheaf.
- `pqf-def-cohomology`: `WeilConjectures.AlgebraicGeometry.PQFCohomology`, `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`, imported publicly. The concrete groups use the existing `Scheme.Modules.H` encoding also used by `eulerChar` and all the projective cohomology inputs. Its source explains the standard comparison with module-derived global sections; this does not introduce another cohomology construction.
- Mathlib's `SheafOfModules.free` and `ShortComplex.ShortExact` are read and reused directly.

Available proof dependencies are imported privately through the recorded modules `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`, `.Projective`, `.Serre`, and `.LongExact`. The two projective-space base-change inputs are already publicly imported transitively by the twist module. The following proof-only nodes have no Lean module recorded on the base and hence supply no import: `lem-pc-finrank-field-base-change`, `lem-sfb-coherent-regular-hyperplane-restriction`, `lem-sfb-m-regular-coherent-sheaf-consequences`. None is needed to type this statement. The theorem docstring includes all ten proof steps, including the larger safe final bound, field-extension descent, the common hyperplane for four modules, plateau argument, and Euler estimate.

Edge cases checked before writing: n=0 has no j in the asserted range (a=0 works); n=1 asks only for H^1(K(a-1)); r=1 is allowed; r=0 is excluded exactly as in the source; F=0 and K=0 cause no undefined objects; arbitrary rational P is allowed and unrealizable polynomials make the implication vacuous; finite fields and arbitrary characteristic remain in the universal quantifier; negative twists and a are allowed. For a length-two quotient of O on P^1 the kernel O(-2) needs a>=2, consistent with the node's enlarged bound and avoiding the source proof's final off-by-one estimate. There are no disputed statements, new nodes, or dependency repairs.

Searches made with the prescribed msearch.py wrapper:

- LeanFinder: `Uniform Castelnuovo Mumford regularity for kernels of coherent quotients of a free sheaf on projective space with fixed Hilbert polynomial`: 8 hits, principally Proj constructions, with no uniform regularity bound.
- Loogle: `"regular", "Sheaf"`: 12 hits about regular sites and projective objects, no Castelnuovo--Mumford regularity statement.
- Mathlib grep: `Castelnuovo|mumford|mRegular|hilbertPolynomial` in AlgebraicGeometry: 0 hits.
- LeanSearch: `There exists a uniform Castelnuovo Mumford regularity bound for kernels of coherent quotients of a free sheaf with fixed Hilbert polynomial`: 8 hits, including constructible-set degree bounds and free sheaf presentation machinery; none states this result.
- Source and project rg: `lem-sfb-free-quotient-kernel-regularity-bound|exists.*regularity|regularity.*bound|kernel.*regular` in lean/WeilConjectures and lean/Sheaf: no matching statement. Source `ProjectiveSpace/Resolution.lean` has a projective-line zero-regularity argument, not a uniform bound over all dimensions, fields and Hilbert polynomials.

Compilation uses only the prescribed scompile.py wrapper. An initial wrong polynomial import path was corrected to `Mathlib.Algebra.Polynomial.Eval.Defs`; subsequent compiler and preflight results are recorded below.

Final direct scompile.py check: clean; sandbox compile 9.5 s and library-path compile 7.2 s, within the standard 60 s limit.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

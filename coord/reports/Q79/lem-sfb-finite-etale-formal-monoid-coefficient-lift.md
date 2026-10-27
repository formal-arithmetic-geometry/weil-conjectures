## Worker report

This delivery records an exact existing statement, without a Lean module:
`AddMonoidAlgebra.finiteEtale_formalMonoid_coefficientLift` in
`Sheaf.RingTheory.FiniteEtaleFormalMonoidCoefficientLift`.
Its owning node is `lem-per-finite-etale-formal-monoid-coefficient-lift`, already
cited by this item's sole proof step. I read the local canonical module and its
live server source using `scompile.py --source`; both supply the signature and
canonical constructions discussed below. The item's statement, statement
dependencies, proof and proof dependencies are unchanged. Only `lean` changes;
`existing` is true and there is no `lean.file`.

The resolved maintenance handoff in
`coord/repair-notes/lem-sfb-finite-etale-formal-monoid-coefficient-lift.json`
explicitly requires precisely this attachment after restoration of the canonical
source. The earlier missing-source ending is obsolete. The sandbox contains no
returned duplicate module. No dependency repair, new node or statement correction
is needed.

Hypothesis and clause comparison with the canonical signature:

1. The coefficient ring is `(E : Type u) [CommRing E]`.
   `[IsRegularLocalRing E]` extends both `IsLocalRing E` and
   `IsNoetherianRing E`; `IsLocalRing` extends `Nontrivial`. These give exactly
   the nonzero regular Noetherian local hypothesis. Completeness is
   `[IsAdicComplete (IsLocalRing.maximalIdeal E) E]`. Mathlib identifies this
   Hausdorff/precomplete condition with bijectivity of the canonical completion
   map, so the item's explanatory sentence imposes nothing further.
2. The additive commutative monoid is `(S : Type v) [AddCommMonoid S]`.
   `hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative S)` is the
   dependency's finite generation, injective group-completion map and saturation
   predicate. The multiplicative wrapper changes notation only.
   `hsharp : ∀ s : S, IsUnit (Multiplicative.ofAdd s) → s = 0` says exactly
   that the only invertible additive element is zero.
3. `AddMonoidAlgebra E S` is the finitely supported monoid algebra, with basis
   `single s 1` and multiplication induced by addition in `S`. The ideal `a`
   is fixed, rather than left arbitrary, by `ha`: it is the join of the image
   of the maximal ideal of `E` and the span of the nonzero monomials.
   `AdicCompletion a (AddMonoidAlgebra E S)` is therefore precisely `H = E[[S]]`,
   the combined-adic completion specified by the node.
4. `f` has that completion type and `hf` places it in the extension of `a` to
   the completion. For a finitely generated sharp monoid and a Noetherian local
   coefficient ring, that ideal is the unique maximal ideal: its residue ring
   is the residue field of `E`, and geometric series invert elements congruent
   to one. This identification is also explained in steps 1 and 2 of the
   existing theorem's proof docstring. There is no `f ≠ 0` hypothesis.
5. The base `A₀` is written explicitly as
   `AdicCompletion a (AddMonoidAlgebra E S) ⧸ Ideal.span {f}`.
   `(K : Type w) [CommRing K] [IsLocalRing K]` includes nonzeroness.
   `[Algebra A₀ K] [Module.Finite A₀ K] [Algebra.Etale A₀ K]` says exactly
   local finite étale algebra. The ring version of étaleness agrees with
   étaleness on affine spectra, as in Mathlib's scheme étale API and the
   recorded dependency. No arbitrary map replaces the algebra structure.
6. The existential coefficient ring is
   `∃ (D : Type (max u v w)) (_ : CommRing D)
      (_ : IsRegularLocalRing D) (_ : Algebra E D), ...`.
   Its regular-local instance includes locality, nonzeroness and Noetherianity.
   `Module.Finite E D ∧ Algebra.Etale E D` gives finite étaleness, and
   `IsAdicComplete (IsLocalRing.maximalIdeal D) D` gives completeness.
   The universes `u`, `v`, `w` remain independent; the existential universe can
   accommodate the finite coefficient extension without restricting the inputs.
7. `Nonempty (IsLocalRing.ResidueField D ≃+* IsLocalRing.ResidueField K)`
   identifies exactly the requested residue fields. `ResidueField` is the
   quotient by the unique maximal ideal in the local ring convention.
8. `IsLocalRing.maximalIdeal D =
     Ideal.map (algebraMap E D) (IsLocalRing.maximalIdeal E)` is exactly
   `m_D = n D`.
9. The next universally quantified clause takes every `x : E` belonging to
   `maximalIdeal E` and not to its square, and concludes that `algebraMap E D x`
   belongs to `maximalIdeal D` and not to its square. This renders every element
   of `n \ n²`, including the vacuous case `n = 0`, with no chosen parameter.
10. `e : K ≃+* CoefficientHypersurface E S a f D` is the required isomorphism.
    The helper is the quotient of the completion of `D[S]` at the coefficient
    extension of `a`, by `formalCoefficientMap E S a D f`. With `m_D = n D`,
    this defining ideal equals the combined ideal `(m_D, [s] : s ≠ 0)`.
    The helper `formalCoefficientMap` is constructed by the monoid-algebra
    coefficient homomorphism at every ideal-power quotient and the compatible
    inverse limit (`AdicCompletion.mapRingHomAlong`); it is exactly the
    coefficientwise image, with no assumed or arbitrarily chosen map.
11. The equation for every `h : H` equates `e` applied to the structural image
    of `h mod f` with the quotient of its coefficientwise image. Since every
    element of `A₀` has a representative in `H`, this is precisely the condition
    that `e` is an `A₀`-algebra isomorphism. No stronger coefficient linearity
    or unspecified target algebra structure is required.
12. The final two `@Continuous` clauses equip `K` with its maximal-ideal adic
    topology and the target with `coefficientHypersurfaceTopology`. The latter
    is the quotient topology from the completed combined-adic monoid ring.
    Both `e` and `e.symm` are continuous. These are the topologies specified
    by the formal monoid construction; they agree with the maximal-ideal
    topologies as detailed in step 10 of the existing proof docstring.

Dependency declarations read and used by the existing statement:

- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`,
  `AlgebraicGeometry.IsRegularScheme`, and its unchanged ring-side Mathlib match
  `IsRegularLocalRing` / `IsRegularRing` in
  `Mathlib.RingTheory.RegularLocalRing.Defs`. This item uses the ring clause.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`; included in `IsRegularLocalRing`.
- `def-weil-pbc-adic-completion`: `AdicCompletion` and `IsAdicComplete` in
  `Mathlib.RingTheory.AdicCompletion.Basic`, with the ring structure and maps
  from its completion algebra API.
- `def-trf-fs-log-blowup`: recorded module
  `Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup`; its public import
  `Sheaf.AlgebraicGeometry.LogRegularPair` supplies
  `AlgebraicGeometry.IsFineSaturatedMonoid`, whose full definition was read.
- `def-weil-finitely-generated-module`: `Module.Finite` in
  `Mathlib.RingTheory.Finiteness.Defs` (finite generation of the top submodule).
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`; the theorem uses its equivalent
  affine ring notion `Algebra.Etale` from `Mathlib.RingTheory.Etale.Basic`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`, the spectra referred to by the preceding
  affine comparison.
- The existing proof dependency is the canonical theorem recorded above. Its
  full proof docstring gives the henselian finite-étale equivalence, finite-basis
  completion calculation, regularity ascent and faithful-flat ideal contraction.
  This item's proof is its direct specialization; the extra final explanatory
  sentences only expand definitions already used by that theorem.

Sources checked: the finite-étale equivalence in `more-algebra.tex`,
`lemma-finite-etale-equivalence` (09ZL); the finite-module completeness lemma
`lemma-when-finite-module-complete-over-complete-ring` (031B), and regularity
ascent `lemma-regular-goes-up` (07NF) in `algebra.tex`. They agree with the
existing assembly and proof docstring; no source-based correction is needed.

Edge cases checked: the trivial monoid `S = {0}` reduces the formal monoid ring
to the completed coefficient ring, so no nontrivial-monoid hypothesis is hidden.
For `E` a field, `n = 0` and the cotangent assertion is vacuous. `f = 0` is
explicitly admitted by `hf`; zero belongs to the extended ideal and no later
clause excludes it. Nonreduced hypersurfaces such as `f = t²` are also admitted;
only `E` and `D`, not `H/(f)` or `K`, are required to be regular. Mixed
characteristic with `f` a coefficient uniformizer is admitted. The zero ring
is excluded exactly by the local-ring instances on `E`, `K` and `D`.

Searches for an existing statement:

- `msearch.py ... leanfinder`: "A local finite etale algebra over a complete
  local formal monoid hypersurface is induced by a finite etale local
  coefficient extension preserving cotangent classes". Eight hits concern
  standard étale presentations and loci; none gives the formal monoid theorem.
- `msearch.py ... leansearch`: "Finite etale local algebras over a complete
  local formal monoid ring arise by finite etale extension of the coefficient
  ring". Eight hits give general étale and formally étale algebra API, not the
  full completed monoid and cotangent statement.
- `msearch.py ... loogle`: `"Etale", "AdicCompletion"`: zero hits.
- `msearch.py ... grep`:
  `(Etale|etale).*(AdicCompletion|MonoidAlgebra)|(AdicCompletion|MonoidAlgebra).*(Etale|etale)`:
  zero hits in Mathlib.
- `rg -n 'finiteEtale_formalMonoid_coefficientLift|formalCoefficientMap|CoefficientHypersurface'`
  in `lean/WeilConjectures` and `lean/Sheaf`: the exact theorem and constructed
  helpers are in the canonical Sheaf module, and no upstream duplicate appears.
- Search of the item id in `lean/WeilConjectures`: zero hits. The DAG proof
  dependency and the resolved maintenance handoff identify the exact existing
  theorem; comparing its statement with the item leaves only explanatory
  definitions in the item's additional final sentences.

No STATEMENT-DISPUTED issue was found. The normal delivery wrapper checks the
existing declaration on the server and performs the maintainer preflight; no
new module is delivered or needs compilation.

## Second reading by Q79

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

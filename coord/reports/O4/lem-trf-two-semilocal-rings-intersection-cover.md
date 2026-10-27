## Worker report

The module `Sheaf.AlgebraicGeometry.TwoSemilocalRingsIntersectionCover` states
`AlgebraicGeometry.two_semilocal_rings_intersection_cover`, with its proof `sorry`.
Its auxiliary `Subring.infTensorProductMap` is the actual canonical ring homomorphism
from the tensor product over the intersection, constructed from Mathlib's
`Algebra.TensorProduct.productMap`. There are no postponed auxiliary theorems.

Source read: `literature/stacks-project/varieties.tex`, Situation
`varieties-situation-glue` (09MY), and Lemma `varieties-lemma-semi-local-both-side`
(09N3), statement and proof. Situation 09MY introduces the subrings, their common
fraction field, and their intersection; 09N3 has exactly the three hypotheses
and the open-cover and tensor-isomorphism conclusions used here. No statement
correction, new node, or dependency repair is needed.

The hypothesis and conclusion correspondence is:

| Node clause | Lean rendering |
| --- | --- |
| A field K | `{K : Type u} [Field K]` |
| Unital subrings C,D of K | `(C D : Subring K)`; Mathlib subrings contain 1 |
| Each has fraction field K, through its inclusion | `[IsFractionRing C K] [IsFractionRing D K]`; the canonical subring algebras into K are inferred |
| Both Noetherian | `[IsNoetherianRing C] [IsNoetherianRing D]` |
| Both semilocal, finitely many maximal ideals | `[Finite (MaximalSpectrum C)] [Finite (MaximalSpectrum D)]` |
| Both have Krull dimension exactly one | `hCdim : ringKrullDim C = 1`, `hDdim : ringKrullDim D = 1` |
| Multiplication C tensor_Z D to K surjective | `hsurj : Function.Surjective (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom ℤ C K) (IsScalarTower.toAlgHom ℤ D K))` |
| R is the actual intersection | The Mathlib subring infimum `(C ⊓ D : Subring K)` throughout |
| Inclusion-induced Spec C to Spec R open immersion | First `IsOpenImmersion` conjunct, using `Subring.inclusion inf_le_left` and `Spec.map (CommRingCat.ofHom ...)` |
| Inclusion-induced Spec D to Spec R open immersion | Second `IsOpenImmersion` conjunct, using `Subring.inclusion inf_le_right` |
| Their images cover Spec R | For every point `x : Spec (CommRingCat.of (C ⊓ D : Subring K))`, membership in one of the two exact morphism ranges |
| The multiplication C tensor_R D to K is a ring isomorphism | `Function.Bijective (Subring.infTensorProductMap C D)`; the map is a ring homomorphism, so bijectivity is equivalent to an isomorphism of rings |

The helper equips C and D with the real algebra structures
`(Subring.inclusion inf_le_left).toAlgebra` and
`(Subring.inclusion inf_le_right).toAlgebra` using `letI` inside the definition.
It equips the inclusions to K with their definitionally commuting algebra-hom
structures and returns Mathlib's `productMap` as a ring homomorphism. Thus its
source is precisely the Mathlib tensor product with the intended R-actions,
and its value on `c ⊗ d` is `c * d` in K by construction. The helper introduces
no arbitrary map or algebra structure as a hypothesis, and contains no `sorry`.
The theorem signature has no `let`, private notation, or extra instance binder.
All variables and the universe are explicitly bound.

Dependency declarations read and used:

- `def-weil-field`: `Field` in `Mathlib.Algebra.Field.Defs`, a commutative division ring.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`, with `isNoetherianRing_iff_ideal_fg`.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim` in
  `Mathlib.RingTheory.KrullDimension.Basic`, valued in `WithBot ℕ∞`.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` in
  `Mathlib.LinearAlgebra.TensorProduct.Defs`; its algebra multiplication map is
  `Algebra.TensorProduct.productMap` in `Mathlib.RingTheory.TensorProduct.Maps`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map` in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-open-immersion`: `AlgebraicGeometry.IsOpenImmersion` in
  `Mathlib.AlgebraicGeometry.OpenImmersion`.

The proof-dependency imports include
`WeilConjectures.RingTheory.JacobsonDenominatorFunctionField`
(`RingTheory.exists_inv_mem_jacobson_of_tensor_surjective`, signature and proof
docstring read), `Mathlib.RingTheory.Jacobson.Ideal` (`Ideal.mem_jacobson_bot`),
`Mathlib.RingTheory.Ideal.Maximal` (`Ideal.exists_le_maximal`),
`Mathlib.RingTheory.Spectrum.Prime.Topology` (`PrimeSpectrum.zeroLocus_eq_iff`),
`Mathlib.AlgebraicGeometry.OpenImmersion`
(`Scheme.isOpenImmersion_SpecMap_localizationAway`), and
`Mathlib.RingTheory.Localization.BaseChange` (`IsLocalization.Away.tensorEquiv`,
`tensorRightEquiv`, `LocalizedModule.equivTensorProduct`). The localization-away
notion is available through these imports. Public imports supply statement
notions; plain imports retain the named proof plan. The theorem docstring
records all six DAG proof steps, with their node names and explicit denominator,
radical, open-cover, and pure-tensor calculations.

Edge cases checked before writing:

- Subrings of a field are nonzero domains automatically; no extra domain or
  nontriviality hypotheses are imposed. Empty spectra and zero rings do not
  arise under the actual subring and dimension hypotheses.
- A field used as either subring has dimension zero, and is correctly excluded
  by equality to 1 rather than merely an upper dimension bound.
- If C = D, multiplication has image C; surjectivity would force C = K,
  contradicting dimension one. The same check rules out nested C,D. No
  unnecessary inequality or noncontainment assumption was added.
- For a concrete case, C = k[t] localized at (t), D = k[t] localized at (t-1),
  the intersection is the semilocal ring at these two points. The complementary
  parameters x = 1-t and y = t give the two charts and the overlap field k(t).
  The tensor-surjectivity hypothesis holds because every nonzero polynomial
  factors into a power of t and a factor invertible in C; t is invertible in D.
- The map and hypothesis are over Z, so all characteristics are admitted.
- The ambient field and its subrings live in the same arbitrary universe u;
  subrings are subsets of K and require no independent size restriction.

Searches performed:

1. `msearch.py ... leanfinder`: "Two independent Noetherian semilocal dimension
   one subrings of a field give open spectra covering the spectrum of their
   intersection and their tensor is the field". Eight results: intersection of
   localizations in a fixed ring, tensor-spectrum embedding, DVR criteria, and
   unrelated integral-closure/etale results. None states this theorem.
2. `msearch.py ... loogle`: `IsOpenImmersion, Subring,
   Algebra.TensorProduct.productMap`. No hits; service reported unknown
   identifier `IsOpenImmersion`.
3. `msearch.py ... grep`, RingTheory, `semilocal|semi.local|intersection.*[Ss]ubring`.
   Thirteen hits: semilocal local properties, Picard groups, valuation subrings,
   finite maximal spectra, and local module structure. None gives these charts
   of the intersection or the canonical tensor-isomorphism theorem.
4. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for semilocal names,
   the node id, and the intended declaration names; no exact existing statement
   or helper. The existing `SemilocalSubringAffineGluing` is the finite-family
   consumer: its proof cites this node, and its theorem does not state the
   canonical two-ring tensor conclusion. It cannot serve as a statement match.
5. Read Mathlib subring inclusion/algebra constructions and
   `Algebra.TensorProduct.productMap`/`productMap_apply_tmul` directly to reuse
   the canonical map. No replacement tensor-product definition was introduced.

There are no statement disputes or node faults.

Validation: the prescribed single-file server compile, dry-run preflight, and
final delivery are run with `scompile.py` and `deliver2.py`; no global build or
direct Git command is used.

## Second reading by O4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

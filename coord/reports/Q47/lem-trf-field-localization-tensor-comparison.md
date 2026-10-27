## Worker report

The module `Sheaf.RingTheory.FieldLocalizationTensorComparison` states
`Algebra.field_localization_tensor_comparison` with its entire proof postponed by
`sorry`. Its only helper, `Algebra.fieldTowerTensorMap`, is the actual
`Algebra.TensorProduct.map (IsScalarTower.toAlgHom k L H) (AlgHom.id k R)`;
its data is complete. No new node, dependency repair, or statement correction is needed.

Source read: `literature/stacks-project/varieties.tex`, Tag 0C4Y,
`lemma-change-fields-flat`, lines 238–280, especially its factorization in proof (3).
The six proof steps in the node are reproduced in the theorem docstring. The algebra
interfaces cited by those steps were opened in Mathlib, including the localization
universal property, tensor cancellation, and iterated-localization theorem.
The example CompactObject module is now withdrawn; its node points to the upstream
`CategoryTheory.IsCompactObject`, so the usual module-system header is followed.

Hypotheses and objects:

- The field tower is `[Field k] [Field L] [Field H]`, with `[Algebra k L]`,
  `[Algebra L H]`, `[Algebra k H]`, and `[IsScalarTower k L H]`. The last two
  encode the composite map, without restricting the tower. The four type universes
  `u v w z` are independent.
- The commutative k-algebra is `[CommRing R] [Algebra k R]`. There is no
  finite-type, finiteness, separability, characteristic, or Noetherian assumption.
- Tensor factors are written in the opposite order everywhere: `S = L ⊗[k] R`,
  `T = H ⊗[k] R`, `H ⊗[k] Localization.AtPrime p`, and
  `H ⊗[L] Localization.AtPrime q`. These are precisely the node's objects under
  `Algebra.TensorProduct.comm`; this is the same standard tensor-product notion,
  not a replacement construction. In this order the standard left algebra structures
  give L acting on S and on its localization; no file-local instance is used.
- `q : Ideal (L ⊗[k] R)` and `[q.IsPrime]` are the prime of S.
  `p : Ideal R`, `[p.IsPrime]`, and `hp : p = q.comap includeRight.toRingHom`
  name its contraction. Quantifying p with this defining equality adds no restriction:
  the contraction is prime by Mathlib's `Ideal.IsPrime.comap` instance. It simply
  avoids hiding the named p behind an unfolding-inaccessible statement-level let.
- `fieldTowerTensorMap k L H R` is j; on `l ⊗ r` it gives
  `algebraMap L H l ⊗ r`. `p.primeCompl` is V and `q.primeCompl` is U.
  Every localization is Mathlib's actual quotient `Localization` or its
  `Localization.AtPrime` abbreviation.

Clause correspondence:

1. The existential ring equivalence `eA` is the first identification
   `H ⊗[k] R_p ≃+* Localization (V.map includeRight.toRingHom)`.
   Its first conjunct specifies, for every h,r,v, the formula
   `h ⊗ (r/v) ↦ (h ⊗ r)/(1 ⊗ v)`. This specifies the canonical comparison
   on generators, not just the existence of an arbitrary ring equivalence.
2. The equivalence `eB` is the second identification
   `H ⊗[L] S_q ≃+* Localization (U.map j.toRingHom)`.
   The second conjunct specifies `h ⊗ (s/u) ↦ ((h ⊗ 1)*j(s))/j(u)`.
   These are the node's numerator and denominator formulas after tensor commutation.
3. The ring homomorphism `f` is the induced map between the two scalar extensions.
   The third conjunct requires `f (eA.symm (t/1)) = eB.symm (t/1)` for every t in T.
   Since fractions generate the first localization, this determines the induced map.
   The fourth conjunct is `IsLocalization` for the algebra structure `f.toAlgebra`,
   at `j(U).map (eA.symm.toRingHom.comp (algebraMap T (Localization ...)))`.
   This is exactly the image of U along `S → T → V⁻¹T`, transported to the first
   scalar extension by eA. Thus the localization property applies to f itself.
4. The final conjunct quantifies over every ideal Q of T, with `[Q.IsPrime]` and
   `Q.comap j.toRingHom = q`. It provides `g` to `Localization.AtPrime Q`.
   The equation `g (eB.symm (t/1)) = t/1` for all t says the map agrees on T;
   it characterizes the canonical map, using uniqueness out of a localization.
5. The next conjunct is `IsLocalization` for `g.toAlgebra` at the image of
   `Q.primeCompl` under `eB.symm ∘ (T → j(U)⁻¹T)`. This is precisely the
   further localization at the images of `T \ Q`.
6. The last conjunct says `g (eB.symm (t/j(u))) = t/d` whenever d in
   `Q.primeCompl` has value j(u). Such d exists for every u by the contraction
   equality. Naming d explicitly only supplies its membership proof to the
   quotient constructor; it does not restrict which fraction formula is asserted.
7. The structural R, L, H compatibilities are all encoded by the two all-fractions
   formulas together with the two all-t equations: specialize respectively to
   h=1, s=1⊗r, s=l⊗1, and r=1 or s=1. Thus eA and eB preserve their structural
   elements, f preserves their common T elements, and g does as well. Ring
   multiplication, including the node's pure-tensor multiplication and unit, is
   Mathlib's `Algebra.TensorProduct.instCommRing` with `tmul_mul_tmul`.

Dependency declarations used:

- `def-pc-field-extension`: `Algebra`, module `Mathlib.Algebra.Algebra.Defs`,
  with fields as specified in its recorded interface.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.tmul`,
  `TensorProduct.lift`, and `TensorProduct.ext'`, modules
  `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Basic`; multiplication and
  inclusions are `Algebra.TensorProduct.instCommRing`, `tmul_mul_tmul`,
  `includeLeft`, `includeRight` from `Mathlib.RingTheory.TensorProduct.Basic`.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime` from
  `Mathlib.RingTheory.Localization.AtPrime.Basic`. Its full definition and
  documentation were read; residue fields and fibre rings are not used here.
- Proof dependencies are all Mathlib leaves: `TensorProduct.AlgebraTensorModule.cancelBaseChange`
  from `Mathlib.LinearAlgebra.TensorProduct.Tower`; the tensor pushout declarations
  `productMap` and `ext` from `Mathlib.RingTheory.TensorProduct.Maps` and `.Basic`;
  `IsLocalizedModule.rTensor` and `map_lTensor` from
  `Mathlib.RingTheory.Localization.BaseChange`; `IsLocalization.lift` and
  `ringHom_ext` from `Mathlib.RingTheory.Localization.Defs`; and
  `IsLocalization.isLocalization_of_submonoid_le` from
  `Mathlib.RingTheory.Localization.LocalizationLocalization`. These modules are
  imported directly or transitively through the listed proof imports.

Searches actually run:

- msearch leanfinder: `field tower localization tensor comparison`. Eight hits,
  including `IsLocalization.tensorProduct_tensorProduct`, `algebraTensorEquiv`,
  `tensor`, `tensorRight`, and `IsLocalizedModule.rTensor`. These supply individual
  localization comparisons, not the full statement with both arrows and formulas.
- msearch loogle: `IsLocalization tensorRight Localization.AtPrime`. Zero hits;
  service diagnostic: unknown identifier `tensorRight`. This query was unusable,
  not evidence of absence; the semantic and source searches supplied the interfaces.
- msearch grep, subdirectory RingTheory: `localization.*tensor|tensor.*localization`.
  Twenty-five hits including `Localization/BaseChange.lean`; its tensor/localization
  declarations were opened and do not state the whole field-tower comparison.
- msearch leansearch: `For a field tower k L H the scalar extension of the local ring
  of R tensor k L is a localization of R_p tensor k H, compatibly with localization
  at a prime`. Eight hits: `IsLocalization.tensor`, Dedekind-specific scalar towers,
  and module base-change lemmas; no exact comparison theorem.
- rg of both `lean/WeilConjectures` and `lean/Sheaf` for localization/tensor concepts,
  and for the proposed declaration names. No exact declaration or name collision.
  The relevant existing `GeometricReducednessLocalBaseChange` theorem is a consumer
  proving a reducedness equivalence, not this comparison. The direct node-id search
  in `lean/WeilConjectures` returned no match. The upstream-name index was also searched.

Edge cases checked: `k = L = H` recovers nested ordinary localizations. `R = 0`
permits no prime q and is correctly vacuous. Nonreduced rings and rings with zero
 divisors remain allowed; no fraction cancellation is assumed. Infinite and
inseparable field extensions are allowed. The Q clause is conditional on contraction,
so it does not assert a choice of prime above q; for each existing Q all its
complement denominators are inverted. Independent type universes exclude no field
or ring sizes. All names and universes are explicitly bound; no local notation,
local instances, private declarations, or statement-level lets occur.

Validation: the final module is checked by `scompile.py` and the delivery dry run.
Only the main theorem has a `sorry`; no result has been proved in this stage.
No statement dispute or node fault was found.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

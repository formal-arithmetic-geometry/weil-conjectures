## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianVariety.TateActionSaturation` states
`AlgebraicGeometry.IsAbelianVariety.tate_action_saturation`. Its single proof is `sorry`.
No definition, new node, dependency repair, or statement correction is needed. The item
node changes only in `lean`.

The source was read in Milne, Abelian Varieties, Chapter I: Remark 7.3 (printed p.34),
Proposition 10.5 and Lemma 10.6 (p.45), and Lemma 10.16 (p.49). In particular, 10.16
says exactly that prime-power divisibility of the Tate action implies divisibility in
Hom over the original field. Also read the current blueprint's
`sec-abelian-varieties/sk-def-av-tate/_section.md`. No algebraic-closure hypothesis
is imposed on the original field.

Clause-by-clause rendering:

- Field k: `(K : Type u) [Field K]`, with explicitly declared universe `u`.
- Abelian varieties A and B over k: `(A B : Over (Spec (.of K)))`, each with
  `[GrpObj ...] [IsAbelianVariety ...]`. The recorded definition supplies exactly
  properness, smoothness and connectedness, with the group structures separate.
- Prime ell different from char k: `(ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [CharP K p]`
  and `(hℓ : ℓ ≠ p)`. Specifying the unique characteristic as p does not restrict k.
- The geometric Tate modules are the existing `tateModule ℓ A` and `tateModule ℓ B`.
  Their definition uses points over `AlgebraicClosure K`, rather than K-rational points.
  The coefficient ring is the existing `ℤ_[ℓ]`, namely `PadicInt ℓ`.
- M is `Additive (Grp.mk A ⟶ Grp.mk B)`. The morphisms in `Grp` are exactly morphisms
  of the k-schemes preserving the group laws. Mathlib's internal-group instances on
  `Grp.mk B`, induced by `IsAbelianVariety.isCommMonObj B`, give this Hom its pointwise
  commutative group law. `Additive` writes that existing law as addition. All underlying
  morphisms are recovered by `f.toMul.hom.hom`; no private Hom type or group law is defined.
- H is exactly `tateModule ℓ A →ₗ[ℤ_[ℓ]] tateModule ℓ B`.
- Finite free of ranks `2 dim A`, `2 dim B`: the first two `Nonempty (... ≃ₗ[ℤ_[ℓ]]
  (Fin (2 * dim ...) → ℤ_[ℓ]))` conjuncts. These give actual finite bases and the claimed
  ranks, equivalently the node's finite-free assertion. The recorded `Module.Free`
  definition is not replaced; finite-coordinate linear equivalences express its
  finite-basis specialization including the precise ranks.
- H is free of rank `4 dim A dim B`: the third conjunct is `Nonempty` of a linear
  equivalence to `(Fin (4 * dim A * dim B) → ℤ_[ℓ])`.
- The componentwise action is an additive homomorphism: the last conjunct gives
  `∃ iota : M →+ H`, with `∀ f, iota f = tateModuleMap (ℓ := ℓ) f.toMul.hom.hom`.
  This equation specifies its value at EVERY group-scheme homomorphism, so this is
  precisely the canonical action, uniquely specified, not an arbitrary map. The
  existing map's definition and `coe_tateModuleMap_apply` give the coordinate formula.
  Bundling the additive action existentially asserts additivity without inventing a
  new definition or postponing data.
- Injectivity of that very action: `Function.Injective iota`.
- Every integer n at least one: `(n : ℕ), 1 ≤ n → ...`. Positive integers are exactly
  these natural numbers; the node has no negative-exponent case.
- Membership `iota(f) ∈ ℓ^n H`: `∃ v : H, iota f = (ℓ : ℤ_[ℓ]) ^ n • v`.
- Divisibility in M: `∃ g : M, f = (ℓ ^ n) • g`, using the pointwise natural scalar
  multiplication on the additive group of homomorphisms.

Dependency declarations used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (reexported by TateModule).
- `def-sc-abelian-variety`: `AlgebraicGeometry.IsAbelianVariety` and its `dim`, in
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs` (publicly imported by TateModule).
- `sk-def-av-tate`: its closed upstream audit names
  `AlgebraicGeometry.IsAbelianVariety.tateModule`, in
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule`. That same module also
  supplies `tateModuleMap` and `coe_tateModuleMap_apply`. I read their definitions,
  signatures and docstrings; the audit's old line numbers are not relied on.
- `def-weil-l-adic-numbers`: recorded Mathlib match `Padic`,
  `Mathlib.NumberTheory.Padics.PadicNumbers`, and its expressly identified integral
  ring `PadicInt`, `Mathlib.NumberTheory.Padics.PadicIntegers`.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`, `Grp`, and `IsMonHom`,
  `Mathlib.CategoryTheory.Monoidal.Grp` / `Mon`; pointwise Hom groups are
  `CategoryTheory.Hom.group` and `Hom.commGroup` in
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`. Read also its internal-group
  instances on `Grp` and the constructors `Grp.homMk`, `Grp.ofHom`.
- `def-weil-pbc-free-module`: `Module.Free`,
  `Mathlib.LinearAlgebra.FreeModule.Basic` (public import); its basis interpretation
  is expressed by the three finite-coordinate linear equivalences.

The module also privately imports the available proof-dependency modules: abelian
variety Basic, Isogeny, Torsion, group-theoretic TateModule, BaseChangeConventions,
GroupScheme.Defs, FieldExtensionFpqcCover, and Mathlib's algebraic closure, fpqc
site, precoverage and finite-morphism modules. The item proof dependencies
`lem-sfb-abelian-field-extension`, `lem-sfb-simple-isogeny-decomposition`,
`lem-sfb-abelian-closed-subgroup-reduced-component`, and
`lem-sfb-abelian-torsion-kernel-divisibility` have no Lean records or Mathlib matches
in the read clone, so there is no recorded module to import for those proof-only nodes.
All nine proof steps and their dependency ids are retained in the theorem docstring.

Edge cases checked before writing: dim A = 0 or dim B = 0 makes the corresponding
`Fin 0` coordinates empty and the Hom rank zero; the only homomorphism is zero and
g = 0 divides it. Neither positive dimension nor nonempty matrix index sets are assumed.
f = 0 and n = 1 are included. n = 0 is outside the node's quantifier, expressed by
`1 ≤ n`. Characteristic zero is included by p = 0, while ell = char k is explicitly
excluded. No algebraic closedness, perfection, finite generation of Hom, Galois
invariance of H, or finite-field assumption is added. The universe is arbitrary and
is the same convention used by the recorded geometric Tate-module construction.

Searches (2026-10-24):

- `msearch.py ... leanfinder "faithful Tate action on abelian varieties injective
  homomorphism saturated divisibility"`: eight hits, including
  `FaithfulSMul.of_injective`, `AddCommGrpCat.injective_of_divisible`, and Selmer and
  torsion maps. No hit states algebraic Tate faithfulness or saturation.
- `msearch.py ... loogle "tateModuleMap, AddCommGroup.tateModule"`: zero hits;
  the service reports unknown identifier `tateModuleMap` (it is project-specific).
- `msearch.py ... grep "tateModuleMap|tateModule" AlgebraicGeometry`: zero hits in Mathlib.
- `msearch.py ... leansearch "The Tate module functor of abelian varieties is faithful
  and detects divisibility by prime powers"`: eight hits about faithful functors,
  including Galois fiber functors, Spec, and derived single functors; no exact match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for Tate-module maps, injectivity,
  saturation, and Hom: found the existing geometric Tate modules, their componentwise
  maps, and rank over algebraically closed fields, but no theorem for this item.
- Search for the item id in upstream Lean and for the proposed name in
  `dag/lean_names_upstream.json`, upstream Lean, and Sheaf: no existing declaration.

Validation: `scompile.py Q148 lem-sfb-abelian-tate-action-saturation <file>` compiles
both the sandbox probe and the actual library module cleanly (6.1 s and 4.0 s).
The initial parser error from using the scoped inverse-notation token `ι` as a binder
was repaired by naming the binder `iota`; no mathematical change resulted.
No statement dispute or source fault was found.

## Second reading by Q148

I reread the finished module against the node and the existing Mathlib internal-group
instances in this dispatcher-started worker; no additional agent was started. The
maintainer's independent review remains the independent reading of this delivery.
The field and both varieties, ell-primality and characteristic exclusion, all three
ranks, canonical componentwise formula, additive-homomorphism property, injectivity,
and positive-power divisibility conclusion each have the counterparts listed above.
In particular, the equality specifying `iota` prevents the existential additive map
from weakening the canonical-action assertion, and `Grp` Hom excludes arbitrary
scheme morphisms. No hypothesis or conclusion mismatch was found. The only repair
was the parser-level renaming `ι` to `iota`; the statement stayed unchanged.

## Worker report

The module `Sheaf.RingTheory.IsEtaleAtFieldExtensionDescent` states
`Algebra.IsEtaleAt.of_fieldExtension`, with proof `sorry`. No definitions, new nodes,
dependency modules, or statement corrections are needed.

Hypothesis and clause correspondence:

- The field `k`, extension field `K`, and their map are `k : Type u`, `K : Type v`,
  `[Field k] [Field K] [Algebra k K]`.
- The commutative `k`-algebra `A` is `[CommRing A] [Algebra k A]`.
- The finitely presented `A`-algebra `B` is `[CommRing B] [Algebra A B]
  `[FinitePresentation A B]`. `[Algebra k B] [IsScalarTower k A B]` specify the
  induced ground-field action, rather than an additional mathematical restriction:
  this compatible action always exists by composing the two algebra maps.
- The primes are `(q : Ideal B) [q.IsPrime]` and
  `(qK : Ideal (B ⊗[k] K)) [qK.IsPrime]`.
- `B_K` and `A_K` are literally `B ⊗[k] K` and `A ⊗[k] K`.
  The `letI` algebra structure is the tensor map of `IsScalarTower.toAlgHom k A B`
  and `AlgHom.id k K`: on pure tensors it sends `a ⊗ c` to `algebraMap A B a ⊗ c`.
- Contraction of `qK` to `q` is exactly `hq`, the equality of the comap along
  `Algebra.TensorProduct.includeLeftRingHom` with `q`.
- The source's `p = q ∩ A` and `p_K = qK ∩ A_K` are auxiliary defined primes;
  neither enters the asserted implication. They can be recovered as comaps along
  `algebraMap A B` and the tensor map above, respectively. There is no extra
  hypothesis on them to impose.
- The assumption is `IsEtaleAt (A ⊗[k] K) qK`, and the conclusion is
  `IsEtaleAt A q`. The node's parenthetical flatness/differentials description is
  its explanation of the same pointwise hypothesis, not an additional conclusion.
  The module uses exactly the node's named Mathlib predicate, without replacing it
  by a global etaleness assumption or a localization of finite presentation.

Dependency declarations read and used:

- `def-pc-field-extension`: Mathlib leaf `Algebra`,
  `Mathlib.Algebra.Algebra.Defs`, lines 95–102; its field specialization is used
  directly, and `RingHom.toAlgebra` (lines 197–198) supplies the tensor-map action.
- `def-sbc-locally-finite-presentation`: Mathlib leaf
  `AlgebraicGeometry.LocallyOfFinitePresentation`,
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, lines 42–48.
  This node explicitly describes the affine finite-presentation condition used
  here; its ring predicate is the existing `Algebra.FinitePresentation`,
  `Mathlib.RingTheory.FinitePresentation`, lines 42–45. The scheme property itself
  is not needed for this ring-only statement, so there is no unused scheme import.
- `lem-weil-pbc-algebra-tensor-base-change-universal-property`: Mathlib leaf
  `AlgHom.liftEquiv`, `AlgHom.liftEquiv_tmul`, `AlgHom.liftEquiv_symm_apply`,
  `Mathlib.RingTheory.TensorProduct.Basic`, lines 766–791. The statement needs the
  underlying tensor product, not an assertion of its universal property.
  `Mathlib.RingTheory.TensorProduct.Maps` supplies the canonical tensor map;
  `includeLeftRingHom` is read in Basic lines 270–277, and `map` in Maps lines
  539–549. These give the same Mathlib tensor product as the dependency.
- `Algebra.IsEtaleAt` and its docstring read in
  `Mathlib.RingTheory.Etale.Locus`, lines 32–36. The two imports supply the actual
  predicates and maps above; no private dependency copies are introduced.

Sources checked: local Stacks checkout is absent on this machine. Read official
[0C4Y](https://stacks.math.columbia.edu/tag/0C4Y),
[02L2](https://stacks.math.columbia.edu/tag/02L2),
[02KY](https://stacks.math.columbia.edu/tag/02KY), and
[02VM](https://stacks.math.columbia.edu/tag/02VM) online. They give local faithful
flatness for field extension and fpqc locality of flatness, finite presentation,
and etaleness; as the node notes, the packaged primewise implication is not a
single tagged statement. The docstring carries all four steps and their named
DAG proof dependencies.

Edge cases checked: `K = k` gives descent along the identity field extension;
no separability, algebraicity, characteristic, or finiteness condition on `K/k`
is imposed. Distinct universes `u v w z` allow all four rings to have different
sizes. Zero rings `A` and `B` are permitted as algebras, but cannot supply the
required primes (the corresponding cases are vacuous). Neither prime is required
to be maximal, and no nonzero or domain hypothesis is added to `A` or `B`.

Searches actually run with `msearch.py H1 lem-sc-etale-local-ring-faithfully-flat-descent`:

- LeanSearch: `etale at a prime descends under field extension tensor base change`:
  unavailable, Internal Server Error (not treated as a negative search).
- LeanFinder: same query: eight hits, including `Algebra.Etale.baseChange`,
  `RingHom.Etale.isStableUnderBaseChange`, `Algebra.IsEtaleAt.comp`, and
  `Algebra.FormallyEtale.of_restrictScalars`; none states this descent implication.
- Loogle: `Algebra.IsEtaleAt`: six hits, namely the predicate, membership,
  composition, etale neighbourhoods, flat/unramified criterion with global
  flatness, and standard-etale neighbourhoods. None is this statement.
- Mathlib grep: `IsEtaleAt|of_etale_tensorProduct`, directory `RingTheory/Etale`:
  eight hits in Locus and Descent. Read both modules; Descent's theorem assumes
  global `Etale T (T ⊗[R] S)`, which differs from the primewise hypothesis.
- `rg` over upstream `WeilConjectures` and project `lean/Sheaf`:
  `IsEtaleAt|Etale.*[Dd]esc|[Dd]esc.*Etale` finds scheme descent and uses of
  pointwise etaleness, but no field-extension primewise descent theorem.
- Upstream node-id search finds no hit; search of `dag/lean_names_upstream.json`
  for the item also finds no hit. Name-clash search `of_fieldExtension` in
  Mathlib's Etale directory, upstream source, and project Lean finds no hit.

Server compile: `scompile.py H1 lem-sc-etale-local-ring-faithfully-flat-descent`
with the module path succeeded in 1.7 seconds, exit 0, no warnings or errors.

## Second reading by H1

I opened the node and the module and matched the statement in order. The objects and
hypotheses render as follows:

- `k : Type u`, `K : Type v`, `[Field k] [Field K] [Algebra k K]` are the field and
  field extension in the node.
- `A : Type w`, `[CommRing A] [Algebra k A]`, and `B : Type z`, `[CommRing B]
  [Algebra A B] [FinitePresentation A B]` are the commutative `k`-algebra and its
  finitely presented `A`-algebra. The explicit `[Algebra k B] [IsScalarTower k A B]`
  arguments express the induced composite action needed by Lean for `B ⊗[k] K` and
  the tensor map; they impose no additional mathematical condition.
- `(q : Ideal B) [q.IsPrime]` and `(qK : Ideal (B ⊗[k] K)) [qK.IsPrime]` are the
  two primes. The equality `hq` is precisely contraction of `qK` along
  `Algebra.TensorProduct.includeLeftRingHom` to `q`.
- The `letI` introduces exactly the node's algebra structure on
  `B_K = B ⊗[k] K` over `A_K = A ⊗[k] K`, using the tensor map of the tower map
  `A →ₖ B` and `id K`.
- The conclusion is the same implication and quantifier order:
  `IsEtaleAt (A ⊗[k] K) qK → IsEtaleAt A q`.

The node's `p = q ∩ A` and `p_K = qK ∩ A_K` are explanatory contractions and are
not extra hypotheses or conclusions; the Lean statement leaves them implicit exactly
as the node does. No clause is missing or strengthened. Edge cases remain covered:
`K = k`, arbitrary characteristics, distinct universes, and zero rings (where the
prime assumptions make impossible cases vacuous); no separability, algebraicity,
nonzero, domain, or maximality hypothesis is introduced.

I repeated the existing-definition searches (LeanSearch, LeanFinder/Loogle, grep in
Mathlib, `WeilConjectures`, and `lean/Sheaf`). They find only the predicate,
base-change/global descent results, and tensor maps; no declaration states this
primewise field-extension descent. The recorded dependencies are therefore usable and
no new or dependency module is needed. The source tags 0C4Y, 02L2, 02KY, and 02VM
support the four proof steps documented on the declaration. No mismatch was found,
so no code or node statement was changed. The module recompiles cleanly with
`scompile.py` (no errors or warnings).

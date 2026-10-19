## Worker report

The module states the Stacks Tag 0AUM equivalence for two `R`-linear maps with common
source.  The left side is domination: for every `R`-module `L`, the kernel of
`a.lTensor L` is contained in the kernel of `b.lTensor L`.  The right side forms the
categorical pushout in `ModuleCat R` and asserts that its canonical leg from `Q'` is
injective after left tensoring with every `L`.  The theorem proof is `sorry`, as required
for stage 2.

The hypotheses are rendered by `(R : Type u) [CommRing R]`, module types
`P Q Q' : Type u`, their `[AddCommGroup]` and `[Module R -]` instances, and maps
`a : P →ₗ[R] Q`, `b : P →ₗ[R] Q'`.  The domination clause is the quantified kernel
inclusion on line 41 of the module.  The pushout is
`pushout (ModuleCat.ofHom a) (ModuleCat.ofHom b)`; its canonical `Q'` leg is
`(CategoryTheory.Limits.pushout.inr (ModuleCat.ofHom a) (ModuleCat.ofHom b)).hom`,
and the universal-injectivity clause is `Function.Injective (LinearMap.lTensor L ...)`
for every `L : Type v` with its additive-group and module instances.

Dependency declarations imported are Mathlib's `CategoryTheory.Limits.pushout` and
`pushout.inr` (from `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`),
`ModuleCat.ofHom` (from `Mathlib.Algebra.Category.ModuleCat.Abelian`), and
`LinearMap.lTensor` (from `Mathlib.LinearAlgebra.TensorProduct.Map`).  The recorded
statement dependency `lem-trf-universal-injective-finite-test` is imported from
`Sheaf.RingTheory.UniversalInjectiveFiniteTest`; its declaration is
`LinearMap.universally_injective_tensor_iff`.

Edge cases checked: the common source maps may be zero, either map may be an identity,
and `L` may be the zero module; the quantifiers do not exclude these cases.  The maps
need not be injective or surjective, and no flatness or finite-generation hypothesis is
added.  All modules are allowed in the displayed tensor test; the finite-test criterion
remains available through the imported dependency.

Searches for an existing declaration were made with `msearch.py` (`leanfinder` query
“pushout of module maps is universally injective exactly when one map dominates the
other”; no matching theorem), `msearch.py` (`loogle` query
“Module.FaithfullyFlat.lTensor_injective_iff_injective”; only unrelated faithfully-flat
results), `msearch.py` (`grep` query “pushout|universally.injective” in Mathlib; no
matching result), `rg` over `WeilConjectures` and `lean/Sheaf` for
`universally_injective|domination|pushout`; no existing declaration of this theorem).
The relevant Mathlib constructions listed above were checked with `#check` in a scratch
file.  `scompile.py` compiled the module cleanly with no warnings.

## Second reading by N1

I reread the node and module together.  The node's ring, three modules, two linear maps,
all additive-group/module hypotheses, and arbitrary tensor test module are present.  The
left clause exactly renders kernel domination; the right clause uses the canonical
`pushout.inr` leg from `Q'` and injectivity of `L ⊗ b'` via `LinearMap.lTensor`.  No
hypothesis or edge case was added or omitted, and the source pushout is the categorical
pushout in `ModuleCat R` as required.  No mismatch was found.

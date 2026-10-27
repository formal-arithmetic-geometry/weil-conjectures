## Worker report

Module: `Sheaf.AlgebraicGeometry.NativeWeilOpenExactConstructible`.
Declaration: `AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZero_exact_constructible`.
One theorem, with `sorry`; no definitions, new nodes, dependency repairs or statement changes.
The node copy differs only in `lean`. The theorem packages all four assertions of this node,
using the framework's actual functor rather than a replacement construction or a generated
instance-name attachment. The preceding worker's failed instance-name attachment is not reused.

Hypotheses and objects, clause by clause:

- Finite field: `(k₀ : Type u) [Field k₀] [Finite k₀]`.
- Prime distinct from the characteristic: `(l : ℕ) [Fact l.Prime]`
  and `[Fact (ringChar k₀ ≠ l)]`; reversing the inequality's order changes nothing.
- Schemes: `(U T : Scheme.{u})`, with both `Over (Spec (CommRingCat.of k₀))` instances.
  The arbitrary universe `u` is shared with the framework; its small pro-etale site has
  objects in `u+1` and arrows in `u`, and is not replaced by a same-universe site.
- Locally of finite type over the field: the two explicit
  `[LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]` and corresponding `T` binders.
  No quasi-compactness of either structure morphism or separatedness is imposed.
- The morphism: `(j : U ⟶ T)` and `[j.IsOver (Spec (CommRingCat.of k₀))]`.
- Quasi-compact open immersion: `[IsOpenImmersion j] [QuasiCompact j]`.
- Native coefficient and Weil categories are exactly `ProEtaleWeilSheaf k₀ l U` and its
  target analogue. Their carrier category is `ProEtale.AdicSheaf` over the geometric fibre,
  the module objects over `ProEtale.adicConstantSheaf`; this is the locally finite continuous
  coefficient sheaf, not the discrete constant coefficient sheaf.
- The stipulated Frobenius comparison is built into `ProEtaleWeilSheaf.extensionByZero`:
  the existing definition is `IsoAlgebra.mapOfNatIso` of
  `ProEtale.adicOpenImmersionLowerShriekGeometricFiberMapCompFrobeniusIso`.
- Additive: first conjunct `(extensionByZero k₀ l j).Additive`.
- Finite limits: second conjunct `PreservesFiniteLimits (extensionByZero k₀ l j)`.
- Finite colimits: third conjunct `PreservesFiniteColimits (extensionByZero k₀ l j)`.
- Every constructible underlying sheaf: final conjunct quantifies over every
  `F : ProEtaleWeilSheaf k₀ l U`, assumes `WeilSheaf.objectProperty k₀ l U F`, and concludes
  `WeilSheaf.objectProperty k₀ l T ((extensionByZero k₀ l j).obj F)`.
  The existing predicate is the inverse image of `adicConstructibleSheaf` under
  `IsoAlgebra.forget`, so this is constructibility of the underlying sheaf, with no
  extra condition on its Frobenius structure. It uses the local finite locally closed
  stratification definition and allows rank to vary with the trivializing cover member.

Dependency declarations read and used:

- `def-sf-native-weil-derived-framework`: public import
  `WeilConjectures.WeilSheaf.LowerShriek`, the node's recorded entry module, which reexports
  `WeilConjectures.WeilSheaf.OpenImmersion` and `.Category`. In those files the declarations
  used are `AlgebraicGeometry.ProEtaleWeilSheaf`,
  `AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZero`, and
  `AlgebraicGeometry.WeilSheaf.objectProperty`. The recorded main declaration
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek` and its signature/docstring were read;
  this theorem needs the ordinary extension functor also explicitly recorded by that node,
  not that derived functor. Read the coefficient and constructibility source definitions in
  `SixFunctors/ProEtale/Adic/ConstantSheaf.lean` and `Constructible.lean` as well.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-open-immersion`: `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`.

Plain proof imports retain the stated DAG proof interfaces:
`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
(`AlgebraicGeometry.Scheme.ProEt.weaklyEtale_localization`),
`Sheaf.CategoryTheory.RingedSheafSliceAdjunction`
(`CategoryTheory.ringed_sheaf_slice_adjunction`),
`WeilConjectures.AlgebraicGeometry.ConstructibleStratificationAssembly`
(`AlgebraicGeometry.Scheme.exists_stratification_of_stratified_partition`), and the Mathlib
modules for open-immersion and quasi-compact base change, affine qcqs,
`Topology.IsConstructible`, and endofunctor algebras. The four native supporting statement
nodes currently have neither `lean` nor `mathlib_match` records in this read snapshot;
they supply only proof dependencies, not notions needed to type this statement. Their proof
steps remain in the theorem docstring and no unsupported import module is invented.

Sources checked: `WeilConjectures/WeilSheaf/OpenImmersion.lean`, ordinary extension at
44-55, constructibility at 92-105, and the additive/finite-preservation instances at 138-150;
`SixFunctors/ProEtale/Adic/ExtensionByZero.lean` at 200-242. All seven DAG proof steps are
carried in the theorem docstring. The exactness argument passes through the faithful exact
conservative forgetting functor; the constructibility argument uses the affine intersection,
its finite lisse stratification, and the rank-zero closed complement.

Edge cases checked mathematically: empty U, empty T, j the identity or an isomorphism,
zero sheaves, empty complement, and empty finite diagrams. None is excluded by the binders.
The zero complement is lisse of rank zero; empty strata can be omitted. The two finite
preservation classes include the empty diagram. Local finite type does not force global
quasi-compactness, so schemes with infinitely many components remain covered. No arbitrary
coefficient ring, finite-coefficient descent, uniform cover rank, or derived fixed-pair
category is substituted. No statement fault or dispute was found.

Searches performed with `msearch.py NM lem-sf-native-weil-open-exact-constructible`:

- leanfinder: `extension by zero on pro etale Weil sheaves is additive exact and preserves
  constructibility`: 8 hits, for condensed/light-condensed sheaves, none the present theorem.
- loogle: `"PreservesFiniteLimits", "PreservesFiniteColimits"`: 2 object-property inverse-image
  instances, neither the present theorem.
- grep: `extensionByZero|IsAdicConstructible|openImmersionLowerShriek`: no Mathlib hits.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and combined
  extension/exactness/constructibility patterns: no declaration of the whole conjunction.
  Reading the upstream OpenImmersion source finds the existing component assertions and
  canonical functor, which this statement uses without redefining any notion.

Validation: `scompile.py NM lem-sf-native-weil-open-exact-constructible` on the delivered
file passed in both sandbox and library module modes (9.5 seconds each). `autoImplicit false`
ensures every variable is bound. All proof bodies are `sorry`, as required for stage 2.

## Second reading by NM

This is an in-thread second reading; the dispatcher explicitly forbids starting another
agent. The maintainer's independent review is still required. I reread the node, delivered
signature and upstream definitions side by side. The three categorical conjuncts concern
all native Weil sheaves; constructibility is an implication for arbitrary F, not a restriction
of the functor's domain. Checked that the name resolves in `ProEtaleWeilSheaf`, rather than
its constructible subcategory `WeilSheaf`. Checked that objectProperty forgets precisely
Frobenius and retains the native adic coefficient-module structure. Checked both structure
morphism locally-finite-type binders, the IsOver condition, quasi-compactness of j, characteristic
restriction, and the final universal quantifier. No signature mismatch found and no changes
made in this pass. No claim is made that the previous refused generated instance name exists.

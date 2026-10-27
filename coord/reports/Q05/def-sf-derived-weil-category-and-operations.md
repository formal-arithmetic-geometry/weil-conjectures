## Worker report

The delivery states the native derived-Weil operations in
`Sheaf.Paper.DerivedWeilOperations`. All definitions have real data.
The five postponed theorems concern the two tensor functor laws, additivity in two
variables, and the defining natural K-flat tensor model. Each has its owning
node's blueprint marker and a complete proof plan in its docstring. No assertion
of constructible tensor closure, tensor-Hom adjunction, right-adjoint existence,
or dual-preservation is added to the main definition.

Hypotheses and clauses, in node order:

- Finite field: `k₀ : Type u`, `[Field k₀]`, `[Finite k₀]`. Prime invertible in
  the field: `l : ℕ`, `[Fact l.Prime]`, `[Fact (ringChar k₀ ≠ l)]`. Universe `u`
  is explicit, with `autoImplicit false`. The geometric algebraic closure is the
  framework's chosen `AlgebraicClosure k₀`, and coefficients are `PadicAlgCl l`.
- Scheme and structure map: `X : Scheme.{u}` and
  `[X.Over (Spec (CommRingCat.of k₀))]`. The derived tensor and duality sections
  assume `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated` for that
  structure map, exactly separated finite type. These assumptions are not needed
  by the preceding underived constructions. The site universes remain the
  framework's original object/morphism universes, without any imposed equality.
- Coefficient sheaf, abelian category, ambient derived category, bounded
  constructible full subcategory, and Frobenius are the dependency's existing
  `ProEtale.AdicSheaf`, `ProEtaleWeilSheaf`, `DerivedCategory`, `WeilComplex`, and
  `WeilSheaf.frobeniusPullback`. They are imported, never copied. Localization is
  the existing `DerivedCategory.Q`.
- Ordinary tensor is exactly `ProEtaleWeilSheaf.tensor`, with `tensorFunctor`.
  Its definition in `WeilConjectures.WeilSheaf.Dual` uses `Mod.tensorLeft` over
  the coefficient algebra and the diagonal composite of both Weil isomorphisms.
  Native tensor maps are the adjunction mates of internal-Hom precomposition;
  hence their underlying maps are the existing relative module tensor maps.
  `nativeTensorBifunctor` curries the right argument first; its `.flip` orders
  the inputs as (left, right).
- Ordinary internal sheaf Hom is the existing `ProEtaleWeilSheaf.ihom` in
  `WeilConjectures.WeilSheaf.Dual`, built from `ProEtale.AdicSheaf.ihom` with
  `Mod.ihomMapIso A.str.symm` followed by the target Weil isomorphism. Thus the
  action is phi_N h phi_M^{-1}; this is not global Hom.
- `nativeTensorTotal` applies `map₂CochainComplex` to that flipped tensor.
  This is `CochainComplex.mapBifunctor` of the tensor-complex dependency, with
  direct sums on p+q=n and differential d_P tensor 1 + (-1)^p 1 tensor d_T.
  Its objects and maps already lie in the equivariant category, so the action
  is diagonal on every summand and commutes with the differential.
- `NativeIsKFlat` directly states the two `QuasiIso` tests on this actual
  `nativeTensorTotal`: `(nativeTensorTotal.obj P).map s` tests `P tensor s`,
  and `(nativeTensorTotal.flip.obj P).map s` tests `s tensor P`. Both quantify
  over every quasi-isomorphism. This cites the two-sided criterion of
  `def-sfb-preserves-kflat-quasi-iso` without changing its landed monoidal interface.
  `NativeKFlatResolution K`
  has a K-flat complex, an augmentation to K and its `QuasiIso` proof.
- `nativeDerivedClosedComparison` selects the compatible data provided by
  `native_closed_forgetful`; tensor is determined by the specified closed
  adjunction up to its unique compatible isomorphism. This is permitted
  universal-property choice, rather than choice from a mere existence of an
  unspecified object. `nativeDerivedTensor` projects that tensor bifunctor.
  `nativeDerivedTensor_models` records its defining isomorphism to Q of the
  actual total tensor of two K-flat complexes, including naturality for every
  pair of complex maps. It introduces no constructibility conclusion.
- Derived internal Hom is exactly the imported
  `ProEtaleWeilSheaf.derivedHom k₀ l X N`. Its source is the opposite ambient
  derived category. The body is `DerivedCategory.bifunctorRHom`, using
  `kInjectiveRep N` for the target, and `HomotopyCategory.KInjectives.Qh.inv`
  followed by the homotopy-category product-Hom functor for the source.
  Precomposition by its representing homotopy class is the morphism action.
  `NativeKInjectiveResolution K` uses Mathlib `CochainComplex.IsKInjective`,
  whose signature says every map from an acyclic complex is null-homotopic,
  and a quasi-isomorphism K to its representative.
- The product terms and conjugation action are exactly the existing
  `CochainComplex.bifunctorHomObj (ihomBifunctor k₀ l X)`. Its live differential
  is the source-degree convention described in the correction below; the
  coefficient (-1)^(np) identifies it with `CategoryTheory.homComplex` of
  `def-pur-hom-complex`. The module imports that exact recorded dependency;
  it does not replace the named live derivedHom construction.
- The structure compact-support functor is the existing
  `WeilComplex.derivedLowerShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))` from
  `WeilConjectures.WeilSheaf.LowerShriek`; its preservation is the recorded
  `WeilComplex.objectProperty_rightDerivedLowerShriek`.
- Right-adjoint existence remains the binder
  `[WeilComplex.HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))]`.
  Existing `WeilComplex.upperShriek` chooses that right adjoint and existing
  `derivedLowerShriekUpperShriekAdjunction` gives the natural Hom bijections.
  No existence theorem is applied to manufacture this assumption.
- The unit and omega are exactly the imported
  `WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec ...))` and
  `WeilComplex.dualizingComplex`. The latter applies the conditional right
  adjoint to this rank-one degree-zero coefficient Weil sheaf.
- `WeilComplex.ambientVerdierDual` is the ambient `derivedHom` into omega.obj,
  using the existing full-subcategory inclusion. `verdierDualOfPreserves`
  uses `ObjectProperty.lift` and takes precisely the node's preservation
  premise `∀ K : WeilComplex ..., objectProperty ... (D.obj (op K.obj))`.
  Supplying the existing preservation theorem gives the same lift as live
  `WeilComplex.verdierDual`; the definition itself asserts no preservation.

Dependency declarations read and used:

- `WeilConjectures.WeilSheaf.LowerShriek`: `WeilComplex.derivedLowerShriek`,
  `WeilComplex.objectProperty_rightDerivedLowerShriek`; its public category
  framework gives `WeilComplex`, its object property and Frobenius pullback.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the recorded relative sheaf tensor.
  The native module-object implementation uses the same relative tensor notion.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, the localized-site sheaf Hom; the native implementation
  uses the module-object internal Hom, not the Hom set of global morphisms.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  `Mathlib.Algebra.Homology.Bifunctor`: `Functor.map₂CochainComplex`.
- `Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso`:
  `CochainComplex.IsKFlatForTotalTensor`,
  `CategoryTheory.Functor.PreservesTotalTensorKFlatQuasiIso`, and its exact-functor
  theorem. The original owning module is publicly imported unchanged; the native
  test is written directly in the item's module, with no generic interface extension.
- `WeilConjectures.Algebra.Homology.HomComplex`:
  `CategoryTheory.homComplex`, the standard-sign product complex.
- `Sheaf.Paper.NativeWeilClosedForgetful`:
  `NativeClosedComparison`, `NativeClosedComparison.weilClosed`,
  `NativeClosedHomModels.nativeModel`, and `native_closed_forgetful`.
- `WeilConjectures.WeilSheaf.DerivedHom`: `ihomBifunctor`, `derivedHom`;
  `WeilConjectures.CategoryTheory.DerivedCategory.BifunctorHom`:
  `bifunctorRHom`, `kInjectiveRep`, and the K-injective inverse equivalence.
- `WeilConjectures.WeilSheaf.VerdierDual`: `HasUpperShriek`, `upperShriek`,
  `derivedLowerShriekUpperShriekAdjunction`, `dualizingComplex`, `verdierDual`.

Edge cases checked by reading the constructions: zero sheaves and zero complexes
are admitted; complexes are unbounded and sums/products are genuinely countable;
no finite-rank or lisse assumption enters the ambient tensor or Hom. Degree-zero
complexes give the underived tensor/Hom conventions. For scalar Weil lines with
actions a,b, tensor has ab and Hom has b/a. For odd source degree p=1 and Hom
degree n=0, the live Hom differential has the minus sign required by the correction;
the (-1)^(np) conversion yields the standard differential in the next degree.
For X=Spec k₀, the chosen right adjoint to the identity compact-support functor
sends the coefficient unit to an isomorphic unit. The empty scheme is allowed.
For general X no right adjoint or dual-preservation hypothesis is silently inferred.

Searches (2026-10-22):

- msearch.py leanfinder, query “Derived tensor and internal Hom of Frobenius
  equivariant module sheaves and Verdier dualizing complex”: 8 hits, all generic
  light-condensed internal-Hom/monoidal declarations; no native Weil match.
- msearch.py leansearch, query “Derived tensor product and Verdier dual functor
  of Weil sheaves”: 8 hits, including generic left-derived-functor constructors,
  Tor, HomologicalComplex.tensorObj and linear tensor duals; no native match.
- msearch.py loogle, query `"derivedHom"`: 0 hits.
- msearch.py grep, query `dualizingComplex|derivedHom|NativeClosedComparison`:
  0 Mathlib hits. Local rg searched Mathlib, WeilConjectures and Sheaf for
  `nativeClosedComparison|nativeDerivedTensor|nativeTensorBifunctor|nativeTensorTotal|
  nativeVerdierDual`, and then for the new exact declaration names. No collision.
  Other unrelated “native tensor” interfaces belong to internal coefficient
  complexes, not this ProEtaleWeilSheaf category.
- Local rg on WeilSheaf found the exact existing tensor and ihom in Dual.lean,
  tensorFunctor and tensorIhomAdjunction, derivedHom in DerivedHom.lean, and
  dualizingComplex/verdierDual in VerdierDual.lean. These are used directly.
  rg for the item id in WeilConjectures returned no attachment.

No new independent notion or DAG node was needed. There is no unresolved
STATEMENT-DISPUTED flag: the sign mismatch is explicitly corrected.

Validation (2026-10-22): prescribed `scompile.py` compiled the sole delivered
module in sandbox mode (41.4 seconds) and library mode (23.0 seconds), both exit 0
with no errors or unexpected warnings. The repaired packet passed `deliver2.py
--no-push`: `OK (dry run): commit f026934e128 passes the preflight and compiles`.
The staged set contains only the item node, DerivedWeilOperations.lean and this
report; no dependency node or generic K-flat module is changed. The final
self-check found exactly five theorem sorries, no lines over 100 characters,
explicit universes and `autoImplicit false`, the verbatim recorded main signature,
and the complete four-citer correction audit.

## Repair of returned delivery 89f6d5018724

H13 and H1 are repaired together. The sandbox dependency node
`def-sfb-preserves-kflat-quasi-iso` is byte-identical to the current read-only
sheaf-dag copy, including its Q11 `lean` record and all three original declarations.
It contributes no dependency-record delta to this delivery. The extra module
`TotalTensorKFlatBifunctor.lean` is removed. `NativeIsKFlat` now contains the two
`QuasiIso` tests on `nativeTensorTotal` directly in `DerivedWeilOperations.lean`,
citing `def-sfb-preserves-kflat-quasi-iso`. Its two clauses are the same tests as
before unfolding the removed helper, so no mathematical statement changes.
The item's `lean.declarations` lists only its 15 local declarations, including
`NativeIsKFlat`; the generic predicate and equivalence theorem are not delivered.
The item's note and this report no longer claim a dependency interface repair.
The unused resolution structures are retained as the explicit notions requested
by the node; their augmentations have the source's respective directions.

## Statement corrected

Only the Hom representative differential is clarified, following the actual
`CochainComplex.BifunctorHom.d`, `d_π`, and `bifunctorHomObj_d_π` in
`lean/WeilConjectures/Algebra/Homology/BifunctorHomComplex.lean`, used by the
named live derivedHom. The old literal standard formula fails already in source
degree p=1 and Hom degree n=0 with d_I=0 and d_J f nonzero over Ω. The live formula
is (-1)^p (d_J f^p - f^{p+1} d_I). Componentwise multiplication by (-1)^(np)
gives its natural isomorphism with the standard-sign complex: the postcomposition
coefficient becomes (-1)^((n+1)p+p-np)=1; the precomposition coefficient becomes
-(-1)^((n+1)p+p-n(p+1))=-(-1)^n. Thus the specified derived functor, its variance,
and every other clause are unchanged. No statement dependency, proof or proof
dependency changes. The item is not a blueprint unit statement (blueprint.is=null).

All four citing nodes, found by scanning stmt_deps and proof_deps:

- `lem-sf-derived-weil-compact-projection-formula`: holds=true. Only the signed direct-sum tensor and its localization are used; their convention is unchanged.
- `lem-sf-weil-verdier-dual-triangulated`: holds=true. Its proof steps 4--6 already
  compare the signed product-Hom model and the standard model by (-1)^(pn), then
  transport coherent shifts and triangles. The correction states that same
  identification explicitly; the live functor and conclusion remain unchanged.
- `lem-sf-weil-verdier-exchange`: holds=true. Still uses the same live derivedHom and dualizing functors; the representative sign clarification leaves its derived transpositions and conclusion unchanged.
- `lem-sf-derived-weil-tensor-hom-adjunction`: holds=true. Only the derived tensor and its constructible closure are used; no Hom differential occurs.

Old statement, verbatim:

```text
Fix a finite field $k_0$, an algebraic closure $k$ of $k_0$, a prime $\ell\ne\operatorname{char}(k_0)$, and $\Omega=\overline{\mathbf Q}_\ell$. Let $X_0$ be a separated finite-type $k_0$-scheme. Use exactly the coefficient-ring sheaf $B_X$ on $\bar X=X_0\times_{k_0}k$, the abelian Weil-sheaf category $\mathcal W_X$, its ambient derived category $D(\mathcal W_X)$ and its bounded constructible full subcategory $\mathrm{WC}^{\mathrm{der}}(X_0)$ of [def-sf-native-weil-derived-framework]. Write $F_X^*$ for the geometric-Frobenius pullback of that framework and $Q_X$ for localization of cochain complexes in $\mathcal W_X$ at quasi-isomorphisms.

For Weil module sheaves $(M,\phi_M)$ and $(N,\phi_N)$, use the sheaf-module tensor $M\otimes_{B_X}N$ [def-pur-sheaf-tensor-product] and the sheaf-module internal Hom $\mathcal Hom_{B_X}(M,N)$ [def-pur-sheaf-hom], not global Hom. The tensor has the diagonal Weil isomorphism
$$F_X^*(M\otimes_{B_X}N)\cong F_X^*M\otimes_{B_X}F_X^*N\xrightarrow{\phi_M\otimes\phi_N}M\otimes_{B_X}N.$$
The internal Hom has the conjugation Weil isomorphism: after the pullback identification with $\mathcal Hom_{B_X}(F_X^*M,F_X^*N)$, it sends a local map $h$ to $\phi_N\circ h\circ\phi_M^{-1}$.

For complexes $P,T$ in $\mathcal W_X$, total tensor means the direct-sum total complex of [def-pc-tensor-complex-sheaves], with terms $\bigoplus_{p+q=n}P^p\otimes_{B_X}T^q$ and differential $d_P\otimes1+(-1)^p1\otimes d_T$ on the $(p,q)$ summand, equipped with the diagonal Weil action. K-flatness in $\mathcal W_X$ means that total tensor with the complex in either variable preserves quasi-isomorphisms [def-sfb-preserves-kflat-quasi-iso]; a K-flat resolution is a quasi-isomorphism from such a complex. For $B,A\in D(\mathcal W_X)$ define $B\otimes^L_{B_X}A$ by localizing this total tensor on K-flat resolutions of $B$ and $A$. The native derived tensor structure used for this construction is supplied by [lem-sf-weil-native-closed-forgetful].

For $N\in D(\mathcal W_X)$ define $R\mathcal Hom_X(-,N)$ by the actual chosen-representative construction `ProEtaleWeilSheaf.derivedHom k₀ ℓ X₀ N`. Here K-injective in $\mathcal W_X$ means that every morphism of complexes from an acyclic complex to it is homotopic to zero; a K-injective resolution is a quasi-isomorphism into such a complex. Choose the K-injective representative $J_N$ of $N$ and use the inverse equivalence from $D(\mathcal W_X)$ to the homotopy category of K-injective complexes to represent the first variable $B$ by $I_B$. Then
$$R\mathcal Hom_X(B,N)=Q_X\mathcal Hom^\bullet_{B_X}(I_B,J_N),\qquad \mathcal Hom^n_{B_X}(I_B,J_N)=\prod_{p\in\mathbf Z}\mathcal Hom_{B_X}(I_B^p,J_N^{p+n}),$$
with differential $d(f)=d_{J_N}\circ f-(-1)^nf\circ d_{I_B}$ [def-pur-hom-complex] and the conjugation Weil action. On a morphism $u:B\to B'$, apply the chosen inverse equivalence and precompose by its representing homotopy class $I_B\to I_{B'}$. Thus this is a functor $D(\mathcal W_X)^{\mathrm{op}}\to D(\mathcal W_X)$, with the native internal-Hom realization of [lem-sf-weil-native-closed-forgetful]. Tensor--Hom adjunction and constructible tensor closure are separate assertions, not clauses of this definition.

Let $s_0=\operatorname{Spec}k_0$ and $a_{X,0}:X_0\to s_0$ be the structure map. Its actual compact-support functor
$$Ra_{X,0!}:\mathrm{WC}^{\mathrm{der}}(X_0)\longrightarrow\mathrm{WC}^{\mathrm{der}}(s_0)$$
is the restricted construction of [def-sf-native-weil-derived-framework], whose preservation is supplied by [lem-sf-native-weil-shriek-triangulated]. When this restricted functor has a right adjoint, choose a functor $Ra_{X,0}^!:\mathrm{WC}^{\mathrm{der}}(s_0)\to\mathrm{WC}^{\mathrm{der}}(X_0)$ with its adjunction, meaning bijections
$$\operatorname{Hom}(Ra_{X,0!}K,L)\cong\operatorname{Hom}(K,Ra_{X,0}^!L)$$
natural in $K$ and $L$ in these bounded constructible categories. Define $\omega_X=Ra_{X,0}^!\mathbf1_0$. Here $\mathbf1_0$ is the rank-one $B_{s_0}$-module sheaf $B_{s_0}$ with its canonical Weil action, placed in degree zero on $s_0$ (live `WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ ℓ (Spec k₀))`). Define the ambient contravariant functor $D_X(B)=R\mathcal Hom_X(B,\omega_X)$, viewing $\omega_X$ in $D(\mathcal W_X)$ by the full inclusion. When $D_X$ carries bounded constructible objects to bounded constructible objects, restrict it to $\mathrm{WC}^{\mathrm{der}}(X_0)^{\mathrm{op}}\to\mathrm{WC}^{\mathrm{der}}(X_0)$. These are live `WeilComplex.dualizingComplex` and `WeilComplex.verdierDual`. Existence of the structure-map right adjoint and preservation under this internal Hom remain separate assertions.
```

## Second reading by Q05

This is the worker's separate second pass, not a claim of an independent agent
review: the dispatcher explicitly forbids spawning another agent, and the
maintainer independently reviews the delivery. I reopened the node, the repaired main module and the original dependency
module. The first pass found the literal Hom sign discrepancy and recorded it
under §1(C); no mathematical output changed. I checked the flipped bifunctor's
order against Mod.tensorLeft (right argument first), so the total sign is attached
to the actual left degree. I checked that K-flatness tests both variables and that
each resolution augmentation has the correct direction. The main derived tensor
has its natural K-flat representative normalization, rather than an arbitrary map
or a Nonempty tensor object. The native K-flat test is written directly as the two tests on the actual total
bifunctor. The dependency's landed Q11 record and original module are untouched;
there is no delivered generalized bifunctor predicate or equivalence theorem.
The ambient Hom remains the exact live functor, with the source-variable inverse
K-injective equivalence. Both the right-adjoint typeclass and the restriction's
preservation premise are explicit; no tensor closure, biduality, or unconditional
preservation clause was inserted. All variables and the universe are explicitly
bound. No additional mismatch remained after the sign correction.

Repair rebase check: the current base gained
`lem-sf-weil-verdier-dual-triangulated` after the returned packet. I read its
statement and proof, including the explicit sign comparison in steps 4--6, and
added it to the complete four-citer audit above and in `statement_change`.
The item's current `lean_audit` and all other unmodified base fields are retained.
The initial saved-packet dry run reported exactly the missing fourth citer in the
record and report; both diagnostics are repaired.

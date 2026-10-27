## Worker report

Module: `Sheaf.Paper.WeilGeometricHomConstructibility`.
Primary declaration:
`AlgebraicGeometry.ProEtaleWeilSheaf.weil_geometric_hom_constructibility`.
The only postponed proof is this theorem. Its docstring gives all four DAG proof
steps and their cited inputs. `nativeGeometricForget` has actual functor data.
No node statement, statement dependency, or proof dependency is changed.

Sources opened: the current `literature/blueprint/latest/blueprint/`
`sec-six-functors/sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md`,
`sec-six-functors-basics/sk-lem-coefficient-heart/_section.md`,
`sec-six-functors-basics/sk-def-sfb-dc-restricted-functors/lem-sfb-dc-hom-preserves.md`,
and both internal-Hom stability statement/proof files under
`sk-thm-sf-ctf-stability/`. The proof follows the finite-subextension coefficient
Hom theorem, rather than substituting the different admissible continuous-map ring.

Hypothesis and object correspondence:

- A finite field is `(k₀ : Type u) [Field k₀] [Finite k₀]`.
- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`, with
  `[Fact (ringChar k₀ ≠ ℓ)]`. This is exactly the displayed characteristic exclusion.
- `X₀ : Scheme.{u}` and `[X₀.Over (Spec (CommRingCat.of k₀))]` give the base scheme.
  `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` of its structure morphism
  give separatedness and finite type.
- The recorded native framework uses its chosen algebraic closure `AlgebraicClosure k₀`;
  `(X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber` is precisely base change to it.
  No extra field or coefficient hypotheses are imposed. This uses the framework's
  standard choice of algebraic closure, as the node explicitly requests its presentation.
- `ProEtaleWeilSheaf k₀ ℓ X₀` is the actual invertible-Frobenius pair category of
  native module sheaves. Its Frobenius is `WeilSheaf.frobeniusPullback`, induced by
  geometric Galois Frobenius, not absolute or relative power Frobenius.
- `DerivedCategory (ProEtaleWeilSheaf k₀ ℓ X₀)` is D(B_X), not fixed pairs in D(A_X).
- `Profinite.padicAlgClRingObj ℓ` is the finite-subextension-valued condensed ring
  underlying `Profinite.padicAlgClCondensedRing ℓ`.
  `ProEtale.condensedRingObj` pulls it to the geometric fibre, giving R_X.
- `nativeGeometricForget` first applies recorded `nativeForget`. The second functor
  applies `AdicSheaf.forgetAb` and `Mod.comap (nativeModuleCoefficientIso ℓ X).hom`,
  and derives their exact composite termwise. Its output is the existing internal
  R_X-module presentation used by Dbc and RHom. It is exactly the forward functor
  `nativeToOrdinaryModules` of the dependency before the final
  `nativeOrdinaryPresentation.functor`. Thus no arbitrary equivalence or map is chosen.
- `WeilComplex.objectProperty` is the native bounded-constructible predicate defining
  WC, and `WeilComplex` is its full subcategory. The recorded module comparison
  identifies its finite locally free strata with the finite scalar local models.

Conclusion correspondence:

1. The first conjunction quantifies over every ambient `M` and states
   `WeilComplex.objectProperty ... M ↔ constantModelBoundedConstructible ... (U.obj M)`.
   The latter is exactly Dbc with the finite-scalar-local-model meaning.
2. The second conjunction quantifies over every `M` and every `a b : ℤ`. It equates
   `∀ n, n < a ∨ b < n → IsZero (Hⁿ M)` and the identical expression for `U.obj M`.
   Thus it preserves and reflects the very same interval, without changing endpoints.
3. The final conjunction quantifies over arbitrary `K L : WeilComplex ...`.
   `finiteTorAmplitude _ (U.obj K.obj)` and the analogous expression for L give
   finite Tor amplitude of each input. Their Dbc membership follows from the first
   conjunction and each full-subcategory object's membership proof; together these
   say both inputs lie in the recorded Dctf subcategory.
4. The last expression applies
   `(constantModelBoundedConstructible ... ⊓ DerivedCategory.finiteTorAmplitude _)`
   to `((CondensedRing.derivedHom ...).obj (op (U.obj K.obj))).obj (U.obj L.obj)`.
   This is exactly Dctf membership of the ambient relative sheaf internal Hom,
   including boundedness and constructible cohomology. The Dbc inclusion is its first
   conjunct by definition. There is no lisse/perfect premise and no global Hom or
   Frobenius-invariant Hom conclusion.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `WeilConjectures.FiniteFieldDatum.geometricFrobenius`, read to check the geometric
  convention; native `WeilSheaf.frobeniusPullback` supplies that convention on its fibre.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`:
  `Profinite.padicAlgClCondensedRing`, `padicAlgClRingObj`, the section presheaf,
  and the finite-subextension subfunctor.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing` and `condensedRingObj`, the existing pullback from the point.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  exactly `SheafOfModules`, used through the dependency's ordinary presentation.
- `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`:
  `CategoryTheory.Endofunctor.IsoAlgebra` and its canonical forgetful functor.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory` and `DerivedCategory.Q`.
- `Sheaf.Paper.NativeWeilClosedForgetful`: `nativeForget`, `native_closed_forgetful`.
- `WeilConjectures.WeilSheaf.LowerShriek` (public native framework entry), with
  `WeilConjectures.WeilSheaf.Category`: `WeilComplex`, `WeilComplex.objectProperty`,
  `ProEtaleWeilSheaf`, `WeilSheaf.frobeniusPullback` and the native constructibility
  definitions it imports.
- `Sheaf.Paper.NativeModuleConstructibilityComparison`:
  `nativeModuleCoefficientIso`, its ring-morphism instance,
  `nativeToOrdinaryModules`, `nativeOrdinaryPresentation`,
  `NativeOrdinaryModules` and `nativeModuleConstructibilityComparison`.
- `Sheaf.Paper.CondensedConstantConstructibility`:
  `constantModelBoundedConstructible`, `ConstantModelConstructibleFiniteTor`,
  `IsConstantModelConstructible` and their finite constant local-model definitions.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`:
  `AlgebraicGeometry.ProEtale.CondensedRing.derivedHom` is the actual ambient RHom.
- Existing exactness APIs: `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`
  for `Mod.comap` finite-limit/colimit preservation,
  `WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian` for additive `mapMod`,
  and `WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleComparison`
  for exact coefficient-sheaf forgetting. These supply instances without new lemmas.

Proof-plan imports include `CoefficientHeart`,
`AdicConstructibilityPredicateComparison`, `CoefficientBoundedConstructibleProEtale`,
Mathlib Noetherian schemes, and upstream `ModuleObject.Derived.BoundedConstructible`.
The recorded proof-only `Sheaf.Paper.BoundedConstructibleHomFiniteness` is deleted
according to its node's note; `scompile.py --source` confirms it is unavailable.
Its note points to the existing upstream `isMonoidalClosed_boundedConstructible`,
which supplies the algebraic-closure case and is exposed by the last proof import.
No unavailable module is imported, and no second finiteness theorem is stated.

Edge cases read before writing: empty scheme/empty stratification; zero and acyclic
complexes; rank-zero local models; degree zero and arbitrary negative degrees;
all intervals including a=b (and a>b, for which both support predicates mean
acyclicity); arbitrary constructible, non-lisse inputs. None is excluded by the
signature. The scheme universe is arbitrary u, with site and coefficient universes
inherited unchanged from the native and condensed frameworks.

Searches for an existing declaration:

- `msearch.py ... leanfinder`, query "For native Weil complexes forgetting Frobenius
  detects bounded constructible cohomology and geometric relative derived internal
  Hom has finite Tor amplitude": eight results, including DerivedCategory.IsGE,
  isGE_Q_obj_iff, isLE_Q_obj_iff, exists_iso_Q_obj_of_isGE_of_isLE and generic condensed
  Grothendieck category facts. No matching geometric Weil statement.
- `msearch.py ... leansearch`, query "Geometric internal derived Hom of bounded
  constructible Weil complexes remains bounded constructible": eight generic
  derived-category/localization/homological-complex results. No match.
- `msearch.py ... loogle`, query `"DerivedCategory", "constructible"`: zero hits.
- `msearch.py ... grep`, query `WeilComplex|constructible.*[Hh]om|[Hh]om.*constructible`:
  ten hits about constructible subsets and finite-presentation scheme morphisms;
  none concern these cohomological or internal-Hom assertions.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for the item id and proposed declaration names: no matches. Concept search for
  native Weil constructibility and geometric Hom found the recorded category,
  `NativeWeilClosedForgetful`, `NativeModuleConstructibilityComparison`, and
  native tensor preservation. They give the ingredients, not this three-part theorem.

Compilation: the complete theorem and canonical functor passed scompile.py in both
sandbox-module and destination-module modes, each around four seconds. Final dry-run
and delivery are performed with deliver2.py. No local/global library build is used.

## Second reading by NG

The dispatcher expressly prohibits starting other agents; this is a second pass by
this worker, and the maintainer's independent reading remains the delivery review.
I reopened the item and the complete Lean signature after compilation. The first
conjunction ranges over D(B_X), not merely WC, and is an equivalence. The second
ranges over that same ambient category with the same two integer endpoints on both
sides. The third quantifies over two arbitrary full-subcategory objects, uses the
underlying ambient objects, supplies both input Tor assertions, and places the
actual condensed-ring relative derived Hom in the intersection defining Dctf.
The public helper is the normalized termwise forgetful construction, not a free
parameter. Reading the definitions showed that the finite-Tor statements for inputs
need their Dbc membership from the first conjunct; that membership is present, so
there is no missing hypothesis or conclusion. No statement mismatch was found.
The compiler initially lacked the additive mapMod instance; importing its existing
owning module fixed this without introducing an auxiliary postponed theorem.

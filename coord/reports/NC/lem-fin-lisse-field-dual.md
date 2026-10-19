## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLisseFieldDual` states
`AlgebraicGeometry.Etale.finiteLisseFieldDual`, with its sole proof `sorry`.
Its helper `finiteLisseDualPullbackComparison` is a real construction: transpose
inverse tensor comparison, pullback of evaluation, and the coefficient-unit
comparison through the existing derived tensor-Hom adjunction. There is no
arbitrary comparison map, extra dualizability hypothesis, or chosen isomorphism.

Hypotheses, clause by clause:
- The prime ell is `(ℓ : ℕ) [Fact ℓ.Prime]`; the coefficient field is
  `ULift.{u+1} (ZMod ℓ)`. The lift changes only size, not the field.
- The scheme is `(T : Scheme.{u})`. The hypothesis
  `IsUnit (ℓ : Γ(T, ⊤))` says ell is invertible on T. A global section is a unit
  exactly when all its germs are units, so this includes the empty scheme.
- C is in the ordinary `Etale.DerivedCategoryModule` of module-valued etale
  sheaves, not an adic, completed, or pro-etale category.
- Boundedness is the explicit existence of integers a ≤ b and `IsZero` for
  cohomology outside [a,b]. No representative is required to be strictly bounded.
- Every integer-degree cohomology sheaf satisfies the recorded
  `Scheme.IsFiniteLocallyConstantSheaf`. This is local constancy plus finitely
  generated module stalks; over the finite prime field these are precisely
  finite stalks, including the zero stalk.

Conclusions, clause by clause:
- The first conjunct asserts the same finite local constancy for every H^q
  of `derivedHom C (constantComplex ...)`, the coefficient dual.
- The second conjunct is the isomorphism H^q(C-dual) ≅ sheaf-Hom(H^(-q)(C),
  the coefficient unit). `Nonempty` asserts an isomorphism rather than literal
  equality of chosen models of cohomology. The underived Hom is `ihom` in
  the tensor-monoidal category of module-valued etale sheaves, not global Hom.
- The third conjunct quantifies over every scheme T' and every v : T' → T
  and asserts `IsIso` of the constructed canonical comparison. Derived upper
  star represents exact inverse image on these constant-coefficient module
  sheaves; no flatness condition on v is imposed.

Existing dependency declarations and compatible interfaces:
- `Sheaf.AlgebraicGeometry.DerivedCategories`: `Etale.DerivedCategoryModule`,
  with `DerivedCategory.homologyFunctor` for H^q.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`: the recorded
  cohomology/boundedness conventions; the stronger constructibility predicate
  is not assumed.
- `Sheaf.Algebra.Homology.DerivedInternalHom`:
  `CategoryTheory.derivedInternalHom`, the ringed-small-site K-injective model.
  Its specialization cannot be applied literally to the ModuleCat-valued
  encoding. The existing upstream `Etale.derivedHom` supplies that same
  mathematical derived internal Hom in the encoding of the recorded derived
  category; it is not a newly invented operation. Read its complete definition
  and the construction in `CategoryTheory.DerivedCategory.Monoidal.Closed`:
  `DerivedCategory.tensorHomAdjunctionQhObj` derives homotopy internal Hom
  using K-injectives, and the closed structure transports this adjunction to
  arbitrary derived objects. Thus it computes the K-injective internal Hom,
  although a named comparison with the ringed-site encoding is not supplied
  in this delivery. Both models are retained as existing declarations.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`:
  `SheafOfModules.homObj`, the ringed-site sheaf Hom. Its ModuleCat-valued
  counterpart is the existing monoidal `ihom`, furnished by
  `Etale.sheafMonoidalClosed`; it is a sheaf of linear maps, not global Ext.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, the recorded inverse-image functor.
- `WeilConjectures.SixFunctors.Etale.Derived.Hom`:
  `Etale.derivedHom` and `Etale.derivedTensorHomAdjunction`.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`:
  `Etale.leftDerivedUpperStarTensorIso`, `Etale.leftDerivedUpperStarUnitIso`.
- `def-weil-size-convention`: explicit universe u; schemes in u, coefficient
  modules in u+1 and derived objects in u+2. Site object and morphism universes
  have not been identified.

The node's six-step proof plan appears in the theorem docstring. All recorded
proof-dependency modules are imported; the bounded-free RHom and ringed exact
restriction nodes have no recorded declarations and so have no module to import.
No proof of either prerequisite is claimed here.

Edge cases checked mathematically: the zero complex, rank-zero local modules,
the empty scheme, negative and zero cohomological degrees, intervals a=b,
v the identity, and arbitrary nonflat v. Ell is prime (including ell=2), and
its invertibility on T pulls back to T'. No connectedness, nonemptiness,
Noetherian, global rank, or morphism-flatness hypothesis was introduced.
No mathematical statement correction or STATEMENT-DISPUTED claim is proposed.

## Second reading by NC

I read the node statement, its blueprint source, and every recorded statement dependency before checking the module line by line.

The node introduces a prime natural number ℓ and coefficient field F_ℓ, a scheme T on which ℓ is invertible, an ordinary bounded derived complex C of etale λ-sheaves, bounded cohomological degrees, and finite locally constant cohomology sheaves. Lean renders these as `(ℓ : ℕ) [Fact ℓ.Prime]`, the coefficient `ULift.{u + 1} (ZMod ℓ)`, `(T : Scheme.{u})`, `_hℓ : IsUnit (ℓ : Γ(T, ⊤))`, `C : DerivedCategoryModule (ULift.{u + 1} (ZMod ℓ)) T`, `_hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ i, (i < a ∨ b < i) → IsZero (H^i C)`, and `_hlisse : ∀ i, Scheme.IsFiniteLocallyConstantSheaf (H^i C)`. The explicit universe and `ULift` implement the size convention without identifying site object and morphism universes.

The first conclusion is exactly finite local constancy of every cohomology sheaf of `derivedHom C (constantComplex ...)`. The second is exactly `∀ q, Nonempty (H^q (derivedHom C (constantComplex ...)) ≅ ihom (H^(-q) C) (𝟙_ ...))`; `ihom` is the monoidal sheaf internal Hom, not global Ext. The third is exactly `∀ (T' : Scheme.{u}) (v : T' ⟶ T), IsIso (finiteLisseDualPullbackComparison v C)`. The helper is the canonical adjunction transpose of pulled-back evaluation, using the recorded tensor and unit comparison isomorphisms, with orientation `v^* C^∨ ⟶ (v^* C)^∨`.

Dependency checks found the recorded etale derived category and homology functor, the source declaration `IsFiniteLocallyConstantSheaf`, the monoidal closed `derivedHom`, the module-sheaf `ihom`, `upperStar`, and the canonical pullback comparison interfaces. No private duplicate notion or arbitrary comparison map occurs.

Edge cases checked: the empty scheme, zero complex and zero stalks, rank zero, `a = b`, degree zero, negative degrees and degree reversal, `ℓ = 2`, identity and arbitrary (including non-flat) `v`, and absence of connectedness, Noetherian, global-rank, or flatness assumptions. All are covered by the binders.

Searches were repeated with `msearch.py` LeanFinder, Loogle, and grep, and with `rg` over Mathlib, the source `WeilConjectures`, and project `lean/Sheaf`, for `finiteLisseFieldDual`, derived internal dual/cohomology formulas, and pullback-dual comparisons. No existing statement or declaration was found. The existing dualizable-pullback theorem was inspected and is insufficient because it assumes dualizability and gives only a nonempty isomorphism.

No mismatch was found, so no Lean, node statement, dependency, or source correction was required. The module compiles cleanly with the mandated server compiler.

Searches for existing statements:
- `msearch.py leanfinder`, “Derived internal dual of a bounded complex of finite
  locally constant etale sheaves over a finite field commutes with pullback”:
  eight underived/condensed results; no statement of this lemma.
- `msearch.py loogle`, `DerivedCategory.homologyFunctor, SheafOfModules`:
  zero hits.
- `msearch.py grep`, `derivedInternalHom|finite.*locally.*constant.*dual`:
  zero Mathlib hits.
- `rg` in upstream WeilConjectures for this item id: zero hits.
- `rg` in upstream and project Sheaf for `derivedInternalHom`, `internalHom`,
  `coefficientDual`, and etale Hom: found the recorded ringed-site construction
  and existing upstream etale Hom/dual APIs, inspected in full. The existing
  perfect-pullback theorem assumes dualizability and gives only a nonempty
  isomorphism; it does not state this lemma's cohomology formula or the
  isomorphism of the specified canonical map.
- `rg` in Mathlib, upstream names index, upstream sources and project Sheaf
  for `finiteLisseFieldDual` and `finiteLisseDualPullbackComparison`: no clashes.

Validation uses only server `scompile.py`, nice 19, two threads, 60 seconds
per file. The initial direct use of a monoidal comparison timed out; the
explicit tensor-Hom adjunction construction compiled in 6.2 seconds. Full
module compilation and the required dry run are the final checks.

## Worker report

The module `Sheaf.RingTheory.AnnihilatorQuotientsGenericFree` states
`Algebra.annihilator_quotients_generic_free`, with one postponed proof and no new
definitions or auxiliary theorems. The node changes only in `lean`.

Clause-by-clause correspondence:

- The commutative integral domain is `(A : Type u) [CommRing A] [IsDomain A]`.
  The finite type commutative algebra is `(B : Type v) [CommRing B] [Algebra A B]
  [Algebra.FiniteType A B]`. The two carrier universes are independent.
- `Localization.AtPrime (⊥ : Ideal A)` is the zero-prime localization K.
  `hb : TensorProduct.tmul A (1 : K) b ≠ 0` is the generically nonzero element.
  The recorded base-change convention places K first: the tensor symmetry
  carries this to the node's `b ⊗ 1`.
- `I` and `J` are named ideal parameters with defining equations `hI` and `hJ`:
  `I = (Ideal.span ({b} : Set B)).annihilator` and
  `J = Ideal.span ({b} : Set B)`. These equations merely name the node's
  explicitly defined ideals; they impose no restriction on A, B, or b.
  By `Submodule.mem_annihilator_span_singleton`, the former means exactly
  `x*b = 0`, equivalently `b*x = 0` by commutativity. The latter is bB.
  The two actual quotients are `B ⧸ I` and `B ⧸ J` throughout.
- The first two conjuncts assert `Algebra.FiniteType A` for both quotients.
- The existential `i : (B ⧸ I) →ₗ[A] B` is specified by
  `∀ x, i (Ideal.Quotient.mk I x) = b*x`, which uniquely determines the map
  because the quotient map is surjective. `Function.Injective i`,
  `Function.Exact i (Ideal.Quotient.mkₐ A J).toLinearMap`, and
  `Function.Surjective (Ideal.Quotient.mkₐ A J)` give exactly the first short
  exact sequence and its stated quotient arrow.
- `∀ a : A, a ≠ 0 → Nontrivial (Localization
  (Algebra.algebraMapSubmonoid (B ⧸ I) (Submonoid.powers a)))` is precisely
  the nonvanishing of C_a for every nonzero a.
- `∃ g : A, g ≠ 0 ∧ ...` supplies the common denominator. Each localized
  algebra E_g is the actual Mathlib ring `Localization
  (Algebra.algebraMapSubmonoid E (Submonoid.powers g))`. This is localization
  at the image in E of the powers of g, with the native Mathlib algebra over
  `Localization.Away g`; no arbitrary localization structures are assumed.
  It is also the localization of the underlying A-module. The native algebra
  is `IsLocalization.localizationAlgebra`, and its scalar tower is the global
  Mathlib instance in `Mathlib.RingTheory.Localization.Basic`.
- The two `Module.Free (Localization.Away g)` conjuncts assert precisely
  freeness of C_g and D_g. There is no finite generation or cardinality bound
  on the bases. `Nontrivial C_g` asserts C_g ≠ 0.
- `ig : C_g →ₗ[A_g] B_g` is the localized injection, characterized on every
  element of C by `ig (algebraMap C C_g x) = algebraMap B B_g (i x)`.
  A_g-linearity extends this to all fractions and determines the map uniquely.
  `qg : B_g →ₐ[A_g] D_g` is characterized on B by the quotient formula.
  `Function.Injective ig`, `Function.Exact ig qg`, and
  `Function.Surjective qg` give exactly the localized short exact sequence.
- `c : B_g / Ann(b/1) ≃ₐ[A_g] C_g` and
  `d : B_g / (b/1) ≃ₐ[A_g] D_g` are the two canonical identifications
  (written in the inverse direction to the node's isomorphism notation).
  The equation for c on every x in B identifies it with localization of the
  original quotient map; these elements generate the localized quotient as
  an A_g-module. The equation `d (Ideal.Quotient.mk _ x) = qg x` for every
  x in B_g identifies the second with the actual quotient arrow. Thus neither
  is an arbitrary isomorphism. The last clause, for every x in B_g, is
  `ig (c (Ideal.Quotient.mk _ x)) = (algebraMap B B_g b)*x`, exactly the
  specified multiplication formula under the first identification.
- There is no Noetherian, finite-presentation, nilpotence, finite-module,
  nontrivial-B, or finite-basis hypothesis. Nontriviality of B follows from hb.

Dependency declarations read and used:

- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`.
- `Mathlib.RingTheory.FiniteType`: `RingHom.FiniteType`,
  `Algebra.FiniteType`, and `RingHom.finiteType_algebraMap`. The recorded
  ring-map definition is exactly the explicit-algebra finite-type class here.
- `Mathlib.LinearAlgebra.TensorProduct.Tower`: `TensorProduct`,
  `LinearMap.baseChange` (the base-change convention, with K first).
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free` and its unrestricted
  basis index type, with `Module.free_iff_set`.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`;
  `Mathlib.RingTheory.Localization.Basic` supplies its ring and algebra
  structures and `IsLocalization.localizationAlgebra` for algebra localizations.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule.Away`,
  `LocalizedModule.mkLinearMap`. Ring localizations realize this same underlying
  localized-module notion; no additional or private localization is defined.
- Proof imports: `Sheaf.RingTheory.ReducedPolynomialModuleGenericFreeness`,
  `MvPolynomial.isOpen_dense_polynomialModuleGoodLocus`;
  `Mathlib.Algebra.MvPolynomial.Basic`, `MvPolynomial`;
  `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`;
  `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`.
  All already stated proof dependencies are imported.

Source read: `literature/stacks-project/more-morphisms.tex`,
`lemma-nonreduced-in-neighbourhood` (Tag 0575), especially the annihilator,
quotient, shrinking and exact-sequence paragraph. Both quotients being free,
without nilpotence, is the node's accepted algebraic strengthening using its
recorded Tag 051Z polynomial-module proof dependency. That dependency's full
Lean signature and proof docstring were read. No statement correction is needed.

Edge cases checked before writing: if b is a unit, I=0, J=top and D=0, so the
empty basis for D remains allowed; A[t] with b=t has infinite-rank C and is
not excluded; A[t]/(t²) with b=t tests a nonzero nilpotent and nontrivial
annihilator. A=Z, B=Z[t]/(2t), b=t has zero generic image and is excluded by
hb, as it must be. A field is allowed with g=1; B=0 and b=0 are excluded
solely by hb. There is no assumption that either ideal is finitely generated.

Searches made through the prescribed msearch.py wrapper:

- leanfinder: "Annihilator and principal quotients of a finite type algebra over
  a domain become simultaneously free on a principal open with exact
  multiplication sequence": 8 hits, including PID freeness, Smith normal
  form, and `Module.FinitePresentation.exists_free_localizedModule_powers`.
  None states this result; PID or module finite-presentation hypotheses
  would exclude cases covered here.
- loogle: `Module.Free, Algebra.FiniteType, IsDomain`: 0 hits.
- grep: `annihilator|generic.*free` in `RingTheory/Localization`: one hit on
  the kernel of algebraMap, not this theorem.
- leansearch: "Annihilator and principal quotients of a finite type algebra
  over a domain become simultaneously free after one nonzero localization":
  8 hits, including freeLocus, localized-quotient instances, annihilator
  quotient and finite localization results; no full matching theorem.
- rg over both `lean/WeilConjectures` and `lean/Sheaf` for
  `annihilator.*[Qq]uotient|annihilatorQuotient|annihilator_quotients|` followed
  by the item id: only unrelated annihilator arguments and quotient modules.
  The item id has no upstream declaration. An exact-name search of both roots
  and `dag/lean_names_upstream.json` found no existing
  `annihilator_quotients_generic_free`.

Validation: scompile.py compiled the delivered file both as sandbox module
and library module cleanly (1.6 and 1.7 seconds respectively). No errors or
warnings. No diagnostic commands are left in the module.

## Second reading by Q44

I reopened the node and the completed module and checked each binder and
conjunct against the correspondence above. This is an in-session self-check;
no independent worker was started, as required by the dispatcher's brief.
The maintainer supplies the independent review. I specifically checked that
hI and hJ fix the ideals rather than assume arbitrary quotients; the tensor
order matches the recorded base-change convention; both localized modules
are free without finite-basis constraints; the two exact sequences include
injectivity and surjectivity; and both quotient equivalences are tied to the
quotient arrows. The final identity quantifies over all of B_g, not merely
its unlocalized generators. No mismatch or change was found in this reading.

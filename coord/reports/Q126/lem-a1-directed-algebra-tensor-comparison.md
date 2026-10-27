## Worker report

The module `Sheaf.RingTheory.DirectedAlgebraTensorComparison` states
`Algebra.TensorProduct.directedAlgebraTensorComparison`, with its sole proof `sorry`.
No definition is introduced, and the accepted DAG statement and split are unchanged.
The module docstring cites Tag 0APJ and the theorem docstring carries all six proof steps.
I read the current dependency nodes and the relevant Mathlib signatures/docstrings,
and the source proof of `lemma-affine-base-change` in `more-groupoids.tex`.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Commutative rings and the ring map R → T | `(R T : Type u) [CommRing R] [CommRing T] [Algebra R T]`; for commutative rings the algebra structure is exactly the ring map. |
| Small nonempty directed preorder | `(J : Type u) [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]`; the standard preorder category has arrows `homOfLE h`. All objects are in a common universe, as required by the project's filtered-colimit convention. |
| Directed R-algebra diagram A and its compatible cocone into C | `A : J ⥤ CommAlgCat R`, `C : Cocone A`; the vertex is `C.pt` and rho_i is `(C.ι.app i).hom`. Functor and cocone laws include identities, composition and compatibility. |
| Directed T-algebra diagram B, regarded over R | `B : J ⥤ CommAlgCat R`, `[∀ i, Algebra T (B.obj i)]`, `[∀ i, IsScalarTower R T (B.obj i)]`, and `b_T`. The tower identifies its R-structure with restriction along R → T; `b_T` says its ring maps commute with T. These encode precisely a diagram of T-algebras, without choosing another scalar structure or another copy of B. |
| T-algebra D and compatible T-algebra cocone sigma_i | `D : Cocone B`, `[Algebra T D.pt] [IsScalarTower R T D.pt]`, and `sigma_T`; its R-cocone laws are already in D and `sigma_T` supplies exactly T-compatibility. |
| Every c is represented and same-stage equal elements eventually agree | `hC_surj` and `hC_eq`; the latter supplies an actual `j` and `h : i ≤ j` and equality under `A.map (homOfLE h)`. |
| The corresponding two hypotheses for D | `hD_surj` and `hD_eq`, using D's legs and B's transition maps. |
| R-algebra maps p and p_i | `p : C.pt →ₐ[R] D.pt` and `p_stage : ∀ i, A.obj i →ₐ[R] B.obj i`. |
| p rho_i = sigma_i p_i | `hp`, equality of algebra homomorphisms using `AlgHom.comp`. |
| b_ij p_i = p_j a_ij | `hp_stage`, for every preorder-category arrow. |
| Canonical stage tensor comparisons are isomorphisms | `hphi`: bijectivity of `Algebra.TensorProduct.productMap (p_stage i) (IsScalarTower.toAlgHom R T (B.obj i))`. `productMap_apply_tmul` gives precisely `p_stage i x * algebraMap T (B.obj i) t`. It is automatically a T-algebra map for right-factor scalars, so bijectivity is equivalent to the stated T-algebra-isomorphism assumption; no arbitrary stage comparison is supplied. |
| C is the module colimit | First `Nonempty (IsColimit (...mapCocone C))`; the forgetful composite is CommAlgCat R → AlgCat R → ModuleCat R. `IsColimit` is data, so its propositional existence is wrapped in Nonempty. |
| D is the underlying R-module colimit | Second `Nonempty (IsColimit (...mapCocone D))`, with the very same forgetful composite. |
| C tensor T is the module colimit with legs rho_i tensor 1 | Third `Nonempty (IsColimit (...mapCocone C))`, now composing with `tensorRight (ModuleCat.of R T)`. The tensor functor's objects are tensor products and its maps and legs are `LinearMap.rTensor T`, so this states the specified cocone, not just existence of some isomorphic vertex. |
| Existence of R-linear comparison isomorphism | `∃ Φ : C.pt ⊗[R] T ≃ₗ[R] D.pt`. |
| Comparison compatibility on every stage | First conjunct under Φ, equality `Φ.toLinearMap.comp (rho_i.toLinearMap.rTensor T) = sigma_i.toLinearMap.comp phi_i.toLinearMap`. |
| Uniqueness among R-linear isomorphisms with those compatibilities | Second conjunct under Φ, quantifying every `Ψ : C.pt ⊗[R] T ≃ₗ[R] D.pt` satisfying the same equations and asserting `Ψ = Φ`. |
| This same Φ is a T-algebra isomorphism | `∃ e : @AlgEquiv T (C.pt ⊗[R] T) D.pt ... (rightAlgebra ...) ...` together with `∀ z, e z = Φ z`. The algebra structure is explicitly Mathlib's `Algebra.TensorProduct.rightAlgebra`; no local instance can escape into the signature. |
| Canonical pure-tensor characterization | `∀ (c : C.pt) (t : T), e (c ⊗ₜ[R] t) = p c * algebraMap T D.pt t`. Since e agrees pointwise with Φ, this characterizes the same comparison. |

Dependencies used:

- `def-weil-pbc-algebra-hom-quotient`: Mathlib's `AlgHom` and `Algebra`, in
  `Mathlib.Algebra.Algebra.Hom` / `Basic`, publicly available through
  `Mathlib.Algebra.Category.CommAlgCat.Basic`. The ideal clauses of this dependency
  are not needed here; no replacement algebra notion is defined.
- `lem-weil-pbc-algebra-tensor-pushout-universal-property`:
  `Algebra.TensorProduct.instCommRing`, `includeLeft`, `includeRight` and `ext`
  from `Mathlib.RingTheory.TensorProduct.Basic`, plus `productMap` and
  `productMap_apply_tmul` from `Mathlib.RingTheory.TensorProduct.Maps`.
  These supply the actual tensor ring and the canonical stage comparison.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone`, `IsColimit`,
  `colimit`, `colimit.desc`, and `CategoryTheory.IsFiltered`; the statement uses
  the first two, imported through `Mathlib.CategoryTheory.Limits.HasLimits`.
  Specified cocones are retained instead of replacing them by chosen colimits.
- `def-weil-module-base-change`: the recorded `TensorProduct` and
  `LinearMap.baseChange` from `Mathlib.LinearAlgebra.TensorProduct.Tower`.
  Following its record's explicit tensor-order equivalence, use
  `LinearMap.rTensor` on M tensor T; this is the conjugate of
  `LinearMap.baseChange T` on T tensor M by `TensorProduct.comm`.
  `ModuleCat.Monoidal.Basic` defines exactly this map as tensorRight's map.
- Proof-only imports implement the recorded Mathlib matches for
  `lem-weil-pbc-filtered-colimit-modules-criterion`:
  `Types.FilteredColimit.isColimitOf'`,
  `ModuleCat.FilteredColimits.forget_reflectsFilteredColimits`, and
  `isColimitOfReflects`, and for `lem-weil-pbc-tensor-commutes-with-colimits`:
  the ModuleCat closed structure, the left-adjoint tensorRight instance,
  adjoint preservation of colimits and `isColimitOfPreserves`.
  They remain plain imports for the later proof, as the stage rules require.

Edge cases checked before writing:

- An empty J is excluded by the node and `[Nonempty J]`, not silently included.
  A one-object J reduces exhaustion/equality to bijectivity of the cocone legs.
- A directed preorder need not be antisymmetric. `[Preorder J]` preserves this case;
  parallel arrows are propositionally unique and no transition is assumed injective.
- Zero rings, zero target T, and zero algebras remain allowed: there is no
  `Nontrivial`, domain, flatness or faithful-flatness assumption.
- T = R specializes to an ordinary comparison of the two directed presentations.
- The right-factor T-action is explicit even if C = T, where the usual globally
  inferred tensor algebra structure would act on the left and need not be the
  specified one. `@AlgEquiv` with `rightAlgebra` resolves this ambiguity directly.
- All small diagrams and carriers use Type u, avoiding any smaller indexing or
  coefficient universe and matching the project's universe convention.

Searches for an existing full statement:

- `msearch.py ... leanfinder "An elementwise directed algebra colimit commutes with tensor product and stagewise tensor algebra isomorphisms induce a canonical algebra isomorphism"`:
  8 hits, including `TensorProduct.directLimitLeft` and unrelated free-product,
  tensor-algebra and presentation results. `directLimitLeft` concerns a constructed
  module direct limit, not both supplied algebra cocones and the T-algebra comparison.
- `msearch.py ... loogle "TensorProduct, CategoryTheory.Limits.IsColimit"`:
  0 hits.
- `msearch.py ... grep "directLimitLeft|isColimit.*[Aa]lgebra|[Aa]lgebra.*[Ii]sColimit" Algebra`:
  3 hits in `Algebra/Colimit/TensorProduct.lean` and `AlgCat/FilteredColimits.lean`;
  none asserts the complete supplied-cocone comparison.
- `msearch.py ... leansearch "Two directed algebra cocones given by representatives and eventual equality, with compatible stagewise base change isomorphisms, give a canonical tensor algebra isomorphism"`:
  8 hits, including `MonoidAlgebra.tensorEquiv`, `IsLocalization.algebraTensorEquiv`,
  tensor cancellation, `distribBaseChange` and algebra tensor congruences; no full match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for directed/tensor/comparison
  patterns found `DirectedSubalgebraTensorColimit`, `DirectedTensorCoconesColimit`
  and tensor-model comparison modules. They address changing base rings or specified
  subalgebras and do not state this comparison. Searching the exact node id in
  `lean/WeilConjectures` found no declaration. The proposed declaration name was
  also searched in Mathlib, both project trees and `dag/lean_names_upstream.json`:
  no collision.

No statement dispute, correction, new node or dependency repair is required.
The final statement has `set_option autoImplicit false` and one explicit universe.
Validation uses the prescribed server compiler and delivery wrapper only.

## Second reading by Q126

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

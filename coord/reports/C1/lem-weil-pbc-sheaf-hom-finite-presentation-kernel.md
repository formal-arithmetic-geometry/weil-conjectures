## Worker report

The module `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomFinitePresentationKernel` states both parts of the node, with two named theorem proofs `sorry`. No new definition, dependency module, or statement correction is needed. The repository and source checkout were read only; all authored files are in this sandbox. The module compiled cleanly on the server (3.6 seconds), with no error or unexpected warning.

### Hypotheses and clauses

- A ringed space is rendered by `{X : Type u} [TopologicalSpace X]` and `{R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}`. This is an arbitrary topological space with a sheaf of commutative rings, without scheme, separation, compactness, or nonemptiness assumptions. All coefficients and module sections live in the common universe `u`; every size can be accommodated by this universe parameter. No additional sheafification or abelian-category hypothesis is imposed: Mathlib supplies the standard instances for this small site.
- `Mod(O_X)` is `SheafOfModules.{u} ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)`, using the existing category rather than a new encoding.
- The sheaf Hom is the recorded `SheafOfModules.homObj (R := R)`, whose sections at `op U` are the module-presheaf morphisms between restrictions to `Over U`. Its existing sheaf theorem promotes this presheaf to the sheaf Hom. The underlying restricted presheaf morphisms have exactly the components of the corresponding restricted sheaf morphisms, since forgetting is fully faithful. `ψ.app (op (Over.mk (𝟙 U)))` is precisely `ψ_U`.
- Part (1) binds arbitrary `E₂ E₁ E`, their maps `a b`, and arbitrary `M`. Hypothesis `h : (ComposableArrows.mk₃ a b (0 : E ⟶ 0)).Exact` is the full right exact sequence `E₂ → E₁ → E → 0`, including both zero composition and exactness at `E₁` and `E`. It does not assume injectivity of `a`.
- The maps `b*` and `a*` are the existing module morphisms `homObjMap (R := R) b (𝟙 M)` and `homObjMap (R := R) a (𝟙 M)`. Their definition precomposes with the restricted input morphism and postcomposes with the identity. Because their types are morphisms in `SheafOfModules`, the module-morphism assertion is part of their construction.
- The conclusion of `homObj_precomposition_exact` is `(ComposableArrows.mk₃ (0 : 0 ⟶ homObj E M) (homObjMap b (𝟙 M)) (homObjMap a (𝟙 M))).Exact`: all of `0 → Hom(E,M) → Hom(E₁,M) → Hom(E₂,M)` is exact, including its initial zero. There is no final zero or unjustified surjectivity assertion.
- Part (2) binds `m n : ℕ`, allowing zero, the module `H`, maps `a b`, and the right-exactness hypothesis `h`. `O_X^m` and `O_X^n` are the recorded free-sheaf construction `free (ULift.{u} (Fin m))` and `free (ULift.{u} (Fin n))`. `ULift` changes only the size of the finite index type, not the rank.
- The basis element `e_i|_U` is `(freeSection (ULift.up i)).eval (op U)`. `freeSection` is Mathlib's tautological basis section, and `sections.eval` views its value in the corresponding module, preserving its scalar structure.
- Coefficients are explicitly bound as `c : Fin n → Fin m → R.obj.obj (op (⊤ : Opens X))`. Hypothesis `hc` states the node's equation `a_X(e_k) = ∑ i, c i k • e_i` at the whole space, using `a.val.app (op ⊤)`. It imposes no condition beyond the node's coefficient identity.
- `M^n` and `M^m` are rendered by `∏ᶜ (fun _ : Fin n => M)` and `∏ᶜ (fun _ : Fin m => M)`. Finite direct sums and finite products of modules agree. Mathlib's evaluation preserves these products (see `SheafOfModules.evaluationPreservesLimitsOfShape` in `Sheaf/Limits.lean`), so their sections are canonically the tuples specified in the node, with componentwise restriction and scalar multiplication. `Pi.π` gives each coordinate. This uses an existing categorical construction; it does not define another tuple-valued sheaf.
- The existential `β α` asserts the formulas define actual sheaf-module morphisms. The first conjunct asserts, for every open `U`, section `ψ`, and coordinate `i`, that the `i`-th projection of `β_U ψ` is `ψ_U(b_U(e_i|_U))`.
- The second conjunct asserts, for every open `U`, input section `x` and output coordinate `k`, that the `k`-th projection of `α_U x` is `∑ i, R.obj.map (homOfLE le_top).op (c i k) • x_i`. The ring map is restriction of the global coefficient to `U`; the input coordinates are obtained through `Pi.π`. Products determine morphisms uniquely through these projections, so the existential does not allow arbitrary unspecified maps.
- The last conjunct `(ComposableArrows.mk₃ (0 : 0 ⟶ homObj H M) β α).Exact` states exactly the node's final left exact sequence, including injectivity of `β` and image equal to kernel at `M^n`.

### Dependencies and declarations read and used

- `def-weil-sheaf-of-modules-category`: `SheafOfModules`, `SheafOfModules.Hom`, and the category in `Mathlib.Algebra.Category.ModuleCat.Sheaf`; the abelian instance in `Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`. `Mathlib.Algebra.Category.Grp.FilteredColimits` supplies the small-site sheafification instances used by this standard abelian instance.
- `def-pur-sheaf-hom`: `SheafOfModules.homObj` and `SheafOfModules.homObjMap` in `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`. The full signatures and docstrings were read, along with `PresheafOfModules.restrictOver`, `restrictOverMap`, `homObj`, and `homObjMap` in the imported presheaf internal-Hom module. Explicit `(R := R)` prevents elaboration from choosing unresolved internal-Hom site/ring parameters.
- `def-pur-localized-ringed-site`: `SheafOfModules.over`, `Hom.over`, `overFunctor`, `overMap`, `overFunctorMap` in `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`. The internal-Hom construction uses the corresponding restrictions; its sections' components at `Over.mk (𝟙 U)` give the displayed local evaluation.
- `def-weil-pbc-exact-sequence`: the recorded `CategoryTheory.ComposableArrows.Exact` in `Mathlib.Algebra.Homology.ExactSequence`, with `ComposableArrows.mk₃`. Its full structure includes `IsComplex` and exactness of each consecutive short complex.
- `def-weil-pbc-module-finite-type-presentation`: the recorded finite-type and finite-presentation signatures in `Sheaf/Generators.lean` and `Sheaf/Quasicoherent.lean` were read, including `Presentation`, `Presentation.isColimit` and `presentationOfIsCokernelFree`. This item uses their underlying recorded free-sheaf notion, specifically `free`, `freeSection`, `freeHomEquiv` and `ιFree` in `Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`. It does not impose local finite presentation on arbitrary `M`.

The module docstrings carry all seven natural-language proof steps, identifying the node's abelian cokernel and local-lifting proof dependencies. Stage 2 does not prove any step.

### Edge cases

Checked before writing: `n = 0`, `m = 0`, both zero, zero `M`, empty space, empty open, non-surjective `a`, and a noninjective presentation map `b`. Empty products have zero module sections; an empty sum is zero. With `n = 0`, right exactness forces `H` to be zero, hence its internal Hom is zero. With `m = 0`, the presentation map `b` is an isomorphism, and the claimed kernel sequence ends with the zero product. No nonempty, positive-rank, field, characteristic, or finiteness-of-space binder excludes any of these cases. The coefficient orientations were checked: `c i k` describes input basis `k` and output basis `i`, so precomposition produces the stated transpose-shaped formula. No statement dispute or node fault found.

### Searches

- `msearch.py ... leanfinder "internal Hom sheaves modules exact first variable finite free presentation kernel"`: eight hits, principally `relationsOfIsCokernelFree`, `generatorsOfIsCokernelFree` and their projection declarations; one light condensed internally-projective result. None is the node's two-clause statement.
- `msearch.py ... loogle "SheafOfModules.homObj, SheafOfModules.free"`: zero hits, unknown identifier `SheafOfModules.homObj` in the service's index. Local source reading supplies the existing internal Hom, which is used.
- `msearch.py ... grep "homObj|def pi|piObj" Algebra/Category/ModuleCat/Sheaf`: zero hits; the internal Hom is in the source project, not Mathlib.
- `msearch.py ... leansearch "internal Hom sheaves modules is left exact contravariant finite presentation kernel"`: unavailable, Internal Server Error; this is not evidence of absence.
- `rg` for `homObj.*[Ee]xact|[Ee]xact.*homObj|homObj.*[Ff]ree` across Mathlib, the source project, and `lean/Sheaf`: the only nearby existing sheaf theorem is `finiteFreeInternalHomExact` in `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact`. It concerns the second argument and short exact sequences from a finite free first argument, and does not state either part of this node. Other matches are unrelated monoidal constructions.
- `rg` for the node id in the source project: no matches. `rg` for both proposed declaration names across `dag/lean_names_upstream.json`, Mathlib, source project and `lean/Sheaf`: no matches.
- Read `Sheaf/Limits.lean` to verify evaluation preserves finite products, and `Sheaf/Free.lean` to use the recorded basis sections instead of introducing another definition.

The literature checkout on this machine lacks `literature/stacks-project/modules.tex`; the source tags were read directly from [Stacks 01CO](https://stacks.math.columbia.edu/tag/01CO), [Stacks 01CQ](https://stacks.math.columbia.edu/tag/01CQ), and [Stacks 0GMV](https://stacks.math.columbia.edu/tag/0GMV). These confirm the first-variable assertion and its finite-presentation coordinate consequence. No source discrepancy requires a correction.

### Verbatim second signature

The node's `lean.statement` records the first signature; its `lean.declarations` names both declarations. The second signature is:

```lean
theorem homObj_finitePresentation_kernel (m n : ℕ)
    (H : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R))
    (a : free (R := (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)
        (ULift.{u} (Fin m)) ⟶ free (ULift.{u} (Fin n)))
    (b : free (ULift.{u} (Fin n)) ⟶ H)
    (h : (ComposableArrows.mk₃ a b
      (0 : H ⟶ (0 : SheafOfModules.{u}
        ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)))).Exact)
    (c : Fin n → Fin m → R.obj.obj (op (⊤ : Opens X)))
    (hc : ∀ k : Fin m,
      (a.val.app (op (⊤ : Opens X))).hom
          ((freeSection (R := (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)
            (ULift.up k)).eval (op ⊤)) =
        ∑ i : Fin n, c i k •
          ((freeSection (R := (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)
            (ULift.up i)).eval (op ⊤)))
    (M : SheafOfModules.{u}
      ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)) :
    ∃ (β : homObj (R := R) H M ⟶ ∏ᶜ (fun _ : Fin n => M))
      (α : (∏ᶜ (fun _ : Fin n => M)) ⟶ ∏ᶜ (fun _ : Fin m => M)),
      (∀ (U : Opens X) (ψ : (homObj (R := R) H M).val.obj (op U)) (i : Fin n),
        ((β ≫ Pi.π (fun _ : Fin n => M) i).val.app (op U)).hom ψ =
          (ψ.app (op (Over.mk (𝟙 U)))).hom
            ((b.val.app (op U)).hom
              ((freeSection
                (R := (sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)
                (ULift.up i)).eval (op U)))) ∧
      (∀ (U : Opens X) (x : (∏ᶜ (fun _ : Fin n => M)).val.obj (op U)) (k : Fin m),
        ((α ≫ Pi.π (fun _ : Fin m => M) k).val.app (op U)).hom x =
          ∑ i : Fin n, R.obj.map (homOfLE (le_top : U ≤ ⊤)).op (c i k) •
            ((Pi.π (fun _ : Fin n => M) i).val.app (op U)).hom x) ∧
      (ComposableArrows.mk₃ (0 : (0 : SheafOfModules.{u}
        ((sheafCompose _ (forget₂ CommRingCat RingCat.{u})).obj R)) ⟶ homObj (R := R) H M)
        β α).Exact
```

## Second reading by C1

I reread the node statement, its Stacks source place, all dependency signatures, and the submitted module.

- The ringed-space objects are rendered by `{X : Type u} [TopologicalSpace X]` and
  `{R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}`; this matches the node's
  arbitrary ringed space and adds no separation, scheme, finiteness, or nonemptiness hypothesis.
- `Mod(O_X)` is `SheafOfModules.{u} ((sheafCompose _
  (forget₂ CommRingCat RingCat.{u})).obj R)`, using the recorded dependency declaration.
- In part (1), `E₂`, `E₁`, `E`, `a`, `b`, and `M` are introduced in the node's order.
  The hypothesis `h : (ComposableArrows.mk₃ a b (0 : E ⟶ 0)).Exact` is exactly the
  right-exact sequence `E₂ → E₁ → E → 0`. The conclusion uses the recorded
  `homObjMap (R := R) b (𝟙 M)` and `homObjMap (R := R) a (𝟙 M)` and asserts exactness
  of `0 → Hom(E,M) → Hom(E₁,M) → Hom(E₂,M)`. Verdict: matches every clause.
- In part (2), `m,n : ℕ`, `H`, `a : free (Fin m) ⟶ free (Fin n)`, `b`, `h`, the
  global coefficients `c : Fin n → Fin m → R(⊤)`, their basis equation `hc`, and `M`
  occur in the same order and with the same quantifiers. `freeSection (ULift.up k)`
  renders the node's basis sections, and the finite products render the componentwise
  direct sums, including the cases `m = 0` and `n = 0`.
- The existential maps `β` and `α` have the node's types. The first displayed
  conjunct is exactly the formula `β_U(ψ)_i = ψ_U(b_U(e_i|_U))`, expressed through
  `Pi.π`; the second is exactly `α_U((x_i))_k = Σ_i c_{ik}|_U • x_i`, with
  `R.obj.map (homOfLE le_top).op` giving restriction of global coefficients. The final
  `ComposableArrows.mk₃ 0 β α` exactness is the node's left-exact sequence.
  Verdict: no stronger or weaker clause and no quantifier mismatch.

Edge cases checked: empty `X` and opens, zero module, `m = 0`, `n = 0`, both zero,
empty products and sums, and noninjective `a`; the binders cover all of them. No field,
characteristic, Noetherian, or positive-rank assumption is present. Universes are shared
between the space, ring sheaf, and module sheaves, as required.

I searched Mathlib, the source checkout, and `lean/Sheaf` with grep, LeanFinder/Loogle,
and the project search script for internal-Hom exactness and the two declaration names.
The only nearby theorem is the distinct `finiteFreeInternalHomExact`; no existing
 declaration states this node. The dependency declarations `SheafOfModules.homObj`,
`homObjMap`, `free`, and `freeSection` were opened and match their uses.

No mismatch was found, so no source, node statement, hypothesis, or Lean code was changed.
The module compiles cleanly with `scompile.py`; its only diagnostics are the two permitted
`sorry` warnings.

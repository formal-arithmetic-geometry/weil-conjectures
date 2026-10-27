## Worker report

The module `Sheaf.RingTheory.LocalizedArrowInjectiveFlatCokernelLimit` states
`Module.injective_flat_cokernel_of_localized_directed_limit`, with `sorry` as its sole
proof. It defines no new notions. The node's natural-language statement, dependencies,
and proof are unchanged. No statement dispute or mathematical node fault was found.

The source was read in `literature/stacks-project/algebra.tex`: Tag 046Y
`lemma-mod-injective-general`, especially its final passage from sufficiently large
stages; Tag 00D7 `lemma-zero-directed-limit`; and the first proof paragraph of Tag
00MO `lemma-another-variant-local-criterion-flatness`. Tensor right exactness is the
recorded Mathlib match of Tag 00DF. This node isolates the general limit passage;
the locality and finite-presentation assumptions of the surrounding 046Y theorem
are not assumptions of this already expanded node.

Every hypothesis and clause is rendered as follows:

| Node clause | Lean rendering |
| --- | --- |
| Small nonempty directed set | `I : Type u`, `[Preorder I]`, `[Nonempty I]`, `[IsDirected I (· ≤ ·)]`. A preorder also permits the directed-poset case. |
| Systems of commutative rings with identity and composition laws | `Ri Si : I ⥤ CommRingCat.{u}`; functor laws include the transition identities and compositions. |
| Stage maps `R_i → S_i` and commuting transition squares | `[∀ i, Algebra (Ri.obj i) (Si.obj i)]`, with the equality `h_ring_arrow` for every comparable pair and every ring element. An algebra structure is equivalent to specifying this commutative-ring homomorphism. |
| Ring colimits `R`, `S`, and compatible cocones | `cR : Cocone Ri`, `cS : Cocone Si`, `hcR : IsColimit cR`, `hcS : IsColimit cS`; the rings are `cR.pt` and `cS.pt`. The cocone laws give compatibility. |
| Cocone legs also used as algebra maps | The indexed `Algebra (Ri.obj i) cR.pt` and `Algebra (Si.obj i) cS.pt` instances, and `hR`, `hS`, identify those maps with the actual cocone legs. |
| Induced colimit ring map `φ : R → S` | `[Algebra cR.pt cS.pt]`, together with the two indexed scalar towers through `Si.obj i` and `cR.pt`, sharing the same `Algebra (Ri.obj i) cS.pt`. These force precisely `φ ∘ r_i = s_i ∘ φ_i`; colimit uniqueness therefore makes it the induced map. |
| Stage modules and linear arrows | `Mi Ni : I → Type u`, their indexed `AddCommGroup` and `Module (Si.obj i)` instances, and `ui : ∀ i, Mi i →ₗ[Si.obj i] Ni i`. |
| Restricted `R_i`-action on `N_i` and its quotient | Indexed `Module (Ri.obj i) (Ni i)` and `IsScalarTower (Ri.obj i) (Si.obj i) (Ni i)`. This is the forced restricted action, not an additional mathematical restriction. |
| Additive transitions | `m` and `n`, families of `AddMonoidHom` indexed by `i ≤ j`. |
| Semilinearity of both transitions | `hm_smul`, `hn_smul`, with the actual transition ring map `(Si.map (homOfLE h)).hom`. |
| Identity and composition laws of both transitions | `hm_id`, `hn_id`, `hm_comp`, `hn_comp`, pointwise for every element. |
| Transition compatibility of the arrows | `h_stage_arrow`: `n i j h (ui i x) = ui j (m i j h x)`. |
| Limit modules and linear arrow | `M N : Type u`, their `AddCommGroup` and `Module cS.pt` instances, and `u : M →ₗ[cS.pt] N`. |
| Restricted `R`-action on `N` and its quotient | `Module cR.pt N` and `IsScalarTower cR.pt cS.pt N`; this is restriction along `φ`. |
| Additive module cocones | `mu`, `nu`, families of additive homomorphisms. |
| Semilinearity over each `s_i` | `hmu_smul`, `hnu_smul` use `algebraMap (Si.obj i) cS.pt`, equal to `s_i` by `hS`. |
| Compatibility of the cocones with transitions | `hmu_comp`, `hnu_comp`. |
| `ν_i u_i = u μ_i` | `h_limit_arrow`, for every stage and element. |
| Every element of `M`, `N` comes from a stage | `hM_represent`, `hN_represent`. |
| Equality of representatives is detected at a common later stage | `hM_equal`, `hN_equal`, with explicit common index and both comparison proofs. The converse follows from cocone compatibility. These are exactly the elementwise algebraic colimit conditions in the node. |
| Canonical scalar-extension isomorphisms for both modules at every index | `alpha`, `beta`, linear equivalences over `cS.pt`, and `h_alpha`, `h_beta`, specifying `s ⊗ x ↦ s • mu i x` and `s ⊗ y ↦ s • nu i y`. Tensor symmetry `x ⊗ s ↦ s ⊗ x` identifies these with the node's right scalar-extension maps. Their formulas determine the canonical maps on all tensors, so no arbitrary comparison map is substituted. |
| Those isomorphisms carry the extended stage arrow to `u` | `h_arrow`, using the actual tensor map `(ui i).lTensor cS.pt`. Under tensor symmetry this is the node's `u_i ⊗ 1`. |
| Canonical ring map `S_i ⊗_{R_i} R → S` | The ring homomorphism `q` in `h_localization`, with its value on every pure tensor prescribed to be the product of the images under `s_i` and `φ`. Those values determine it uniquely. |
| Localization at a multiplicative subset, denominators invertible | `W : Submonoid ...` and `∀ w : W, IsUnit (q w)`. |
| Every element of the target is a fraction | `∀ s, ∃ a w, s * q w = q a`, equivalent to `s = q a / q w` because these denominators are units. |
| Every source element mapping to zero is killed by a denominator | `∀ a, q a = 0 → ∃ w : W, (w : ...) * a = 0`. Together these are the elementary localization characterization written explicitly in the node. |
| Stage cokernels `C_i` and limit cokernel `C` | `Ni i ⧸ LinearMap.range (ui i)` and `N ⧸ LinearMap.range u`, with the standard quotient modules and `Submodule.mkQ` quotient maps. |
| Some `i₀` has all subsequent arrows injective and cokernels flat | Binder `i₀ : I` and `h_tail : ∀ j, i₀ ≤ j → Function.Injective (ui j) ∧ Module.Flat (Ri.obj j) (...)`. A theorem for every chosen witness is the implication from existence of such a witness. |
| Limit arrow is injective | First conclusion, `Function.Injective u`. |
| Limit cokernel is `R`-flat | Second conclusion, `Module.Flat cR.pt (N ⧸ LinearMap.range u)`. |
| Canonical cokernel scalar-extension map is an isomorphism for every `i` | Final conclusion: for every `i`, an `S`-linear equivalence `e` from the scalar-extended stage quotient to the limit quotient, with `e (s ⊗ [y]) = s • [nu i y]`. After the same tensor symmetry, the formula is exactly `[y] ⊗ s ↦ s[ν_i(y)]`. The pure-tensor formula characterizes the map uniquely, including on arbitrary quotient representatives by surjectivity of `mkQ`. |
| No locality, Noetherianity or finite generation | None of these is assumed in the signature. No `Nontrivial` assumption occurs. |
| Common sufficiently large universe | The index, all ring carriers, and all module carriers use the explicitly bound universe `u`; tensor products and quotients stay there. `CommRingCat.{u}` itself is in `Type (u+1)`, without restricting the carriers. No independently smaller test universe is imposed. |

Dependencies used, with the recorded declarations read in their source modules:

- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit`; here the recorded `Cocone` and `IsColimit`
  declarations express the given colimits directly. The functors encode the rings
  and ring cocones. `Mathlib.CategoryTheory.Category.Preorder` supplies the index category.
- `def-weil-pbc-module-tensor-product`: the recorded Mathlib match `TensorProduct`
  (`Mathlib.LinearAlgebra.TensorProduct.Defs`), `TensorProduct.lift` and
  `TensorProduct.ext'` (Basic), and `LinearMap.rTensor` (Map). The corresponding
  left-tensor map `LinearMap.lTensor` is used after tensor symmetry. The ring tensor
  structure comes from `Mathlib.RingTheory.TensorProduct.Basic`, publicly imported.
- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`
  and `Module.Flat`; only the module-flatness notion is needed here.
- Proof dependency `lem-weil-pbc-tensor-right-exact`: its recorded Mathlib matches
  `lTensor_exact` and `rTensor_exact`, in
  `Mathlib.LinearAlgebra.TensorProduct.RightExactness`, imported non-publicly.
- Proof dependency `lem-weil-pbc-localized-base-change-quotient-flat`:
  `Module.flat_quotient_localized_baseChange` in the recorded upstream module
  `WeilConjectures.RingTheory.LocalizedBaseChangeQuotientFlat`, imported
  non-publicly. Its signature, localization witness, arbitrary ideal, and complete
  proof docstring were read. The stage-3 proof specializes it to the zero ideal.

Edge cases checked before writing: a singleton index set; zero rings (including
localization with a zero denominator) and zero modules; a nonempty directed
preorder rather than a chosen initial stage; an arbitrary characteristic;
noninjective arrows before the specified tail; and the comparison conclusion at
indices before `i₀`. The conclusion at every index uses right exactness, so does
not require injectivity at that index. Empty indexing is excluded exactly as in
the node. Tensor symmetry preserves the canonical maps and imposes no flatness
or finite-generation condition. Common-universe placement is expressly allowed
by the node.

Searches for an existing statement:

- `msearch.py`, `leanfinder`, query: "A directed colimit of semilinear module arrows
  with eventually injective maps and flat cokernels has injective limit and flat
  cokernel under localized base change". Eight hits, including
  `Module.DirectLimit.lift_injective`, `Module.flat_of_isLocalized_span`,
  `Module.Flat.of_isLocalizedModule`, and tensor-injectivity lemmas. These give
  ingredients for fixed rings or localization, not this varying-ring statement.
- `msearch.py`, `loogle`, query: `Module.Flat, TensorProduct`. Twelve hits, concerning
  nontriviality, linear independence, flat tensor products, and injective tensor
  inclusions; no match for this statement.
- `msearch.py`, `grep`, query: `flat.*cokernel|cokernel.*flat|localized.*arrow`,
  restricted to `RingTheory`: zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, queries for the node id,
  localized injective arrows, and injective flat cokernel limits: no hits for the
  item or its statement. A wider search for localized arrows and cokernels found
  unrelated category-theoretic constructions and
  `Sheaf.RingTheory.LocalModuleArrowNoetherianDescent`; none states the present
  directed-limit assertion. The DAG's recorded searches also confirm this split
  has no full-statement Mathlib match.

Validation: the prescribed `scompile.py NO
lem-trf-localized-arrow-injective-flat-cokernel-limit` compiled this file against
the published live library, separately in the sandbox and library configurations
(4.2 s and 6.9 s). Both runs exited successfully without errors or warnings.
`autoImplicit` is explicitly false, all variables and the universe are bound,
and the module has only the one stated theorem with `sorry`.

## Second reading by NO

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

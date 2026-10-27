## Worker report

This delivery records an exact existing theorem; it introduces no Lean module, definition,
proof, hypothesis, or statement correction. The declaration is
`AlgebraicGeometry.grothendieckDevissage_secondAdicSystem_torsion_cokernel` in
`WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicTorsionCokernel`,
lines 27–56 of the read clone's upstream source. The server source returned by
`scompile.py --source` has the same signature. The node changes only in `lean`.
The old `lead_note` describes an earlier missing reflection declaration, which no longer
prevents importing this upstream theorem in the published live build.

Clause-by-clause comparison:

- A Noetherian scheme is `{X : Scheme.{u}} [IsNoetherian X]`. Mathlib's class extends
  `IsLocallyNoetherian X` and `CompactSpace X`, exactly the Noetherian convention used here.
- The quasi-coherent ideals are `(I K : X.IdealSheafData)`.
- The coherent I-adic and K-adic systems are `(M : CoherentFormalModule X I)` and
  `(N : CoherentFormalModule X K)`. Their objects are inverse systems of coherent ordinary
  sheaf modules. Their morphisms are compatible natural transformations. Level `op n`
  means the positive adic level `n+1`, so both zero-based indices in this node are included.
- The thickening hypothesis is `hthick : ∀ (e : ℕ), 1 ≤ e → ∀ (hZ : IsNoetherian
  (K ^ e).subscheme), Functor.IsEquivalence (@completion ((K ^ e).subscheme) hZ
  (I.comap (K ^ e).subschemeι))`. It quantifies over every positive power and every
  Noetherian instance, retaining the node's instance-sensitive quantifier. The closed
  subscheme is precisely V(K^e) and `comap` is the extended ideal.
- The coherent module is `(H : CoherentModules X)`. This is the full subcategory defined
  using `RingedSpace.IsCoherent`, namely finite type with all finite-free relation kernels
  of finite type, not an arbitrary module or just a finite-presentation hypothesis.
- The fixed maps are `(α : M ⟶ (completion X I).obj H)` and
  `(δ : N ⟶ (completion X K).obj H)`; these are inputs, with no existential conclusion.
- `θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
  (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip` has at (e,n) the
  source (H/K^(e+1)H)/I^(n+1) and target (H/I^(n+1)H)/K^(e+1), as required.
  The outer and inner functor isomorphisms give naturality in both indices.
- `σ : N.obj ⋙ formalCompletionFunctor I ≅
  (M.obj ⋙ formalCompletionFunctor K).flip` has component
  N_e/I^(n+1)N_e ≅ M_n/K^(e+1)M_n, natural in both indices.
- `hsquare : ∀ e n : ℕ, ...` is exactly sigma followed by alpha reduced modulo
  K^(e+1), equal to delta reduced modulo I^(n+1) followed by theta. Its reductions are
  `formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1))` and
  `formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1))`.
- `(t : ℕ) (ht : 1 ≤ t)` retains the positive integer restriction.
- `hα : ∀ n : ℕ, IsZero (... (kernel (α.hom.app (op n)))) ∧
  IsZero (... (cokernel (α.hom.app (op n))))` retains BOTH ordinary sheaf annihilation
  hypotheses. In each expression the omitted product is
  `Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2`.
- The conclusion is `∀ e : ℕ, IsZero (Scheme.idealModuleProduct
  (Scheme.idealSheafPower K.toModulesι (4 * t)).2 (cokernel (δ.hom.app (op e))))`.
  All these kernels, cokernels and images are taken in `X.Modules`, the ambient sheaf
  module category. This is precisely the cokernel conjunct singled out by this item.
- There is no extra condition on theta, in particular no equality with a quotient
  projection, no existence of N or delta, and no added kernel conclusion for delta.

Dependency declarations inspected:

- `pqf-def-locnoeth`: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; the same file's `IsNoetherian` adds compactness.
- `def-weil-pbc-coherent-formal-module`:
  `WeilConjectures.AlgebraicGeometry.CoherentFormalModule`, declarations `CoherentModules`,
  `IsCoherentFormalModule`, `CoherentFormalModule`, `formalModuleQuotient`,
  `formalModuleQuotientπ`, `formalModuleQuotientMap`, `formalCompletionSystem`,
  `formalCompletionFunctor`, and `completion`, in namespace `AlgebraicGeometry`.
- `pqf-def-coherent` currently points to
  `Sheaf.AlgebraicGeometry.CoherentFiniteType` / `Scheme.Modules.IsQuasiCoherentFiniteType`.
  I read that declaration: it is the quasi-coherent plus finite-type conjunction, whereas
  the coherent notion used by the item is already supplied by the recorded formal-module
  dependency's `CoherentModules`, using the exact `RingedSpace.IsCoherent` of
  `WeilConjectures.AlgebraicGeometry.Coherent`. This existing theorem uses the latter exact
  notion, not a private copy of either predicate. No dependency replacement is required
  to attach this already published exact theorem.
- `lem-weil-pbc-quasi-coherent-ideal-closed-subscheme` is a Mathlib match, requiring no new
  `lean`: `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`,
  `AlgebraicGeometry.Scheme.IdealSheafData.subscheme`, `subschemeι`, `ker_subschemeι`,
  `subschemeCover`, `opensRange_subschemeCover_map`, `subschemeCover_map_subschemeι`.
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` supplies the closed-immersion instance.
- `def-nagata-extended-ideal`: `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`,
  `AlgebraicGeometry.Scheme.IdealSheafData.comap`; its definition is exactly
  `(pullback.fst f I.subschemeι).ker`.
- The proof imports are the upstream
  `WeilConjectures.AlgebraicGeometry.CoherentMapReductionTorsionCoker` /
  `AlgebraicGeometry.coherentMap_reduction_torsion_coker` and
  `WeilConjectures.AlgebraicGeometry.CompletionThickeningCokernelReflection` /
  `AlgebraicGeometry.completion_thickening_cokernel_reflection`; their statements and
  proof docstrings were read. The latter now exists even though its DAG lean field is empty.

Source and edge-case checks:

I read `literature/stacks-project/coherent.tex`, Remark
`remark-inverse-systems-kernel-cokernel-annihilated-by` and Lemma `lemma-existence-tricky`
(Tags 0888 and 088A), including the two successive bounds K^(2t) and K^(4t).
The existing theorem follows exactly the fixed-comparison extraction in the node.
Indices e=0 and n=0 mean first positive levels, never zeroth-power quotients.
The least allowed t=1 gives the asserted fourth-power bound. No empty scheme, zero H,
zero systems, zero ideal, unit ideal or characteristic is excluded. In particular if K
is the unit ideal, the K-adic terms and the target completion are zero, so the conclusion
is appropriate; for K=0 its positive-power annihilation assertion is automatic. If I is
the unit ideal, the strong equivalence hypothesis remains in place and is not silently
removed. There is no nonempty affine-cover binder or restriction on the scheme universe.

Searches for an existing statement (2026-10-23):

- `msearch.py ... leansearch "An ideal power annihilates cokernels of morphisms of coherent
  adic systems under equivalence of completion"`: eight adic-completion module hits,
  including `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`; no sheaf-level match.
- `msearch.py ... leanfinder "Uniform ideal power annihilation of cokernels of second adic
  systems reflected from completion"`: eight hits including `IsAdicComplete` and
  `AdicCompletion.exists_smodEq_pow_smul_top_and_mkQ_eq`; no exact Mathlib match.
- `msearch.py ... loogle "IsAdicComplete, Ideal"`: twelve completeness hits, no exact match.
- `msearch.py ... grep "annihilat.*completion|completion.*annihilat"`: zero Mathlib hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for second-adic names and torsion
  cokernels located the exact upstream file and an older duplicate Sheaf file.
- A direct blueprint-id search in `lean/WeilConjectures` located line 26 of the upstream
  module. Its complete signature and docstring were read, then confirmed with
  `scompile.py --source WeilConjectures.AlgebraicGeometry.GrothendieckDevissageSecondAdicTorsionCokernel`.
  The existing upstream theorem is preferred to the duplicate Sheaf declaration.

Validation: a module-mode scratch probe imports only the exact upstream module, then
runs `#check` and `#print axioms` for the declaration. `scompile.py NF <item>
scratch/ExistingProbe.lean` passed both sandbox and library probes (1.3 seconds each),
with no error or warning. The axioms are exactly `propext`, `Classical.choice`, `Quot.sound`.
No scratch probe is a delivered module. No new sorry is introduced.
There is no statement dispute or correction in this delivery.

## Second reading by NF

The dispatcher expressly forbids starting other agents and assigns the maintainer the
independent delivery review. This section records the worker's separate consistency
pass, not a claim that another worker performed an independent reading.
With the JSON and upstream signature reopened, I checked every binder and clause listed
above: arbitrary I and K on a Noetherian scheme, the positive-thickening equivalences with
all Noetherian instances, coherent M/N/H, the two fixed maps, both natural isomorphisms,
the comparison-square orientation, positive t, both alpha bounds, and the single ordinary
cokernel conclusion with exponent 4*t. The signature has no quotient-projection condition.
No mismatch with the item was found. The coherent dependency's inaccurate finite-type
record is noted explicitly above; the exact coherent notion is already provided and used
by the formal-module dependency and this theorem. No Lean or node statement changed in
this pass. Independent review remains the maintainer's responsibility as specified by
the dispatch brief.

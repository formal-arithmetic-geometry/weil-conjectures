## Worker report

The module states `AlgebraicGeometry.Scheme.Modules.universalExact_affine_power_reduction`.
The three chart/test helpers and the canonical composition comparison contain actual data;
only the main theorem is postponed, with exactly one `sorry`. No node statement changes,
new independent notions, or dependency repairs are needed.

Hypothesis and conclusion audit against the unchanged DAG statement:

- Schemes and the morphisms f and t: `{X S B : Scheme.{u}} (f : X ⟶ S) (t : B ⟶ S)`.
- The original sequence: `F : ShortComplex X.Modules`, `hF : F.ShortExact`; its three
  quasi-coherence hypotheses are separately bound typeclass arguments. No finite-type or
  coherence hypothesis is imposed.
- Exactness after every scheme base change: `hbase`, quantified over all `T : Scheme.{u}`
  and `s : T ⟶ S`, asserts short exactness of the two actual `tensorPullback` maps.
  The existential proof of their zero composite adds no constraint or arbitrary map.
- `Y = X ×_S B` and p, q: the actual `pullback f t`, `pullback.fst`, and `pullback.snd`.
- Affine opens: `A C : CommRingCat.{u}`, open immersions `v : Spec A ⟶ B` and
  `z : Spec C ⟶ pullback f t`. The algebra structure and equation `hz` express precisely
  the factorization `Z → V → B`. They are coordinate presentations of the two chosen
  affine opens, with no affineness of f, flatness, or non-zero-divisor requirement.
- Scalar: `a : A`; its image is always the explicit `algebraMap A C a`.
- H_i: `(tensorPullback (pullback.fst f t)).obj F.Xᵢ`. The first three conjuncts
  state quasi-coherence individually. The helper `universalExactAffineChart` restricts
  by tensor pullback along the open immersion z. `universalExactAffineSections` uses
  the existing `moduleSpecΓFunctor`, so these are the actual N_i and section maps.
- Counits and identification of the associated-sheaf sequence: the next three
  `IsIso ...fromTildeΓ` clauses and the two squares with `(tilde.functor C).map`.
- Short exact affine sections: the separate `Function.Injective`, `Function.Exact`,
  and `Function.Surjective` conjuncts.
- Every n including zero: `∀ n : ℕ`; `universalExactPowerTest` is literally
  `Spec(A/(a^n)) → Spec A → B → S`.
- The quotient base chart: `eZ` identifies the actual fibre product over Spec A
  with `Spec(C/(alpha^n))`; its two projection equations specify this isomorphism
  over Spec C and the test scheme. `w`, `IsOpenImmersion w`, and both projection
  equations give the open subscheme of `X ×_S T_n` under fibre-product pasting.
- Ring comparison: `e`, with its formula on every `c ⊗ class(r)`, is the ring
  isomorphism `C ⊗_A A/(a^n) ≃ C/(alpha^n)`. The formula fixes the canonical
  isomorphism, including its C-structure. `ρ` and its formula fix the induced
  map from A/(a^n).
- Quotient module comparison: `Q` is a short exact sequence of modules over the
  quotient ring; the `e₁,e₂,e₃` are C-linear equivalences to the actual quotients
  by `(alpha^n) • ⊤`. The two formulas on quotient classes identify both arrows,
  so Q is a presentation of the quotient sequence, not an unrelated exact sequence.
  The `lᵢ` identify its terms with scalar extension along the actual quotient map;
  the three pure-tensor formulas give precisely `class(c) ⊗ m ↦ class(c • m)`.
- Restriction of the original pulled-back sequence: `ψ₁,ψ₂,ψ₃` identify tilde Q
  with pullback directly from X along the composite chart map; the equations for w
  identify that composite with the restriction of `pullback.fst f T_n`. The two
  ψ squares include both original sequence maps. Their three unit normalizations
  use the canonical `universalExactAffineChartComposition` and
  `tensorPullbackSection`, fixing the comparison on `1 ⊗ m`.
- Injectivity modulo powers: `Function.Injective (fun x ↦ e₂ (Q.f (e₁.symm x)))`.
  The final conjunct states `i(m) = alpha^n • x → m = alpha^n • y` in existential
  form, exactly the divisibility implication. With the two class formulas this is
  the usual equivalent kernel criterion for the injective quotient map.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Spec`, `Spec.map`.
- `Mathlib.Algebra.Homology.ExactSequence`: `ShortComplex`, `ShortComplex.ShortExact`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: publicly exposes Mathlib's
  `SheafOfModules.IsQuasicoherent`; the stronger conjunction is not assumed.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`: existing `tensorPullback`,
  `tensorPullbackSection`, `tensorPullbackSectionComp` with its normalized adjunction.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: actual chosen pullbacks
  and their projections (available through `Mathlib.AlgebraicGeometry.Pullbacks`).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; proof uses its
  base-change stability.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `tilde.functor`, `tilde.toOpen`,
  `moduleSpecΓFunctor`, `Scheme.Modules.fromTildeΓ`, `tilde.adjunction`, and
  `isIso_fromTildeΓ_of_isQuasicoherent`.
- `Mathlib.LinearAlgebra.Quotient.Defs` and `.Basic`: actual `Submodule.Quotient`,
  quotient structures and maps (publicly available from the tensor quotient import).
- Proof imports: `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`
  (`isQuasicoherent_pullback`), `WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`
  (`quasiCoherent_cokernel_image`), `WeilConjectures.AlgebraicGeometry.TensorPullbackTilde`
  (`exists_tensorPullback_tilde_iso`); Mathlib supplies `pullbackSpecIso`,
  `TensorProduct.quotTensorEquivQuotSMul` and
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot` for the tensor calculations.

Edge cases: n=0 gives the unit ideals, zero quotient modules and empty spectra.
The zero ring and empty affine opens are allowed. For a=0 and n>0 the quotient is
unchanged and divisibility means zero; injectivity of i gives the implication.
For a a unit every quotient is zero and divisibility is automatic. A nonflat C/A
is allowed. The ordinary short exact sequence Z --2--> Z → Z/2 with a=2 would
fail the asserted quotient injection; it is excluded precisely by hbase, not by
an added flatness hypothesis. All universes are explicit, with base-change tests
in the schemes' own universe, not a smaller independent universe.

Searches: prescribed msearch LeanFinder query “A universally exact sequence of quasi
coherent sheaves gives injective affine section maps modulo every power of a scalar
after arbitrary scheme base change” returned eight stalk/localization/limit results,
none the statement. Loogle `CategoryTheory.ShortComplex.ShortExact` returned its
12 generic declarations, used for the existing notion. Mathlib grep
`universally.?exact|universally.?injective|quotient.*pullback` in AlgebraicGeometry
returned 14 geometric-morphism/base-change hits, none this sheaf comparison. LeanSearch
“A universally exact sequence of quasi coherent sheaves gives injective affine section
maps modulo powers of a scalar” returned eight results including `QuotSMulTop.map_exact`
and `LinearMap.exact_smul_id_smul_top_mkQ`, but no universal affine comparison.
Local rg of `lean/WeilConjectures` and `lean/Sheaf` found the parent
`ModuleStrictTransformUniversalExact` and affine tensor-exact opcycles results, which
have different conclusions. Exact item-id searches found no existing declaration.
The quotient and tilde definitions found by search are reused, not copied.

The source read is `literature/stacks-project/divisors.tex`, lines 9037–9072,
Tag 080W. The accepted node expands that affine step using the cited scheme results.
No statement dispute or correction is needed.

## Second reading by Q03

The dispatcher requires this worker to work alone; this section records a fresh
self-audit with the node and module open, not an independent-agent review. The
maintainer supplies the independent review after delivery. The audit checked every
clause listed above. It caught a draft that identified only the chart pullback and
not the original sequence on X: the ψ targets now pull back directly from X, and
the normalized composition comparison relates their sections to the chart units.
It also replaced an irrelevant identity-pullback comparison with the actual
quotient-ring tilde comparison, with all three scalar formulas and both maps.
No hypothesis, power-zero case, or quotient-map clause has been dropped.

Validation: scompile.py compiled the complete module in both sandbox and library mode;
the initial file-wide heartbeat-option warning was repaired by scoping the option to
the main declaration. The per-file compilation limit remains 60 seconds.

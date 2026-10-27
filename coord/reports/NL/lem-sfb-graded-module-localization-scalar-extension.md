## Worker report

This stage-2 delivery states `LocalizedModule.exists_gradedLocalization_scalarExtension_equiv`
in `Sheaf.Algebra.Module.GradedLocalizationScalarExtension`. Its only theorem has proof `sorry`.
There are no new definitions, helper theorems, dependency repairs, or statement corrections.
The accepted stage-1 split is preserved. The current queue assigns the item to stage 2,
and the base node has no Lean record: the inherited stage-1 unchanged-item rejection is
not relevant to this stage-2 packet (standing brief §0).

The statement retains all hypotheses and conclusions of the node. The following matches
every clause to its Lean rendering.

| Node clause | Lean rendering |
| --- | --- |
| Commutative rings R, S, A, and unital R → S | Independent `R : Type u`, `S : Type v`, `A : Type w`, `CommRing` instances, and `[Algebra R S]`; the ring homomorphism is `algebraMap R S`. |
| Nonnegative unital grading A = ⊕ A_n, with R → A_0 | `𝒜 : ℕ → Submodule R A`, `[Algebra R A]`, and `[GradedAlgebra 𝒜]`. This class includes the direct-sum decomposition, graded multiplication, and `1 ∈ 𝒜 0`. Because `𝒜 0` is an R-submodule, `algebraMap R A r = r • 1` lies there. Thus precisely the given map factors through grade zero. |
| M an A-module with the induced R-action | `M : Type t`, `[AddCommGroup M]`, `[Module A M]`, `[Module R M]`, `[IsScalarTower R A M]`. The tower forces the R-action to be the restriction of the given A-action, and is structure compatibility rather than an extra mathematical assumption. |
| Z-grading M = ⊕ M_i | `𝓜 : ℤ → Submodule R M`, `h𝓜 : DirectSum.IsInternal 𝓜`. Using R-submodules is valid because R acts in degree zero. `IsInternal` says exactly that summing components is bijective; no boundedness is assumed. |
| A_n M_i ⊆ M_(n+i) | `hsmul : ∀ (n : ℕ) (i : ℤ) (a : A) (x : M), a ∈ 𝒜 n → x ∈ 𝓜 i → a • x ∈ 𝓜 ((n : ℤ) + i)`. |
| C = S ⊗_R A, C_n = S ⊗_R A_n | Mathlib `S ⊗[R] A` with its canonical commutative ring structure. The imported `GradedAlgebra.baseChange` gives exactly the grading `fun n ↦ (𝒜 n).baseChange S`. There is no independent C or arbitrary grading to choose. |
| N = S ⊗_R M, N_i = S ⊗_R M_i | Mathlib `S ⊗[R] M`, with components `(𝓜 i).baseChange S` used explicitly in the target carrier. `DirectSum.IsInternal.toBaseChange_bijective 𝓜 h𝓜 i` identifies each of these submodules with `S ⊗[R] 𝓜 i`, and `DirectSum.IsInternal.baseChange` supplies the tensor grading. Thus a nonflat coefficient change does not collapse a component inclusion. |
| C-action (s ⊗ a)(t ⊗ x) = st ⊗ ax | The signature's `ρ` is `AlgHom.liftEquiv R S A _ ((Module.End.baseChangeHom R S M).comp (Algebra.lsmul R R M))`. Its `Module.compHom` action first extends each action endomorphism on M to `S ⊗ M`, then extends S-linearly in the algebra argument. On pure tensors it is `s • (t ⊗ (a • x)) = (s*t) ⊗ (a • x)`. The explicit `letI IsScalarTower S C N` is obtained from `ρ.commutes`, not assumed or postponed. All action data are actual Mathlib constructions. |
| f ∈ A_d and d > 0 | `{d : ℕ}`, `hd : 0 < d`, `{f : A}`, `hf : f ∈ 𝒜 d`. |
| f_S = 1 ⊗ f | The expression `(1 ⊗ₜ[R] f : S ⊗[R] A)` occurs in every target localization and denominator. |
| M_f and N_(f_S), ordinary fraction relation | `LocalizedModule.Away f M` and `LocalizedModule.Away (1 ⊗ₜ[R] f) (S ⊗[R] M)`. These are the dependency's `LocalizedModule` at `Submonoid.powers`; `LocalizedModule.mk` gives the fractions, and `LocalizedModule.mk_eq` is exactly the stated multiplication-by-a-power relation, including zero divisors. |
| Every integer j | The unrestricted parameter `(j : ℤ)`. |
| Source piece consists exactly of x/f^m, x ∈ M_(md+j) | The conclusion existentially supplies `H : Submodule R (LocalizedModule.Away f M)` and asserts its carrier equals `homogeneousPieceAway (fun i ↦ (𝓜 i).toAddSubgroup) f (d : ℤ) j`. This existing definition uses `j + (m : ℤ) * d`, equal to `md+j`. |
| Target piece defined similarly with N | The conclusion supplies `K : Submodule S (LocalizedModule.Away f_S (S ⊗[R] M))` whose carrier is exactly `homogeneousPieceAway (fun i ↦ ((𝓜 i).baseChange S).toAddSubgroup) f_S (d : ℤ) j`. |
| These sets are R- and S-modules, addition by common denominator | `H` and `K` are submodules of the ordinary localizations with their inherited coefficient actions. The carrier equalities assert closure of exactly the specified sets; neither a span enlargement nor an assumed closure condition is used. Their addition is inherited from `LocalizedModule.mk_add_mk`. A submodule with a specified carrier is unique, so these existential submodules do not introduce arbitrary module structures. |
| The specified S-module isomorphism | `∃ e : (S ⊗[R] H) ≃ₗ[S] K`, followed by its equation on every pure tensor with a homogeneous fraction. |
| λ(s ⊗ (x/f^m)) = (s ⊗ x)/f_S^m | The final universal clause quantifies `s`, `m`, `x` with `x ∈ 𝓜 (j + m*d)`, and `z : H` with underlying fraction `mk x ⟨f^m, ...⟩`; the equation states the underlying value of `e (s ⊗ z)` equals `mk (s ⊗ x) ⟨f_S^m, ...⟩`. The carrier equality guarantees that such z exists for every eligible numerator and denominator. Since every H element has such a representative and pure tensors generate, this specifies the canonical comparison, rather than a bare isomorphism. |
| No flatness, finite generation, boundedness or regularity of f | None of these appears in any binder. Neither `Nontrivial` nor injectivity of the coefficient homomorphism is required. |

Dependency declarations read and used:

- `def-weil-pbc-module-localization`: `LocalizedModule`, `LocalizedModule.mk`,
  `LocalizedModule.mk_eq`, `LocalizedModule.mk_add_mk`, and `LocalizedModule.Away`
  from `Mathlib.Algebra.Module.LocalizedModule.Basic` (the recorded declaration).
- Added landed statement dependency `def-sc-localized-homogeneous-piece`:
  `LocalizedModule.homogeneousPieceAway` from
  `Sheaf.Algebra.Module.LocalizedHomogeneousPiece`. Its full signature and docstring
  were read, and its additive-subgroup interface is used directly by `toAddSubgroup`.
  Only `stmt_deps` gains this landed definition; its node and module are unchanged.
- Proof dependency `def-weil-pbc-category-colimit`: the recorded
  `CategoryTheory.Limits.colimit`, `Cocone`, `IsColimit` interface from
  `Mathlib.CategoryTheory.Limits.HasLimits` (plain proof import).
- Proof dependency `lem-weil-pbc-tensor-commutes-with-colimits`: the Mathlib match
  `CategoryTheory.ihom.instIsLeftAdjointTensorRightOfClosed` and
  `CategoryTheory.Limits.isColimitOfPreserves`, with ModuleCat's monoidal-closed
  structure. Its modules `Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed` and
  `Mathlib.CategoryTheory.Monoidal.Closed.Braided` are plain proof imports.
- Other existing constructions are Mathlib `GradedAlgebra`, `Submodule.baseChange`,
  `DirectSum.IsInternal`, `Module.End.baseChangeHom`, `Algebra.lsmul`,
  `AlgHom.liftEquiv`, `Module.compHom`, and `IsScalarTower.of_algebraMap_smul`.
  Their source definitions and relevant signatures were inspected before use.

Edge cases checked mathematically against the signature:

- `S = 0`, `R = 0` when the corresponding unital algebra exists, and `M = 0`:
  no nontriviality binder excludes them; the module equivalence is between zero modules.
- `f = 0` or f nilpotent: the ordinary localization relation makes both sides zero;
  zero is homogeneous in every degree and `hd` places no regularity restriction on f.
- Nonflat `Z → F_2`, `A = Z[t]`, `f = 2t`: the target denominator is zero;
  the source piece tensors to zero, as required. No cancellation was used.
- `j < 0`, arbitrary d > 0, and M unbounded below: all component indices are integers,
  and only the denominator exponent is natural. No truncation of M occurs.
- `m = 0`: the denominator is 1, and the formula is the usual coefficient tensor map
  on an element of M_j. `j = 0` is included without specializing M to A.
- Rings and modules have four independent explicit universes; no size equality is imposed.

Searches made, before writing:

- `msearch.py ... leanfinder`, query: “For a graded module scalar extension commutes
  with each homogeneous degree of localization at a homogeneous element”. Eight hits
  on homogeneous ring localization and scalar towers, including
  `HomogeneousLocalization.mk_smul`, `map` and `map_mk`; none treats arbitrary modules.
- `msearch.py ... loogle`, query `LocalizedModule, Submodule.baseChange`: zero hits.
- `msearch.py ... grep`, query `homogeneous|graded`, restricted to
  `RingTheory/Localization/BaseChange.lean`: zero hits. The ungraded tensor-localization
  interface does not state the homogeneous-degree comparison.
- `msearch.py ... leansearch`, query: “Scalar extension of a graded module commutes
  with the homogeneous pieces of localization at one homogeneous element”. Eight hits
  on ungraded `IsLocalizedModule.mapExtendScalars` and homogeneous ring localization;
  no exact theorem for arbitrary graded module pieces.
- `rg` in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and the upstream declaration
  index for homogeneous/localized graded modules, scalar extension and the item id:
  no existing statement of the item. The search found the reused
  `LocalizedModule.homogeneousPieceAway`, the project theorem
  `HomogeneousLocalization.exists_away_scalarExtension_equiv` (only ring case, degree
  zero), and upstream `degreeZeroFractions` and `gradedModuleAwayRestriction`
  (degree-zero localization/restrictions, without coefficient extension).
- `python3 tools/blueprint_refs.py search 'homogeneous localized module'`:
  zero blueprint matches. DAG search finds the already landed homogeneous-piece
  definition; no duplicate definition is introduced.

Source checked: `literature/stacks-project/constructions.tex`,
`lemma-base-change-map-proj` (Tag 01N2), whose proof reduces to standard opens.
The node explicitly labels its arbitrary-module refinement as agent supplied;
its four proof steps, reproduced in the theorem docstring, supply that refinement.
There is no false statement or missing hypothesis found, hence no
`STATEMENT-DISPUTED` marker or `statement_change`.

Validation: the complete module was compiled with `scompile.py NL
lem-sfb-graded-module-localization-scalar-extension <module>` against the live
published library. Both sandbox and actual-module checks passed cleanly
(3.7 s and 3.5 s), with no warnings. All variables/universes are bound explicitly,
all lines are at most 100 characters, and the only postponed proof is the
node's named theorem. No source or Git mutation was made in the shared repository.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

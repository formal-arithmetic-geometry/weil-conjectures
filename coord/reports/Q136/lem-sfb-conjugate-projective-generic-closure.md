## Worker report

The module `Sheaf.AlgebraicGeometry.ConjugateProjectiveGenericClosure` states
`AlgebraicGeometry.exists_conjugate_projective_generic_closure`, with one whole-proof
`sorry`. It introduces no definitions, axioms, helper theorems, or new DAG nodes.
Only the item's `lean` field changes. All variables and both universes are bound
explicitly; `autoImplicit` is disabled.

Source read: ILO, Travaux de Gabber, Exposé X, Theorem 3.4, Step 4, printed
pp. 160--161 (PDF pp. 166--167). This is the motivation for dominating by a
projective Galois alteration; the node explicitly supplies its more general agent
conjugate-product expansion. Also read Stacks `coherent.tex`,
`remark-chow-Noetherian`, Tag 0201 (2),(3); `constructions.tex`,
`lemma-segre-embedding`, Tag 01WD; and `schemes.tex`,
`lemma-reduced-closed-subscheme`, Tag 01J3, with the definition following it.
The current blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/` direct-images proof was read
from `literature/blueprint/latest/`; this item is an agent-expanded supporting
lemma, not the statement of that unit.

Hypotheses, individually matched:

| Node hypothesis | Lean rendering |
| --- | --- |
| k is a field | `(k : Type u) [Field k]` |
| S is an integral k-scheme | `(S : Scheme.{u}) [IsIntegral S]`, with named structure map `ρS` |
| S is projective and finite type over k | `[IsHProjective ρS] [LocallyOfFiniteType ρS] [QuasiCompact ρS]` |
| K = k(S) | The carrier `S.functionField`, the generic stalk, is used literally throughout |
| J is a finite group | `(J : Type v) [Group J] [Finite J]`; no faithfulness condition |
| Compatible actions on S and k | `h : J →* Aut S`, `τ : J →* (k ≃+* k)`, and `hS` |
| B is integral, projective, finite type over k | B, its `IsIntegral` instance, named map `ρB`, and the three corresponding geometric instances |
| u is a finite k-morphism | `uB : B ⟶ S`, `[IsFinite uB]`, and `huB : uB ≫ ρS = ρB` |
| M/K is finite | `[Field M] [Algebra S.functionField M] [Module.Finite S.functionField M]` |
| Spec M identifies the generic fibre of B | `eB : Spec (.of M) ≅ pullback uB (S.fromSpecStalk (genericPoint S))` |
| η_B is its resulting generic map | `ηB`, with `heB` equating it to the first projection of `eB`; `heBK` fixes the second projection to the specified K-algebra map |
| J acts on B semilinearly | `a : J →* Aut B` and `hB` for the same `τ` |
| J acts on M by field automorphisms | `σ : J →* (M ≃+* M)` |
| u a_j = h_j u | `hu : ∀ j, (a j).hom ≫ uB = uB ≫ (h j).hom` |
| a_j η_B = η_B d_j, d_j = Spec(σ_j⁻¹) | `hη`, using `Spec.map (CommRingCat.ofHom (σ j).symm.toRingHom)` |
| T is integral and finite type over k | T, `IsIntegral T`, `ρT`, `LocallyOfFiniteType ρT`, and `QuasiCompact ρT` |
| r is a proper k-morphism | `r : T ⟶ S`, `[IsProper r]`, and `hr` |
| L/K is finite and T_K = Spec L | Field/algebra/module-finiteness instances for L, `eT`, and its base projection normalization `heTK` |
| Fixed K-embedding L → M | `ι : L →ₐ[S.functionField] M`; a homomorphism between fields is injective |

Every scheme and field is in the arbitrary scheme universe u, the standard size
convention for this scheme category. The finite group has the independent universe v.
There is no restriction on characteristic, separability, normality, or faithfulness.
An action on functions induces the inverse automorphism on spectra: `hS`, `hB`,
and all later semilinearity equations consistently use `Spec(τ_j⁻¹)`.
`Aut` multiplication is reverse categorical composition (`Aut_mul_def`), so its
monoid homomorphisms encode the ordinary left actions in the node.

Conclusions, individually matched:

| Node clause | Lean rendering |
| --- | --- |
| Integral projective finite-type Y/k | Existential Y, its `IsIntegral` witness, `ρY`, and `IsHProjective ρY ∧ LocallyOfFiniteType ρY ∧ QuasiCompact ρY` |
| Proper surjective k-morphism π : Y → T | Existential π, `IsProper π ∧ Surjective π ∧ π ≫ ρT = ρY` |
| Isomorphism over a nonempty open of T | `∃ U : T.Opens, (U : Set T).Nonempty ∧ IsIso (π ∣_ U)` |
| v = rπ | Written directly as `π ≫ r`, avoiding a statement-local let |
| Y_K = Spec L, induced by π | `eY`, with normalized second projection and `eY.hom ≫ pullback.fst _ _ ≫ π = eT.hom ≫ pullback.fst _ _` |
| Induced generic morphism f : Spec M → Y | Existential f and its equality to `Spec.map ι.toRingHom ≫ eY.hom ≫ pullback.fst _ _` (with the ring hom bundled in `CommRingCat`) |
| Y_j has underlying scheme Y and structure map h_j v | The `some j` leg of D is exactly `π ≫ r ≫ (h j).hom` |
| P = B ×_S ∏_j Y_j | `D : WidePullbackCone ...` with `Nonempty (IsLimit D)`; P is `D.pt` |
| Projections p_B and p_j | `D.π none` and `D.π (some j)` |
| The displayed fibre-product data are well defined | The cone contains all common-base equations and its limiting witness gives the universal property; q below has exactly the prescribed components |
| P embeds in finite-dimensional projective space over k | `IsHProjective (D.base ≫ ρS)`, precisely the recorded projectivity convention |
| q_B = η_B | `q ≫ D.π none = ηB` |
| q_j = f d_(j⁻¹) | `q ≫ D.π (some j) = Spec.map (σ j⁻¹).symm.toRingHom ≫ f` with the displayed bundling |
| Action on P | `A : J →* Aut D.pt` |
| p_B g_P = a_g p_B | `(A g).hom ≫ D.π none = D.π none ≫ (a g).hom` |
| p_(gj) g_P = p_j | `(A g).hom ≫ D.π (some (g * j)) = D.π (some j)` |
| P-action lies over h_g | `(A g).hom ≫ D.base = D.base ≫ (h g).hom` |
| P-action is semilinear on k | The following explicit equation for `(A g).hom ≫ D.base ≫ ρS`, with `Spec(τ_g⁻¹)` |
| q is equivariant | `q ≫ (A g).hom = Spec(σ_g⁻¹) ≫ q` |
| i : C ↪ P is the reduced induced closed structure on closure of q(*) | `IsIntegral C`, `IsClosedImmersion i`, `Set.range i = closure (Set.range q)`, and `i.ker = Scheme.IdealSheafData.vanishingIdeal ⟨closure (Set.range q), isClosed_closure⟩` |
| C is integral projective finite type over k | Integral witness for C and the three geometric properties of `i ≫ D.base ≫ ρS` |
| Action restricts to C | `AC : J →* Aut C`, with `(AC g).hom ≫ i = i ≫ (A g).hom` |
| p = u p_B i is equivariant | p is written `i ≫ D.base`, equal by the cone relation to `i ≫ D.π none ≫ uB`; the explicit equation for `(AC g).hom ≫ i ≫ D.base` expresses equivariance |
| q factors through the closure, compatibly with actions | `qC ≫ i = q`, and `qC ≫ (AC g).hom = Spec(σ_g⁻¹) ≫ qC` |
| C_K ≅ Spec M induced by q | `eCK : Spec (.of M) ≅ pullback (i ≫ D.base) ηS`; its first projection is qC and its second projection is the original K-algebra map |
| k(C) = M induced by q | `eC : C.functionField ≅ CommRingCat.of M`, with `qC = Spec.map eC.hom ≫ C.fromSpecStalk (genericPoint C)` |
| Both isomorphisms compatible with actions | The normalized first projection of eCK, normalization of eC by the canonical generic-point map, and qC's explicit equivariance equation identify their induced action with `Spec(σ_g⁻¹)` |
| c = p_1 i and v c = p | `c = i ≫ D.π (some 1)` and `c ≫ π ≫ r = i ≫ D.base` |
| rπc = p and πc is a k-morphism | The same composite equality and `c ≫ ρY = i ≫ D.base ≫ ρS`, together with π's k-morphism equation |
| No action on Y or T or equivariance of those projections | Neither action is an input or a conclusion |

The closure is expressed by its defining reduced closed immersion and ideal,
rather than identifying a chosen carrier with a particular implementation of
`vanishingIdeal.subscheme`. This is exactly the uniqueness clause of the recorded
reduced-induced-closed-subscheme theorem. Since Spec M has a single point,
`closure (Set.range q)` is the node's singleton closure. Integrality includes
reducedness, and the ideal equality additionally fixes the canonical structure.
The wide pullback over the family indexed by `Option J` is the same fibre product
as B times the J-indexed product over S; its universal property is identical, so
no associativity or choice convention changes the claim.

Dependency declarations used (source declarations and docstrings read):

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the recorded
  `Scheme.functionFieldOfComponents` explicitly delegates its integral-scheme
  clause to `Mathlib.AlgebraicGeometry.FunctionField`, `Scheme.functionField`.
  This item uses precisely that clause, not a component product for a curve.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, with `algebraMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.fst`, `pullback.snd`. The finite family uses the same universal
  property via `WidePullbackCone` and `IsLimit` from
  `Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsHProjective`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `Scheme.IdealSheafData.reduced_induced_closed_subscheme`, whose signature
  gives the vanishing ideal, reduced closed structure, support and uniqueness.
  `Scheme.IdealSheafData.vanishingIdeal` is the actual ideal construction used.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `Surjective`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`, represented here
  by the standard open subscheme U and morphism restriction `(π ∣_ U)`.

Proof imports are plain imports. Available proof-node modules include
`ProjectiveImpliesProper`, `IntegralChowRelativelyAmple`,
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product`, and the upstream
closed-immersion and properness extensions. Other recorded Mathlib proof matches
are already imported through the statement API. The proof node
`lem-sfb-projective-fibre-product-closed-model` currently has no recorded Lean
module or Mathlib match, so there is no module to import for it; the main
docstring retains its use for stage 3. No missing statement dependency remains.

Searches actually run:

- `msearch.py ... leanfinder` with query "Equivariant conjugate product of
  projective schemes and reduced closure of a generic point with prescribed
  finite function field": eight hits, including `Scheme.PartialMap.fromFunctionField`,
  rational-map analogues and Proj properness, none stating this result.
- `msearch.py ... leansearch` with query "equivariant projective conjugate
  product generic graph reduced closure": eight hits on action homomorphisms,
  conjugation and the Maschke averaging map; no exact result.
- `msearch.py ... loogle` with query
  `AlgebraicGeometry.IsHProjective, AlgebraicGeometry.Scheme.functionField, CategoryTheory.Limits.widePullback`:
  zero hits and the message `unknown identifier 'AlgebraicGeometry.IsHProjective'`.
  This upstream-only declaration was then read directly; the search result is
  not treated as evidence that the declaration is absent.
- `msearch.py ... grep` with pattern
  `conjugate.*[Pp]roject|[Gg]eneric.*[Cc]losure|widePullback` in
  `AlgebraicGeometry`: zero hits (the wide-pullback definitions are in
  `CategoryTheory`, read directly).
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `conjugate.*[Pp]roject|[Gg]eneric.*[Cc]losure|lem-sfb-conjugate-projective-generic-closure`:
  unrelated generic-closure references, no declaration of this node.
- `rg` of those source trees and `dag/lean_names_upstream.json` for the proposed
  full declaration name and conjugate-product phrases: no collision or match.
  Searched the exact item id in the upstream source tree as well; no declaration.

Edge cases checked before writing and again against the signature:

- J may act nonfaithfully or trivially. There is no injectivity assumption.
  J cannot be empty because it is a group; `some 1` is always available. The
  independent group universe v does not exclude finite groups of another size.
- Degree-one M/K and L/K, trivial field actions, and nontrivial semilinear field
  actions are all allowed. No separability or perfection appears, so purely
  inseparable extensions are retained. The closed-section generic argument works
  for them scheme-theoretically.
- S, B, T, Y and C are nonempty because they are integral; the open witnessing
  birationality is explicitly nonempty. The product need not itself be reduced
  or integral; no such condition is imposed on D.pt.
- Zero-dimensional schemes and projective 0-space are allowed by `IsHProjective`.
  The statement never assumes positive dimension or positive characteristic.
- The spectrum action uses σ inverse, while the j-component of q uses the
  inverse group index as well. At j = 1 this is f, so c has the original
  untwisted structure map; for arbitrary g the displayed permutation is gj.
- Arbitrary isomorphisms of the abstract generic fields would be insufficient.
  `heBK`, `heTK`, the eY projection equations, the formula for f, and both eCK
  projection equations retain all specified K-identifications. The eC generic
  normalization excludes an unrelated automorphism of M.

No statement correction, unusable dependency, or STATEMENT-DISPUTED issue was found.

Validation: the prescribed `scompile.py` compiled this module in sandbox and
library modes without errors or warnings (the theorem's expected `sorry` is
permitted). `deliver2.py --no-push` then compiled both modes again and printed
`OK (dry run): commit 61cda976624 passes the preflight and compiles; nothing pushed`.
Only this report's exact grep-query transcription and validation paragraph were
updated after that passing dry run. Final compilation is also run by `deliver2.py`.

## Second reading by Q136

The section delivered under this heading was a re-reading by the same worker (it says
so itself). This replacement is an independent clause-by-clause reading of
`AlgebraicGeometry.exists_conjugate_projective_generic_closure` against the node, made by the
maintainer's stage-2 reviewer (delivery 70d9d34c89fc); the Lean and all records are unchanged.

Conventions. `Aut` multiplication is `(f * g).hom = g.hom ≫ f.hom` and `RingEquiv`
multiplication is composition, so `h, a, A, AC` are left actions, and `b_j = Spec(τ_j⁻¹)`,
`d_j = Spec(σ_j⁻¹)` satisfy `b_g b_l = b_{gl}`, `d_g d_l = d_{gl}`.

Hypotheses (node → Lean, verdict):
- k field → `[Field k]`: ok. S integral projective finite type → `IsIntegral S`,
  `IsHProjective ρS` (closed immersion into `ℙ(n; Spec k)`, n finite: def-kun-projective),
  `LocallyOfFiniteType ρS ∧ QuasiCompact ρS` (recorded finite-type convention): ok.
- K = k(S) → `S.functionField`, the integral clause the def-sc-function-field record delegates to: ok.
- J finite group acting on S and k compatibly → `h`, `τ`, `hS : ρS ∘ h_j = b_j ∘ ρS`: ok, nonfaithful allowed.
- u : B → S finite k-morphism, B integral projective finite type → `IsFinite uB`, `huB`, B instances: ok.
- generic fibre ≅ Spec M, M/K finite, η_B → `eB`, `heB` (η_B = fst ∘ eB), `heBK` (snd = Spec(K → M)), `Module.Finite`: ok.
- a_j semilinear, σ_j field automorphisms, u a_j = h_j u, a_j η_B = η_B d_j → `a`, `σ`, `hB`, `hu`, `hη`: ok, verbatim orientation.
- r : T → S proper k-morphism, T integral finite type (not projective) → `IsProper r`, `hr`, T instances: ok.
- T_K = Spec L, L/K finite, K-embedding L ↪ M → `eT`, `heTK`, `ι : L →ₐ[K] M`: ok.

Conclusions:
- Y integral projective finite type; π proper surjective k-morphism; iso over nonempty open →
  `IsHProjective ρY ∧ LocallyOfFiniteType ρY ∧ QuasiCompact ρY ∧ IsProper π ∧ Surjective π ∧ π ≫ ρT = ρY`,
  `∃ U, U nonempty ∧ IsIso (π ∣_ U)`: ok.
- Y_K = Spec L induced by π → `eY` with snd normalized and `eY ≫ fst ≫ π = eT ≫ fst`; together these say
  `eY ≫ (Y_K → T_K) = eT`, so the induced map is the iso: ok. f → `Spec ι ≫ eY ≫ fst`: ok.
- P = B ×_S ∏ Y_j, Y_j with map h_j v → wide-pullback cone, legs `uB` and `π ≫ r ≫ h_j`, `Nonempty (IsLimit D)`: ok.
- P projective over k → `IsHProjective (D.base ≫ ρS)`: ok.
- q_B = η_B, q_j = f d_{j⁻¹} → the two q-equations (`(σ j⁻¹).symm`): ok.
- action, p_B g_P = a_g p_B, p_{gj} g_P = p_j, over h_g, semilinear → the four A-equations; I checked they are
  mutually consistent (base ∘ g_P = h_{gj} v p_j = h_g base) and compose to an action: ok.
- q equivariant → `q ≫ A g = d_g ≫ q`; consistent: p_{gj} q d_g = f d_{j⁻¹g⁻¹} d_g = f d_{j⁻¹}: ok.
- C reduced induced closure of q(*) → `IsIntegral C`, `IsClosedImmersion i`, ker = vanishingIdeal of the
  closure, range = closure; by the uniqueness clause of lem-weil-pbc-reduced-induced-closed-subscheme this is
  that subscheme up to its unique isomorphism: ok. C projective finite type → three properties of `i ≫ base ≫ ρS`: ok.
- action restricts, p = u p_B i equivariant (p = `i ≫ D.base` by the cone relation) → `AC` equations: ok.
- C_K ≅ Spec M, k(C) = M induced by q and compatible with actions → `qC ≫ i = q`, qC equivariance,
  `qC = Spec eC ≫ fromSpecStalk`, `eCK` fst = qC and snd = Spec(K → M): ok, all identifications pinned.
- c = p_1 i, v c = p, r π c = p → `c = i ≫ D.π (some 1)`, `c ≫ π ≫ r = i ≫ D.base`, `c ≫ ρY = …`: ok.
- no action on T, Y assumed: none appears: ok.

Edge cases: J trivial (then P = B ×_S Y, the single factor `some 1`); nonfaithful actions; M = L = K;
inseparable M/K (no separability assumed); zero-dimensional schemes (IsHProjective allows ℙ^0).
Universes: all schemes and fields in u (needed for `Spec`), J in independent v; no restriction.

Records: `lean.statement` is verbatim the file's signature; only the item's `lean` field changes; the 13
stmt_deps are all used through their recorded declarations; module/blueprint docstrings and an 11-step proof
docstring are present; whole proof `sorry`; no definitions, hence nothing hollow. Searches: `rg` for
`conjugate_projective_generic|ConjugateProjectiveGeneric` in the live lean/ trees: no other declaration.
No mismatch found.

## Worker report

The module `Sheaf.AlgebraicGeometry.SemilinearTranslatedModificationProduct` states
`AlgebraicGeometry.exists_semilinear_translated_modification_product`, with proof `sorry`.
There are no definitions, auxiliary theorems, new nodes, dependency repairs, or statement
corrections. The declaration docstring contains the node's complete eight-step proof plan.

Hypotheses and their Lean renderings, checked against the node:

- The field and its spectrum are `(k : Type u) [Field k]` and `Spec (.of k)`.
  Schemes are `(X Y : Scheme.{u})`, with the specified structure map
  `(f : X ⟶ Spec (.of k))`.
- The finite group is `(H : Type v) [Group H] [Finite H]`; its universe is independent
  of the scheme universe. A group is necessarily nonempty, including the trivial group.
- The compatible field action is `(rho : H →* (k ≃+* k))`; the scheme action is
  `(a : H →* Aut X)`. The left-action identity and multiplication laws are encoded
  by these monoid homomorphisms. `CategoryTheory.Aut` multiplication is reverse
  categorical composition, i.e. composition in the function order used in the node.
- The base action `b_h` is the explicit term
  `Spec.map (CommRingCat.ofHom (rho h⁻¹).toRingHom)`. Thus inverse field automorphisms
  are used exactly as requested; a separate name or independently chosen base action
  would contain no further data. `ha` is exactly `f a_h = b_h f`.
- The modification map is `(π : Y ⟶ X)`, the dense open is `(U₀ : X.Opens)` with
  `hU₀ : Dense (U₀ : Set X)`, and `hπ : IsIso (π ∣_ U₀)` asserts that its restriction
  over this open is an isomorphism. No properness or integrality is assumed.
- The integer `n ≥ 0` is `n : ℕ`. The specified embedding is `i`, with
  `[IsClosedImmersion i]` and `hi` asserting that its composite with projective space's
  structure morphism is `π ≫ f`. The homogeneous coordinate type is
  `ULift.{u} (Fin (n + 1))`, a universe-compatible copy of exactly `n+1` coordinates.
  This is the upstream `ProjectiveSpace` construction, not a second notion of projectivity.

Every conclusion of the node and its rendering:

- Each underlying `Y_g` is the original `Y`; its map `q_g` is `π ≫ (a g).hom`,
  and `p_g` is its composite with `f`. Their equality with the base-translated maps
  follows from `ha`. The first conjunct quantifies over every `g` and supplies
  `ig` with `IsClosedImmersion ig` and the exact structural equation into the same
  `ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec (.of k))`.
- The finite fibre product is supplied as
  `c : WidePullbackCone (fun g : H ↦ π ≫ (a g).hom)` with
  `Nonempty (IsLimit c)`. Its scheme is `c.pt`, its base map `c.base`, and its
  projections are `c.π g`. A cone already includes `c.π g ≫ q_g = c.base`;
  `IsLimit` is the full universal property. This existential statement includes
  existence of the product, rather than assuming it as a new hypothesis. It does not
  choose any data from a sorry theorem in a definition.
- The open `U : X.Opens` has the exact equality
  `(U : Set X) = ⋂ g : H, (a g).hom '' (U₀ : Set X)`. Its openness is built into
  `X.Opens`, its density is the next conjunct, and its invariance is the image equality
  for every `h`.
- The left action is `A : H →* Aut c.pt`. The next conjunct is precisely
  `(A h).hom ≫ c.π g = c.π (h⁻¹ * g)`. The following quantified conjunct says any
  scheme endomorphism `t` satisfying all those projection equations equals `(A h).hom`;
  hence uniqueness holds even among all scheme morphisms, as in the node.
- The action identities `A_1 = 1` and `A_h A_l = A_(hl)` and invertibility of every
  element are carried by the monoid homomorphism into `Aut c.pt`.
- Equivariance over `X` is `(A h).hom ≫ c.base = c.base ≫ (a h).hom`.
  Semilinearity over `Spec k` is the immediately following equation using the same
  inverse field automorphism as `ha`.
- `aU : H →* Aut U.toScheme` is the restriction action; its equation
  `(aU h).hom ≫ U.ι = U.ι ≫ (a h).hom` specifies exactly the restricted scheme
  automorphism, uniquely since `U.ι` is an open immersion and a monomorphism.
- The isomorphism over `U` is `e : pullback c.base U.ι ≅ U.toScheme` together with
  `e.hom = pullback.snd c.base U.ι`. Thus it is the particular projection asserted
  by the node, not an unspecified isomorphism between those schemes.
- The inverse defines `j` by `e.inv ≫ pullback.fst c.base U.ι = j`.
  The remaining conjuncts give `IsOpenImmersion j`, `j ≫ c.base = U.ι`, and
  `j ≫ (A h).hom = (aU h).hom ≫ j` for every `h`, exactly the final three claims.

Dependency declarations read in full, including their docstrings:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec`, `AlgebraicGeometry.Spec.map`
  (def-pc-scheme and def-weil-affine-spectrum).
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  (def-weil-open-immersion), and
  `AlgebraicGeometry.MorphismProperty.isOpenImmersion_stableUnderBaseChange`
  (lem-weil-pbc-open-immersion-base-change, proof dependency).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (def-weil-closed-immersion).
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective` (def-kun-projective), read to verify the
  finite-projective-space embedding convention. The present statement retains a specified
  `n` and embedding, using the more precise data requested by the item rather than the
  existential class. This module publicly imports the actual projective-space construction.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`:
  `AlgebraicGeometry.ProjectiveSpace` and its `CanonicallyOver` structure morphism
  (def-nagata-projective-space-base-change, proof dependency).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`, and `pullback.lift`
  (def-pc-fibre-product). The actual base-changed map is the canonical binary pullback.
- `Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks`:
  `WidePullbackCone`, `WidePullbackCone.base`, `WidePullbackCone.π`, and `IsLimit`
  give the iterated fibre-product universal property without a private copy of a notion.
- `Mathlib.CategoryTheory.Endomorphism`: `Aut`, its group instance and `Aut_mul_def`
  fix the left-action composition convention.

Source checks: read Stacks `morphisms.tex`, lemma-H-projective-base-change (Tag 01WF),
`constructions.tex`, definition-projective-space (Tag 01NF), and the current blueprint
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`. As the node itself records, the current
blueprint paragraph does not state this agent-explicit finite-translate prerequisite;
its eight proof steps provide the exact construction being stated here.

Edge cases checked before writing: empty `X` and `Y` are allowed, and density is vacuous
on the empty space. For `n=0` there is one coordinate, not an empty coordinate type.
The trivial group gives one factor and `U=U₀`. A nonfaithful or trivial action is allowed
on either field or scheme. No assumption excludes positive characteristic, inseparability,
non-Noetherian schemes, or reducible schemes. The original dense open need not be invariant;
its finite intersection of translates is the precise conclusion. The finite index type
may inhabit any universe `v` because the limiting cone is existentially stated, without
requiring a large-index limit instance for schemes. There are no automatic implicit binders,
file-local notation, local instances or hidden `let` binders.

Searches for an existing statement (all wrapper searches were run and logged):

- `msearch.py ... leanfinder`, query “Finite semilinear group action permuting translated
  scheme factors of a fibre product and its invariant dense isomorphism open”: eight
  Galois-category action results; none states this scheme construction.
- `msearch.py ... leansearch`, query “A finite group acting semilinearly on a scheme acts
  by permutations on the fibre product of all translates of a modification, with a dense
  invariant isomorphism open”: eight hits about actions on sets and permutation groups;
  none supplies the scheme, embeddings or isomorphism-open conclusions.
- `msearch.py ... loogle`, query
  `CategoryTheory.Limits.widePullback, AlgebraicGeometry.Scheme.Hom.restrict`:
  no hits; the second name is unknown. Read the actual restriction notation and
  `WidePullbackCone` sources instead.
- `msearch.py ... grep`, query `widePullback|semilinear`, subdirectory `AlgebraicGeometry`:
  four structure-sheaf semilinear-map hits, no match.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `semilinear.*(product|modification)|translatedModification|translated_modification|widePullback`
  found general wide-pullback maps and the parent equivariant Chow theorem, but no
  declaration stating this item. The parent has stronger hypotheses and different
  conclusions, and cannot replace the finite-translate construction.
- Direct `grep -rn` of `lean/WeilConjectures` for the item id found no declaration.
  Search of `dag/lean_names_upstream.json` found no corresponding name.

No node fault or STATEMENT-DISPUTED issue was found. Compilation with the prescribed
`scompile.py` passed separately in sandbox and final-module modes, with no errors or
unexpected warnings (1.5 s and 1.8 s reported).

## Second reading by NC

This reading was written by the maintainer's independent stage-2 reviewer. The delivered
section was the author's own recheck, so the reviewer replaced it with this section. The Lean
module and the node record are unchanged.

Node statement, clause by clause, with its Lean rendering and verdict:

1. Field `k` and `S = Spec k`: `(k : Type u) [Field k]`, `Spec (.of k)`. Correct.
2. Morphism `f : X → S`: `(f : X ⟶ Spec (.of k))`, with `X Y : Scheme.{u}`. Correct.
3. Finite group `H`: `(H : Type v) [Group H] [Finite H]`. A group is never empty, so the
   index set of the product is never empty. Correct.
4. Left actions `a_h` and `b_h`, with `b_h` induced by inverse field automorphisms. The
   rendering is `a : H →* Aut X`; `Aut_mul_def` gives `(f*g).hom = g.hom ≫ f.hom`, which is the
   function composition `f∘g`, so this is a left action with `a_1 = 1`. Write
   `b_h = Spec.map (rho h⁻¹)`. `RingEquiv.mul_apply` and the contravariance of `Spec.map` give
   `b_l ≫ b_h = Spec.map(ρ(l⁻¹)∘ρ(h⁻¹)) = Spec.map(ρ((hl)⁻¹)) = b_{hl}`, and `b_1 = 1`.
   `ha` says `a_h ≫ f = f ≫ b_h`, which is `f a_h = b_h f`. Correct. The node itself says the
   `b_h` come from an action on `k`, so `rho` adds no assumption.
5. `π` is an isomorphism over a dense open `U₀`: `(U₀ : X.Opens)`, `Dense`, and
   `IsIso (π ∣_ U₀)`, where `π⁻¹U₀ → U₀` is the restriction. Correct.
6. A closed immersion `i : Y → P^n_S` over `S` with `n ≥ 0`: `n : ℕ`, together with
   `i : Y ⟶ ℙ(ULift (Fin (n+1)); Spec k)`, `[IsClosedImmersion i]` and `hi : i ≫ ↘ = π ≫ f`.
   This is the H-projective convention of def-kun-projective, with `n+1` homogeneous
   coordinates, so `n = 0` is included. The explicit embedding is needed because the
   conclusion embeds each `p_g` in the same `P^n_S`. Correct.
7. Conclusion: each `p_g = π ≫ a_g ≫ f` has a closed immersion into the same projective space
   over `S`. Correct.
8. `P = ∏_{g,X} Y_g`, with `q_g = π ≫ a_g`, `r` and `ρ_g`: `c : WidePullbackCone (fun g ↦ π ≫ (a g).hom)`
   with `Nonempty (IsLimit c)`. All the following clauses are invariant under the unique
   isomorphism of limit cones, so the existential form is equivalent to the statement for
   any chosen product. Correct.
9. `U = ⋂ a_g(U₀)` is a dense `H`-invariant open: an exact set equality, `Dense`, and
   `a_h '' U = U`. Correct.
10. The action `A_h` with `ρ_g A_h = ρ_{h⁻¹g}`, unique, satisfying `A_hA_l = A_{hl}` and `A_1 = 1`:
    `A : H →* Aut c.pt` gives the action laws and invertibility, and the next clause is the
    projection equation. The uniqueness clause ranges over all endomorphisms. Correct.
11. `rA_h = a_hr` and `frA_h = b_hfr`: both are stated, the second with the same `b_h` as in
    `ha`. Correct.
12. `P ×_X U → U` is an isomorphism: `e : pullback c.base U.ι ≅ U` with `e.hom = pullback.snd`,
    so the isomorphism is the projection itself and not an arbitrary one. Correct.
13. `j` is defined by the inverse, `rj = u`, `j` is an open immersion, and `A_hj = j(a_h|_U)`:
    `e.inv ≫ fst = j`, `IsOpenImmersion j`, `j ≫ c.base = U.ι` and
    `j ≫ A_h = aU_h ≫ j`. Here `aU` is determined by `aU_h ≫ U.ι = U.ι ≫ a_h`, because `U.ι`
    is a monomorphism, so it is the restricted action. Correct.

The reviewer checked the mathematics of the last clause. We have
`ρ_g A_h j = s_{h⁻¹g} = s_0 a_{g⁻¹h} u` and
`ρ_g j a_h|_U = s_0 a_{g⁻¹} u a_h|_U = s_0 a_{g⁻¹h} u`. Both maps lie over `a_h u`, so they agree.

Edge cases:
- The trivial group gives a single factor, and then `U = U₀`.
- Empty `X` or `Y` is allowed.
- `n = 0` gives one coordinate.
- Non-faithful actions are allowed, and so is any characteristic.
- The universe `v` of `H` is independent of `u`. This is possible because the cone is
  existential.

No assumption beyond the node's is present.

Searches: the logged node searches, and an `rg` of the project's `lean/Sheaf` and
`lean/WeilConjectures` for `TranslatedModification` and `WidePullbackCone (fun`. They found
only Čech/pro-étale wide pullbacks and the parent
`exists_semilinear_equivariant_chow_modification`, which has different hypotheses and
conclusions. No duplicate exists (H4).

Dependency declarations read: `IsHProjective` (WeilConjectures/AlgebraicGeometry/Morphisms/Projective.lean),
`ProjectiveSpace` and its `CanonicallyOver` instance (ProjectiveSpace.lean:130),
`WidePullbackCone` with `.π`/`.base`/`condition` (Mathlib WidePullbacks.lean:388),
`Aut_mul_def` and `RingEquiv.mul_apply`.

Advisory: `ProjectiveSpace` is owned by def-nagata-projective-space-base-change. That node is
a proof dependency here. It reaches the statement through def-kun-projective, whose
statement defines `P^N_Y` as that node's object. There is a precedent of the same form.

Pilot gates:
- No definitions.
- The proof is `sorry` only.
- The module and the theorem docstrings give the source place and
  `(blueprint: lem-sfb-semilinear-translated-modification-product)`, and the theorem
  docstring carries the eight proof steps.
- `lean.statement` is verbatim in the file.
- No dependency records were changed.
- No pro-étale substitute.

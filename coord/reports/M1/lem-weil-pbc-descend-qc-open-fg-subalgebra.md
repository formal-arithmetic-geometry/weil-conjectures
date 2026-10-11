## Worker report

The module defines and states `AlgebraicGeometry.descend_qc_open_fg_subalgebra` in `lean/Sheaf/AlgebraicGeometry/DescendQCOpenFGSubalgebra.lean`. It formalizes Tag 0388: for a field `k`, a `k`-scheme `X` represented by `f : X ⟶ Spec k`, a commutative `k`-algebra `A`, and a quasi-compact open `V` of the pullback `X_A`, there is a finitely generated `k`-subalgebra `A'`, a quasi-compact open `V'` of `X_{A'}`, and the canonical base-change map `π : X_A ⟶ X_{A'}` induced by `Subalgebra.val A'`, with `V = π ⁻¹ᵁ V'`. The theorem proof is `sorry` as required for stage 2.

The hypotheses and clauses are rendered as follows. `k : Type u` with `[Field k]` is the base field; `X : Scheme.{u}` and `f : X ⟶ Spec (CommRingCat.of k)` are the scheme over `k`; `A : Type u` with `[CommRing A] [Algebra k A]` is the commutative `k`-algebra. `V` is an element of the `Opens` of `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))`, and `IsCompact V.1` expresses quasi-compactness of the open. The conclusion quantifies `A' : Subalgebra k A` with `A'.FG`, then `V'` in the corresponding pullback opens with `IsCompact V'.1`. It quantifies `π` between the two pullbacks and equates it to `baseChangeMap f` applied to the `Over.homMk` of `Spec.map (Subalgebra.val A')`; the displayed compatibility proof is the contravariant functoriality of `Spec` and the algebra-map identity. Finally `V = (π ⁻¹ᵁ V')` is equality of open subsets.

The dependency declarations used are the standard scheme, base-change, and affine-spectrum notions recorded by the node: `def-weil-scheme-over-base` (the source repository's `Scheme`/structure-map convention), `def-pc-base-change` (the pullback/base-change convention), and `def-weil-affine-spectrum` (`AlgebraicGeometry.Spec` and `Spec.map`). The module imports `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` for the topology and `WeilConjectures.AlgebraicGeometry.PicardFunctor` for `baseChangeMap`.

Edge cases checked against the statement: `V = ⊥` (empty open) is allowed by `IsCompact V.1`; `A' = ⊥` is permitted when the descended open is empty; `A' = ⊤` handles the case `A` itself is finitely generated; and `A = k` gives the identity base change. No separatedness or quasi-separatedness assumptions occur.

Searches made: `msearch.py leanfinder` for “quasi-compact open subset of base change of scheme to a k-algebra A descends to finitely generated subalgebra” returned only unrelated compactness results; `msearch.py loogle` for `AlgebraicGeometry.exists_preimage_eq` and related open-descent names found no exact statement; grep over Mathlib `AlgebraicGeometry/AffineTransitionLimit.lean` found `AlgebraicGeometry.exists_preimage_eq` (Tag 01Z4), which is a related affine-transition-limit theorem but requires an additional limit identification and is not this statement. `rg` over the project and source found no existing declaration of this node or an exact specialization.

## Earlier second reading (a previous round; superseded)

Re-read the source statement and the Lean signature clause by clause. The field, scheme-over-field map, algebra, quasi-compact open, finitely generated subalgebra, descended open, canonical `Spec` map, and pullback equality are all present; no separatedness or quasi-separatedness hypothesis was added. The module compiles on the server with only the expected `sorry` declaration warning.

## Second reading by M1

I independently opened the item JSON, its Lean module, all three statement-dependency nodes,
the recorded Mathlib/source declarations, and the landed `BaseChangeConventions.lean`.
The local literature checkout is absent, so I read the server's Stacks `varieties.tex`
lines 780–855 over SSH, including the complete statement and proof of
`lemma-descend-open` (Tag 0388). It introduces its own field and scheme and imposes no
standing finite-type, separatedness, or quasi-separatedness assumption. The node agrees
with that source; there is no statement correction or `statement_change` to review.

The node's objects, hypotheses, and conclusion clauses, in order, match as follows:

1. A field `k`: `(k : Type u) [Field k]`. Exact, with no characteristic condition.
2. A scheme `X` over `k`: `(X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))`.
   Exact structure-morphism data of `def-weil-scheme-over-base`. I read
   `Scheme.Over` and `Scheme.Hom.isOver_iff` in Mathlib `AlgebraicGeometry/Over.lean`;
   an explicit structure morphism is the same data and is appropriate here because
   the existing `baseChangeMap` takes it. No additional geometric property of `X`.
3. A commutative `k`-algebra `A`: `(A : Type u) [CommRing A] [Algebra k A]`.
   Exact; neither finite generation nor nontriviality of `A` is assumed.
4. `X_A = X ×_Spec(k) Spec(A)` and `X_{A'}`: respectively
   `pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))` and the same expression
   with `A'`. Exact. The dependency `def-pc-base-change` records this very notation
   in `Sheaf.AlgebraicGeometry.BaseChangeConventions`; its primary declaration
   `moduleBaseChange` is module base change and is not mistakenly used as scheme base
   change. The needed scheme construction is the existing categorical `pullback`.
5. A quasi-compact open `V` of `X_A`: `∀ (V : (...).Opens), IsCompact V.1 → ...`.
   Exact: `Opens` supplies openness, and Lean's `IsCompact` requires no Hausdorff
   assumption, so it expresses quasi-compactness in the Zariski topology.
6. A `k`-subalgebra `A' ⊆ A`, finitely generated as a `k`-algebra:
   `∃ (A' : Subalgebra k A), A'.FG ∧ ...`. Exact. I also read
   `Subalgebra.fg_iff_finiteType` in Mathlib `RingTheory/FiniteType.lean:197`;
   this is algebra generation, not finite generation as a module.
7. A quasi-compact open `V'` of `X_{A'}`:
   `∃ (V' : (...).Opens), IsCompact V'.1 ∧ ...`. Exact, depending on the chosen `A'`.
8. The canonical morphism `π = id_X × Spec(A' ↪ A)`:
   the existential `π` is constrained by equality to `baseChangeMap f` of the
   `Over.homMk` of `Spec.map (CommRingCat.ofHom (Subalgebra.val A'))`.
   Exact, not an arbitrary morphism. I read `Spec` and `Spec.map` in Mathlib
   `AlgebraicGeometry/Scheme.lean:470,479`, and `baseChangeMap` in upstream
   `AlgebraicGeometry/PicardFunctor.lean:296`: it is `pullback.map` with `𝟙 X`,
   the given morphism of bases, and `𝟙 S`. The inline proof only verifies the
   structure-map commutativity from contravariance of `Spec`; it introduces
   no extra hypothesis or postponed proof.
9. The equality `V = π⁻¹(V')`: `V = (π ⁻¹ᵁ V')`. Exact equality of opens,
   hence equality of underlying subsets, with quantifiers in the required order.

Edge cases: `V = ⊥` and the empty scheme are included, with an empty family of principal
opens and zero generators (`n = 0`); `A' = ⊥` and `V' = ⊥` are admissible. The zero
commutative algebra `A` is included: there is no `Nontrivial A` assumption and its
spectrum is empty. `A = k` and finitely generated `A` are included. All field
characteristics are allowed. `u` is explicitly declared and arbitrary, matching
Mathlib's single-universe category of schemes and the recorded `baseChangeMap`;
any set-sized collection of the field, algebra and scheme data fits in a common
universe. No implicit object, universe, or instance is unbound. There is no index-set
binder whose nonemptiness could exclude the empty-cover case.

Independent searches on 2026-10-11:

- LeanFinder via `msearch.py`: “a compact open in a scalar extension of a scheme
  descends to a finite type subalgebra”. Eight hits including `isCompact_iff_exists`,
  the compact-open finite-basic-open characterization, and finite spectrum maps;
  no exact open-descent statement.
- Loogle via `msearch.py`: `"exists_preimage_eq"`. Found
  `AlgebraicGeometry.exists_preimage_eq`; I opened its signature in Mathlib
  `AlgebraicGeometry/AffineTransitionLimit.lean:341`. It needs a cofiltered diagram,
  affine transition maps, and an identified limit cone. It is a general ingredient,
  not this field/algebra specialization without constructing that diagram and limit.
- LeanSearch via `msearch.py`: “A quasi compact open of X base changed to an algebra A
  is inverse image of an open over a finitely generated subalgebra of A”. The service
  returned Internal Server Error; recorded as unavailable, not a negative result.
- `msearch.py grep` for `0388|descend.*open|exists_preimage_eq` in Mathlib
  `AlgebraicGeometry`, and direct `rg` using those terms and
  `descend.*[Ss]ubalgebra` in upstream `WeilConjectures`, repository `lean/Sheaf`,
  and `dag/lean_names_upstream.json`. No exact declaration or name collision.
  I also opened upstream `exists_descendsAtWithOpen` and its `DescendsAtWithOpen`
  definition in `WeilConjectures/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`:
  they require a finite-presentation model that is quasi-compact and quasi-separated,
  unlike the arbitrary `X` here, so are not an existing realization of this node.

Found and repaired H8/H9 documentation omissions: added the standard copyright header
and the missing source/blueprint module docstring; expanded the theorem docstring to
carry all four node proof steps and both proof-dependency names. In particular it
retains the source's warning that `V ∩ U_{i,A}` need not be quasi-compact. The theorem
signature is unchanged; the node's `lean.statement` now records its exact multiline
text rather than whitespace-normalized text. No new definition nodes or dependency
modules are needed, no private or hollow definitions occur, and the sole theorem
remains `:= by sorry` as stage 2 requires.

Validation: `scompile.py M1 lem-weil-pbc-descend-qc-open-fg-subalgebra` on the delivered
module returned exit code 0 (compiled in 1.8 seconds), with no errors or warnings.
All Lean lines are at most 100 characters. Both imports are used: the quasi-compact
scheme API and the existing canonical `baseChangeMap`.

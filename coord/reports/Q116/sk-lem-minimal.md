## Worker report

The node is recorded as an exact existing declaration, so no Lean module is written. The source module is `WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`; its declarations are `AlgebraicGeometry.Scheme.IsQcqsLocalProperty` and `AlgebraicGeometry.exists_spec_field_of_isQcqsLocalProperty`.

The target's `T` is rendered by `(T : Scheme.{u})` with `[CompactSpace T]` and `[QuasiSeparatedSpace T]`, which are the qcqs hypotheses. The property `P` is rendered as
`P : ⦃T' : Scheme.{u}⦄ → (T' ⟶ T) → Prop`, the predicate on schemes over `T`.
The four numbered hypotheses are exactly the four fields of
`T.IsQcqsLocalProperty P`: `invariant_under_thickening`,
`compatible_with_cofilteredLimit`, `of_opens_or_closedComplement`, and
`not_of_isEmpty`. The conclusion is exactly
`∃ (K : Type u) (_ : Field K) (g : Spec (CommRingCat.of K) ⟶ T), P g`.
Thus the field and the morphism `Spec K → T` are both present with the same
universe and the same predicate conclusion. No extra hypothesis or conclusion is introduced.

The recorded statement dependency `sk-def-bc` is the base-change property used by later applications of this generic lemma; the existing minimal-counterexample declaration itself is independent of the coefficient/base-change definitions, so no additional import or duplicate declaration is needed.

I read the complete source declaration and docstrings in
`/home/ubuntu/weil-src-slopmaster2/WeilConjectures/Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean` (the structure at lines 4615–4640 and the theorem at lines 4745–4892), and refreshed the module with `scompile.py --source`. The theorem docstring identifies blueprint `sk-lem-minimal` and explains the Zorn/minimal-closed-subscheme argument. Its statement is sorry-free in the source.

Edge cases checked: `P` may be any predicate, including one that holds only on a point; the empty-scheme failure is explicitly required by `not_of_isEmpty`; `q` and coefficient data from `sk-def-bc` are irrelevant to this generic lemma; arbitrary universe `u` is retained; and the identity morphism `𝟙 T` is the exact premise used by the theorem. The theorem permits empty or nonempty `T` exactly as the node does, subject only to the stated qcqs and property hypotheses.

Searches made on 2026-10-17:

- `msearch.py leanfinder "minimal counterexample qcqs local property exists spectrum field"`: eight generic Mathlib hits and no exact declaration in the LeanFinder index.
- `msearch.py loogle "exists_spec_field_of_isQcqsLocalProperty, IsQcqsLocalProperty"`: zero hits (`unknown identifier` for the source-only declaration).
- `msearch.py grep "exists_spec_field_of_isQcqsLocalProperty|IsQcqsLocalProperty" WeilConjectures/Mathlib/AlgebraicGeometry`: the search wrapper returned no indexed hits; direct `rg` in the read-only source found the exact structure and theorem in `AffineTransitionLimit.lean`.
- Direct `rg` over `WeilConjectures/`, project `lean/Sheaf`, and `dag/nodes` found no competing project declaration; the only exact source declaration is the one recorded here.

No statement dispute, correction, new node, or dependency repair is needed.

## Earlier second reading (a previous round; superseded)

I independently compared the node text with the source structure and theorem. Clause (1) is `invariant_under_thickening`, including closed immersion and surjectivity on points. Clause (2) is `compatible_with_cofilteredLimit`, including a cofiltered category, affine transition morphisms, qcqs stages, and a limit cone. Clause (3) is `of_opens_or_closedComplement`, including a quasi-compact open and a closed complement. Clause (4) is `not_of_isEmpty`. The source theorem then assumes `P (𝟙 T)` and returns a field `K : Type u`, a `Field K` instance, and `g : Spec (CommRingCat.of K) ⟶ T` with `P g`. Every hypothesis and conclusion in the node is represented, and no mismatch was found.

## Second reading by Q116

Independent second reader, 2026-10-17. I opened the sandbox node, its exact blueprint source
`literature/blueprint/main-20261015/blueprint/sec-smooth-base-change/sk-lem-minimal/_section.md`,
the recorded upstream structure and theorem, and the source returned by
`scompile.py --source WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`.
The current source has the structure at line 4638 and theorem at line 4768; their signatures
agree with the local read-only source despite shifted line numbers. There is no repair note
for this item and no `statement_change` to audit.

My object/hypothesis/conclusion inventory and comparison follows. All fields named below
belong to `AlgebraicGeometry.Scheme.IsQcqsLocalProperty`.

1. Base: a qcqs scheme `T`. Lean: `(T : Scheme.{u}) [CompactSpace T]
   [QuasiSeparatedSpace T]`. PASS: these are absolute quasi-compactness and
   quasi-separatedness, with no Noetherian, separatedness, or base-field assumption.
2. Property: `P` of qcqs schemes over this fixed `T`. Lean:
   `(P : ⦃T' : Scheme.{u}⦄ → (T' ⟶ T) → Prop)`. PASS: a morphism encodes the
   structure over `T`; composition supplies its restriction to another scheme. Although
   the predicate is defined on every scheme, the stability conditions test qcqs schemes;
   its values outside that domain impose no additional requirement.
3. Thickening invariance: condition (1). Lean: `invariant_under_thickening` quantifies
   over `i : T₁ ⟶ T₂` with `[IsClosedImmersion i]` and `Function.Surjective i.base`,
   and every `f₂ : T₂ ⟶ T`, concluding `P (i ≫ f₂) ↔ P f₂`. PASS: a surjective
   closed immersion is precisely a thickening, not merely a finite-order thickening.
   Only `T₂` needs explicit qcqs instances: its closed subscheme `T₁` is qcqs as well.
4. Limit compatibility: condition (2). Lean: `compatible_with_cofilteredLimit` takes
   `{I : Type u} [Category.{u} I] [IsCofiltered I]`, `D : I ⥤ Over T`, affine transition
   morphisms, qcqs stages, and a cone whose underlying scheme cone is limiting. Its
   conclusion is `(∀ i, P (D.obj i).hom) → P c.pt.hom`. PASS: no stagewise implication
   is reversed and no arbitrary replacement for the limit is used. The limit is qcqs
   for such diagrams. The index universe follows the project's scheme-limit convention.
5. Closed/open alternative: condition (3). Lean: `of_opens_or_closedComplement` takes a
   qcqs `T'`, `f : T' ⟶ T`, `V : T'.Opens`, `IsCompact (V : Set T')`, and any closed
   immersion `i : Z ⟶ T'` with `Set.range i.base = (V : Set T')ᶜ`. It concludes
   `P f → P (V.ι ≫ f) ∨ P (i ≫ f)`. PASS: every closed subscheme structure on the
   complement is admitted; no reducedness or extra condition on `f` is assumed.
6. Empty scheme: condition (4). Lean: `not_of_isEmpty` says
   `∀ {T'} (f : T' ⟶ T), IsEmpty T' → ¬ P f`. PASS: it covers every presentation of
   the empty scheme, not just one selected initial object.
7. Starting premise: `P(T)`. Lean: `(hP : P (𝟙 T))`. PASS: this is exactly `T` as an
   object over itself, and is a premise after the four property conditions.
8. Conclusion: a field `K`, a morphism `Spec K → T`, and `P` for that morphism. Lean:
   `∃ (K : Type u) (_ : Field K) (g : Spec (CommRingCat.of K) ⟶ T), P g`.
   PASS: all three existential data and their order match, without a prescribed field,
   algebraic closure, characteristic, or stronger condition on `g`.

Source check: Stacks `etale-cohomology.tex`, `lemma-formal-argument` (Tag 0F06),
lines 17041–17078, introduces its own arbitrary qcqs base and property; it does not
inherit the coefficient/invertibility or `q ≥ 1` assumptions of the surrounding lemmas.
Its conditions (1)–(3) are exactly the first three fields. The archived Stacks text omits
the empty-scheme condition; the item's actual blueprint explicitly includes condition (4),
as does the recorded Lean. This prevents, for example, the empty base with an always-true
property from contradicting the conclusion. No correction of the item's statement is needed.
I also read `more-morphisms.tex`, `definition-thickening`, which defines a thickening as a
closed subscheme with the same underlying topological space; this verifies item 3 above.

Dependency check: I opened `sk-def-bc` and
`WeilConjectures/SixFunctors/Etale/SmoothBaseChange/Defs.lean`, including
`Etale.baseChangeHomologyMap`, `Etale.BaseChangeProperty`, and
`Etale.UniversalBaseChangeProperty`, with their coefficient and scheme binders. They encode
the application to base-change failure; none appears in this generic theorem's signature.
Consequently no coefficient ring, degree, smoothness, or invertibility assumption should
be imported into this statement. There are no new nodes or dependency modules to review.

Edge cases: if `T` is empty, condition (4) contradicts `hP`, so no impossible field-valued
point is asserted from consistent premises. Empty `V` and empty `Z` are both allowed in
condition (3), with the disjunction reducing as condition (4) requires. Empty stages and
empty limits are not silently excluded; condition (4) forces the corresponding `P` to fail.
An inverse system here is nonempty/cofiltered; an empty diagram is not such an inverse
system and is correctly excluded by `IsCofiltered`. A zero-ring spectrum is empty and is
handled by the same clause. `n = 0`, cohomological degree, and coefficient zero objects
are not parameters of this generic statement. The universe `u` is arbitrary, including
`u = 0`; `K : Type u` and `Scheme.{u}` have matching sizes. No independent test universe
makes a stability hypothesis vacuous. A residue field of an affine chart already has this
size. All variables and universes in the existing declaration are bound.

Independent searches, using different conceptual terms from the first report:

- `msearch.py Q116 sk-lem-minimal leanfinder "scheme property invariant thickening inverse
  limit closed complement spectrum field"`: eight Mathlib candidates, including affine
  reduction and nonempty inverse-limit results; none is this four-condition theorem.
- `msearch.py Q116 sk-lem-minimal loogle '"spec_field"'`: zero hits. An earlier exploratory
  query with three name fragments returned a parse error and was not used as evidence.
- `msearch.py Q116 sk-lem-minimal grep
  "formal.argument|thickening.*property|field.*qcqs|IsQcqsLocalProperty"`: one unrelated
  measure-theory hit in the index. Direct `rg` over Mathlib, upstream `WeilConjectures`,
  and project `lean/Sheaf` found the exact upstream structure/theorem and their consumers,
  with no competing Mathlib or project definition.
- Direct DAG search also found `sbc-lem-bc-minimal-counterexample`. I opened it: it already
  binds the same upstream theorem. Reusing that very declaration here respects H4 and
  introduces no second definition.

H5/H6/H8/H9: no module, definition, or proof is added. The existing theorem's source
docstring identifies `sk-lem-minimal`, cites Stacks 0F06 via its attribute, and describes
Zorn, the closed-complement contradiction, affine neighborhoods, localization at a minimal
prime, and the final thickening to a residue field. This is the node's proof, with the
localization/residue-field argument implementing the generic-point step. The existing
proof is reused rather than rewritten. A programmatic comparison confirmed
`lean.statement` is verbatim the current source signature, excluding `:= by`.

Validation: the scratch-only `ReviewProbe.lean` imports the recorded module, checks the
structure, all four projections and theorem, and prints the theorem's axioms. Compiled
with `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q116 sk-lem-minimal
<sandbox>/scratchpad/ReviewProbe.lean`: exit 0, no warnings or errors, and axioms exactly
`propext`, `Classical.choice`, `Quot.sound`. The probe is not a delivered library module;
there are no delivered `.lean` files because the match is `existing: true`.

Mismatches found: none in the node-to-Lean binding. Changes: appended this independent
source/dependency/clause/edge-case/search/validation review; left the correct node and
`## Worker report` intact. No statement dispute, correction, or dependency repair remains.

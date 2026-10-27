## Worker report

The module `Sheaf.CategoryTheory.AdjointProjectionTensorTransfer` states
`CategoryTheory.adjointProjectionTensorTransfer`, with its sole proof `by sorry`.
Three explicit helper definitions in namespace
`CategoryTheory.AdjointProjectionTensorTransfer` give the node's `q`, its
transferred projection expression `transferredQ`, and `h = r ∘ (1 ⊗ η)`.
These are the node's own displayed constructions, not additional notions;
none uses choice, a postponed existence theorem, or sorry data.
Only the item's `lean` field changes. No statement correction or dependency
repair is needed, and there are no new nodes or disputed statements.

The source was read in the current blueprint:
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-cohsm/lem-pur-co-smooth-etale-locality.proof.md`,
Step 1, and
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/thm-pur-composition-coherence.proof.md`,
Step 1 (remaining co-projection factors). The theorem docstring carries all
seven steps of the accepted DAG proof.

Hypothesis-by-hypothesis translation:

- The categories are `C : Type uC`, `D : Type uD`, with independent
  `[Category.{vC} C]`, `[Category.{vD} D]`. Their tensor and specified unitors
  are `[MonoidalCategory C]`, `[MonoidalCategory D]`. Both categories have
  `[SymmetricCategory ...]`; this includes naturality, the two hexagons and
  involutivity of `β_`. The stated unit equation is the existing consequence
  `braiding_leftUnitor` of the Mathlib braided-category axioms, not a further
  assumption. Thus the chosen symmetry is the one carried by these structures.
- `F S : C ⥤ D`, `G T : D ⥤ C` and the two actual adjunctions
  `aF : F ⊣ G`, `aS : S ⊣ T` provide precisely the node's units, counits
  (`aF.counit`, `aS.counit`) and natural Hom bijections (`homEquiv`).
- `d : F ≅ S` is the natural isomorphism; `u : T.obj (𝟙_ D) ≅ 𝟙_ C`
  is the specified isomorphism of unit objects.
- `P` and `p` have exactly the displayed objectwise isomorphism types.
  `hP` and `hp` state naturality in the two variables together, for every
  `f : M ⟶ M'`, `g : K ⟶ K'`. This is equivalent to naturality in each
  variable separately by taking one arrow to be an identity and composing.
  No unit or associativity coherence for these projection isomorphisms is added.
- `hd` is the projection compatibility square, in Lean order:
  `P.hom ≫ d.hom = (d.hom ⊗ₘ 𝟙 K) ≫ p.hom`.
- `hev` is exactly the assumed equation at `M = T(𝟙_ D)`;
  `S.map ((u.hom ⊗ₘ 𝟙 (T.obj K)) ≫ (λ_ (T.obj K)).hom)` is `S(a_K)`.
  There is no evaluation equation assumed at general `M`.
- No functor has a faithfulness, fullness, or monoidal-structure hypothesis.

Construction and conclusion-by-conclusion translation (Lean `≫` runs left
to right, opposite to the written order of mathematical `∘`):

- `ρ` is always the existing `conjugateEquiv aF aS d.inv`; there is no
  arbitrary comparison map binder. `W` is written `G.obj (𝟙_ D)` throughout.
  `η` is the composite of that conjugate's component at the unit and `u.hom`
  in the definition of `h`.
- `q` is explicitly `F.map β.hom ≫ P.inv ≫ (ε_1 ⊗ₘ 𝟙 K) ≫ λ.hom`,
  with source `F.obj (T.obj K ⊗ G.obj (𝟙_ D))` and target `K`.
  Every occurrence of `τ_K` in the theorem is its specified transpose
  `aF.homEquiv (T.obj K ⊗ G.obj (𝟙_ D)) K (q aF T P K)`.
- Conjunct 1 is `IsIso ρ`. Conjunct 2 is the counit characterization
  `d_GK ≫ S.map ρ_K ≫ ev_K = ε_K`. Conjunct 3 says any natural
  transformation `G ⟶ T` satisfying that characterization equals this `ρ`;
  it does not presume that the competing transformation is invertible.
- Conjunct 4 gives the Hom identity for every `N`, `K`, `b`, with
  `aS.homEquiv N K (d.inv.app N ≫ b)` on the left and
  `aF.homEquiv N K b ≫ ρ_K` on the right.
- Conjunct 5 identifies `d_N.inv ≫ q_K` with `transferredQ`.
  The latter definition uses exactly
  `S.map β.hom ≫ p.inv ≫ ((d_W.inv ≫ ε_1) ⊗ₘ 𝟙 K) ≫ λ.hom`.
  Conjunct 6 identifies it with `S.map h_K ≫ ev_K`. Together these are
  the node's full three-term equality for `N = TK ⊗ W`.
- Conjunct 7 is precisely `τ_K ≫ ρ_K = h_K`, for every `K`.
- Conjuncts 8–11 assert naturality of `q`, `τ`, `h`, and the common
  transferred expression `d_N.inv ≫ q_K`, respectively. For example the
  last equation is
  `S.map (T.map f ⊗ₘ 𝟙 W) ≫ d_NL.inv ≫ q_L = d_NK.inv ≫ q_K ≫ f`.
  The two equal expressions from conjuncts 5–6 therefore have this same
  naturality. Universal component equalities plus these naturality equations
  are exactly equalities of the natural transformations they define: the source
  functor is `K ↦ TK ⊗ W` (composed with `F` or `S` where appropriate),
  with arrow `T.map f ⊗ₘ 𝟙 W`; targets are the identity, `G`, or `T`.
  This records the node's natural-transformation assertion without introducing
  proof-dependent natural-transformation structures inside a definition.

Dependency interfaces read and used:

- `def-sfb-monoidal-category`: `CategoryTheory.MonoidalCategory`, from
  `Mathlib.CategoryTheory.Monoidal.Category`, brought in by public import of
  `Mathlib.CategoryTheory.Monoidal.Braided.Basic`. The latter supplies
  `BraidedCategory`, `SymmetricCategory`, `β_` and its unit compatibility.
- `def-weil-pbc-adjunction-mate`: `CategoryTheory.mateEquiv`, from
  `Mathlib.CategoryTheory.Adjunction.Mates`, along with the genuine
  `Adjunction`, counits and `homEquiv` used in the signature.
- `def-weil-pbc-adjunction-conjugate`: `CategoryTheory.conjugateEquiv`,
  from that same public Mathlib import, applied in the required direction
  to `d.inv : S ⟶ F`. Its full signature and implementation were read,
  together with `conjugateEquiv_counit` and `conjugateIsoEquiv`.
- Proof-only dependency `lem-pur-adjunction-mate-transpose`:
  `CategoryTheory.adjunctionMate_transpose`, from the plain import
  `Sheaf.CategoryTheory.DerivedCategory.AdjunctionMateTranspose`. Its full
  signature/docstring were read; the theorem's proof plan uses it with
  identity vertical functors. No unusable dependency record was encountered.

Edge cases checked before writing:

- Distinct object and morphism universes for the two categories are retained;
  no smallness, equal-universe, nonempty-object, or existence-of-limits assumption
  is introduced. The theorem is only conditional on the actual data in the node.
- For identity adjunctions, identity projection maps and unit comparison,
  `ρ`, `τ` and `h` reduce to the expected unit identifications.
- For identity functors on vector spaces with `d = c·id` (`c ≠ 0`),
  compatible standard projections and `u = id`, conjugation gives
  `ρ = c⁻¹·id`; thus `η = c⁻¹·id` and both sides of `τ ≫ ρ = h`
  scale by `c⁻¹`. This detects reversing `d` or the conjugation direction.
- With an arbitrary automorphism `u` of the tensor unit, the evaluation
  normalization is retained as a hypothesis, so this case is not silently
  specialized to an identity comparison.
- Terminal categories, and zero objects in additive examples, make all
  equations well typed; no cancellation through any functor is assumed.

Searches for an existing statement (msearch log is `searches.jsonl`):

- LeanFinder query: "Isomorphic left adjoints with compatible projection
  formulas transfer the counit tensor transpose at the monoidal unit".
  Eight hits include `Adjunction.map_μ_comp_counit_app_tensor`,
  `Adjunction.map_ε_comp_counit_app_unit`, and `mateEquiv_counit`.
  They supply general identities or require monoidal structures on functors;
  none gives this theorem under the node's hypotheses.
- Loogle query: `CategoryTheory.conjugateEquiv`. Twelve hits give the
  conjugate bijection, its identity/isomorphism laws and unitor cases;
  these supply the reused dependency, not the projection-tensor calculation.
- LeanSearch query: "Adjunction transpose of inverse projection and counit
  equals tensor with the adjunct at the unit". Eight hits concern tensor/Hom
  adjunctions, opposite counits and monoidal units; no matching statement.
- msearch grep `projectionFormula|projection_formula|frobeniusReciprocity`
  under Mathlib `CategoryTheory`: zero hits. The query
  `conjugate.*(tensor|projection)|projection.*(counit|adjunction)` gives
  four hits in `Monoidal/Closed/Basic.lean`, internal-Hom conjugations.
- Local `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `projectionFormula|projection_formula` and transfer names found geometric
  projection-formula results and the upstream module-object projection formula.
  Those have different hypotheses (including structured functors) and do not
  assert this normalized comparison for two arbitrary adjunctions.
- Local `rg` of both roots, Mathlib and `dag/lean_names_upstream.json` for
  `AdjointProjectionTensorTransfer|adjointProjectionTensorTransfer` found no
  declaration; the node-id search in `WeilConjectures` also found none.

Validation: scompile.py compiled the file in module mode as both its sandbox
copy (7.6 s) and intended library module (5.7 s), without errors or unexpected
warnings. All variables/universes are explicit and autoImplicit is disabled;
all Lean lines are within 100 characters. The only postponed proof belongs to
this DAG node.

## Second reading by Q53

I reopened the node and the Lean file for a separate clause-by-clause self-audit;
this is not a claim of independent worker review. The dispatch explicitly
forbids starting another agent and assigns independent delivery review to the
maintainer.

I checked the two symmetric-category binders, all four functor directions,
both adjunctions, the direction of `d`, the unit isomorphism and all four
normalization/naturality hypotheses against the node. In particular `hev`
has domain `S(T1) ⊗ K`, and its image under `S` is exactly `a_K` rather
than a general evaluation compatibility assumption. `q` and `transferredQ`
both start at the symmetry on `TK ⊗ W`, so each inverse projection has the
right source. The counit characterization starts with `d_GK`, whereas the
Hom-transfer formula starts with `d_N.inv`; these opposite directions are
intentional and match the conjugate of `d.inv`. The uniqueness quantifier
covers every natural transformation. The two projection expressions and
the evaluation expression have identical source `S(TK ⊗ W)` and target `K`;
the tensor-transpose equality has source `TK ⊗ W` and target `TK`.
I checked all four naturality equations with the same arrow `K ⟶ L` and
confirmed the last equation makes both equal transferred expressions natural.
No mathematical mismatch or missing clause was found. I corrected two prose
composition-order descriptions in helper/proof docstrings; no signature or
node statement changed. The original source statement and all non-lean JSON
fields are preserved.

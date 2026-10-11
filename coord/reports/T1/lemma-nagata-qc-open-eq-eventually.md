## Worker report

The module `Sheaf.AlgebraicGeometry.NagataQCOpenEqEventually` states
`AlgebraicGeometry.nagataQCOpenEqEventually`. The original node was corrected:
the landed dependency `nagataQCOpenEqualityStage` selects an index only, so the
original chartwise data could not be bound. The corrected statement has a
preorder `J`, schemes `Y j` and `Y₀`, maps `q j : Y j ⟶ Y₀`, transition maps
`t j k h : Y k ⟶ Y j`, and the commuting equation
`(t j k h) ≫ q j = q k`. It assumes equality of the two open preimages at
`stage`, and concludes equality at every `j ≥ stage`. The proof is `sorry` as
required by stage 2.

The hypothesis `hEq` is rendered by
`q stage ⁻¹ᵁ W₁ = q stage ⁻¹ᵁ W₂`; the conclusion is rendered by
`q j ⁻¹ᵁ W₁ = q j ⁻¹ᵁ W₂`; the transition compatibility is the `comm`
hypothesis. The selected stage in the application is supplied by
`AlgebraicGeometry.nagataQCOpenEqualityStage` from
`Sheaf.AlgebraicGeometry.NagataQCOpenEqualityStage`.

Edge cases checked: `J` may have one element; `stage = j`; `W₁` or `W₂` may
be empty or top; no nonemptiness, compactness, or separatedness assumptions
are added to the corrected transport lemma.

Searches: `msearch.py leanfinder` for eventual equality of inverse images
returned `AlgebraicGeometry.exists_map_preimage_eq_map_preimage`, which does
not state eventual transport; `msearch.py loogle` for `IsCompactOpen,
Scheme.Open, inverse image equality` returned no match; grep of
Mathlib/AlgebraicGeometry and `WeilConjectures/` found no matching statement;
`rg` of `lean/Sheaf` found only the selected-stage definition. No existing
exact declaration was found.

## Earlier second reading (a previous round; superseded)

Read the corrected node and module independently. `J`, `Y`, `Y₀`, `q`, `t`,
`comm`, `stage`, `W₁`, `W₂`, and `hEq` all have explicit Lean binders. The
single conclusion quantifies every later index and matches the corrected node
clause by clause. No chartwise objects from the old statement remain. The
module compiles locally with only the expected `sorry` warning.

## Statement corrected

The first worker's transport-only correction is superseded by this second reading.
The landed `def-nagata-qc-open-equality-stage` now chooses an equality witness via
Stacks 01Z4(2) and takes a finite upper bound; it no longer supplies chartwise data.
The original item's reference to that data needs correction, but its conclusion
at the prescribed selected stage must be retained. Assuming `hEq` at an arbitrary
stage, as the first worker did, removes the central obligation. The repaired
statement binds the landed definition's geometric inputs, assumes equality only
on the limit, uses exactly its returned stage, and concludes equality above it.
The hypothesis on `d` is the selected-common-upper-bound property in the source
and `def-nagata-directed-finite-upper-bound`, not a new geometric restriction.
The extra tail binder `h₀ : i₀ ≤ j` only makes the base-changed scheme typeable:
`i₀ ≤ selected stage` follows from the upper-bound theorem, so no later index is
excluded. The unit's statement is unchanged.

All citers were opened and checked against the restored statement:

- `lemma-nagata-relative-gluing-axioms-eventually`: holds; its common bound
  includes the finitely many selected open-equality stages.
- `def-nagata-morphism-descent`: holds; in the rebased system the compact union
  and whole scheme have equal limit preimages, and the final bound is above the
  selected stage. The lemma supplies the needed cover at that bound.
- `lemma-nagata-morphism-eq-eventually`: holds; proof step 2 applies precisely to
  the compact inverse-image opens on qcqs X, equal on the limit, above their
  selected equality stage.

## Second reading by T1

I opened the original node, the first worker's corrected node and module, the
landed stage-selection definition and its node, the base-change declarations,
the finite-upper-bound declaration and node, and all three citers. I first
checked the proposed correction against Stacks 01Z4(2), reading the actual TeX
`limits.tex`, `lemma-descend-opens`, and its throughout hypotheses in
`situation-descent` (affine transitions, nonempty directed indexing, qcqs stages).
The same source was checked at https://stacks.math.columbia.edu/tag/01Z4.
In our base-changed diagram the stages are affine over qcqs Y₀, so the source's
qcqs conditions follow from the bound inputs. No qcqs condition on the original
D stages is needed. The selected-definition implementation already invokes the
proved Mathlib equality-descent theorem on this base-changed cone.

Object/hypothesis/conclusion checklist (all verdicts concern the final repair):

- Nonempty directed preorder I: `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. Exact recorded selection inputs.
- Inverse system of schemes: `D : Iᵒᵖ ⥤ Scheme.{u}`. Same orientation and
  same object/index universe as the dependency, not an unrelated system.
- Specified limit S and projections: `c : Cone D`, `hc : IsLimit c`;
  `c.π.app (Opposite.op i₀)` is the required projection. No limit existence
  or surjectivity is assumed beyond the given limit cone.
- Affine transitions: `[∀ {i j : Iᵒᵖ} (f : i ⟶ j),
  IsAffineHom (D.map f)]`. Exactly the source/descent hypothesis.
- Base stage, scheme, map: `i₀ : I`, `{Y₀ : Scheme.{u}}`,
  `p : Y₀ ⟶ D.obj (Opposite.op i₀)`. Same objects as the stage definition.
- Y₀ qcqs: `[CompactSpace Y₀] [QuasiSeparatedSpace Y₀]`. Absolute qcqs,
  not the weaker relative property; no Noetherian/separated/finite-type instance.
- Two compact opens: `W₁ W₂ : Y₀.Opens`,
  `hW₁ : IsCompact (W₁ : Set Y₀)`, and corresponding `hW₂`. Both retained.
- Equality on the limit: `hEq` compares inverse images along
  `pullback.fst p (c.π.app (Opposite.op i₀))`. This is exactly the vertex
  projection of the recorded `baseChangeCone`; equality at a finite stage is
  neither assumed nor substituted for this hypothesis.
- Selected upper bounds and enumeration order: `d : I → I → I`,
  `hd : ∀ i j, i ≤ d i j ∧ j ≤ d i j`, `r : LinearOrder I`.
  `r` is explicit auxiliary data, never installed as the preorder of I.
- Exact selected stage: the threshold is literally
  `nagataQCOpenEqualityStage D c hc i₀ p W₁ W₂ hW₁ hW₂ hEq d r`.
  There is no arbitrary `stage` binder and no free finite-stage equality.
- Every later stage on the base-changed tail: `∀ (j : I) (h₀ : i₀ ≤ j),
  selectedStage ≤ j → ...`. The tail constraint is redundant above the bound,
  as the corrected node explicitly records; it chooses the transition map.
- Full conclusion: equality of inverse images along
  `pullback.fst p (D.map (homOfLE h₀).op)`. By the opened `baseChangeDiagram`
  declaration its object at `Over.mk (homOfLE h₀).op` is precisely this
  pullback. Both compact opens and the full equality of opens are retained.

Dependency reading: `baseChangeDiagram` (upstream AffineTransitionLimit,
line 2185) constructs the actual fibre products and transition maps;
`baseChangeCone` (line 2200) has the actual limit fibre product as vertex.
`nagataQCOpenEqualityStage` chooses from a proved existential, then applies
`directedFiniteUpperBound` to `{i₀, τ}`. Its arbitrary `d` input requires `hd`
in this theorem. `le_directedFiniteUpperBound` supplies exactly the two index
inequalities needed; it is cited in `proof_deps` and the proof docstring.
The sandbox contained an unchanged copy of the already landed stage-definition
node; I removed that redundant dependency delivery. No new definitions or
replacement dependency modules are required.

Edge cases: empty I is correctly outside the node's nonempty setting; singleton
I and j equal to the bound are included. Empty Y₀, empty schemes in D, and
empty/top opens are permitted; compactness of opens is required exactly where
stated. Zero rings and every characteristic are covered through arbitrary
schemes. There is no n parameter. The universe u is explicit; index and scheme
universes match the recorded inverse-limit convention. No variables or universe
levels are left implicit. Proof irrelevance makes different witnesses of h₀
immaterial. No hollow definition, private notation, local instance, or extra
proved statement is introduced; the only proof is `sorry` as stage 2 requires.

Independent searches, with different wording from the first worker:

- `msearch.py leansearch`: "Equality of quasi compact opens after base change
  descends to every index above a selected finite upper bound"; service returned
  Internal Server Error, recorded unavailable.
- `msearch.py leanfinder`: "Two compact open subsets equal on an inverse limit
  become equal at sufficiently large finite stages"; eight hits, mainly
  `InverseSystem` and `Profinite` equivalences; none states this selected-stage
  scheme result.
- `msearch.py grep`: `preimage.*eq.*preimage|nagataQCOpenEqEventually` on
  Mathlib AlgebraicGeometry; found `exists_map_preimage_eq_map_preimage` and
  unrelated open-immersion equalities. I opened the existential theorem at
  AffineTransitionLimit line 294: it chooses some equality stage, and does not
  state equality above the particular stage selected by our definition.
- `rg` on upstream WeilConjectures and project Sheaf, using
  `open.*equal|equal.*open|preimage.*preimage|eventual` and the exact prospective
  names: only the known existential usage, stage definition, and unrelated
  descent statements; no existing declaration realizes the repaired node.
  The exact name is also absent from `dag/lean_names_upstream.json`.

Mismatches repaired: (H3/H7) removed the first worker's added finite-stage
equality assumption and restored the exact selected-stage conclusion from
limit equality; corrected the node with full geometric data rather than the
transport-only special obligation; added the explicit common-upper-bound
hypothesis; restored its upper-bound proof dependency and complete proof steps;
(H8) replaced the transport-only docstring with the selection/witness/bound/
transition argument and the precise Stacks source. Other module conventions and
the theorem name were retained. `lean.statement` was extracted verbatim from
the final signature with whitespace normalized.

Validation: `lcompile.py` on the final module succeeded in 1.8 seconds with no
errors or warnings. Final server compilation and preflight are run by deliver2.

Final dry run: deliver2.py --no-push printed OK; server compilation and
maintainer preflight passed.

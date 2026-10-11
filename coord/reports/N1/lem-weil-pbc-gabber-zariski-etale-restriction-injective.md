## Worker report

The module states `AlgebraicGeometry.gabber_zariski_etale_restriction_injective`. It binds a scheme X, a closed immersion i : Z ⟶ X, an étale sheaf F, Zariski sheaves on X and Z, and asserts existence and uniqueness of a family of section maps beta, each injective. The theorem proof is `sorry` as required for stage 2.

The hypotheses are rendered by the explicit binders `X Z`, `i`, `[IsClosedImmersion i]`, `F`, `Fzar`, and `iFzar`. The conclusion is rendered by `∃! beta` and the clause `∀ V, Function.Injective (beta V)`.

Dependencies used: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `Mathlib.AlgebraicGeometry.Sites.Etale`, `Mathlib.Topology.Sheaves.Functors`, `Sheaf.Paper.ZariskiEtaleInclusionMorphismOfSites`, and `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.

Edge cases checked: arbitrary schemes and closed immersions, including empty opens; the section maps use the terminal open and no nonempty assumptions.

Searches: `rg` over `lean/Sheaf` and `WeilConjectures` found no existing declaration for this node; Mathlib site and sheaf searches found no comparison theorem. The recorded dependency declarations were inspected in their node records.

## Earlier second reading (a previous round; superseded)

The module compiles locally; the declaration and node metadata are aligned for delivery.

## Second reading by N1

I opened the node, its six proof steps, all eight statement dependencies and their
recorded declarations, the delivered file, and Stacks `etale-cohomology.tex`,
`lemma-gabber-h0` (Tag 09ZF), first two proof paragraphs. The repository's literature
checkout is absent on this machine; the available local Stacks source was read at
`/home/ubuntu/c1-stacks-review/etale-cohomology.tex`, lines 14975–15015.
The original Lean did **not** state the node. The node itself is unchanged.

Objects, hypotheses and conclusions, with their repaired Lean rendering:

| Node item | Lean rendering | Verdict |
| --- | --- | --- |
| Schemes X and Z, closed immersion i : Z → X | `{X Z : Scheme.{u}}`, `(i : Z ⟶ X)`, `[IsClosedImmersion i]` | Exact; no finiteness or separation hypothesis added. |
| Sheaf of sets F on the small étale site of X | `F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v))` | Exact, with sufficiently large and arbitrarily enlargeable coefficient universe. |
| F_Zar(W) = F(W → X), including restriction maps | `Fzar`, together with presheaf **natural** isomorphism `eX` to precomposition of `F.obj` by `MorphismProperty.Comma.lift X.restrictFunctor` | Exact. Lift only adds the existing proof that open immersions are étale. The isomorphism is an identification of the chosen restriction sheaf, not an arbitrary extra sheaf. |
| Topological inverse image i⁻¹_Zar F_Zar, and its unit | `sheafPullbackConstruction.sheafPullback (Opens.map i.base) ...` and `sheafAdjunctionContinuous ... .unit.app Fzar` | Exact: left Kan extension followed by sheafification and the composite adjunction unit, as the dependency's Mathlib match requires at the larger universe. |
| Étale inverse image i⁻¹F, and its unit | The same existing `sheafPullbackConstruction` and `sheafAdjunctionContinuous`, along `MorphismProperty.Over.pullback @Etale ⊤ i` | Exact set-valued construction. The recorded upstream `Etale.upperStar` requires an abelian coefficient category, so it cannot be applied to sets; the node expressly cites the generic continuous-functor construction for sets, which is what is used. |
| (i⁻¹F)_Zar(V) = (i⁻¹F)(V → Z) with its restriction maps | `iFzar` and presheaf natural isomorphism `eZ` | Exact, for the same canonical lifted restriction functor on Z. |
| Identify W ×_X Z with the preimage open | `a W : Scheme.Etale.mk (i ⁻¹ᵁ W).ι ≅ ...`, with `ha W` fixing the projection to W as `i ∣_ W` | Exact canonical identification. The other projection is already fixed because `a W` is an isomorphism **over Z**. Pullback universality fixes this isomorphism uniquely; it exists for every W, so these binders merely name the identification the node instructs us to make. |
| Morphism beta of sheaves on Z | `beta : (topological sheafPullback ...).obj Fzar ⟶ iFzar` | Exact, including all naturality conditions. |
| Compatibility beta_(i⁻¹W)(eta_W(s)) = i* s for every W and s | The equation under `∀ (W : X.Opens) (s : Fzar.obj.obj (op W))`, evaluated for `beta'` | Exact. `eX.hom` identifies s with its étale section; the étale unit pulls it back; restriction along `(a W).hom.op` identifies the fibre product; `eZ.inv` returns the Zariski section. |
| Existence and uniqueness among **all** compatible sheaf morphisms | `∃ beta, ... ∧ ∀ beta', (∀ W s, unit equation) ↔ beta' = beta` | Exact. Taking beta' = beta gives compatibility; any compatible morphism equals beta, whether or not injectivity is assumed of it. |
| Each beta_V is injective | `∀ V : Z.Opens, Function.Injective (beta.hom.app (op V))` | Exact, with the inverse-image sections on V as domain. |
| Global restriction factors as beta_Z composed with the topological unit | The same unit equation at `W = ⊤` | Exact specialization, not a separate hypothesis: `i ⁻¹ᵁ ⊤` is the top open of Z. The right side is the canonical étale global restriction under `eX`, `a ⊤`, and `eZ`; the middle component is injective by the preceding clause. |

Source scope: the full Tag 09ZF lemma assumes quasi-compactness,
quasi-separatedness, and two global-section hypotheses to prove **bijectivity**.
This node extracts the first paragraph's comparison injectivity and the second
paragraph's factorization. Its six-step proof uses none of those additional
hypotheses; we neither claim global injectivity without the topological criterion
nor claim global surjectivity. Thus the node's arbitrary-scheme scope is retained.

Dependency inspection: `Scheme` is the locally affine locally ringed space in
Mathlib; `IsClosedImmersion` extends surjectivity on stalks by a closed embedding;
`Sheaf` is the full subcategory of presheaves satisfying the given topology.
`pullback`, `pullback.fst`, and `pullback.snd` are the categorical fibre product
and projections. The restriction dependency `zariski_to_etale_is_morphism` gives
the open-subscheme inclusion with forgetful composite `X.restrictFunctor`.
The inline `Comma.lift` is precisely that inclusion, using Mathlib's existing
lift, not a new notion or a private definition. Its theorem is not imported
because no reference to that existential theorem is needed to type the statement.
Mathlib `sheafPullbackConstruction` and `sheafAdjunctionContinuous` implement the
recorded continuous-functor dependency and the topological dependency's larger
universe form. Upstream `upperStar` and its adjunction were opened and checked:
they require `[Abelian A]`, so their use for sets would be wrong. The imported
upstream module supplies continuity of étale base change; no continuity assumption
has been added to the theorem. No new nodes or dependency modules are needed.

Edge cases: the empty scheme and empty open are allowed. On the empty open the
source and target are sections of actual sheaves (hence singleton), instead of
unrelated global sections. No nonempty condition is imposed; the empty set-valued
sheaf is allowed. Zero abelian objects, characteristic and n = 0 introduce no
conditions in a theorem of arbitrary sheaves of sets. Both `u` and `v` are bound;
`max (u + 1) v` supports the small étale category and arbitrary enlargement.
No field, Noetherian, quasi-compact or quasi-separated instances occur.

Independent searches (2026-10-12):
- LeanSearch through `msearch.py`: "Zariski restriction of etale sheaf inverse image
  injective" returned service unavailable (Internal Server Error); no negative
  verdict is inferred from that failure.
- LeanFinder through `msearch.py`: "comparison morphism topological pullback etale
  sheaf monomorphism" returned étale pullback existence, scheme mono and
  representability/gluing declarations, none stating this comparison.
- Loogle through `msearch.py`: `"sheafPullback"` returned the existing generic
  constructed and abstract pullbacks and their adjunctions, which were opened and
  reused; none states comparison injectivity.
- `rg` on Mathlib's AlgebraicGeometry/Sites and Topology/Sheaves, the project's
  `lean/Sheaf`, and upstream `WeilConjectures`: searched `09ZF`,
  `zariski.*[Ii]nject`, `Zariski.*[Ii]nject`, and `gabber.*restriction`.
  Project hits are the citer `GabberH0EtaleCriterion`, composition-unit lemmas,
  and preservation of injective abelian objects under Zariski open restriction.
  The latter concerns injective objects, not injectivity of this map.
  Upstream `Gabber.lean` and `BaseChangeTheorems/DegreeZero.lean` were opened:
  they give abelian/module sheaf comparison over henselian bases, not this
  arbitrary closed-immersion set-valued comparison. No existing exact statement
  was found.

Repairs: removed unconstrained Zariski sheaves by adding their natural
restriction identifications; replaced the family from global sections by a sheaf
morphism from the actual topological inverse image; supplied both units and the
canonical fibre-product identification; restored compatibility, genuine
fixed-sheaf uniqueness, sectionwise injectivity, and the global factorization.
Enlarged the coefficient universe; replaced the malformed/missing statement
proof docstring with all six proof steps and their cited nodes; moved the module
docstring after imports, added the standard header, and removed the unused
Zariski-inclusion theorem import. No declaration is proved and no definition is
hollow. The sole theorem proof is `sorry`. The node's `lean.statement` is the
verbatim repaired signature. Local single-file compilation is clean; the final
server compile and delivery preflight are run by `deliver2.py`.

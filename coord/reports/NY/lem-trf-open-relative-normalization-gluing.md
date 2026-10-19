## Worker report

Delivered statement: `AlgebraicGeometry.Scheme.Hom.open_relative_normalization_gluing`
in `Sheaf.AlgebraicGeometry.Morphisms.OpenRelativeNormalizationGluing`.
The only postponed proof is this named theorem, with the source-based four-step
proof in its docstring. No definitions, instances, helper axioms or additional
postponed theorems were introduced. No independent notion is missing.

The ORIGINAL statement is false. The correction is material, authorized by §1(C),
and does not change the blueprint unit's own statement. It restores the actual
relative-normalization construction, including its quasi-compact input hypothesis;
it does not claim to repair the arbitrary-open extension theorem. See the complete
correction and citer audit below.

Hypotheses and clauses of the CORRECTED node, matched to Lean:

- Schemes S, U, V: `{S U V : Scheme.{u}}`, with `universe u` explicit.
- Open immersion U→S: `(j : U ⟶ S) [IsOpenImmersion j]`.
- Integral morphism V→U: `(g : V ⟶ U) [IsIntegralHom g]`.
- Composite quasi-compact: `[QuasiCompact (g ≫ j)]`. This is the required
  hypothesis in source Definition 035H, now recorded explicitly by §1(C).
  Quasi-separatedness of the composite is inferred from its separatedness; the
  statement adds no separate separatedness or quasi-separatedness hypothesis.
- The specified relative normalization N→S is `(g ≫ j).normalization` with
  map `(g ≫ j).fromNormalization`. These are the existing declarations of
  `lem-weil-pbc-relative-normalization`, not a new choice or construction.
- Its chart ring on each W is `(g ≫ j).normalizationDiagram.obj (.op W.1)`.
  Reading its definition gives precisely
  `CommRingCat.of (integralClosure Γ(S,W.1) Γ(V,(g ≫ j) ⁻¹ᵁ W.1))`, with
  the algebra structure `( (g ≫ j).app W.1 ).hom.toAlgebra`. In particular,
  these are sections on the FULL inverse image of W, not one cover member.
- Canonical principal localization compatibility is the first conjunct,
  `((AffineZariskiSite.toOpensFunctor S).op.whiskerLeft
  (g ≫ j).normalizationDiagramMap).Coequifibered`.
  `AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway` identifies
  this with localization of the chart ring at every base section, with the
  algebra structure supplied by the actual restriction map. The condition is
  exactly the canonical pushout square in CommRingCat. This retains the map,
  rather than asserting existence of unrelated ring isomorphisms.
- The cocycle is carried by the existing `normalizationDiagram` functor and
  `normalizationGlueData` construction. Its map-composition law identifies
  successive restrictions; the relative gluing data carries their cocycle.
  No tautological functor-law conjunct has been added to the theorem.
- The existing canonical affine chart ψ_W is
  `(g ≫ j).normalizationOpenCover.f W`, for `W : S.affineOpens`.
  By the definition of `normalizationOpenCover` and `relativeGluingData`,
  its source is `Spec` of exactly the above diagram object. The second
  conjunct asserts `IsOpenImmersion` for every one of these chart maps.
- The equation in that same conjunct identifies ψ_W followed by ν with
  `Spec.map ((g ≫ j).normalizationDiagramMap.app (.op W.1)) ≫ W.2.fromSpec`.
  The diagram map is A_W→C_W and `W.2.fromSpec` includes the spectrum of
  the affine base ring into S, so this is the stated compatibility over S.
- The final equation in that conjunct is precisely
  `ν ⁻¹ᵁ W.1 = ψ_W.opensRange`, recording the full affine inverse image.
- Joint covering is the third conjunct:
  `∀ x : N, ∃ W y, ψ_W y = x`. There is no finite-cover requirement.
- Integrality of the resulting morphism is the fourth conjunct
  `IsIntegralHom (g ≫ j).fromNormalization`.
- Recovery over U is the last conjunct, an isomorphism
  `e : pullback (g ≫ j).fromNormalization j ≅ V` satisfying
  `e.hom ≫ g = pullback.snd (g ≫ j).fromNormalization j`.
  The equation is essential: the isomorphism is over U, not just an
  isomorphism of the underlying schemes.

Dependencies read and used:

- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Scheme`, `Scheme.Hom`. Read the local-affine field
  and the full Hom structure, not just the recorded abbreviated signature.
- `def-weil-open-immersion`: Mathlib.AlgebraicGeometry.OpenImmersion,
  `AlgebraicGeometry.IsOpenImmersion`, the locally ringed space condition.
- `def-weil-finite-integral-morphism`: Mathlib.AlgebraicGeometry.Morphisms.Integral,
  `AlgebraicGeometry.IsIntegralHom`, extending `IsAffineHom` and requiring
  integral section maps on EVERY affine target open. The dependency also
  records `IsFinite`, but this theorem requires only its integral notion.
- `def-pc-fibre-product`: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `pullback`, `pullback.fst`, `pullback.snd`; read their HasPullback binders.
- `def-weil-affine-spectrum`: Mathlib.AlgebraicGeometry.Scheme,
  `AlgebraicGeometry.Spec`, `Spec.map`.
- `def-weil-pbc-integral-closure`: Mathlib.RingTheory.IntegralClosure.Algebra.Basic,
  `integralClosure`, with carrier `{r | IsIntegral R r}`; used by the
  actual canonical normalization diagram, not privately redefined.
- `def-weil-pbc-module-localization`: Mathlib.Algebra.Module.LocalizedModule.Basic,
  `LocalizedModule`; read its OreLocalization construction and mk_eq.
  The ring-localization statement uses the existing `IsLocalization` API.
- `lem-weil-pbc-glue-schemes`: its mathlib_match is
  Mathlib.AlgebraicGeometry.Gluing, `Scheme.GlueData`; read the cocycle data,
  `glued`, `ι_isOpenImmersion`, `ι_jointly_surjective`, `glue_condition`,
  and `vPullbackConeIsLimit`. Relative gluing is Mathlib's existing specialized
  construction, not an unusable dependency interface needing replacement.
- Proof dependency `lem-weil-pbc-integral-closure-commutes-localization`:
  Mathlib.RingTheory.Localization.Integral, `IsLocalization.integralClosure`;
  read all localization, algebra and scalar-tower hypotheses. It is imported
  without `public`, as a proof-only dependency.
- Added source-correction dependency `def-weil-finite-type-morphism`:
  its recorded `AlgebraicGeometry.QuasiCompact` in
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact is the new hypothesis.
  No locally-of-finite-type hypothesis is imposed.
- Added source-correction dependency `lem-weil-pbc-relative-normalization`:
  status mathlib, with its full mathlib_match in Mathlib.AlgebraicGeometry.Normalization.
  Read the module's qcqs binders, `normalizationDiagram`, `normalizationDiagramMap`,
  `coequifibered_normalizationDiagramMap`, `normalizationGlueData`,
  `normalizationOpenCover`, `toNormalization`, `fromNormalization`,
  `ι_fromNormalization`, `fromNormalization_preimage`,
  `normalizationObjIso`, `fromNormalization_app`, `normalizationObjIso_hom_val`,
  and the integral/dominant instances. Its existing construction supplies the
  notion completely, so no extra definition node or dependency repair is needed.

Edge cases checked before writing:

1. U=S and g=id, with S=Spec(Q[t]) and cover D(t),D(1-t), disproves the old
   construction; see below. The corrected normalization is S itself.
2. U empty and V empty: the composite is quasi-compact, and the closure in
   the zero section rings gives the empty normalization; its pullback is V.
3. V empty and U arbitrary: the composite is still quasi-compact even if j
   is not, so the chosen composite hypothesis does not unnecessarily require
   `QuasiCompact j`.
4. j=id and g arbitrary integral: the composite is quasi-compact automatically;
   normalization is V by Tag 03GP, with no finite-type or surjectivity hypothesis.
5. Non-quasi-compact j with g=id: the hypothesis can fail. This exclusion is
   explicit in statement_change, and the downstream arbitrary-open invocation
   is marked holds:false, never silently treated as available.
6. Empty affine opens, zero rings, disconnected/reducible bases, and arbitrary
   characteristics are admitted. All schemes share the usual arbitrary universe u.
7. No surjectivity, normality, reducedness, noetherianity, finite presentation,
   or finiteness of g is assumed. The qc hypothesis is not hollow in general.

Searches performed (recorded automatically in sandbox searches.jsonl):

- msearch leanfinder: “Extending an integral morphism across an arbitrary open
  immersion by relative normalization”: 8 hits, chiefly normalizationDesc and
  toNormalization; all relevant signatures require quasi-compact and
  quasi-separated input, none proves the old arbitrary-open chart claim.
- msearch loogle: `IsIntegralHom, IsOpenImmersion`: 0 hits, unknown identifier.
- msearch grep: `extend.*integral|integral.*extend|normalization.*glue`
  in AlgebraicGeometry: 6 hits, normalizationGlueData and the integral class;
  no extension/gluing theorem as originally stated.
- msearch leansearch: “relative normalization of a quasi compact quasi separated
  scheme morphism with its affine chart cover”: 8 hits, canonical normalization
  maps, integral instance, and `ι_fromNormalization`.
- msearch loogle: `AlgebraicGeometry.Scheme.Hom.normalization`: 12 hits,
  including normalizationOpenCover, fromNormalization and their qcqs signatures.
- rg of normalization/integralClosure in upstream WeilConjectures and local
  lean/Sheaf: the upstream ExtendOverInertia module has
  `pullbackFromNormalizationIso` WITH explicit qcqs composite hypotheses.
  Read its full signature and construction; it does not establish the original
  node. No existing single declaration assembles the corrected chart and
  localization theorem, so the statement is not recorded as existing:true.
- grep of the exact item id in upstream WeilConjectures: no match.
- `tools/blueprint_refs.py search 'relative normalization'` and a DAG search
  found thm-pqf-immersion-descent citing the already existing
  lem-weil-pbc-relative-normalization. This avoids introducing a duplicate notion.
- Full citer scan: `rg -l '"lem-trf-open-relative-normalization-gluing"' dag/nodes`,
  followed by parsing stmt_deps/proof_deps of all nodes: exactly one actual citer,
  lem-trf-integral-surjective-open-extension.

Source passages opened: local morphisms.tex Section “Relative normalization”,
including 035F, Definition 035H, Lemma 035K; local more-morphisms.tex 0CNX
and its proof; tag-to-label table confirms normalization-in-integral is 03GP.
Also checked the current official pages https://stacks.math.columbia.edu/tag/0CNX
and https://stacks.math.columbia.edu/tag/035F: the former still invokes the
normalization without the qc input its definition requires. This is reported
as a source proof gap, not silently repaired by inventing an arbitrary-open API.

Validation: scompile.py compiled this single module as sandbox and library module
with no compiler errors or warnings. Only the theorem proof is `sorry`.

## Statement corrected

The exact original statement is preserved verbatim in node.statement_change.old_statement.
It claims that closures of A in separate B_i over D(f_i) have overlaps
D(f_i f_j), satisfy gluing, and give an integral morphism recovering V for
an arbitrary open immersion j.

Counterexample: S=U=V=Spec(Q[t]), j=g=id. Refine S by D(t),D(1-t).
Their inverse-image rings are Q[t,1/t] and Q[t,1/(1-t)]. Their integral
closures of Q[t] are BOTH Q[t], as Q[t] is integrally closed in Q(t).
The proposed gluing identifies the two copies of Spec(Q[t]) only over
D(t(1-t)), giving doubled points over 0 and 1. It is non-separated over S,
so not integral; restriction to U=S cannot give V=S. Even the proposed
self-overlap D(f_i²) is not the whole Spec(C_i), as gluing data require.

Correction source: morphisms.tex Definition 035H constructs normalization
for a quasi-compact and quasi-separated map f using the integral closure
in f_*O_V; its affine chart is therefore Γ(f⁻¹W,O_V), NOT a separate B_i.
Tags 035F/0307 provide principal localization and gluing; 035K provides
restriction compatibility, and 03GP identifies normalization of an integral
morphism with its source. The corrected theorem explicitly assumes
QuasiCompact(g≫j); quasi-separatedness follows from separatedness here.
This is a source-required hypothesis, not an API-induced universe restriction.
No claim that the arbitrary-open extension assertion is false is made.
The source's 0CNX proof has a qc gap when invoking this definition for an
arbitrary open; the fictitious principal-cover argument cannot fill it.

The node's statement, stmt_deps, proof and proof_deps were changed only
as required by this correction. statement_change saves all changed original
fields. No source, title, unit, status, reviewed field or citer was edited.
The item is a created helper, with blueprint.is=null and unit=sk-i-curve-zero;
this correction does not edit the unit's own statement.

Complete citer audit:

- `lem-trf-integral-surjective-open-extension`: **holds:false**. Its Step 1
  explicitly invokes the rejected arbitrary-open principal-cover gluing.
  Its hypotheses do not give QuasiCompact(g≫j), so the corrected lemma
  does not justify that step. The extension theorem may remain true, but
  its proof needs an independent repair. The citer is not modified.

## Second reading by NY

This is a delivery self-check, not an independent second-agent review: the
worker brief prohibits spawning other agents and assigns independent review
to the maintainer. The module and corrected node were read together. Every
binder and conjunct is matched above; the counterexample was checked before
writing. A source-tag error in the first draft (035R) was corrected to 03GP
using the local tag-to-label table. There is one theorem, one node file,
no new nodes or dependency modules, no hidden definitions or assumptions,
and the sole affected citer is explicitly marked holds:false.

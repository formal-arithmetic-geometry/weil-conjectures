## Worker report

The module `Sheaf.AlgebraicGeometry.RepresentableProperFppfTargetTest` states
`CategoryTheory.representable_proper_fppf_target_test`, with its entire proof `sorry`.
It states the supplied node without a mathematical statement correction. There are no
new definitions, no new nodes and no dependency-module repairs.

I read Stacks `stacks-properties.tex`, Section 04XB, especially
`lemma-check-property-covering` (Tag 04XD), lines 466–500, and its preceding
`lemma-property-spaces-too`. The source permits an algebraic-space cover W; this
node explicitly specializes W to a scheme, and the Lean retains that specialization.
The supplied node already corrects the source proof's typographical reference to
`T ×_Y V → T` as the covering: the covering used is `T ×_Y W → T`.
The example CompactObject module has been withdrawn and contains no declarations;
I followed the current module conventions and the existing AlgebraicModuliStack module.

Hypothesis and clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Arbitrary base scheme S, size convention | `{S : Scheme.{u}}`; explicit `u v₁ w₁ v₂ w₂`. Every scheme test is `Over S`, with schemes of universe u, and the two total stack categories have independently explicit object/morphism levels. No small test universe independent of u is introduced. |
| Algebraic stacks X and Y | `X : BasedCategory.{v₁, w₁} (Over S)`, `Y : BasedCategory.{v₂, w₂} (Over S)`, `hX : IsAlgebraicModuliStack X`, `hY : IsAlgebraicModuliStack Y`. This existing predicate includes stack descent, representable algebraic-space diagonal and smooth surjective scheme atlas. |
| Morphism f : X → Y | `f : BasedFunctor X Y`, a functor over the fixed base. |
| f representable by algebraic spaces | `hf : IsRepresentableByAlgebraicSpaces f`, quantifying over every scheme map into Y and using projection-compatible presentations. |
| Scheme W and its morphism p : W → Y | `W : Over S`, `p : BasedFunctor (discreteModuli (yoneda.obj W)) Y`. W includes its required structural S-map. |
| p representable | `hp : IsRepresentableByAlgebraicSpaces p`. |
| p surjective after every scheme base change | `hs`: for every `T` and `t : h_T → Y`, a presentation `HasSpaceBaseChange p T t Z a` has `SpaceMapIsSurjective Z T a`. The latter says every point of T lifts to a point in some étale scheme chart of Z. This is exactly surjectivity on the point space of the algebraic-space projection, without assuming rational-point lifting over the original residue field. |
| p flat on étale scheme charts | `hflat : ModuliSpaceTest @Flat p`. This uses the actual algebraic-space projection in each scheme base change and tests its composites with every representable étale scheme chart. |
| p locally finitely presented on étale scheme charts | `hlfp : ModuliSpaceTest @LocallyOfFinitePresentation p`, with precisely the same scheme-base-change convention. |
| V = X ×_Y W and projection V → W | `moduliTwoFiberFst p f`, whose domain is `moduliTwoFiberProduct p f`. The ordering W ×_Y X makes the required projection the first projection; swapping the two factors gives exactly the node's X ×_Y W. No arbitrary map or chosen pullback object replaces the construction. |
| f proper iff V → W proper | The displayed `↔` between two explicit scheme-test propositions. The left tests f over all `T,t`; the right tests `moduliTwoFiberFst p f` over all scheme maps to `discreteModuli (yoneda.obj W)`. |
| Proper means every scheme base-change projection is proper as a space map | Each side requires `∃ Z a, HasSpaceBaseChange ... Z a ∧ MapIsProper (ObjectProperty.homMk ⟨a⟩ : Z ⟶ schemeSpace T)`. The bundled map contains exactly a, the projection in the comparison; `schemeSpace T` is the existing Yoneda scheme space. Isomorphism invariance makes this independent of the presentation witness. |
| Separated, finite type, universally closed | `AlgebraicSpace.MapIsProper` unfolds to `MapIsSeparated ∧ MapIsFiniteType ∧ MapIsUniversallyClosed`. These are respectively a diagonal representable by closed immersions; quasi-compactness and locally finite type on every compatible pair of étale scheme charts; and closed maps of point spaces after every algebraic-space base change. This uses the node's full properness convention. |
| Agreement with scheme properness | The chart and closed-immersion predicates use the recorded Mathlib scheme notions. The node's scheme convention `IsProper` is imported; universally closed scheme maps are quasi-compact, so its locally-finite-type formulation agrees with the node's finite-type formulation. |

In particular properness is not rendered by `ModuliSpaceTest @IsProper`, which would
incorrectly demand properness of arbitrary source étale charts. Nor is the DM-specific
intrinsic `IsProperModuliMap` substituted for the node's representable-map definition.
The inline quantified expressions state the supplied convention directly and introduce
no second definition of any notion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `IsRepresentableByAlgebraicSpaces`, `HasSpaceBaseChange`, `SpaceMapIsSurjective`,
  `discreteModuli`, `moduliTwoFiberProduct`, `moduliTwoFiberFst`; I read their definitions
  and docstrings, including the comparison over the test scheme in HasSpaceBaseChange.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`, its
  representability, étale and surjectivity predicates; these supply the chart vocabulary.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`, including
  `IsSmoothModuliAtlas` and `SpaceMapIsSmooth`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSpaceTest`; only this
  general representable chart-test predicate is used from the DM vocabulary.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsProper`,
  `MapIsSeparated`, `MapIsFiniteType`, `MapIsUniversallyClosed`, with their real definitions.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`, whose data is the
  actual representable fppf sheaf; its algebraic-space property is supplied by the named
  `schemeSheaf_isAlgebraicSpace` theorem.
- Recorded Mathlib scheme declarations `Smooth`, `Flat`, `LocallyOfFinitePresentation`,
  `IsProper`, `IsClosedImmersion`, `LocallyOfFiniteType`, `QuasiCompact` were read with
  their full class definitions and docstrings in the respective Morphisms modules.
- Proof imports use `Scheme.fppfPrecoverage`/`Scheme.fppfTopology` from
  `Mathlib.AlgebraicGeometry.Sites.Fpqc`,
  `AlgebraicSpace.flat_proper_fp_locality` from AlgebraicSpaceFlatProperFpLocality,
  the eight chartwise calculus statements from StackChartwiseSmoothEtaleCalculus,
  and `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme` from AlgebraicSpaceFibreProductsEtaleCovers.
  The recorded locality theorem's properness specialization supplies both arbitrary
  space base change and fppf locality. The two proof-only nodes
  `lem-sfb-space-proper-base-change` and
  `lem-sfb-fibred-groupoid-representable-smooth-calculus` currently have no Lean record
  in the read clone, so there is no module recorded for them to import. They are not
  needed to type the statement. Their roles are retained in the theorem's proof docstring.

Only the item's `lean` and `stmt_deps` change. Its four new statement dependencies are
already-landed definition owners: `def-sfb-algebraic-moduli-stack`,
`def-sfb-dm-stack-morphism-properties`, `def-sfb-space-morphism-properties`,
`def-trf-scheme-algebraic-space`. Their statements, records and source declarations
were read before use. The original ten statement dependencies remain in place.

Edge cases checked before writing:

- Empty W: `hs` forces each scheme base change to Y to have empty point space;
  no nonempty target point can be hidden by the test convention. No `Nonempty W`
  binder excludes this case. Empty X and the empty base likewise remain allowed.
- Identity cover: W a scheme representing Y and p its identity gives the usual
  equivalence between properness and properness of all its scheme base changes.
- Non-quasi-compact fppf cover: `hs`, `hflat`, `hlfp` contain no quasi-compactness
  hypothesis, as required. Neither finite presentation nor properness of p is assumed.
- Space base changes need not be schemes: `Z : AlgebraicSpace S`, not a scheme
  representative, occurs on both sides, preserving the full representability hypothesis.
- Nontrivial stack stabilizers are retained by BasedCategory, BasedFunctor and the
  iso-comma 2-fibre product; no quotient by isomorphism classes replaces these objects.
- Characteristic, Noetherianity, separatedness of S, flatness of f and finite
  presentation of f are unrestricted. No genus or moduli-family assumptions are imported
  into this abstract stack assertion through binders.

Searches actually run:

- `msearch.py leanfinder`: “Properness of representable morphisms of algebraic stacks
  is local on the target for a surjective flat locally finitely presented scheme cover”.
  Eight hits: scheme flat descent, scheme Zariski locality, etc.; no stack statement.
- `msearch.py loogle`: `"IsProper", "Flat"`: zero hits.
- `msearch.py grep`, AlgebraicGeometry: `[pP]roper.*(fpqc|fppf)|(fpqc|fppf).*[pP]roper`:
  five module-comment/precoverage hits; no stack assertion.
- `msearch.py leansearch`: “Properness of a representable algebraic stack morphism
  is equivalent to properness after an fppf scheme cover of the target”. Eight hits,
  all ordinary scheme properness statements, with no matching stack theorem.
- `rg` of WeilConjectures for representable/proper and fppf/proper phrases found
  Picard/Hilbert properness declarations or unrelated comments; none state the item.
  `grep -rn` of its exact node id in WeilConjectures returned no hits.
- `rg` of Sheaf for `representable_proper_fppf`, `proper_fppf_target` and
  `HasSpaceBaseChange.*MapIsProper` returned no matching existing declaration.
  Broader searches located the existing predicates and the locally-quasi-finite fppf
  target theorem, which has a different property and cannot serve as this item.
- `tools/blueprint_refs.py search 'proper fppf target'`: zero blueprint-node matches.
  No missing notion was found, so no new definition node is proposed.

No STATEMENT-DISPUTED finding. The first scompile.py check compiled the delivered file
in sandbox mode (5.4 s) and library mode (3.3 s), with no errors or warnings.

## Second reading by Q117

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

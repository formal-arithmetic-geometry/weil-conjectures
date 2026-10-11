## Worker report

Module: `Sheaf.AlgebraicGeometry.BaseChangeConventions`. The node is a bundle of conventions,
not a new replacement for categorical pullback. Its principal new declaration is
`AlgebraicGeometry.Scheme.Modules.moduleBaseChange`, the functor of module pullback along
`g_X`; `Scheme.Hom.geometricFiberAt` specifies the geometric fibre at a point for an arbitrary
chosen algebraic closure. Four theorems state the comparison and section clauses with `sorry`.
No definition contains `sorry`. No statement, dependency list or other node field was changed;
no new nodes and no dependency modules were needed.

Clause-by-clause correspondence:

- A scheme morphism `f : X → S`: explicitly bound `X S : Scheme.{u}` and `f : X ⟶ S`.
  No finiteness, smoothness, flatness, separatedness or nonemptiness hypothesis is imposed.
- An `S`-scheme `T` with its structure morphism: `T : Over S`, with underlying scheme `T.left`
  and structure morphism `T.hom`. This is the bundled version of the recorded `Scheme.Over`.
- `X_T = X ×_S T`, `pr_T : X_T → T`, and `f_T : X_T → X`:
  `(Over.pullback T.hom).obj (Over.mk f)` is already the bundled `T`-scheme whose `left` is
  `Limits.pullback f T.hom` and whose `hom` is `pullback.snd f T.hom`; `f_T` is
  `pullback.fst f T.hom`. These definitions are reused, not redeclared. The module docstring
  fixes this notation and all theorem signatures use these exact objects and projections.
- For an `S`-morphism `h : A → B`: `A B : Over S` and `h : A ⟶ B` encode exactly the
  commuting structure-morphism condition. The base-changed morphism is the existing
  `(Over.pullback T.hom).map h : (Over.pullback T.hom).obj A ⟶
  (Over.pullback T.hom).obj B`. Its type already makes it a morphism over `T`.
  `baseChange_morphism_projections` states both projection equations, identifying its
  underlying morphism with `h ×_S id_T` by the recorded pullback universal property.
- For `g : T' → T` over `S`: `T T' : Over S`, `g : T' ⟶ T`. The exact existing
  `AlgebraicGeometry.baseChangeMap f g` is `id_X ×_S g`, defined by `pullback.map`.
  `baseChange_iterated` states an isomorphism from `pullback f T'.hom` to
  `pullback (pullback.snd f T.hom) g.left`, with first projection exactly this `g_X` and
  second projection exactly `pr_{T'}`. Thus the identification is the prescribed one,
  not an arbitrary isomorphism of schemes.
- A sheaf `F` of `O_{X_T}`-modules: the domain of `moduleBaseChange f g` is
  `(Limits.pullback f T.hom).Modules`, and its codomain is
  `(Limits.pullback f T'.hom).Modules`. Its definition is literally
  `Scheme.Modules.tensorPullback (baseChangeMap f g)`. Consequently its application
  `.obj F` is `g_X^* F`, using the dependency's tensor-formula pullback, not Mathlib's
  abstractly chosen adjoint.
- A point `t ∈ T`: `t : T.left`. Its residue field is `T.left.residueField t`, its canonical
  point morphism is `T.left.fromSpecResidueField t`, and its map to `S` is the composite
  `T.left.fromSpecResidueField t ≫ T.hom`. `baseChange_fiber` compares the node's literal
  `pullback f` along that composite with the recorded scheme-theoretic fibre
  `(pullback.snd f T.hom).fiber t`. It states compatibility of the isomorphism with both
  the map to `X` and the map to `Spec κ(t)`.
- A chosen algebraic closure of `κ(t)`: `Ω : Type u`, `[Field Ω]`,
  `[Algebra (T.left.residueField t) Ω]`, `[IsAlgClosure (T.left.residueField t) Ω]`.
  `Scheme.Hom.geometricFiberAt f T t Ω` is exactly `pullback f` along
  `Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField t) Ω)) ≫
  T.left.fromSpecResidueField t ≫ T.hom`. This allows any chosen algebraic closure,
  rather than restricting to a particular construction of `AlgebraicClosure`.
- Geometric points are a reference to the dependency's definition, not a second independent
  definition in this node. They remain `Spec (.of Ω) ⟶ T.left` for an algebraically closed
  field, identified with a point and residue-field map by `Scheme.SpecToEquivOfField Ω T.left`.
- A section `σ` of `f`: `σ : SplitEpi f` supplies exactly `σ.section_ : S ⟶ X` and
  `σ.id : σ.section_ ≫ f = 𝟙 S`. The induced section is reused from the source as
  `sectionBaseChange f σ.section_ σ.id T : T.left ⟶ pullback f T.hom`.
  `baseChange_section_characterization` states the two equations
  `σ_T ≫ pr_T = id_T` and `σ_T ≫ f_T = T.hom ≫ σ.section_`, and states uniqueness of
  a morphism satisfying them. Its first equation is precisely the section condition.
  The source `sectionBaseChange` is the universal lift; equivalently it is the base change
  of `σ` with the canonical identification `S ×_S T ≅ T`.

Dependencies and declarations read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (full structure signatures and docstrings read).
- `def-weil-scheme-over-base`: `Scheme.Over`, `Scheme.Hom.IsOver`, `Scheme.asOver`,
  `Mathlib.AlgebraicGeometry.Over`; bundled data use `CategoryTheory.Over` and `Over.mk`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`,
  `pullback.lift`, `pullback.map`, `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`;
  `HasPullbacks Scheme`, `Mathlib.AlgebraicGeometry.Pullbacks`. Mathlib's `Over.pullback`
  (full functor body read in `Mathlib.CategoryTheory.Comma.Over.Pullback`) packages these.
- `def-pc-module-pullback`: `AlgebraicGeometry.Scheme.Modules.tensorPullback`,
  `Sheaf.AlgebraicGeometry.TensorPullback`. Full module and definition were read; it is the
  explicit tensor pullback specified by the dependency, including its named functor-law proofs.
- `def-pc-scheme-fibre`: `Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField`,
  `fiberOverSpecResidueField`, `Mathlib.AlgebraicGeometry.Fiber`.
- `def-weil-residue-field`: `Scheme.residueField`, `Hom.residueFieldMap`,
  `fromSpecResidueField`, `Mathlib.AlgebraicGeometry.ResidueField`.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`, `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-geometric-point`: its recorded unbundled specification with `IsAlgClosed` and
  `Scheme.SpecToEquivOfField`, `Mathlib.AlgebraicGeometry.ResidueField`.
- `def-pc-section`: `CategoryTheory.SplitEpi`, `Mathlib.CategoryTheory.EpiMono`.
- Other reused existing declarations: `AlgebraicGeometry.baseChangeMap` and
  `isPullback_baseChangeMap`, `WeilConjectures.AlgebraicGeometry.PicardFunctor`;
  `AlgebraicGeometry.sectionBaseChange`, `WeilConjectures.AlgebraicGeometry.Picard.Defs`.
  Both full definitions and their docstrings were read, as were the section projection lemma
  and the base-change cartesian-square lemma.

Sources: the local blueprint/literature checkout is absent on this machine (the recorded
`.md` source path does not exist). The node and its stage-1 source audit were read, and the
external definitions were opened directly: https://stacks.math.columbia.edu/tag/01JX,
https://stacks.math.columbia.edu/tag/01K0, https://stacks.math.columbia.edu/tag/0095.
Tag 01K0 is currently numbered Definition 26.18.4; the source record's old numbering 26.18.2
has no effect on the mathematical content. The module does not alter the unit statement.

Edge cases checked before writing: `X`, `S`, `T` and `T'` may be empty; neither a point nor a
section is asserted to exist. A point clause is only bound after `t : T.left` is supplied;
if `T` is empty this produces no false existence assertion. A section of an empty-base
morphism is allowed; no nonempty instance is required. Base change along identity maps and
`f = id_S` uses the same pullback universal property. Module base change admits the zero
module and arbitrary modules, not just quasi-coherent or invertible modules. The field and
closure are of arbitrary characteristic. `u` is explicit and arbitrary, and every scheme,
residue field and chosen closure lives in that common universe; enlarging it accommodates
any input sizes. No automatically bound variables occur.

Searches (2026-10-11 UTC):

- `msearch.py ... leansearch "base change of a scheme and induced section of a scheme morphism"`:
  service unavailable (Internal Server Error), recorded as unavailable without a verdict.
- `msearch.py ... leanfinder "base change of schemes, morphisms, modules, geometric fibres and
  induced sections"`: eight hits, including `Scheme.Modules.pullback` and pullback tensor
  points; no declaration for this complete convention bundle.
- `msearch.py ... loogle "CategoryTheory.Limits.pullback, CategoryTheory.Limits.pullback.map"`:
  twelve hits, including `pullback.map`, its composition/id lemmas, and `Over` pullback lemmas.
- `msearch.py ... grep "baseChange|base_change|pullbackRightPullback|pullbackLeftPullback"
  AlgebraicGeometry`: 25 hits, principally morphism-property stability, Weierstrass curves,
  and pullback pasting. No complete bundle.
- `rg -n 'BaseChange|base change|pullback.map|fiber'` in project `lean/Sheaf` and source
  `WeilConjectures`: broad existing base-change uses; focused searches for declarations found
  `baseChangeMap` in `PicardFunctor.lean` and `sectionBaseChange` in `Picard/Defs.lean`, reused.
- `rg -n 'def-pc-base-change'` in `WeilConjectures` and `dag/lean_names_upstream.json`: no hits.
- `rg -n 'geometricFiber'` in source and project: source `Scheme.Hom.geometricFiber` in
  `GeometricFrobenius.lean` is only for a scheme over a field and its canonical algebraic
  closure, not a fibre at an arbitrary point with a chosen closure. Its signature and body
  were read. Source `Scheme.Hom.GeometricFiber` in `Morphisms/Finite/GeometricFiber.lean`
  is a set of lifting geometric points, not a scheme; its signature/docstring were read.
- `rg -n 'moduleBaseChange|geometricFiberAt|baseChange_morphism_projections|baseChange_iterated|
  baseChange_fiber|baseChange_section_characterization'` over Mathlib, source, project Lean,
  and upstream declaration index: only unrelated `KaehlerDifferential.moduleBaseChange` hits;
  none of the full declaration names added here exists.

Validation: the single module compiled cleanly on the server through `scompile.py` after
qualifying `Limits.pullback` in the module namespace (to avoid name resolution to module
pullback). Every theorem remains `sorry`; there are no compiler warnings. Delivery dry run
is the final verification; the independent second reader supplies the second-reading section.

## Second reading by H1

Independent review on 2026-10-11, with the item node, module and all nine dependency
nodes open. Verdict: the Lean renders every clause of the node; no statement or definition
repair was needed. Only this second-reading report was added. The item has no
`statement_change`, new definition nodes or dependency modules, so H12/H13 and the
correction/citer checks do not apply.

Source reading: the local literature checkout contains only indexes, not the blueprint or
Stacks sources. I obtained the upstream Stacks `schemes.tex` and `sheaves.tex` into this
sandbox and read `section-base-change`, `definition-base-change`, `definition-fibre`,
`section-ringed-spaces-functoriality-modules` and `definition-pushforward`, including their
surrounding assumptions. I also checked the tag pages [01JX](https://stacks.math.columbia.edu/tag/01JX),
[01K0](https://stacks.math.columbia.edu/tag/01K0),
[0095](https://stacks.math.columbia.edu/tag/0095) and
[03PO](https://stacks.math.columbia.edu/tag/03PO).
The examples of varieties over Q in the section introduction impose no assumptions on
the subsequent definitions. These definitions require arbitrary schemes and morphisms
and arbitrary sheaves of modules. Stacks writes the base factors in the opposite order;
the node explicitly chooses `X ×_S T`, which is exactly the order used in Lean.

My object/hypothesis/conclusion checklist and correspondence:

1. Arbitrary schemes X and S, and a morphism f: rendered by the explicit universe `u`,
   `{X S : Scheme.{u}}` and `(f : X ⟶ S)`. `Scheme` and `Scheme.Hom` in the recorded
   Mathlib module are locally affine locally ringed spaces and their morphisms.
   Verdict: exact; no geometric property or extra structure is assumed.
2. An arbitrary S-scheme T, including its structure morphism: `(T : Over S)`, with
   `T.left` and `T.hom`. I read `Scheme.Over`, `Scheme.Hom.IsOver`, `Scheme.asOver` and
   the body of `CategoryTheory.Over.pullback`. The bundled category is the recorded
   dependency's category Sch/S, not a category of affine or finite type objects.
   Verdict: exact, including the commuting condition on its morphisms.
3. X_T, pr_T and f_T, and the T-scheme structure: the reused
   `(Over.pullback T.hom).obj (Over.mk f)` has underlying scheme `pullback f T.hom` and
   structure map `pullback.snd f T.hom`; `pullback.fst f T.hom` is its map to X.
   The module docstring fixes these conventions. I read `pullback`, `fst`, `snd`,
   `lift`, `map` and the Scheme pullback instance. Verdict: the chosen universal
   fibre product and its actual projections, without a private redefinition.
4. An arbitrary S-morphism h from A to B, and h_T over T: `{A B : Over S}` and
   `(h : A ⟶ B)`; `(Over.pullback T.hom).map h` is already a T-morphism.
   `baseChange_morphism_projections` states its first projection is `fst ≫ h.left`
   and its second is `snd`. The functor body is the universal lift of precisely
   these maps. Verdict: exactly h ×_S id_T, with both projection clauses present.
5. An arbitrary S-morphism g from T' to T, and g_X: `{T T' : Over S}` and
   `(g : T' ⟶ T)`; the reused `baseChangeMap f g` is, by its source body in
   `PicardFunctor.lean`, `pullback.map` with maps `id_X`, `g.left`, `id_S`.
   `baseChange_iterated` gives an isomorphism to
   `pullback (pullback.snd f T.hom) g.left` whose two projection composites are
   exactly `baseChangeMap f g` and `pullback.snd f T'.hom`.
   Verdict: the prescribed cartesian identification, not an arbitrary isomorphism.
6. Any O_{X_T}-module sheaf F and its base change along g_X:
   `Scheme.Modules.moduleBaseChange f g` has domain `(Limits.pullback f T.hom).Modules`
   and codomain `(Limits.pullback f T'.hom).Modules`, and its entire body is
   `Scheme.Modules.tensorPullback (baseChangeMap f g)`; apply `.obj F` to get F_{T'}.
   I read the recorded `TensorPullback.lean` module, including its ring map,
   `tensorPullbackObj`, morphism map and functor: the object is the explicit inverse
   image followed by change of rings along g-sharp, as in Tag 0095.
   Verdict: uses the dependency's tensor formula for arbitrary module sheaves.
7. A point t of T, its residue field and canonical morphism:
   `(t : T.left)`, `T.left.residueField t` and `T.left.fromSpecResidueField t`.
   I read their signatures/bodies in `ResidueField.lean`: the field is the local
   stalk modulo its maximal ideal and the point morphism is induced by the quotient.
   The morphism to S is `T.left.fromSpecResidueField t ≫ T.hom`.
   Verdict: exactly the node's residue field and canonical map, not a chosen rational point.
8. X_t equals the scheme-theoretic fibre of pr_T: `baseChange_fiber` identifies
   `pullback f (T.left.fromSpecResidueField t ≫ T.hom)` with
   `(pullback.snd f T.hom).fiber t`, respecting both the map to X and the map to
   `Spec κ(t)`. I opened the recorded `fiber`, `fiberι` and
   `fiberToSpecResidueField`: these are the pullback and its two projections.
   Verdict: equality of geometric constructions up to their canonical isomorphism,
   with the residue-field scheme structure retained.
9. A chosen algebraic closure of κ(t), and X_bar_t:
   `(Ω : Type u) [Field Ω] [Algebra (T.left.residueField t) Ω]`
   `[IsAlgClosure (T.left.residueField t) Ω]` in `Scheme.Hom.geometricFiberAt`.
   I read `IsAlgClosure`: it asserts algebraic closedness and algebraicity, and
   the field-base embedding is supplied by the algebra structure. The body is
   the literal pullback along `Spec.map (CommRingCat.ofHom (algebraMap _ Ω))`
   followed by the canonical point map and `T.hom`. I read `Spec` and `Spec.map`.
   Verdict: an arbitrary chosen algebraic closure, with exactly the specified map.
10. Geometric points: reused as `Spec (.of Ω) ⟶ T.left` for an algebraically closed
    field, as explained in the module docstring. I read the recorded
    `Scheme.SpecToEquivOfField` signature and body: it identifies such morphisms
    with a point and a residue-field embedding. Verdict: the dependency's notion;
    no second definition or extra assertion about all geometric points was introduced.
11. A given section σ of f: `(σ : SplitEpi f)` has `σ.section_ : S ⟶ X` and
    `σ.id : σ.section_ ≫ f = id_S`. I opened the recorded `SplitEpi` structure.
    The reused `sectionBaseChange` in `Picard/Defs.lean` is the universal lift of
    `T.hom ≫ σ.section_` and `id_T`. Verdict: precisely a given section, with
    no extra surjectivity hypothesis and no assertion that f always has a section.
12. Induced section, both equations and uniqueness:
    `baseChange_section_characterization` first asserts its second projection is
    `id_T` (the section property), then its first projection is `T.hom ≫ σ.section_`,
    then quantifies over every `s : T.left ⟶ pullback f T.hom` satisfying both
    equations and concludes equality with the reused induced section.
    Verdict: all clauses, with the hypotheses and quantifiers in the correct order;
    the identification S ×_S T ≅ T is realized by this universal lift.

Edge cases: all schemes may be empty and the point/section clauses only apply when a point
or section is supplied. Arbitrary module sheaves include the zero object. Identity base
maps and f = id_S are included. There is no index set or integer n in this node, so empty
index sets and n = 0 introduce no missing case. No characteristic assumption is present.
All scheme and field variables use an explicit arbitrary common universe `u`, as do the
recorded scheme category and its module dependency; no fixed small universe or unbound
variable is introduced. IsAlgClosure adds exactly the algebraic-closure condition required
by the node, not an additional finite-extension condition.

Independent searches, using queries different from the first worker's:

- `msearch.py H1 def-pc-base-change leanfinder "scheme fibre over a point algebraic
  closure and pullback of sections"`: eight hits, including `Scheme.Hom.fiber`,
  `fiberToSpecResidueField`, `fiberOverSpecResidueField` and pullback-point constructions.
  These are existing ingredients used here, not this full convention bundle.
- `msearch.py H1 def-pc-base-change loogle "CategoryTheory.Over.pullback"`: twelve
  hits, including `Over.pullback`, its object/map equations, `pullbackId` and
  `pullbackComp`. I opened `Over.pullback`; scheme/morphism base change uses it directly.
- `msearch.py H1 def-pc-base-change leansearch "scheme geometric fibre at a point with
  a chosen algebraic closure of the residue field"`: unavailable, Internal Server Error;
  no verdict inferred from the unavailable service.
- Independent `rg` over Mathlib, `WeilConjectures` and project `lean/Sheaf` for
  `def.*(geometricFiber|geometric_fiber|geometricFibre)`, `def.*(baseChange|base_change)`
  and pullback-pasting isomorphism names found the existing field-base geometric fibre,
  etale-site points, set-valued geometric fibres, compactification/curve base changes and
  paper-specific constructions. I opened `Scheme.Hom.geometricFiber` in
  `GeometricFrobenius.lean`: its base is Spec k and its closure is the fixed
  `AlgebraicClosure k`, so it does not give this arbitrary-point/chosen-closure definition.
  I also opened `Scheme.Hom.GeometricFiber` in `Morphisms/Finite/GeometricFiber.lean`:
  it is a subtype of maps lifting a geometric point, not a scheme.
- A focused search for all six delivered declaration names over Mathlib algebraic
  geometry, the source repository, project Lean and `dag/lean_names_upstream.json`
  found no collision. Existing base-change maps and sections are reused by name.
  There is no exact existing declaration for the complete item, so the module is retained.

H5/H6/H8/H9: both definitions have concrete data; no definition contains `sorry`.
All four new theorem proofs are exactly `by sorry`. The node itself has an empty proof
list; each theorem docstring nevertheless gives the universal-property argument step by
step and names the dependencies. Every declaration has its source and
`(blueprint: def-pc-base-change)`; the module header and namespaces follow the contract,
and no line exceeds 100 characters. The node's `lean.statement` is verbatim the main
definition's signature. No mismatches found; Lean and node left unchanged.

Validation: independent `scompile.py H1 def-pc-base-change` of
`lean/Sheaf/AlgebraicGeometry/BaseChangeConventions.lean` compiled in 2.1 seconds,
exit code 0, with no errors or warnings. Delivery dry run and push follow this review.

## Worker report

Item: `lem-sfb-stack-quasi-coherent-scheme-restriction`.
Module: `Sheaf.AlgebraicGeometry.StackQuasiCoherentSchemeRestriction`.
Main declaration: `CategoryTheory.exists_moduliSchemeRestriction`.
The original statement, dependencies and proof are unchanged. There is one postponed
proof, the main theorem, with the complete six-step DAG argument in its docstring.
All auxiliary data are explicit constructions from existing APIs. The two structures
only package the conclusion of this theorem; neither is assumed as a hypothesis.
Their helper declarations belong to this node and are listed in `lean.declarations`.
No new node or dependency repair is needed.

The sources read are `stacks-sheaves.tex`, Tags 06WI
(`lemma-characterize-quasi-coherent`), 06WK (`lemma-quasi-coherent`) and 06WH
(`lemma-pullback-quasi-coherent`), together with `descent.tex`, 03DX
(`proposition-equivalence-quasi-coherent`)(1), 03LC
(`proposition-equivalence-quasi-coherent-functorial`)(1), and 06VE
(`lemma-equivalence-quasi-coherent-limits`)(1),(3),(4),(7).
The precomposition construction also follows the structural-ring equality and tensor
formula at 06TW/06WE. In particular, 06VE(6) warns that the big-site associated-sheaf
functor need not be left exact; no such assertion occurs here.

Hypotheses and clauses, with the node and final file read together:

1. The size convention is rendered by explicit `u v w m`. Schemes have universe `u`;
   the total site's morphisms and objects have independent bounds `v` and `w`.
   The ambient coefficient bound is the dependency's `max (u + 1) v w`.
   Both based categories in the functorial clause use the same chosen ambient site
   bounds; this is the common-universe convention, not an equality between the object,
   morphism and scheme universes. There are no extra smallness binders on the theorem.
2. An arbitrary scheme is `{S : Scheme.{u}}`; the fibred category is
   `(C : BasedCategory.{v, w} (Over S))` with precisely
   `(hC : IsFibredInGroupoids C)`. Its topology and rings are the recorded
   `moduliFppfTopology C` and `moduliModuleRings C hC`, not a site of isomorphism
   classes or an atlas. No algebraic-stack instance appears.
3. Quasi-coherence on the total site is `ModuliQCoh C hC`, an abbreviation for
   the full subcategory of Mathlib's `SheafOfModules.IsQuasicoherent`, hence the
   local-free-presentation predicate from the recorded dependency. There is no
   finiteness condition on the generators or relations. This subcategory appears
   inside the conclusion's functors, so the result quantifies over every such F.
4. For every `x : C.obj`, `schemeTestBase C x` is its actual underlying scheme T.
   The field `restriction x` is a functor into ordinary Zariski modules on T,
   and `quasicoherent x F` asserts the same Mathlib predicate for its value F_x.
   Coefficients and module sections use the existing sectionwise `ULift` transport,
   with its canonical down-map ring equivalence. This permits ambient-size modules
   without shrinking them to the universe of T.
5. The tensor meaning of u* is explicit: `schemeTestPullback` uses the canonical
   module pullback on the lifted ordinary structure sheaves. Its existence is the
   existing universe-general pushforward-adjoint theorem, and its unit, identity
   and composition maps are the corresponding canonical Mathlib constructions.
   `tensorPullback_agreement` identifies this functor, after the existing module
   coefficient lift, with the dependency's `Scheme.Modules.tensorPullback`.
   `tensorPullback_agreement_sections` identifies the actual section 1 tensor s
   with `Scheme.Modules.tensorPullbackSection`, including restriction from u^-1(top)
   to top. Thus the recorded tensor pullback and its normalization are used, with
   no equality imposed on scheme and coefficient universes. No alternate
   `Scheme.Modules.pullback` is used.
6. The entire slice sheaf, rather than just its terminal evaluation, is specified.
   `realization x` is defined on ALL ordinary quasi-coherent modules on T and lands
   in module sheaves on the actual site `(moduliFppfTopology C).over x`.
   For every `z : Over x`, `realization_sections x M z` identifies its value with
   Gamma(T_z, (base(z.hom))^* M). The additive equivalence and `realization_smul`
   give the module identification. `realization_restriction` specifies every
   restriction map by the concrete `schemeTestSliceTransition`: pull back the
   section, apply the tensor compositor, and use the commuting triangle in Over x.
   `realization_naturality` specifies every map of associated sheaves by tensor
   pullback of the ordinary module map. `realization_counit x F` identifies this
   sheaf with the existing `F.obj.over x`. Its section formula is explicitly
   `realization_counit_sections`. The projection C/x to Sch/T is the equivalence
   coming from the fibred-groupoid axioms, as explained in proof step 1; the
   coordinates retain its objects and arrows and give precisely the displayed
   sheaf on (Sch/T)_fppf, without replacing C by isomorphism classes.
7. In particular, `sections x F` is the additive global-section comparison
   F(x) ≃ Gamma(T,F_x), and `sections_smul` makes it linear over the actual
   structural rings. `sections_naturality` gives naturality for every F -> G.
8. For every actual arrow `a : y ⟶ x`, `comparison a F` is an isomorphism from
   tensor pullback of F_x along its actual scheme map to F_y.
   `comparison_sections` fixes the restriction-induced map by the tensor unit.
   Together with the counit formula on every slice object and
   `comparison_comp`, this specifies its local restriction coordinates too.
   `comparison_naturality` is its naturality square for F -> G.
   `comparison_id` uses the actual tensor unitor, and `comparison_comp` uses
   the actual tensor compositor and the base functor's map_comp equality.
   Neither a cartesian action nor arbitrary comparison maps are hypotheses.
9. `realization_fullyFaithful x` is full faithfulness on all ordinary
   quasi-coherent test modules, including ones not given as restrictions of global
   modules on C. It implies the node's unique compatible isomorphism: for another
   ordinary realization M with a specified isomorphism to F|C/x, compose that
   isomorphism with `realization_counit x F` inverse and lift uniquely through
   full faithfulness. Lift the inverse too; faithfulness makes the composites
   identities. This also gives uniqueness of every compatible ordinary module map.
10. `unit_quasicoherent`, `unit_comparison`, and `unit_sections` identify the
    structure module with the ordinary structure module, by the identity map on
    regular functions. `tensor_quasicoherent`, `tensor_comparison` and
    `tensor_sections` identify the tensor products using the existing
    `siteSheafTensorRight` and `siteSheafTensorTmul`. The pure-tensor formula on
    every test, and the slice restriction formulas above, fix the natural tensor
    comparison on local sections and hence its naturality in both factors.
11. `surjective_iff` states both implications as an iff, for every morphism of
    quasi-coherent modules. Its left side is the existing
    `Presheaf.IsLocallySurjective` for the underlying sheaf map on C_fppf.
    Its right side is `∀ x, Epi ((restriction x).map f)` in ordinary Zariski
    module sheaves. In this abelian sheaf category, epimorphism is exactly local
    sheaf surjectivity, not surjectivity on whole-space sections.
12. The second conjunct of the theorem quantifies over every fibred category D,
    its fibred-groupoid hypothesis, and every `BasedFunctor D C` a.
    Its witness `ModuliQuasicoherentPrecomposition hD hC a` supplies continuity,
    a right adjoint to set-sheaf precomposition, and finite-limit preservation;
    hence this is the geometric inverse-image direction Sh(D) -> Sh(C).
    The actual structural-ring isomorphism is constructed by whiskering `a.w`
    with Gamma and the existing coefficient lift. The formula is identity on
    functions on the common underlying scheme; no structural map is chosen.
    `moduliModulePrecomposition` is the existing continuous-module functor for
    that map and has sections M(a(d)), the same restrictions and the same maps.
    `moduliRawPrecomposition` first retains the ring a^-1 O_C.
    `moduliTensorPrecomposition` is literally the existing sheafified scalar
    extension O_D tensor_(a^-1 O_C) a^-1 M along the inverse structural-ring
    isomorphism. `tensor_comparison` in this witness identifies this tensor
    formula with module precomposition for all module sheaves;
    `tensor_sections` is r tensor s -> r s with the explicit structural ring
    map, and `tensor_naturality` specifies every module morphism.
    Finally its `quasicoherent` field states preservation for every F in ModuliQCoh.
13. Neither theorem binder nor witness construction imposes algebraicity,
    quasi-compactness, finite type, finite presentation, representability or
    geometric flatness on C, D, a, or any scheme arrow.

Dependency declarations used:

- `def-weil-size-convention`: the convention record has no declaration;
  universes and the ambient bounds above implement it directly.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-sfb-stable-pointed-moduli-groupoids`:
  `CategoryTheory.IsFibredInGroupoids`, with Mathlib `BasedCategory` and
  `BasedFunctor`, exposed by `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`.
  Only the general fibred-groupoid vocabulary is used, not stable-curve hypotheses.
- `def-sfb-stack-quasi-coherent-algebra`: `moduliSchemeForget`,
  `moduliFppfTopology`, `moduliStructureSheaf`, `moduliModuleRings`, and the
  existing slice sheafification instances, from
  `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`.
- `pqf-def-coherent`: its repaired module
  `Sheaf.AlgebraicGeometry.CoherentFiniteType` exposes the existing
  `SheafOfModules.IsQuasicoherent`. This item uses that predicate, not the
  stronger finite-type conjunction or coherence.
- `def-pc-module-pullback`: the explicit `Scheme.Modules.tensorPullback` and
  normalized `tensorPullbackSection`, publicly exposed by
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`.
- Additional reused universe APIs: `CochainUniverseTransport.ring`, `.ringFunctor`,
  `.functor` from `Sheaf.CategoryTheory.CochainCoefficientUniverseTransport`,
  `module_pushforward_isRightAdjoint_of_universes` from
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.PullbackExistsOfUniverses`, and existing
  `hasSheafify_coefficientUniverse` / `wEqualsLocallyBijective_coefficientUniverse`.
  The six small instance wrappers apply these existing results directly; they
  introduce no new axiom, theorem obligation, or categorical structure.
- The proof imports are
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`
  (`SheafOfModules.exists_localizedSiteTensorRestriction`) and
  `WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`.
  General-site localization is the existing `SheafOfModules.over` /
  `overFunctor` / `overMap` from Mathlib. The recorded
  algebraic-space quasi-coherence module is already publicly imported by the
  stack-algebra dependency. The currently unstated ringed-fppf inverse-image and
  big-fppf scheme-equivalence proof nodes are cited in the proof docstring;
  the statement itself requires no missing declaration from them.

Edge cases checked by reading the actual signature and formulas: empty total
category; empty test scheme and zero structure ring; zero module and zero maps;
arbitrary, possibly infinite presentations; automorphisms in C; identity arrows;
composable arbitrary nonflat scheme maps; non-quasi-compact tests. No whole-space
section-surjectivity claim replaces sheaf surjectivity. The slice comparison has
actual Over objects and maps, so stabilizers have not been discarded. Scalar
universes are independently bound, and existing lifts place both rings and module
carriers in the ambient universe; no forced equality with the site universe occurs.

Searches actually run (launcher results are in the sandbox search log):

- LeanFinder: "A quasi coherent module on a category fibred in groupoids restricts
  to a quasi coherent Zariski module on every scheme test compatibly with tensor
  pullback and surjections". Eight generic local-presentation/quasi-coherence hits;
  no statement of the complete scheme-test comparison.
- Loogle: `SheafOfModules.IsQuasicoherent, SheafOfModules.pullback`. Zero hits.
- Launcher Mathlib grep: `moduli.*[Mm]odule|[Ff]ibred.*[Qq]uasi|[Bb]igFppf`.
  Zero hits.
- LeanSearch: "A quasi coherent module on a fibred fppf site restricts on each scheme
  test to its quasi coherent Zariski module with canonical tensor base change and
  detection of surjections". Eight generic `IsQuasicoherent` /
  `QuasicoherentData` declarations, no match for this theorem.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf` and
  `dag/lean_names_upstream.json` for the scheme-restriction names and
  quasi-coherent/scheme/restriction wording: no exact theorem. Direct
  `grep -rn` of this node id in `lean/WeilConjectures`: no hits.
- Direct source searches located the existing general-site quasicoherence,
  pullback, slice, coefficient transport and tensor definitions used above.
  They are reused; no second definition of these mathematical notions is supplied.

Validation: prescribed `scompile.py` compiled the complete module cleanly
against the current server sources. A subsequent repeat exposed costly unfolding
of helper abbreviations; the construction helpers are now ordinary definitions
so their bodies need not expand throughout the statement. The 60-second limit
is unchanged. The adjusted final module compiled cleanly in 34.0 and 40.3 seconds
for the sandbox and library checks respectively. There are no diagnostic commands in the delivered module and only the
expected postponed theorem proof. No `STATEMENT-DISPUTED` issue or node fault was
found. Delivery dry run and push results are recorded by the delivery wrapper.

## Second reading by Q04

I reopened the node, the complete source file, and the cited Stacks clauses for
this second pass. This is a self-check by the dispatched worker, not a claim that
another agent reviewed the delivery; the dispatch explicitly forbids starting
other agents, and the maintainer performs the independent delivery review.

The clause checklist above was checked against the final structure fields and
main theorem. The initial draft was insufficient in three places, all repaired:
full faithfulness initially quantified only over images of global modules, so
`realization` and its fully faithful functor now cover every ordinary test module;
the slice formula initially supplied only global evaluations, so its value,
restriction, map and counit equations now cover every object and arrow of C/x;
the functorial clause now includes the actual sheafified extension-of-scalars
construction, normalized on every local tensor and natural in every module map.

I also checked the recorded tensor-pullback dependency rather than equating
carrier universes: the final witness includes agreement with its explicit
`tensorPullback` and normalized `tensorPullbackSection` after the existing
coefficient lift. Identity/composition fields use the specified adjunction
comparisons; surjectivity is local on sheaves in both directions; all scheme
maps remain arbitrary. The source's right-exactness warning is respected.
The two witness structures are conclusions, and every helper is built from
existing declarations with real data. The node's statement and proof have
not been corrected or weakened. The compile-time universe repairs only made
instance applications explicit and used the same canonical ULift throughout.

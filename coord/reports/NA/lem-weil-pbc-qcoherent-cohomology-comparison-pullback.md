## Worker report

The module `Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback` states
`AlgebraicGeometry.Scheme.Modules.exists_qcoherentCohomologyComparisonPullback`.
Its only postponed proof is the theorem's `sorry`. The helper
`qcoherentPullbackSection` has real construction data: the canonical tensor-section
unit, normalized composition isomorphisms, equality transport around the square,
and the pullback of the given module morphism. No arbitrary coefficient map is
introduced. This is a helper of the same comparison notion, not a new independent
notion or theorem.

Hypotheses and clauses:

- Schemes are `X Y : Scheme.{u}`; quasi-compactness is `CompactSpace X/Y` and
  separatedness is `Scheme.IsSeparated X/Y`. There is no assumption on the scheme
  morphism `g : Y ⟶ X`. The sheaves `F : X.Modules`, `G : Y.Modules` have exactly
  `F.IsQuasicoherent` and `G.IsQuasicoherent`.
- The explicitly corrected coefficient operation is the already defined
  `liftedCoherentEtaleSheaf F`: sectionwise `AddCommGrpCat.uliftFunctor.{u+1,u}`
  applied to the recorded `etaleTensorSectionsSheaf F`. Both schemes use this same
  coefficient category. See the correction below for the original coefficient cases.
- A single existential binder `∃ c : ∀ X ... F ... q, ...` supplies the family
  simultaneously over all schemes, modules and nonnegative degrees. Each value is
  an additive equivalence `Sheaf.H (liftedCoherentEtaleSheaf F) q ≃+
  ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F)`.
  `Sheaf.H` is the Ext presentation used by the recorded `Etale.cohomologyMap`;
  the dependency record explicitly delegates its resolution comparison to stage 3.
- The first conjunct normalizes degree zero on every section `s : Γ(F, ⊤)`.
  Under `Sheaf.H.equiv₀`, the input is `ULift.up` of the tensor-unit pullback of
  `s` to the terminal etale object. Its output is
  `globalSectionsFunctor.toRightDerivedZero.app F s`, the canonical section-to-H0
  map. Thus the comparison is down on sections, with the terminal tensor-unit
  identification; it is not an arbitrary degree-zero additive equivalence.
- For every `ψ : (tensorPullback g).obj F ⟶ G`, the second conjunct supplies its
  adjoint coefficient morphism `θ : L(F_et) ⟶ g_* L(G_et)`. The equation for EVERY
  etale object `U` and EVERY section `s` fixes all its components. Its value is
  `ULift.up (qcoherentPullbackSection ... s)`: pull back along the first projection
  of `U ×_X Y`, identify the two composites around the pullback square, undo the
  tensor composition along the second projection and `g`, then apply the pullback
  of `ψ`. These formulas determine θ uniquely, since every lifted section is up
  of a section and sheaf morphisms are determined by components. The existential
  is asserting this map exists; it is not assuming an unspecified map as input.
- The inverse of `Etale.upperStarLowerStarAdjunction.homEquiv` gives exactly
  `ψ_et : g^-1 L(F_et) ⟶ L(G_et)`. `Sheaf.H.map` after the EXISTING
  `Etale.cohomologyMap` is its cohomology pullback. The other side is precisely
  `moduleCohomologyFMap g` applied to the adjoint of ψ under the recorded
  tensor-pullback adjunction. The elementwise equality expresses the required
  equality of additive homomorphisms, for all degrees and all input classes.
- The third conjunct explicitly states the scalar specialization for every
  `a : Γ(X, ⊤)`. It uses the existing `F.smulHom a` (multiplication by the
  restriction of a on each open), `coherentEtaleMap` for its lifted sectionwise
  action, and `moduleCohomology.map` for its action on module cohomology. It is the
  identity-morphism specialization of the preceding naturality assertion.

Dependency declarations used (modules and names):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme` / `AlgebraicGeometry.Scheme`.
- `def-weil-pbc-scheme-conventions`: `None` / `None`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.Coherent` / `AlgebraicGeometry.RingedSpace.IsCoherent`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules` / `CategoryTheory.ringedSiteModules`.
- `def-sc-etale-qcoherent-module`: `Sheaf.AlgebraicGeometry.EtaleTensorSectionsSheaf` / `AlgebraicGeometry.Scheme.Modules.etaleTensorSectionsSheaf`.
- `pqf-def-cohomology`: `Sheaf.Paper.PQFCohomology` / `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`.
- `def-weil-pbc-etale-cohomology`: `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek` / `AlgebraicGeometry.Etale.cohomology`.
- `def-pc-module-pullback`: `Sheaf.AlgebraicGeometry.TensorPullback` / `AlgebraicGeometry.Scheme.Modules.tensorPullback`.
- `def-weil-pbc-cohomology-pullback`: `WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance` / `AlgebraicGeometry.Etale.cohomologyMap`.
- `def-weil-pbc-module-cohomology-fmap`: `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap` / `AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap`.
- `def-weil-size-convention`: `None` / `None`.
- `def-pbc-canonical-coherent-etale-comparison`: `Sheaf.AlgebraicGeometry.CanonicalCoherentEtaleComparison` / `AlgebraicGeometry.Scheme.Modules.canonicalCoherentEtaleComparison`.

For coherent's quasi-coherent clause the declaration is the existing Mathlib
`SheafOfModules.IsQuasicoherent` (as the Coherent module's docstring states), not
`IsCoherent`. For general ringed-site modules the recorded abbreviation is the
same Mathlib `SheafOfModules`, specialized here by `X.Modules`.
The convention nodes have no declaration or module by design.
`def-pbc-canonical-coherent-etale-comparison` is cited only for its already defined
`liftedCoherentEtaleSheaf` and `coherentEtaleMap`, both of which accept arbitrary
schemes. The proper-scheme-over-a-field comparison itself is NOT used to replace
this statement. No field or properness assumption has been added.

All recorded proof-dependency modules are imported as proof imports, except
`lem-weil-pbc-ringed-site-cech-refinement-square`, which has no recorded Lean module
yet. The separated-affine-intersection Mathlib leaf imports
`Mathlib.AlgebraicGeometry.Morphisms.Affine`. The complete natural-language six-step
proof is in the theorem docstring: affine covers and intersections; affine
acyclicity with the coefficient lift; invertible Cech/module edges and down;
cover independence via refinements; the pullback square; scalar specialization.

Edge cases checked: q = 0 has the explicit normalization, not merely an unspecified
isomorphism. q > 0 is unrestricted. Zero modules and empty schemes are allowed;
compactness and separatedness do not impose nonemptiness. Arbitrary g, including
identity and the empty-scheme map, is allowed. No affine inverse-image condition,
flatness, characteristic, dimension, Noetherian, finite-type, base-field or
properness assumption is present. The first projection need not be etale; tensor
pullback and the section unit apply to every scheme morphism. The second projection
is exactly the etale base-change object's structure map. Every variable and universe
is explicitly bound; `autoImplicit` is disabled.

Searches made:

- msearch leanfinder, "Quasi coherent cohomology Zariski etale comparison natural
  under arbitrary scheme pullback": eight hits on generic module pullback,
  pseudofunctor associativity and free modules; none gives this comparison.
- msearch loogle, "Sheaf.H, cohomologyMap": zero hits, unknown identifier Sheaf.H.
- msearch grep, "etale.*zariski|qcoh.*comparison", Mathlib AlgebraicGeometry:
  only `zariskiTopology_le_etaleTopology`.
- Direct rg of project and upstream sources for etaleTensorSections, cohomologyMap,
  comparison and lifted coefficients: existing fixed-scheme comparisons and the
  once-lifted proper-scheme canonical comparison, all read and reused where relevant;
  none states this simultaneous arbitrary-scheme pullback theorem.
- Direct rg of Mathlib and upstream for smulHom found the real multiplication map
  in `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`, rather than the similarly
  named `Modules.smul`, which acts only on a single section group.
- Searches for both proposed declaration names and this node id in upstream and
  project modules gave no duplicate declaration.

## Statement corrected

The old statement, verbatim:

Let $X,Y$ be quasi-compact separated schemes [def-pc-scheme, def-weil-pbc-scheme-conventions], $g:Y\to X$ a scheme morphism, and $F$ and $G$ quasi-coherent modules on $X$ and $Y$ respectively [pqf-def-coherent, def-weil-sheaf-of-modules-category]. Let $F_{\mathrm{et}},G_{\mathrm{et}}$ be their associated additive etale sheaves [def-sc-etale-qcoherent-module]. Fix either the identity coefficient operation $L$, or sectionwise $\operatorname{ULift}$ into a common larger coefficient universe, transporting addition and applying the same operation to every restriction map. For every $q\ge0$ there are canonical additive isomorphisms
$$c^q_{X,F}:H^q(X_{\mathrm{et}},L(F_{\mathrm{et}}))\xrightarrow{\sim}H^q(X,F),$$
where the right side is Zariski module cohomology [pqf-def-cohomology] and the left side is abelian etale cohomology [def-weil-pbc-etale-cohomology]. In degree zero $c^0$ is identity on sections, or $\operatorname{ULift.down}$ if $L$ is a lift. These isomorphisms are simultaneous for all such schemes and modules and natural as follows. For every module morphism $\psi:g^*F\to G$ [def-pc-module-pullback], let $\psi_{\mathrm{et}}:g^{-1}L(F_{\mathrm{et}})\to L(G_{\mathrm{et}})$ be adjoint to the sectionwise map sending a section on an etale $U\to X$ to its structural pullback on $U\times_XY$, followed by the pullback of $\psi$. Then
$$c^q_{Y,G}\circ H^q(\psi_{\mathrm{et}})\circ g_{\mathrm{et}}^*=\psi_{\mathrm{Zar}}^*\circ c^q_{X,F},$$
where $g_{\mathrm{et}}^*$ is [def-weil-pbc-cohomology-pullback] and $\psi_{\mathrm{Zar}}^*$ is the module cohomology map of the adjoint $F\to g_*G$ [def-weil-pbc-module-cohomology-fmap]. In particular, for $g=\mathrm{id}$ and multiplication by $a\in\Gamma(X,\mathcal O_X)$ these comparisons intertwine multiplication by $a$ on both cohomology groups (or by its lift on the left).

The identity coefficient case lies in `AddCommGrpCat.{u}`, and the arbitrary-larger
lift case can lie in `AddCommGrpCat.{max (u+1) v}`. The full recorded
`Etale.cohomologyMap` signature, on schemes `Scheme.{u}`, accepts exactly
`AddCommGrpCat.{u+1}`. The earlier sandbox probes demonstrate both mismatches;
there is no additional geometric hypothesis that repairs them. The correction
uses the explicit human authorization in this worker brief: record the common
u+1 lift with the degree-zero down map, following Stacks 03P2 and the size convention.
This is a CHANGE to the original coefficient quantification, recorded in
`statement_change`: the original identity and arbitrary-further-lift assertions
are not silently claimed proved by the once-lifted statement. No schemes are
universe-lifted, and no arbitrary map replaces the canonical cohomology pullback.
The source comparison itself is independent of its set-theoretic presentation;
this statement now uses the same coefficient bound as the supplied inverse-image
API. The corrected node is a subordinate lemma, not the blueprint unit statement.

Full citer audit (all nodes whose stmt_deps or proof_deps name this item):

- `lem-weil-pbc-smooth-curve-etale-structure-direct-images`: holds true. It requests
  the structure and finite-locally-free sheaves in the same coefficient universe
  as direct image and Artin–Schreier. The common u+1 lift supplies exactly that
  case, and scalar naturality is retained. No identity-coefficient or arbitrary
  higher-universe comparison is needed for its stated use. The citer is not edited.

No other citer was found. Only statement, stmt_deps (the size convention and
owners of the reused lifted-sheaf helpers), statement_change and lean change in
the copied item. Proof and proof_deps remain verbatim.

## Validation

Server-only scompile.py accepted the theorem and helper, with the scalar clause,
without warnings. The delivered file is checked again by deliver2.py --no-push;
the second reader will supply the independent reading before delivery. No local Lean compiler,
Lake build, live library write, or delivery push is used.


## Second reading by NA

I independently read the corrected node first against the local Stacks sources:
`etale-cohomology.tex`, theorem-zariski-fpqc-quasi-coherent (03P2), including
its affine and separated-case proof, and `cohomology.tex`,
lemma-functoriality-cech (01FD), including the tuple formula and resolution diagram.
03P2 assumes only a scheme and a quasi-coherent module; the qc separated restriction
here belongs to this subordinate node and its finite-cover proof, not an extra
Lean restriction. 01FD permits arbitrary ringed-space morphisms and f-maps.

My object/hypothesis/conclusion checklist, with the Lean open:

- Schemes X and Y, quasi-compact and separated: `Scheme.{u}`, `CompactSpace`,
  `Scheme.IsSeparated`. These are the node's schemes and properties. PASS.
- Arbitrary scheme morphism Y to X: `g : Y ⟶ X`, without properties on g. PASS.
- Quasi-coherent O-modules F and G: `F : X.Modules`, `G : Y.Modules`,
  `[F.IsQuasicoherent]`, `[G.IsQuasicoherent]`. The Coherent dependency explicitly
  delegates this clause to Mathlib's `SheafOfModules.IsQuasicoherent`; its primary
  declaration `RingedSpace.IsCoherent` is not mistakenly imposed. PASS.
- Associated additive etale sheaves: `etaleTensorSectionsSheaf` really evaluates
  at U as sections of `tensorPullback U.hom`; I read that definition and
  `etaleTensorSectionsPresheaf`, its unit/normalized-composition restrictions,
  and `tensorPullbackObj` (change of rings on inverse image). These are the
  recorded dependency notions, not Mathlib's different scheme pullback. PASS.
- The corrected common coefficient operation: `liftedCoherentEtaleSheaf F` is
  exactly `sheafCompose ... AddCommGrpCat.uliftFunctor.{u+1,u}` applied to that
  sheaf. I read its signature and body in CanonicalCoherentEtaleComparison.
  It has no properness or field binder. PASS against the corrected statement.
- All degrees and simultaneous family: the single outer `∃ c : ∀ X ... F ...
  (q : ℕ), ... ≃+ ...` precedes all naturality quantifiers. The source is
  `Sheaf.H`, the Ext presentation already explicitly adopted in the recorded
  etale-cohomology/pullback dependencies; the target is the actual right-derived
  `RingedSpace.moduleCohomology`. PASS; the resolution/Ext bridge remains the
  dependency's recorded stage-3 obligation, not a new definition here.
- Degree-zero normalization: the first conjunct applies `Sheaf.H.equiv₀.symm`
  to `ULift.up (tensorSectionsUnit terminal.hom F s)` and gives the canonical
  `globalSectionsFunctor.toRightDerivedZero.app F s`. Terminal etale objects
  are isomorphic to X; the tensor unit is the correct section identification.
  Hence this says down on sections, not an unspecified H0 equivalence. PASS.
- For every ψ from g*F to G: the second conjunct binds exactly
  `ψ : (tensorPullback g).obj F ⟶ G`. Its θ is not an arbitrary coefficient
  hypothesis: all components on all lifted sections are prescribed. I traced
  qcoherentPullbackSection through unit along the first projection, normalized
  composition, equality transport, inverse composition along the second
  projection and g, then the second projection's pullback of ψ. This is precisely
  the node's section formula on U times_X Y. Up is surjective onto the lifted
  group, so these formulas determine θ uniquely. PASS.
- The adjoint etale map is `(upperStarLowerStarAdjunction ...).homEquiv.symm θ`;
  the square uses `Sheaf.H.map` after the recorded `Etale.cohomologyMap`.
  The other side uses the recorded `moduleCohomologyFMap` on the adjoint of ψ
  under `exists_tensorPullbackAdjunction`. I read the resolution-based fmap
  definition and the upstream cohomologyMap signature/body. Directions, order,
  all q, all x, and both target groups agree. PASS.
- Scalar specialization: the final conjunct uses `F.smulHom a`, its existing
  `coherentEtaleMap`, and `(moduleCohomology ...).map (F.smulHom a)`.
  Reading `etale_zariski_qcoh_comparison` confirms coherentEtaleMap has the
  actual tensor-pullback components, so the left scalar is the lifted action
  of the restricted base function. PASS.

Correction/citer audit: the original identity-coefficient and arbitrary-higher-lift
cases do not fit the recorded `cohomologyMap` signature, which explicitly fixes
`AddCommGrpCat.{u+1}` for `Scheme.{u}`. The human expressly authorizes the common
u+1 formulation here. The correction records the removed quantification and down
normalization explicitly, and agrees with 03P2's universe-independent section
comparison under the size convention; it does not change a target unit. I parsed
every DAG node's stmt_deps and proof_deps independently. There is exactly ONE citer,
`lem-weil-pbc-smooth-curve-etale-structure-direct-images`, so no second citer exists
to open. I opened its statement and read its coefficient-universe and scalar-action
clauses: it places the structure sheaves in the common universe of abelian direct
image and Artin--Schreier and expressly permits the sectionwise lift. Its recorded
holds:true use is valid in that formulation. Text hits in the three ringed-site
nodes merely mention this item outside dependency lists and are not omitted citers.

Edge cases: q=0 is explicitly normalized, all positive q are included. Zero
modules, empty schemes, identity g, and maps from the empty scheme are admitted.
No cover/index type is a hypothesis, so an empty affine cover introduces no
nonempty-index exclusion. There is no field, characteristic, flatness, finite type,
Noetherian, affine inverse-image, or properness assumption. The universe u is
arbitrary; the coefficient successor is the explicit recorded correction rather
than a hidden equality of site universes. Every variable is bound with autoImplicit
false. The helper has actual construction data and no sorry. Only the main named
theorem is postponed; its docstring follows all six DAG proof steps, including
refinements, the totalization sign, and scalar specialization. There are no new
nodes or dependency modules in this delivery, so H12/H13 introduce no extra audit.

Independent searches: msearch leanfinder query "quasicoherent module cohomology
isomorphism change scheme naturality" returned eight module/group-cohomology
hits, none this assertion. msearch loogle query "CategoryTheory.Sheaf.H.map"
returned the existing coefficient-map API (reused), not this comparison. Direct
rg on Mathlib AlgebraicGeometry, upstream WeilConjectures AlgebraicGeometry,
and this project's lean/Sheaf for etale/Zariski comparisons, this theorem name,
and qcoherentPullbackSection found no duplicate arbitrary-scheme-pullback theorem.
I opened EtaleZariskiQcohComparison and CanonicalCoherentEtaleComparison: the former
is fixed-scheme module-map naturality; the latter's chosen comparison is restricted
to proper schemes over a field. Neither replaces this node. Their general helper
constructions are correctly reused.

Mismatches found: none in the supplied corrected Lean or node record. I retained
the statement, helper, correction and signature verbatim. The second reading adds
this independent source/interface/citer audit; no mathematical rewrite was needed.

Second-reader validation: server scompile.py passed the delivered module in 4.8 s
with no diagnostics (nice 19, two threads, 60-second per-file limit). Its private
overlay also compiled the required side-only imports separately within the limit.

I also independently attempted msearch leansearch: "quasi coherent etale Zariski
cohomology comparison natural for morphisms of schemes". The service returned
UNAVAILABLE (Internal Server Error); no mathematical search verdict is inferred.
LeanFinder, Loogle and direct source searches above supplied the fallback checks.

## Worker report

The module `Sheaf.CategoryTheory.Sites.FreeRepresentableModuleExtEvaluation` states
`CategoryTheory.free_representable_module_ext_evaluation`, with its proof exactly `by sorry`.
There are no new definitions, new nodes, dependency repairs or statement corrections. Only
`lean` changes in the existing item node. The source is Stacks, sites-cohomology.tex, Tags
07AC and 03FD, with the object-resolution convention in lemma-cohomology-of-open; these
source passages were read. The natural-language proof in the docstring follows all four
steps of the DAG proof, including the same-universe Ext smallness justification.

For readability in this report only, put P = `(PresheafOfModules.free R.obj).obj
(yoneda.obj U)`, E = `(PresheafOfModules.sheafification (𝟙 R.obj)).obj P`, F =
`sheafToPresheaf J AddCommGrpCat.{u} ⋙ (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U)`,
and G = `SheafOfModules.toSheaf R ⋙ F`. These are written out in the actual theorem;
there is no local notation, hidden let, chosen object, or duplicate free-module construction.

The hypothesis and clause correspondence is:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Small site in one universe containing objects and arrows | `{C : Type u} [SmallCategory C] (J : GrothendieckTopology C)`. Grothendieck topologies encode the associated covering sieves. Since C is u-small, their arrow and object indexing sets are in u; no subcanonical or global pullback hypothesis is imposed. The site dependency explicitly retains `Sheaf` and right-derived object cohomology for this encoding. |
| Sheaf R of commutative rings in that universe | `(R : Sheaf J RingCat.{u})` with `_hcomm : ∀ (V : Cᵒᵖ) (a b : R.obj.obj V), a * b = b * a`. The existing Ring structures and ring-valued restriction maps are retained; the displayed property is exactly commutativity in every value. This is equivalent to a CommRingCat-valued sheaf and avoids a replacement coefficient construction. |
| Sheaves of R-modules | `ringedSiteModules.{u} R`, the recorded transparent abbreviation for `SheafOfModules.{u} R`. All module values are in u. |
| Any object U | `(U : C)`, without a terminal-object assumption. |
| P_U(V) is the free R(V)-module on arrows V to U | P above is Mathlib `PresheafOfModules.free` applied to `yoneda.obj U`; `freeObj` uses `ModuleCat.free` on precisely those arrow sets. |
| Restriction sends r e_a to R(h)(r) e_(a h) | The `freeObj.map` construction is the semilinear `ModuleCat.freeDesc` taking a generator to the generator indexed by `yoneda.map`; thus it precomposes a with h and restricts r. This is inherited data, not an arbitrary map. |
| E_U is the module sheafification, with unit eta | E is the recorded `PresheafOfModules.sheafification (𝟙 R.obj)` applied to P. `sheafificationHomEquiv (𝟙 R.obj) α` is exactly precomposition by `(sheafificationAdjunction (𝟙 R.obj)).unit.app P`, with the identity restriction of scalars. |
| The module category has enough injectives | The first existential witness `_hI : EnoughInjectives (ringedSiteModules.{u} R)` is a conclusion. The next witness `_hExt : HasExt.{u} ...` supplies the technical Ext size bound, also as a conclusion; neither is an extra hypothesis. |
| Natural additive isomorphism Hom(E_U,N) to N(U) | `θ : preadditiveCoyoneda.obj (op E) ≅ G`. Both functors take values in AddCommGrpCat, so its components and their inverses are additive isomorphisms. |
| theta(alpha) = (alpha eta)_U(e_id) | The first conjunction evaluates `sheafificationHomEquiv (𝟙 R.obj) α` at `op U` on `ModuleCat.freeMk (𝟙 U)`. The definition of that equivalence identifies it with the actual unit composite. |
| Inverse sends a section s to the unique sheaf map with r e_a mapped to r N(a)(s) | The second conjunction quantifies N, s, V, a and r and gives this equality for `θ.inv.app N s` after `sheafificationHomEquiv`. Being an inverse is part of `θ`; the generators span P and the sheafification adjunction supplies uniqueness. |
| theta_(N')(b alpha) = b_U theta_N(alpha) | This is exactly the naturality field `θ.hom.naturality b`, evaluated on alpha. G.map b is b's component at U, and preadditiveCoyoneda maps b by postcomposition. |
| All module sheaves M and all q >= 0 | The natural isomorphisms x and y are functor isomorphisms on the entire module category, indexed by `q : ℕ`. The following formulas quantify M and every InjectiveResolution M. |
| Ext_R^q(E_U,M) is compared with module-derived evaluation | `x q : (Abelian.extFunctor q).obj (op E) ≅ G.rightDerived q`. `Abelian.Ext` is the existing derived-category Ext of def-pc-ext, rather than a newly defined substitute. |
| Both module derived functors computed by injective module resolutions | `Functor.rightDerived` is Mathlib's injective-resolution construction. `I.isoRightDerivedObj G q` identifies its value with the homology of the evaluated module resolution. `I.extMk s ... hs` is the class in the recorded Ext/resolution comparison of a Hom cocycle s; its kernel is the Hom coboundaries, giving Ext = H^q Hom(E,I). |
| First comparison induced by theta in each degree for every resolution | The third conjunction, inside x and y, quantifies every I, degree q, Hom cocycle s, and evaluation cycle c with `iCycles q c = θ.hom.app (I.cocomplex.X q) s`. It asserts that x sends `I.extMk s ...` to the class `homologyπ q c` under `I.isoRightDerivedObj G q`. Naturality of θ at the differential identifies the two complexes. This fixes the map on every Ext class, not just abstract isomorphism types. |
| Module-derived evaluation compared with H^q(U,M_ab) | `y q : G.rightDerived q ≅ SheafOfModules.toSheaf R ⋙ F.rightDerived q`. `toSheaf R` is exactly the underlying abelian sheaf. `F.rightDerived q` is object cohomology as defined in part (2) of the dependency, not global sections at an assumed terminal object. |
| Canonical second comparison | The final clause gives the arbitrary-resolution formula from the existing general comparison: for a module resolution I, an abelian resolution K, and every augmentation-compatible lift phi, y followed by K's resolution comparison equals I's resolution comparison followed by the homology map of the evaluated phi. Thus the map is independent of resolutions and lifts and uses the source's canonical coefficient comparison. |
| Comparisons natural in M | x and y are natural isomorphisms of functors; this includes every coefficient map, rather than just separate objectwise additive equivalences. |
| Degree zero is theta followed by identity on M(U) | The fourth conjunction says `x 0` sends `Ext.mk₀ α` to `G.toRightDerivedZero.app M (θ.hom.app M α)`. The fifth says `G.toRightDerivedZero ≫ (y 0).hom = whiskerLeft (toSheaf R) F.toRightDerivedZero`. Under the standard degree-zero identifications these are theta and identity respectively. |
| No abelian injectivity or integer-flatness assumption | The only ring hypothesis is commutativity. The only class witnesses for module injectives/Ext size are existential conclusions. In particular no injectivity of `toSheaf R M`, no flatness, and no terminal, subcanonical, or projectivity assumption occurs. |

This node compares Ext and cohomology groups (the degree-indexed right derived functors).
It does not replace a statement asserting an isomorphism of complexes with a weaker assertion
about their homology. The cocycle normalization records exactly how the degreewise theta map
computes these group isomorphisms on every module resolution.

Dependency interfaces read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `CategoryTheory.Precoverage.IsSiteForCoverings`
  and its documented retention of `Sheaf J` and object cohomology. This theorem uses the
  associated Grothendieck-topology encoding directly, with no extra coverage axioms.
- `def-weil-size-convention` is a metatheoretic convention, not a Lean declaration; the
  explicit common universe `u` realizes it here.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification`, `sheafificationHomEquiv`, and
  `sheafificationAdjunction` (including its actual unit formula).
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution`:
  `CategoryTheory.Injective` and `InjectiveResolution`; these are imported through the
  public injective-Ext/derived modules.
- `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`: `CategoryTheory.Abelian.Ext`
  and `Ext.mk₀`; `extFunctor` packages the same Ext groups functorially.
- `Mathlib.CategoryTheory.Abelian.RightDerived`: `Functor.rightDerived`,
  `InjectiveResolution.isoRightDerivedObj`, and `Functor.toRightDerivedZero`.
- The ordinary additive represented functor is `preadditiveCoyoneda.obj (op E)`.
  Free representability uses the recorded Mathlib match
  `PresheafOfModules.freeYonedaEquiv` in `.Presheaf.Generator`.
- The stated proof imports are
  `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses` /
  `SheafOfModules.isGrothendieckAbelianOfUniverses`,
  `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives` /
  `IsGrothendieckAbelian.enoughInjectives`,
  `WeilConjectures.CategoryTheory.Abelian.ExtRightDerivedCocycleComparison` /
  `exists_ext_rightDerived_cocycle_comparison`,
  `Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison` /
  `module_abelian_evaluation_comparison_general` (the additional declaration recorded
  in the dependency), and `Mathlib.CategoryTheory.Abelian.Injective.Ext` /
  `InjectiveResolution.extAddEquivCohomologyClass` and `extMk`.
  These imports cover every recorded proof dependency; those also used in signatures
  are public imports. No proof-import cycle was introduced.

Edge cases checked before writing and again against the final signature:

- q = 0 is included explicitly by both zero formulas; there is no positive-degree-only claim.
- M = 0 and the zero ring are allowed; all corresponding additive groups may be trivial.
- An empty site causes no false existence assertion of U: the theorem quantifies U : C.
- No arrows from a test object V to U means the free value at V is zero. The direct sum
  and restriction definitions remain valid; generator formulas are simply vacuous there.
- Non-subcanonical sites are allowed: P is sheafified, with no representable-sheaf assumption.
- The point site with R = F_p is allowed. An injective F_p-module need not be an injective
  abelian group; the comparison uses evaluation acyclicity instead, as required by 03FD.
- Common universes include all coefficient and module values and Hom/index types. There is
  no independently smaller test universe that could make a hypothesis vacuous.

Searches for reuse (all through the prescribed msearch wrapper or read-only source search):

- LeanFinder: `Ext of the sheafified free representable module equals right derived
  evaluation and abelian sheaf cohomology` returned 8 ingredient hits, including `Sheaf.H`,
  `sheafificationHomEquiv`, `sheafifyHomEquiv`, and `cohomologyPresheafFunctor`; none is the
  whole variable-ring-module theorem with these normalizations.
- Loogle: `PresheafOfModules.freeYonedaEquiv, Sheaf.H` reported unknown identifier
  `Sheaf.H`, no hits. Retried with `"freeYonedaEquiv"`: three hits, the presheaf equivalence,
  its identity-basis evaluation, and naturality; these are ingredients only.
- LeanSearch: `Ext from a sheafified free representable module is naturally right derived
  evaluation on a ringed site` returned 8 hits, including `SheafOfModules.evaluation`,
  `PresheafOfModules.free`, `freeYonedaEquiv`, `freeObjDesc`, and free/global-section
  formulas, but no full theorem.
- Mathlib grep: `freeYonedaEquiv|sheafificationHomEquiv|ext.*[Ee]valuation` in
  `Algebra/Category` returned 15 hits in presheaf sheafification, generators and pullback;
  these give ordinary adjunctions, not the full derived comparison.
- Read-only rg of `lean/WeilConjectures` and `lean/Sheaf` for free representables,
  free Yoneda and Ext/evaluation found the existing downstream
  `ModulePullbackInjective.freeRepresentable` and `homEvaluation` helpers and the
  separate module/abelian comparison. The downstream helper is not imported back into
  this prerequisite. The canonical Mathlib construction is written directly instead.
- rg for `free_representable_module_ext_evaluation|freeRepresentable.*[Ee]xt|
  free_representable.*[Ee]xt` in the project source and upstream name index returned no hits.
  `grep -rn 'lem-trf-free-representable-module-ext-evaluation' lean/WeilConjectures`
  returned no hits.

No STATEMENT-DISPUTED issue was found. No source hypothesis or conclusion was corrected.
The one initial compile issue was missing public imports supplying small-site abelian and
sheafification instances; explicit Mathlib Grp/AB, FilteredColimits and Grothendieck-sheaf
imports repaired it without any new assumptions. The resulting server sandbox and library
compiles passed cleanly (8.4 s and 8.8 s respectively). Final delivery validation uses the
prescribed dry-run and push wrappers.

## Second reading by Q60

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

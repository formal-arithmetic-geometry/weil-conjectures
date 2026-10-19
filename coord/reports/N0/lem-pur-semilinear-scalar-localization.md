## Worker report

Item: `lem-pur-semilinear-scalar-localization`, group N0, stage 2, 2026-10-17.
Module: `Sheaf.CategoryTheory.SemilinearScalarLocalization`.
Main declaration: `CategoryTheory.ScalarLocalization.existsUnique_semilinear_extension`.
All 26 explicit declarations are listed in `lean.declarations`. Every theorem has only
`sorry` as its proof. Definitions contain data, and the only choice of a Hom map comes
from its unique additive extension with the prescribed values on every pure tensor.
There is no arbitrary choice of a functor, comparison map, or shift isomorphism.

The source read is the current blueprint main-20261015 finite-extension sentence in
`sec-smooth-purity/sk-lem-sp-field-extension/prop-pur-rational-purity-transitivity-summands.proof.md`.
It describes tensor transport for a finite coefficient extension. This node states the
generic semilinear localization fact used for that transport; its nine proof steps are
rendered by the corresponding declaration docstrings. No source or node correction is
needed, and no statement is disputed.

Hypotheses, each matched to Lean:

- Commutative rings R and S: `{R : Type r} [CommRing R]` and
  `{S : Type s} [CommRing S]`, with independent universes.
- The inverted elements and unital coefficient map: `(t : R) (b : S) (φ : R →+* S)`.
  Here `b` is the node's element u, to keep u available as a universe name.
- Invertibility only after target localization:
  `h : IsUnit (algebraMap S (Localization.Away b) (φ t))`.
  No condition that φ(t) be a power of b, or be a unit in S, is imposed.
- C is R-linear and D is S-linear:
  `[Category.{v} C] [Preadditive C] [Linear R C]` and
  `[Category.{x} D] [Preadditive D] [Linear S D]`.
  These are exactly the `CategoryTheory.Linear` interface recorded by
  `def-weil-linear-category`. They do not assume biproducts or zero objects in this part.
- Raw localizations and Q: `ScalarLocalization R C t`, `ScalarLocalization S D b`,
  `localization R C t`, and `localization S D b`, all imported from the recorded dependency.
  Their Hom modules have scalar-first tensor order, as in that dependency; the canonical
  tensor commutor identifies this with the Hom-first notation in the natural statement.
- Additive, φ-semilinear F: `(F : C ⥤ D) [F.Additive]` and
  `hF : IsSemilinear φ F`. The predicate is exactly
  `∀ (K L : C) (a : R) (f : K ⟶ L), F.map (a • f) = φ a • F.map f`.
  This is the notion explicitly introduced by this node, not a replacement for an
  existing linear-category or localization definition.

Conclusions, each matched to Lean:

- The induced coefficient map is the real definition `coefficientMap`, using
  `IsLocalization.Away.lift`. `coefficientMap_unique` characterizes it by composition
  with the canonical map R → R[1/t]; hence it is the induced map, not an arbitrary map.
- Existence and uniqueness of an additive extension with the same object map,
  semilinearity for the induced coefficient map, and integral agreement is the entire
  statement of `existsUnique_semilinear_extension`: `∃! J`, `J.Additive`,
  `IsSemilinear (coefficientMap t b φ h) J`,
  `∀ K, J.obj ⟨K⟩ = ⟨F.obj K⟩`, and
  `localization R C t ⋙ J = F ⋙ localization S D b`.
- `extension` constructs that functor. Its object map is definitionally
  `K ↦ ⟨F.obj K.obj⟩`; its Hom maps are the unique additive maps from
  `existsUnique_semilinearHom` sending `a ⊗ f` to `coefficientMap a ⊗ F.map f`.
  `extensionHom_laws` supplies its identity and composition proofs;
  `extensionAdditive` uses the additive Hom maps. The choice defining `extensionHom`
  is permitted unique-object choice, with its entire data determined on generators.
- `extension_spec` gives the localized semilinearity and integral functor equality,
  followed by the formula at every K, L, f and n:
  `(extension ...).map (invSelf(t)^n ⊗ f) = Ring.inverse(λ(φ(t)))^n ⊗ F.map f`.
  The right side is precisely φ(t)^(-n) Q_S(F(f)). `Ring.inverse` is Mathlib's inverse
  of a unit in a general commutative ring, rather than a field-inverse operation.
  `extension_unique` also states uniqueness directly for any candidate extension.
- For arbitrary additive φ-semilinear F and G and every `η : F ⟶ G`,
  `extensionNatTrans` has component `(localization S D b).map (η.app K.obj)`.
  `extensionNatTrans_naturality` is naturality on all localized arrows, and
  `extensionNatTrans_unique` gives unique existence with exactly those components.
  No extra condition on natural transformations is imposed.
- `extensionNatIso` uses `Q_S.mapIso (e.app K.obj)` for every `e : F ≅ G`;
  `extensionNatIso_spec` identifies both its hom and inverse with the specified
  transformation extensions. It therefore extends the original isomorphism itself.
- `extensionNatTrans_laws` states identity preservation and vertical composition.
  `extension_id_and_linear` states preservation of the identity functor and identifies
  extension of any R-linear endofunctor with the existing `ScalarLocalization.map`.
- Compatible composition allows a third independent ring T, T-linear category E,
  element c, coefficient map ψ and the sole new inversion condition
  `hψ : IsUnit (algebraMap T (Localization.Away c) (ψ b))`.
  `semilinear_composition` explicitly retains h and hψ with `include`, derives
  invertibility for ψφ(t), and derives semilinearity of the composite. Neither is
  assumed as an additional hypothesis. `extension_comp` identifies both the induced
  coefficient composite and the extended functor composite by equality.
- `extensionNatTrans_whiskerRight` and `extensionNatTrans_whiskerLeft` cover both
  whiskering directions. `HEq` transports the equal functor endpoints from
  `extension_comp`; it does not weaken equality to an unspecified isomorphism.
- `extension_comparisonSquare` explicitly sends an arbitrary integral square
  `a ≫ b' = c ≫ d` (allowing different intermediate functors) to the corresponding
  square of extensions. Identity, composition, and both whiskering laws give, by
  induction on a finite composite expression, preservation of all well-typed
  equations of the operations named in the node. This includes unit and associator
  equations. Linear shift functors are covered by `extension_id_and_linear`, so
  shift equations are included as well.
- For the last paragraph, the `Triangulated` section binds the source and target
  zero-object, integer-shift, additive-shift, `Pretriangulated` and `IsTriangulated`
  structures and the linearity of the shift by one, separately over R and S.
  It also binds those structures on each raw localization. `hshiftC` and `hshiftD`
  identify the induced shifts with the existing tensor extensions. The Q shift
  structures have canonical identity comparisons, expressed by `hQC` and `hQD`.
  `hdistC` and `hdistD` say, in both directions, that a distinguished localized
  triangle is one isomorphic to the Q-image of an integral distinguished triangle.
  These are exactly the structures and normalizations supplied by
  `exists_triangulated_scalarLocalization`; none changes the category or takes a
  Karoubi envelope. The parameters are retained with `include` where needed.
- Exactness of the original specified functor is `[F.CommShift ℤ] [F.IsTriangulated]`.
  `extension_exact` supplies `∃ cs : (extension ...).CommShift ℤ` such that the
  extension is `IsTriangulated` with that cs and, at every original K, its shift-one
  comparison is `HEq` to `Q_S.map ((F.commShiftIso 1).hom.app K)`.
  This is the localized specified comparison, not merely existence of an unrelated
  shift structure. The instance-binding lambda just scopes the existential cs.
- `extension_exactComparison` uses exactly the dependency's
  `NatTrans.CommShiftCore η (1 : ℤ)` for an exact comparison. For any two specified
  localized comparisons with the preceding component normalizations, its first
  clause preserves this predicate for every transformation η. Its second clause
  preserves it for both the hom and inverse of every exact natural isomorphism.
  Thus the isomorphism and inverse equations from the earlier clauses are retained
  together with the additional exact-comparison equation.

Dependency interfaces read and used:

- `def-weil-linear-category`: `CategoryTheory.Linear`,
  `Mathlib.CategoryTheory.Linear.Basic`, including its full class and docstring.
- `def-weil-linear-scalar-localization`: `CategoryTheory.ScalarLocalization`,
  `.composition`, `.localization`, `.map` and their category, preadditive and linear
  instances, in `Sheaf.CategoryTheory.ScalarLocalization`; full source read.
- `def-weil-triangulated-category`: `Pretriangulated`, `IsTriangulated`,
  `Functor.CommShift`, `Functor.IsTriangulated`, and `Functor.mapTriangle` from the
  Mathlib triangulated interfaces recorded in the node; class signatures read.
- `lem-weil-linear-scalar-localization-triangulated`:
  `CategoryTheory.ScalarLocalization.exists_triangulated_scalarLocalization`,
  `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`; its complete signature and
  docstring read. The exactness section matches its supplied structures clause by clause.
- `def-weil-ring-localization-away`: `Localization.Away` with `algebraMap`, and
  `IsLocalization.Away.lift` in `Mathlib.RingTheory.Localization.Away.Basic`.
- `pur9-def-exact-transformation`: `CategoryTheory.NatTrans.CommShiftCore` and its
  `shift_app_comm`, `Mathlib.CategoryTheory.Shift.CommShift`; the full structure and
  objectwise equation were read. The source's orientation is the symmetric equation.
- Proof dependencies `def-weil-pbc-module-localization-away` and
  `lem-weil-pbc-localization-module-tensor`: `LocalizedModule.Away`,
  `IsLocalizedModule.lift` and `IsLocalizedModule.isBaseChange`; signatures and
  docstrings read in `Mathlib.Algebra.Module.LocalizedModule.Basic` and
  `Mathlib.RingTheory.Localization.BaseChange`. Their modules are proof imports.

Edge cases checked before writing and during self-review:

- No `Nontrivial` assumption on either ring; zero rings are allowed. The inverse and
  tensor formulas still make sense, including in a zero target localization.
- t or b may be zero or nilpotent, and φ(t) may become a unit only after localizing.
  The hypothesis is exactly invertibility in the localized target; nothing presumes
  that t or φ(t) was already invertible, regular, nonzero, or a power of b.
- For n = 0 the fraction formula specializes to the integral arrow formula.
- Zero arrows, zero Hom modules, empty categories, and categories without zero objects
  remain included in the additive-functor part. Triangulated hypotheses occur only
  in the final conditional section.
- Rings, categories, and Hom sets have independent universes. No equality of site,
  object, Hom, or coefficient universes is introduced.
- Identity coefficient maps, identity functors, and a linear shift recover the
  existing raw localization constructions. Composite inversion is derived even
  when φ(t) is not a power of the target's inverted element.
- Natural transformations and isomorphisms need no separate linearity assumption;
  their integral naturality extends on fractions.

Searches for reuse, all under this item's prescribed `msearch.py` wrapper:

- LeanFinder: `Semilinear additive functors between linear categories over different
  rings extend uniquely to localization at scalars` returned eight generic
  localization-linear/shift results, including
  `CategoryTheory.Localization.functor_linear_iff` and
  `CategoryTheory.Shift.linear_of_localization`; no raw different-ring theorem.
- LeanSearch: `Semilinear functors extend to scalar localization with natural
  transformations` returned eight scalar-extension/functor-category results,
  including `LinearMap.extendScalarsOfIsLocalization` and
  `CategoryTheory.functorCategoryLinear`; no matching category theorem.
- Loogle: `CategoryTheory.Functor.Linear, IsLocalization.Away.lift` returned zero hits.
  Loogle: `"Localization", "liftNatTrans"` returned seven generic categorical
  localization transformation results. Their full `liftNatTrans` source was read:
  it requires a categorical localization and lifting instances and does not state
  the raw semilinear tensor construction, coefficient map, or fraction formula.
- Mathlib grep: `[Ss]emilinear|[Ss]emiLinear` in `CategoryTheory` returned zero hits.
- `rg` of the same semilinear names in the upstream `WeilConjectures` source found
  group-scheme semilinear maps in `AbelianVariety/TateModule`, not this notion.
  `grep -rn` of the exact item id there found no declaration.
- `rg` of `semilinear.*local|local.*semilinear|Semilinear|SemiLinear` in `lean/Sheaf`
  found module, cohomology, tensor-complex and ringed-section uses, not a categorical
  semilinear scalar-localization interface. A focused search of
  `lean/Sheaf/CategoryTheory` confirmed only the existing same-ring raw localization.
- `rg` of `ScalarLocalization|IsSemilinear|semilinear.*local` in
  `dag/lean_names_upstream.json` found no matching upstream name. Broader semilinear
  search there found a module-cohomology map, not this functor statement.

No new nodes or dependency repairs are needed: the node itself introduces semilinearity,
and the coefficient map and extension helpers belong to the single construction it
states. All existing category and ring localizations are reused.

Validation: the final 26-declaration module compiled cleanly with the required
`scompile.py N0 lem-pur-semilinear-scalar-localization` wrapper, both in its sandbox
module view (4.9 s) and its actual library module view (5.8 s). All variables and
universes are explicit, no lines exceed 100 characters, and no non-sorry warnings
were emitted. Delivery preflight and its required per-file compile follow below.

## Second reading by N0

Independent maintainer second reading, 2026-10-17, of immutable delivery
b12a4a333ed9d53e5e1872f9e0ed8da4ee3ed8f3. This reading was performed after the
worker delivered; it replaces the delivered placeholder and does not attribute an
independent group reading to the worker. Verdict: mathematically accepted; report-only FIX.

I read the packet, the complete item node and its nine proof steps, all six statement
dependency nodes, the delivered module and every one of its 26 declarations, the worker
report, and the dependency sources. The clause-by-clause checks are as follows.

1. Rings, elements, and inversion: independent `R : Type r`, `S : Type s`, both
   `CommRing`, `t : R`, `b : S`, and `φ : R →+* S` render exactly R, S, t, u, φ.
   `h : IsUnit (algebraMap S (Localization.Away b) (φ t))` is precisely the inversion
   condition after target localization. There is no field, nonzero, regularity,
   finiteness, or power-of-b assumption. `coefficientMap` is Mathlib's canonical
   `IsLocalization.Away.lift`; `coefficientMap_unique` characterizes its integral values.
2. Categories and raw localization: the independent object and Hom universes and
   `[Category] [Preadditive] [Linear R C]` / `[Linear S D]` are exactly the recorded
   `def-weil-linear-category` interface. The original `ScalarLocalization`, tensor
   composition, and `localization` functors are reused, not redefined. The scalar-first
   tensor order differs from the node's typography by the canonical tensor symmetry.
   Wrapped objects retain the same original objects. No idempotent completion occurs.
3. Additive semilinear functors: `[F.Additive]` and `IsSemilinear φ F` give the exact
   scalar equation for every K, L, a, f. `existsUnique_semilinearHom` specifies an
   additive map on every pure tensor, uniquely; those tensors generate the additive
   group. Thus `extensionHom` chooses uniquely determined data, not an arbitrary map.
   `extensionHom_laws`, `extension`, and `extensionAdditive` provide the required
   functor and additivity. Their definitions contain real data and named proof inputs.
4. Existence, uniqueness, and fractions: `existsUnique_semilinear_extension` quantifies
   over all functors J and requires additivity, semilinearity for the induced coefficient
   map, the same object map, and equality `Q_R ⋙ J = F ⋙ Q_S`. `extension_unique`
   supplies the direct uniqueness statement. `extension_spec` supplies the same integral
   equality and the formula on every f and n: `invSelf(t)^n ⊗ f` maps to
   `Ring.inverse(λ(φ(t)))^n ⊗ F.map f`. Since λφ(t) is a unit, this is exactly the
   node's inverse-power formula, including its target Q. The recorded main
   `lean.statement` is verbatim the signature in the immutable file, before `:= by`.
5. Transformations and isomorphisms: `extensionNatTrans_naturality` states naturality
   on every localized arrow. `extensionNatTrans` has exactly the components Q_S(η_K),
   and `extensionNatTrans_unique` states unique existence with those components.
   There is no extra hypothesis on η. `extensionNatIso` uses Q_S.mapIso of the actual
   component isomorphisms, and `extensionNatIso_spec` identifies its hom and inverse.
6. Equations: `extensionNatTrans_laws` states identity and vertical composition;
   `semilinear_composition` derives composite inversion and semilinearity from h and
   hψ, rather than assuming composite inversion. `extension_comp` identifies both the
   coefficient-map composite and functor composite. The two whiskering theorems use
   HEq to compare transformations with endpoints equal by that theorem. This is equality
   with transport, not a replacement by an arbitrary isomorphism. `extension_comparisonSquare`
   states an arbitrary commutative integral square remains commutative.
   `extension_id_and_linear` identifies identity and linear endofunctor extensions with
   the existing constructions. These laws give preservation of finite composite
   equations, including unit, associator, shift, and comparison-square equations.
7. Triangulated hypotheses: source and target carry the recorded Mathlib zero-object,
   shift, additive-shift, Pretriangulated and IsTriangulated structures, with linear
   shift by one. The structures on the fixed raw localized categories, `hshiftC/D`,
   identity normalization `hQC/QD`, and distinguished-triangle characterizations
   `hdistC/D` match exactly the existential structures in the recorded
   `exists_triangulated_scalarLocalization` declaration. These are the node's induced
   structures, not an additional mathematical restriction. The final theorems retain
   the required section parameters with `include`.
8. Exactness and exact comparisons: `[F.CommShift ℤ] [F.IsTriangulated]` express the
   specified original exact functor. `extension_exact` supplies a shift structure for
   the actual constructed extension, exactness with that structure, and the component
   normalization Q_S(σ_K) at shift one. It does not merely choose some exact structure.
   For arbitrary normalized localized shift comparisons, `extension_exactComparison`
   preserves `NatTrans.CommShiftCore η (1 : ℤ)` and the hom and inverse conditions for
   exact natural isomorphisms. I checked the equation against CommShiftCore.shift_app_comm:
   σF ≫ η[1] = η_at_shift ≫ σG, the symmetric form of the source's equation.

Sources and dependency audit:

- Current blueprint main-20261015, sec-smooth-purity,
  sk-lem-sp-field-extension/prop-pur-rational-purity-transitivity-summands.proof.md:
  read the entire proof, especially the finite-extension tensor-transport sentence.
  Also read sk-prop-sf-localization/pur9-def-exact-transformation.md in full.
- Stacks algebra.tex: definition-localization (00CO, line 1068), module localization
  (07JZ, line 1159), its universal property (07K0, line 1171), and the tensor
  identification (00DK, line 2088). Stacks derived.tex: proposition-construct-localization
  (05R6, line 1360), including the isomorphic-image description of distinguished triangles.
  The fraction arguments require no domain or torsion-free hypothesis.
- Read the full project modules Sheaf.CategoryTheory.ScalarLocalization and
  Sheaf.CategoryTheory.ScalarLocalizationTriangulated in the read-only N0 clone,
  including composition, localization, map, their instances and theorem docstrings.
- Read Mathlib CategoryTheory.Linear.Basic.Linear; Triangulated.Pretriangulated,
  Triangulated.IsTriangulated and Functor.IsTriangulated; Shift.CommShift and
  NatTrans.CommShiftCore; Localization.Away and IsLocalization.Away.lift. The proof
  imports match the two module-localization proof dependencies; their nodes and
  IsLocalizedModule.lift / isBaseChange signatures were also inspected.

Reuse and completeness checks:

The worker report records LeanSearch, Loogle, LeanFinder, and grep searches. Independent
rg searches used the different phrases `semilinear.*functor`, `functor.*semilinear`,
`change.*scalar`, and `scalar.*change` over Mathlib category theory, the upstream
WeilConjectures tree, and project Sheaf modules. No duplicate categorical construction
or theorem was found. I read Mathlib Localization.Predicate.liftNatTrans: it requires
an established categorical localization and lifting instances and does not provide the
raw different-ring coefficient construction or fraction formula. The project
LocalizationModelSemilinear module concerns derived module-cohomology maps, not this
notion. The existing same-ring ScalarLocalization.map is explicitly reused by agreement.
No independent missing helper or unusable statement dependency was found; no §1(B)
repair or §1(C) correction/citer audit is needed.

Edge cases:

Zero rings, zero/nilpotent t or b, zero Hom modules, torsion, zero arrows, empty
categories in the non-triangulated part, and n=0 are included. In a zero target
localization the unit hypothesis and inverse formula still make sense. No zero object
or biproduct is assumed before the triangulated section. Identity coefficient maps,
identity functors, and composite maps with φ(t) not a power of b are covered. Ring,
category-object and Hom universes are independent (r,s,q,u,v,w,x,y,z); tensor Hom
universes use their maxima. No silent universe equality or pro-etale substitute occurs.

Maintainer and compiler checks:

All 26 explicit declarations are recorded. Every declaration and the module have source
and blueprint docstrings, and theorem docstrings explain the corresponding proof steps.
There are 19 theorem proofs, all exactly `by sorry`. Definitions and instances contain
no sorry data or local postponed proof. No line exceeds 100 characters. Import paths
and namespace comply with the project conventions; there is no Sheaf declaration prefix.
The proof-only imports are authorized stage-3 proof-plan imports by brief-stage2 §3.

I reproduced compilation of the immutable module with:
`python3 /home/ubuntu/weil-launcher-nt/scompile.py N0 lem-pur-semilinear-scalar-localization <absolute snapshot module path>`.
The installed wrapper currently uses a server overlay (its implementation supersedes
its stale local-overlay description). It returned exit 0, sandbox 3.3 s and library
3.6 s, private overlay `/dev/shm/nt-tmp/nt-local-compile-lnic8qq8/.lbuild`, with no
errors or warnings. Both per-file invocations retained the 60-second limit. This
reproduces the worker's recorded successful per-file check, without asserting that its
historical 4.9/5.8-second timings were independently recovered.

Finding and correction: delivery-errors H11, also the substantive report requirement
in H1: the delivered second-reading section was only a statement that no reading had
occurred. This completed independent reading replaces that placeholder. The Worker
report is preserved verbatim. No mathematical, Lean, dependency or node change is
needed. No build, delivery, merge, claim, direct ssh, project-clone edit or Git mutation
was performed by this reviewer; only the prescribed compile wrapper was invoked.

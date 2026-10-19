## Worker report

The module states `AlgebraicGeometry.Scheme.proEtaleConstantModulePullback_locallyConstant`
with one postponed proof. No definitions, dependencies, source statements, or proof plans change.

Hypothesis and clause correspondence:

- Any scheme morphism `f : V ⟶ X` is bound with `{V X : Scheme.{u}}`; no geometric property,
  nonemptiness or connectedness hypothesis is imposed.
- A finite commutative coefficient ring is `(A : Type u) [CommRing A] [Finite A]`.
  The existing constant-ring construction lifts it to `ULift.{u+1,u} A`; the lift retains
  its ring and finite-module structures and matches the project's size convention.
- The small sites are exactly `X.ProEt`, `V.ProEt` and `ProEt.topology`; object universe
  is `u+1`, morphism universe is `u`. No equality of these universes is assumed.
- The constant ring `A_X` is `proEtaleConstantRing X A`, forgetting commutativity only
  to form its `SheafOfModules.{u+1}` category. `F` is an object of that category.
- The specified `f^*` is `proEtaleConstantModulePullback f A F`: actual inverse image
  followed by sheafified tensor extension along `proEtaleCoefficientInverseImageMap f A`.
  It is not an arbitrary left adjoint. The recorded coefficient-isomorphism theorem is
  available for the proof; it is not added as a hypothesis.
- The given local-constancy witness is explicit: `(I : Type (u+1))`, `(U : I → X.ProEt)`,
  arrows `a` to `ProEt.mk (𝟙 X)`, and `hcover` in `ProEt.precoverage X`.
  This unpacks the recorded ringed-site local-constancy predicate rather than adding a
  separate redundant hypothesis of local constancy.
- Each model is `M i : ModuleCat.{u+1} (ULift A)`; `hfinite : ∀ i, Finite (M i)` means
  its underlying module set is finite, not merely finitely generated or finite free.
- `htrivial` is precisely the given family of isomorphisms of module sheaves on the
  localized ringed sites: `F.over (U i) ≅ proEtaleConstantModuleSheafOver X A (U i) (M i)`.
- The base-changed objects in the conclusion are exactly `(proEtaleBaseChange f).obj (U i)`.
  Its existing definition uses `U_i ×_X V`, canonically the displayed `V ×_X U_i`.
  The existential arrows `b` go from precisely these objects to `ProEt.mk (𝟙 V)`;
  as arrows over V to its identity they are unique, hence the canonical projections,
  with no freedom to substitute another morphism or another cover.
- The first conjunct says this exact family covers V. The second gives isomorphisms
  of the restricted pulled-back module sheaves with the localized constants of the
  very same `M i`. Finiteness is retained because these are the input modules themselves.
- The final conjunct uses `IsLocallyConstantProEtaleModuleSheaf V A` for the specified
  pullback, rendering the final 'in particular' clause. The stronger finite-model witness
  is already explicitly supplied by the preceding conjunct and `hfinite`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: the small site and constant-ring
  `SheafOfModules` presentation reexported by the imports; read its full abbreviation.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`, the
  sheafification of the identity-restriction constant presheaf.
- `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport` reexports
  `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`,
  `proEtaleConstantRing`, `proEtaleCoefficientInverseImageMap`, and
  `proEtaleConstantModulePullback`. Read the recorded adjunction and the underlying
  original tensor construction, not merely their names.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`:
  `AlgebraicGeometry.ProEtale.finiteCoefficientInverseImageMap_isIso` and
  `finiteCoefficientInverseImageMap_constant`, for the proof's coefficient identification.
- `Sheaf.Paper.ProEtaleFixedModuleLocalConstancy` publicly imports
  `Sheaf.Paper.ProEtaleLocallyConstantSheaf`, whose ringed-site declarations
  `proEtaleConstantModuleSheafOver` and `IsLocallyConstantProEtaleModuleSheaf` are used.
  Both constructions were read in full. The original presentation directly states this
  node, so no repair or second definition of local constancy is needed.
- Proof-only imports: `Sheaf.CategoryTheory.SiteInverseImageTensor`,
  `CategoryTheory.siteInverseImage_tensor`, and `Sheaf.Paper.LocalizeRingedSiteMorphism`,
  `SheafOfModules.localize_ringed_site_morphism`. Their full signatures and proof docstrings
  were read. The two other proof nodes (constant left-module inverse image and general
  constant-module comparison) have no Lean record yet, so supply no import here; their
  uses remain explicit in the proof docstring and unchanged DAG proof dependencies.
- Read `coord/pefw-upstream-framework.md` and the exact framework finite-coefficient
  upper/lower-star reexport module. No framework construction is duplicated.

Edge cases checked against the statement and constructions: I may be empty (no
`Nonempty I`), either scheme may be empty, and individual U_i or their pullbacks may
be empty. The restriction and constant module constructions sheafify over the localized
site, so on an empty object both sheaves have the unique zero-module sections. No point,
nonzero scalar, faithful action, module rank, or nonzero ring is assumed. Zero modules
and the zero coefficient ring are included. The identity morphism returns the same
models and cover up to the canonical chosen fibre-product isomorphism. There are no
characteristic restrictions or finite-cover assumptions.

Source read: `literature/stacks-project/sites-modules.tex`,
`lemma-pullback-locally-constant` (Tag 093R), including its surrounding definition and
its omitted proof. The delivered docstring carries the node's two-step argument,
including coefficient normalization, localization, and the empty cases.

Searches for an existing exact declaration:

- `msearch.py leanfinder`, query 'Pullback of locally constant finite module sheaves on
  the pro-etale site preserves local trivializations on base-changed covers': eight
  hits, concerning condensed locally constant modules, free-sheaf pullback and light
  condensed constructions; no arbitrary pro-etale morphism/local-model statement.
- `msearch.py loogle`, query `SheafOfModules.pullback, CategoryTheory.constantSheaf`:
  zero hits.
- `msearch.py grep`, query `IsLocallyConstant|pullback.*constant|constant.*pullback` in
  `Algebra/Category/ModuleCat/Sheaf`: zero hits.
- `rg` on the upstream `WeilConjectures` and project `lean/Sheaf` for the node id and
  `pullback.*[Ll]ocallyConstant|[Ll]ocallyConstant.*pullback`: etale finite-local-constancy
  results and local-constant functions, no exact pro-etale module-cover theorem.
  Also searched the relevant ProEtale and Paper modules for constant-module, pullback
  and local-constancy names: found the dependency constructions reused above.

No statement dispute, correction, new node, or dependency module is needed.

## Second reading by Q48

The delivered section of this name said that no independent reading was made (an author
self-check). This section replaces it with a reading made against the node, the source and
the compiled declarations, by the maintainer's second reader; the module, the node and the
lean record are unchanged.

Node statement, item by item, with the Lean and the verdict:

1. Any morphism of schemes `f : V → X` [def-pc-scheme]: `{V X : Scheme.{u}} (f : V ⟶ X)`.
   No property of `f`, no nonemptiness. Correct.
2. A finite commutative ring `A`: `(A : Type u) [CommRing A] [Finite A]`; the constant ring
   uses `ULift.{u+1,u} A`, the project's recorded size convention. Correct, not stronger.
3. Small pro-etale sites [def-weil-pbc-proetale-site]: `X.ProEt`, `V.ProEt`,
   `ProEt.topology`, coverings `ProEt.precoverage`, exactly the site used by the recorded
   local-constancy predicate. Object universe u+1, morphism universe u; no universe equality.
4. Constant ring sheaves `A_X, A_V` [def-weil-pbc-constant-sheaf]: `proEtaleConstantRing X A`,
   an abbrev for `(constantSheaf (ProEt.topology X) CommRingCat.{u+1}).obj (CommRingCat.of
   (ULift A))`, definitionally the coefficient ring of `IsLocallyConstantProEtaleModuleSheaf`.
5. `F` an `A_X`-module sheaf [def-weil-sheaf-of-modules-category]: `F : SheafOfModules.{u+1}`
   over that ring after `forget₂` to `RingCat`. Correct.
6. The module inverse image `f^*` of [def-weil-proetale-inverse-image] with the coefficient
   map of [prop-weil-pbc-proetale-constant-ring-map]: `proEtaleConstantModulePullback f A F`
   = `SheafOfModules.changeOfRings (proEtaleCoefficientInverseImageMap f A)` applied to
   `proEtaleModuleInverseImage f`, i.e. `f^{-1}F ⊗_{f^{-1}A_X} A_V` along `c^f_A`, the
   recorded declaration of the inverse-image node. The isomorphism of `c` is a recorded
   theorem (`finiteCoefficientInverseImageMap_isIso`), correctly not a hypothesis.
7. Hypothesis "locally constant with finite module models": unpacked exactly as the
   recorded predicate `IsLocallyConstantProEtaleModuleSheaf` (def-weil-proetale-locally-
   constant-sheaf, record rebound to this predicate on main by Q135, 2026-10-17):
   `(I : Type (u+1)) (U : I → X.ProEt) (a : ∀ i, U i ⟶ ProEt.mk (𝟙 X))`, `hcover`,
   `M : I → ModuleCat.{u+1} (ULift A)`, `htrivial : ∀ i, Nonempty (F.over (U i) ≅
   proEtaleConstantModuleSheafOver X A (U i) (M i))`. `F.over` is Mathlib's
   `SheafOfModules.over`, the restriction to the localized ringed site, as the node says.
8. "every `M_j` is a finite `A`-module": `hfinite : ∀ i, Finite (M i)`. Since `A` is finite,
   finitely generated over `A` is equivalent to finite as a set (for `A = 0` both force
   `M = 0`). Equivalent, not stronger.
9. Conclusion "on the base-changed covering `{V ×_X U_j → V}`": `∃ b`, arrows from
   `(proEtaleBaseChange f).obj (U i)` (= `Over.pullback f`, the chosen `U_i ×_X V`) to
   `ProEt.mk (𝟙 V)`; such over-arrows are unique (they must equal the structure map), so the
   existential chooses nothing. First conjunct: this family is a covering. Correct.
10. "isomorphisms `(f^*F)|_{V×_XU_j} ≅ \underline{M_j}`": second conjunct, the same `M i`,
    restricted with `.over` to the base-changed object. Correct.
11. "In particular `f^*F` is locally constant": third conjunct
    `IsLocallyConstantProEtaleModuleSheaf V A (proEtaleConstantModulePullback f A F)`;
    "with the same finite models" is conjuncts 2 with `hfinite`. Correct.

Edge cases: `I` empty (then `X` is covered by the empty family and the conclusion's empty
family covers `V`; no `Nonempty I`), `X` or `V` empty, empty `U_i` or `W_i` (both sheaves
are zero), `A = 0`, `M_i = 0`, `f = 𝟙`. No point, nonzero element, rank or freeness is
assumed. Universes: only `u`; all variables are bound (`autoImplicit false`).

Searches: the delivered searches plus a check of the project for a second definition of
local constancy: `IsLocallyConstantProEtaleModuleSheaf` (used) and the fixed-coefficient
`IsLocallyConstantProEtaleFixedModuleSheaf` (a different coefficient presentation); no
existing declaration states this lemma. Source: Stacks sites-modules.tex line 8434, Tag 093R,
proof omitted; the docstring carries the node's two proof steps.

Compilation: `nt_compile.py` on the module, rc = 0, no error and no warning, 3.4-4.4 s.

Mismatches found: none in the Lean; only the previous text of this section, replaced.

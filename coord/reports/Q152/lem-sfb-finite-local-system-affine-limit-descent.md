## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteLocalSystemAffineLimitDescent` states
`AlgebraicGeometry.Scheme.exists_finite_localSystem_affineLimit_descent` with one `sorry`.
It introduces no definitions. The natural-language node, statement dependencies and proof
are unchanged; the only node-field change is `lean`. There is no statement dispute or
correction.

Source checked directly: `literature/stacks-project/etale-cohomology.tex`,
`lemma-category-loc-cst-is-colimit` (Tag 0GL2), part (3) and its entire proof. The source
assumes a Noetherian coefficient ring; the node specializes to a finite commutative ring,
which is Noetherian, and uses finite module values, equivalently finite-type locally
constant sheaves over that ring. The schemes are qcqs without Noetherian hypotheses.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Nonempty directed set I | `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]` |
| Inverse system of schemes | `D : Iᵒᵖ ⥤ Scheme.{u}`; functoriality supplies identities and composition |
| Each stage quasi-compact | `[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]` |
| Each stage quasi-separated | `[∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]` |
| Affine transition morphisms | `[∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]` |
| X is the limit with projections p_i | `(c : Cone D) (hc : IsLimit c)`; X is `c.pt`, p_i is `c.π.app (op i)` |
| Finite commutative ring Λ | `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]` |
| F a Λ-module sheaf on the small etale site | `F : Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ)` |
| A jointly surjective etale trivializing cover | `∃ d : LocallyConstantDatum F`; its `cover : Cover etalePrecoverage c.pt` packages etaleness and joint surjectivity |
| Every member has a finite module model M_a | `∀ a : d.cover.I₀, ∃ M : ModuleCat.{u + 1} Λ, Finite M ∧ ...` |
| Restricted F is the constant module sheaf on M_a | `Nonempty (F.over (d.cover.etalePrecoverageToEtale a) ≅ (constantSheaf (c.pt.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale a)) (ModuleCat.{u + 1} Λ)).obj M)` |
| Some stage and a sheaf F_i there | `∃ (i : I) (Fᵢ : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ)), ...` |
| F_i locally constant with finite module values in the same sense | The first conclusion conjunct repeats exactly the existential `LocallyConstantDatum`, finite module value and localized constant-sheaf isomorphism, now for Fᵢ on D_i |
| p_i inverse image of F_i is isomorphic to F | `Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj Fᵢ ≅ F)` |
| Module inverse image with canonical constant coefficients | `Etale.upperStar` is evaluated in `ModuleCat Λ`, so the functor and isomorphism are module-valued and module-linear, using the recorded canonical coefficient inverse-image interface |
| No Noetherian hypothesis on schemes | No such binder occurs; there is no finite-type or separatedness restriction beyond qcqs |

The localized-site expression is exactly the restriction specified by the node, rather
than an extra geometric restriction. `LocallyConstantDatum.isConstant` is redundant
given the explicit constant-value isomorphisms, but is the existing project's packaging
of trivializing data, and its presence changes no hypothesis. Unlike a bare
`IsLocallyConstantSheaf` assertion, the statement explicitly requires finite values.
All isomorphisms are in sheaf categories with coefficients `ModuleCat Λ`, including
the local models and final descent isomorphism; these cannot be mistaken for mere
set-sheaf isomorphisms. No arbitrary pullback map or functor is assumed or chosen.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`:
  `AlgebraicGeometry.exists_limit_affine_transition`; its diagram and cone conventions
  are used verbatim, with an arbitrary given limit cone rather than a chosen one.
- `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`,
  `Scheme.etalePrecoverage`, and `Scheme.Etale`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the transparent Mathlib `SheafOfModules` alias. This general ringed-site dependency
  is imported as recorded. Constant-coefficient module sheaves use the already established
  `Sheaf ... (ModuleCat Λ)` encoding, as do constructible module limit descent and the
  node's proof dependencies; no duplicate ringed-module category is constructed.
- `WeilConjectures.ConstructibleSheaf.Defs`: `Scheme.LocallyConstantDatum`,
  `Scheme.Cover.etalePrecoverageToEtale`, `Scheme.IsLocallyConstantSheaf`, and
  `Scheme.upperStarConstantSheafIso`. The datum's cover is not required to be finite,
  affine, connected, or nonempty.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`,
  sheafification of the constant presheaf, here with values in `ModuleCat Λ`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.upperStar`, `upperStarLowerStarAdjunction`, and
  `upperStarComp`. The first is the canonical left-Kan-extension/sheafification
  construction, with no extra assumption that the scheme morphism is etale.
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`:
  `CategoryTheory.ConstantLeftModuleInverseImageData` and
  `CategoryTheory.constant_left_module_inverse_image`. This recorded dependency is
  imported for the canonical constant-coefficient module inverse-image interpretation.
  Its abstract small-site presentation is not imposed as an extra hypothesis on the
  full small etale sites: the canonical scheme-site `Etale.upperStar (ModuleCat Λ)`
  already supplies the coefficient-valued construction, as in the recorded inverse-image
  and constructible-descent declarations.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients` supplies
  the established coefficient-category and sheafification instances. They compile with
  scheme universe u and module/ring universe u+1, without equating site object and
  morphism universes.

Proof-only imports retain the node's plan:
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent`
(`Scheme.exists_constructible_etaleModuleSheaf_descent`),
`WeilConjectures.AlgebraicGeometry.AffineEtaleBaseChangeSystem`
(`Scheme.exists_affineEtale_baseChange_system`),
`WeilConjectures.AlgebraicGeometry.EtaleFiniteCoverFactorizationDescent`
(`etale_finiteCoverFactorizationDescent`),
`WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison`
(`Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf`),
`WeilConjectures.ConstructibleSheaf.Pullback`
(`Scheme.IsConstructibleSheaf.upperStar`), and
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`
(`isLimitBaseChangeCone`). The constructible predicate module arrives through the
constructible-descent import. The Mathlib permanence and finite-affine-cover matches
arrive through the affine-limit imports; `Mathlib.AlgebraicGeometry.Cover.QuasiCompact`
adds the recorded `QuasiCompactCover.exists_hom` cover-refinement match. The remaining
proof dependency `lem-sfb-constructible-module-affine-limit-hom` has no recorded Lean
declaration in the read repository and is not needed to type this statement, so its
import is omitted. Its two uses and the inverse-identity argument are retained in the
seven-step proof docstring. No unstated theorem is introduced as a definition or axiom.

Edge cases checked before writing:

- Empty limit scheme: an empty etale covering is allowed; the conclusion permits an
  empty stage or a descended zero sheaf on a stage. No nonemptiness of X or a cover
  member is assumed.
- Zero coefficient ring: `CommRing` permits it; the zero module and zero sheaf remain
  admissible. No nontriviality or rank hypothesis appears.
- Zero sheaf: finite zero-module constant values fit both the assumption and conclusion.
- One-stage and constant diagrams: an arbitrary limit cone is allowed, so the canonical
  pullback along its projection gives the expected form of the assertion.
- Directed preorders with equivalent indices are allowed; antisymmetry is not assumed.
- I is explicitly nonempty and has the scheme universe, in agreement with the project's
  affine-limit convention. The sheaf values and coefficient ring have universe u+1.
- Finite modules need not be free, projective, or have a common rank or cardinality.
  Models may vary between cover members, and no unnecessary transition compatibility
  between trivializations is required.

Searches made for an existing statement (the msearch outputs are also recorded in
the sandbox's `searches.jsonl`):

- `msearch.py ... leanfinder`: "Finite locally constant etale module sheaves descend
  along inverse limits of quasi compact quasi separated schemes with affine transitions".
  Eight hits: structure-sheaf section descent, scheme-morphism descent, and condensed
  locally constant objects; none is module-local-system affine-limit descent.
- `msearch.py ... loogle`: `"Sheaf", "IsLocallyConstant"`. Zero hits.
- `msearch.py ... grep`:
  `locallyConstant.*[Ll]imit|[Dd]escent.*[Ll]ocally[Cc]onstant|[Ll]ocally[Cc]onstant.*[Dd]escent`.
  Fourteen hits, all condensed locally constant presheaf colimits and profinite locally
  constant functions; none matches the node.
- `msearch.py ... leansearch`: "Finite locally constant sheaves of modules descend to
  a stage of a quasi compact quasi separated inverse system of schemes with affine
  transition maps". Eight hits about condensed sheaves, categorical module-sheaf limits,
  and `SheafOfModules.IsFiniteType`; none is the required theorem.
- Direct `rg -n` in `lean/WeilConjectures` and `lean/Sheaf` for finite local constancy,
  descent/limit combinations, and `0GL2`: found etale-cover descent, finite-monodromy
  trivialization, and finite locally constant values. None descends module local systems
  along affine inverse limits. `ConstructibleEtaleModuleLimitDescent` only descends a
  constructible model; it does not assert local constancy at a stage.
- Direct search of the item id in `lean/WeilConjectures`: no occurrence. The new
  declaration name has no existing occurrence in either project source tree.
- Read `WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues` and its
  node: it equates finite local models with the stalk-based predicate, but gives no
  affine-limit descent theorem. The explicit model condition is reproduced as syntax
  in this theorem's binders and conclusion, without creating another predicate.

Validation: `scompile.py Q152 lem-sfb-finite-local-system-affine-limit-descent` on the
delivered module succeeded in sandbox and library mode (2.2 s and 2.1 s). All variables
and universes are explicit, with `set_option autoImplicit false`. The one proof is
`sorry`; there are no definitions, hidden proofs, probe commands, or overlong Lean lines.
The exact theorem signature is recorded verbatim in `lean.statement`.

## Second reading by Q152

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

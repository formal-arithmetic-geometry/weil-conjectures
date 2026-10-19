## Worker report

The module `lean/Sheaf/Paper/PurityLisseUniqueness.lean` states
`AlgebraicGeometry.ProEtale.lisse_map_restriction_unique`. It uses the fixed finite coefficient
ring `P.Coefficient` from `WeilConjectures.PurityFiniteSetting`, a separated finite-type
`P`-field scheme `B`, an open immersion `j : G ⟶ A¹_B` whose range is the complement of the
zero section, and a section `e : B ⟶ G` whose composite with `j` is the unit section.

The conclusion has exactly the two source clauses. For `L₁,M₁` on `A¹_B`, it says that for
every pair of morphisms `φ ψ`, equality after applying the pro-etale inverse image
`ProEtale.upperStar ... j` implies `φ = ψ`. For `L₂,M₂` on `G`, it says the analogous
implication after applying `ProEtale.upperStar ... e`. The hypotheses `hL₁,hM₁,hL₂,hM₂`
use the project's canonical `Scheme.IsLisseProEtaleFixedModuleSheaf`, which packages local
constancy and finite geometric stalks. The proof is left as the required `sorry`; its proof
docstring records the component, geometric-stalk comparison, and rigidity route from the node.

Statement dependencies used:

- `def-pur-conventions`: `Sheaf.Paper.PurityFiniteSetting`, `WeilConjectures.PurityFiniteSetting`;
- `def-weil-proper-morphism`: Mathlib `AlgebraicGeometry.IsProper` (the separated and finite-type
  hypotheses are stated directly on `aB`);
- `def-weil-finite-type-morphism`: Mathlib `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`;
- `def-sbc-affine-space`: Mathlib/WeilConjectures `AlgebraicGeometry.AffineSpace`;
- `def-weil-pbc-proetale-site`: `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` and the
  `ProEt` site from its imported framework;
- `def-weil-pbc-proetale-operations`: the published finite-coefficient pro-etale operations
  imported from `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`;
- `def-weil-proetale-locally-constant-sheaf`: fixed-coefficient local constancy in
  `Sheaf.Paper.ProEtaleFixedModuleLocalConstancy`;
- `def-weil-proetale-geometric-stalk`: `Scheme.proEtaleGeometricFixedModuleStalk`, imported by
  `Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk` and used by the lisse predicate.

The source's two assertions are represented as a conjunction of explicit universal
implications, preserving both map pairs and both restriction equalities. `aB` carries
`IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`, which is the Lean form of separated
finite type over `Spec P.field.k`. No nonemptiness assumption is added; the empty-base case is
included. Zero source or target sheaves and disconnected bases are allowed. The range equality
for `j` and the unit-section equation `he` retain the source's geometric hypotheses.

Searches made:

- Maintainer review, 2026-10-16: `msearch.py Q35 lem-pur-lisse-uniqueness leansearch`
  with query "A morphism between finite locally constant module sheaves on the small
  pro-etale affine line is determined by its restriction to the complement of zero, or
  to the unit section on the punctured line" returned
  `[leansearch] UNAVAILABLE 0 hit(s) | service unavailable: Internal Server Error`.
  This is an unavailable search, not evidence of no match. The other searches below
  and the maintainer's direct source searches supply the duplicate check.
- `msearch.py ... leanfinder` for morphisms of lisse finite module sheaves determined by affine-line
  and unit-section restriction: no exact match; only general `Scheme.Modules.hom_ext` and affine-space
  morphism extensionality appeared.
- `msearch.py ... loogle` for `Scheme.IsLisseProEtaleFixedModuleSheaf`,
  `ProEtale.upperStar`, and injectivity: no match (the lisse predicate is project-specific).
- `msearch.py ... grep` for `IsLisseProEtaleFixedModuleSheaf|upperStar.*Injective|lisse_map_restriction`:
  no match in the upstream `WeilConjectures` source.
- `rg` in the upstream source found the etale-only declarations
  `AlgebraicGeometry.Etale.injective_upperStar_map_of_isFiniteLocallyConstantSheaf` and
  `injective_upperStar_oneSection_map_of_isFiniteLocallyConstantSheaf`; these use the small etale
  site and therefore do not state this small pro-etale lemma.
- `rg` in the project found `Scheme.IsLisseProEtaleFixedModuleSheaf` in
  `Sheaf.Paper.ProEtaleLisseOrigin`; that is the canonical existing lisse notion used here.

The file compiles cleanly with `scompile.py` (local overlay and server confirmation), with only the
expected declaration-uses-`sorry` warning suppressed by the project options. No new definition or
dependency repair was needed.

## Earlier second reading (a previous round; superseded)

I reread the source node, every statement dependency, and the full signatures of the recorded
project declarations. The two conclusions are encoded as universal equality implications, so no
injectivity clause is weakened or strengthened. The fixed-coefficient lisse predicate is the
project's canonical specialization of local constancy plus finite geometric stalks. The empty
scheme, disconnected bases, zero sheaves, and identity/unit-section cases remain permitted.
The module was recompiled with `scompile.py` after the final imports and signature, and the
signature was recorded using `tools/stage2_delivery.py signature` so the node field matches the
stage-2 parser exactly.

## Second reading by Q35

I independently opened the node, all eight statement dependency records and their declarations,
and `lean/Sheaf/Paper/PurityLisseUniqueness.lean`. The item-by-item correspondence is:

1. Fixed purity datum: `P : WeilConjectures.PurityFiniteSetting.{u}` and its actual finite
   coefficient ring `P.Coefficient`. PASS: the field and finite quotient are the recorded
   constructions, rather than arbitrary data.
2. Base: `B : Scheme.{u}` and `aB : B ⟶ Spec (.of P.field.k)` with `[IsSeparated aB]`,
   `[LocallyOfFiniteType aB]`, `[QuasiCompact aB]`. PASS: exactly separated finite type over
   the fixed field, with no extra nonempty or Noetherian hypothesis.
3. Affine line: `AffineSpace (ULift.{u} (Fin 1)) B`. PASS: the recorded relative affine-space
   construction with one coordinate; its zero section is the published `AffineSpace.zeroSection`.
4. Punctured line and inclusion: `G`, `j`, `[IsOpenImmersion j]`, and `hj`, which identifies
   the range with the complement of the zero section. PASS: presenting the open complement by
   an arbitrary open immersion with precisely that range is equivalent to the node's inclusion.
5. Unit section: `e : B ⟶ G` and `he : e ≫ j = AffineSpace.oneSection ... B`. PASS: this is
   precisely the section t = 1, not an arbitrary section.
6. Ordinary finite locally constant module sheaves: `L₁ M₁` on the pro-etale affine line and
   `L₂ M₂` on pro-etale `G`, valued in `ModuleCat.{u + 1} P.Coefficient`; `hL₁`, `hM₁`,
   `hL₂`, `hM₂` use `Scheme.IsLisseProEtaleFixedModuleSheaf`. PASS: opening its definition
   gives exactly coverwise constant module sheaves and finite geometric stalks, with no freeness.
7. First conclusion: `∀ (φ ψ : L₁ ⟶ M₁), (upperStar ... j).map φ =
   (upperStar ... j).map ψ → φ = ψ`. PASS: both morphisms and the restriction equality are
   explicit, and the universal implication is precisely the first source clause.
8. Second conclusion: the same universal implication for `L₂`, `M₂` and `e`. PASS: it is
   conjoined with the first clause, preserving the second source clause and quantifier order.

Edge cases: the empty base, empty total spaces, zero sheaves and disconnected bases are allowed.
There is no variable index set or dimension parameter; this lemma is about dimension one, so an
n = 0 case is not claimed. The positive coefficient level and distinct characteristics come from
`P`; no further characteristic restriction is added. The single universe `u` with coefficient
lift `u+1` retains the site's object/morphism size convention, with no additional universe equality.

The dependency signatures were read in `PurityFiniteSetting`, `ProEtaleDerivedCategory`,
`ProEtaleFiniteCoefficientDirectImage`, `ProEtaleFixedModuleLocalConstancy`,
`ProEtaleGeometricStalk`, `ProEtaleLisseOrigin`, the published affine-space/zero-section
modules and Mathlib's finite-type/separated morphism modules. In particular `ProEtale.upperStar`
is the actual Kan-extension/sheafification inverse image for fixed modules, not etale restriction.
The fixed-module and ring-sheaf coefficient descriptions are identified by the canonical
realization interface, without an assumed arbitrary coefficient map.

Repeated independent searches: LeanFinder through `msearch.py` for morphism maps of lisse
pro-etale sheaves determined by restriction; Loogle query `"upperStar", "Injective"` (zero hits);
and `rg` over Mathlib, upstream `WeilConjectures`, and project `lean/Sheaf`. General module
restriction hits do not address pro-etale finite locally constant sheaves. I opened the upstream
`Etale.injective_upperStar_map_of_isFiniteLocallyConstantSheaf` and
`Etale.injective_upperStar_oneSection_map_of_isFiniteLocallyConstantSheaf`: these use the small
etale site, so neither is this statement. No exact existing theorem was found.

The archived blueprint source was read directly in the server literature mirror, along with
`sk-def-purity-conv/_section.md`. The latter explicitly supplies separated finite type for the
affine-line base. The source, unit `sk-prop-a1-inv`, and current node agree on both clauses.
No new or dependency module, hollow definition, extra theorem proof or statement correction is
introduced. No mathematical signature mismatch was found; the node signature is retained. I repaired the
missing non-public proof-dependency import `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
and expanded the proof docstring to record the affine charts and diagonal checks, the residue
field closures, and the coefficient-ring isomorphism and tensor identification. These were
explicit steps of the node proof that the previous docstring compressed too far.
All binders and `u` are explicit. The required `scompile.py` compile succeeded after the
initial stale local overlay cache was refreshed. The final module passed both its sandbox
and library-position local overlay compiles after the import/docstring repairs.

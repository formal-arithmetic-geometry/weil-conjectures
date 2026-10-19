## Worker report

The module `lean/Sheaf/AlgebraicGeometry/ProEtaleClassicalSheavesModules.lean` defines
`AlgebraicGeometry.ProEtale.IsClassicalModuleSheaf` and states
`AlgebraicGeometry.ProEtale.proEtaleClassicalSheavesModules` with proof `sorry`.
The module-valued encoding `Sheaf (Scheme.ProEtale.topology X) (ModuleCat.{u + 1} Λ)` is the
fixed-coefficient presentation of sheaves of `Λ_X`-modules used by the pro-etale six-functor
framework. `IsClassicalModuleSheaf` says, for every `I : Type (u + 1)` with
`[SmallCategory I] [IsCofiltered I]` and every `AffinePresentation X I`, that the canonical
`continuityMap P F.obj` in `ModuleCat.{u + 1} Λ` is an isomorphism.

The theorem has these clauses. It binds a scheme `X : Scheme.{u}`, a discrete commutative ring
`Λ : Type (u + 1)`, and `[CommRing Λ]`. Its first clause provides the canonical adjunction
`comparisonUpperStar (ModuleCat.{u + 1} Λ) X ⊣ comparisonLowerStar (ModuleCat.{u + 1} Λ) X`.
The next two clauses state preservation of finite limits and finite colimits by the inverse-image
functor, rendering exactness. The fourth clause expands full faithfulness as a bijection on every
module-sheaf hom set, via `Function.Bijective (fun f ↦ comparisonUpperStar.map f)`. The fifth clause
identifies classical module sheaves with those whose counit component is an isomorphism. The final
clause identifies the same classical objects with the essential image, spelling out the witness
`F` and `Nonempty ((comparisonUpperStar ...).obj F ≅ G)`; together with the displayed adjunction,
this records `comparisonLowerStar` as the quasi-inverse on the full classical subcategory.

The declarations used are:

- `AlgebraicGeometry.Scheme.smallModelProEtaleComparison` and its supporting declarations from
  `Sheaf.AlgebraicGeometry.ProEtaleSmallModelComparison` (site comparison dependency record).
- `AlgebraicGeometry.Scheme.IsLocallyConstantEtaleSheafOfSets` and the sheaf-category material
  from `WeilConjectures.AlgebraicGeometry.EtaleSheaves` (etale-sheaves dependency record).
- `AlgebraicGeometry.Scheme.proEtaleDerivedCategory` from
  `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory` (pro-etale-site dependency record).
- `CategoryTheory.constantSheaf` from `Mathlib.CategoryTheory.Sites.ConstantSheaf`.
- `CategoryTheory.ringedSiteModules` / Mathlib's `SheafOfModules` from
  `Sheaf.CategoryTheory.RingedSiteModules` (module-sheaf dependency record).
- `AlgebraicGeometry.ProEtale.AffinePresentation` and
  `AlgebraicGeometry.ProEtale.continuityMap` from
  `Sheaf.AlgebraicGeometry.ClassicalContinuityMap` (continuity-map dependency record).
- `AlgebraicGeometry.ProEtale.comparisonUpperStar`, `comparisonLowerStar`, and their canonical
  adjunction from `WeilConjectures.SixFunctors.ProEtale.Comparison`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB` supplies the Grothendieck-abelian
  instance for `ModuleCat`, needed by the comparison functors.

Edge cases checked: `I` is any universe-`u+1` small cofiltered index. The
`IsCofiltered I` class already includes nonemptiness, exactly as in the dependency
and the source; an empty category is not a cofiltered presentation. No additional
nonemptiness or finite-generation assumption is added. The zero module and zero ring are allowed by `[CommRing Λ]`.
The empty scheme is covered because all functors and affine-presentation quantifiers are uniform in
`X`; no stalk or point nonemptiness is assumed. The continuity condition uses the canonical
`ModuleCat` colimit, so it includes the degree-zero and identity-presentation cases.

Searches made:

- `msearch.py ... leanfinder "fully faithful exact equivalence classical module sheaves etale proetale"`:
  generic fully faithful and condensed hits only; no etale/pro-etale module comparison theorem.
- `msearch.py ... loogle "Functor.FullyFaithful, PreservesFiniteLimits, IsClassicalModule"`:
  no matching declaration (Loogle reported unknown `Functor.FullyFaithful`).
- `msearch.py ... grep "comparisonUpperStar|IsClassicalModule" WeilConjectures`:
  no exact classical-module equivalence declaration; generic comparison framework only.
- `rg` over `lean/Sheaf` and `WeilConjectures` for `comparisonUpperStar`, `IsClassicalModule`,
  and module adjunction names: found the canonical comparison framework and the set/intrinsic
  continuity predicate, but no declaration of this node's module theorem.
- `grep` over Mathlib site and module-sheaf files for `proetale`, `classical`, and comparison
  equivalence: only generic sheaf pullback and condensed-module results, not this theorem.

No statement correction or `STATEMENT-DISPUTED` flag is needed. The file compiles cleanly with
`scompile.py`; the required proof warning is suppressed by the project options.

## Second reading by Q19

I independently opened the node, its blueprint statement and proof, all six statement
 dependency records and their actual declarations, and the available proof-dependency
 declarations. The Worker report above describes the pre-review file; the account below
 describes the delivered file. Verdict: the repaired Lean states exactly the node,
 using the fixed-coefficient encoding explicitly authorized in the
 `def-weil-pbc-etale-sheaves` record. No natural-language statement correction is needed.

Objects, hypotheses and conclusions, matched item by item:

1. An arbitrary scheme X: `(X : Scheme.{u})`. There is no affine, quasi-compact,
   separated, Noetherian or nonempty assumption. The Stacks comparison section
   `proetale.tex`, lines 3737 onward (Tag 099R), also starts with an arbitrary scheme.
   Verdict: exact.
2. A discrete commutative ring Λ: `(Λ : Type (u + 1)) [CommRing Λ]`. No topology,
   finiteness, torsion, field or characteristic condition is imposed. Discrete
   coefficients are ordinary rings in this presentation. Verdict: exact.
3. The constant ring sheaf Λ on the etale site and its comparison pullback Λ_X:
   `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and
   `Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)`. These are the
   fixed-scalar encoding in the etale-sheaves dependency's explicit two-encoding
   convention, not arbitrary variable ring sheaves. A sectionwise Λ-action extends
   uniquely to the constant ring sheaf by sheafification and gluing; conversely
   restrict its action along the constant-section maps. This identifies the
   objects and linear arrows with modules over the stipulated constant rings.
   `comparisonUpperStarUnitIso`, opened in upstream Comparison.lean, identifies
   inverse image of the constant unit with the pro-etale constant unit. Verdict:
   the coefficient identification is built into the allowed fixed-ring encoding.
4. The canonical functors ν* and ν_*: `comparisonUpperStar` and
   `comparisonLowerStar`, opened in upstream Comparison/Defs.lean. They are exactly
   left Kan extension followed by sheafification along `toProEt X`, and restriction
   along that same inclusion. They require an abelian Grothendieck value category;
   the imported ModuleCat.AB supplies these instances without any assumption on Λ.
   The current recorded site-comparison module supplies AsSmall models and publicly
   retains the original comparison. No new inclusion or arbitrary map was chosen.
   Verdict: exact.
5. An adjoint pair: `∃ (adj : comparisonUpperStar ... X ⊣ comparisonLowerStar ... X)`.
   This is an adjunction on those specified functors, not merely unspecified
   equivalent categories. Verdict: exact.
6. Exactness of inverse image: `PreservesFiniteLimits ... ∧ PreservesFiniteColimits ...`.
   The same upstream Defs module provides its additive structure for all such value
   categories. In the abelian module-sheaf categories these clauses express exactness.
   I read Stacks sites-modules.tex, `lemma-flat-pullback-exact` (04JC): abelian inverse
   image is exact, and module inverse image is exact for a flat coefficient map;
   here the coefficient map is an isomorphism. I also read `lemma-abelian` (03DA)
   and the following limits/colimits lemma. No source-wide finiteness assumption is
   missing. Verdict: exact.
7. Full faithfulness: the universal clause over `F G : Sheaf X.smallEtaleTopology ...`
   and `Function.Bijective (fun f : F ⟶ G ↦ comparisonUpperStar.map f)` is precisely
   the induced Hom-set bijection for every ordered pair. Verdict: exact.
8. Classical objects: both last clauses now use the existing
   `IsClassical ((sheafCompose ... (forget (ModuleCat ...))).obj G)`. I opened
   ClassicalContinuityMap.lean: IsClassical universally tests the canonical
   `continuityMap` on every `AffinePresentation`. Its clause 3, the node statement,
   and `isClassicalModule_iff` all identify module classicality with this exact
   underlying-set predicate. Verdict: exact, with no private second definition.
9. Equivalence onto the full classical subcategory: the final universal clause
   says classicality iff there exists an etale module sheaf F and an isomorphism
   from its specified inverse image to G. Full faithfulness plus this essential
   image gives exactly that equivalence; no extra class of objects is included.
   Verdict: exact.
10. Restriction as quasi-inverse: the preceding universal clause identifies
    classicality with `IsIso (adj.counit.app G)` for the displayed adjunction.
    Full faithfulness makes its unit invertible; these unit and counit with the
    adjunction's triangle identities give the equivalence with the specified
    right adjoint as quasi-inverse. This is stronger evidence than an arbitrary
    equivalence witness, and is equivalent to the node's assertion. Verdict: exact.

Dependency reading: I opened the current SmallModelComparison, ProEtaleDerivedCategory,
RingedSiteModules and ClassicalContinuityMap modules, the shared upstream EtaleSheaves,
and the original comparison functors. RingedSiteModules is transparently SheafOfModules,
not another category. ProEtaleDerivedCategory uses intrinsic constant-ring modules;
this theorem does not bind a derived object or confuse that category with ModuleCat.
The mixed dependency record explicitly permits the latter for the six-functor comparison.
The intrinsic IsClassicalModule has smaller lifted coefficients; using the existing
set-sheaf predicate avoids imposing that intrinsic interface on larger fixed coefficients.
I opened ProEtaleClassicalSheavesUnit and SitePullbackAbelianExact and fetched the
current ModuleSheavesColimitsForgetful through `scompile.py --source`; their signatures
match the uses explained in the expanded proof. The site-exactness theorem is on
small sites in one ambient universe; the node proof explicitly uses small models in
that common larger universe. No extra hypothesis was added to this item.
`det-pe-classical-sheaves-image` has no recorded Lean module, so its proof import is
necessarily absent; its natural-language use remains step 5. There are no new nodes
or dependency modules in this delivery.

Edge cases: IsCofiltered already requires a nonempty category, so the existing
predicate excludes exactly the empty presentations the source excludes. Terminal and
identity presentations are included. Finite-limit/colimit preservation includes the
empty finite diagrams, hence zero objects. Both the zero ring and zero module are
allowed; there is no Nontrivial hypothesis. The empty scheme is allowed. There is no
n, degree bound or positive-characteristic restriction in this theorem. Universes
are explicitly bound with autoImplicit false. Site objects and module/set sections
are in the common larger universe u+1 and site morphisms stay in u; no equality
between those site universes is imposed. Coefficients are allowed throughout u+1,
including its genuinely large rings, following the recorded fixed-scalar convention.

Independent searches (2026-10-17):

- LeanFinder through msearch.py: `essential image inverse image sheaves modules
  classical etale proetale counit isomorphism`. Eight hits were condensed locally
  constant module counits, generic sheaf equivalence counits, or Zariski open
  restriction. I opened Mathlib/Condensed/Discrete/Module.lean: its discrete/locally
  constant equivalence is on CompHaus, not these two scheme sites. No exact match.
- Loogle through msearch.py: `"comparison"`. Twelve hits were generic initial/terminal
  comparison maps and linarith internals, not classical pro-etale module sheaves.
- LeanSearch through msearch.py: `A sheaf of modules is in the essential image of
  etale to proetale inverse image if and only if its underlying sheaf is classical`.
  Eight hits concerned constant sheaves, tilde modules or generic module pullback;
  none identified this classical essential image.
- `rg` on Mathlib sites/condensed, all upstream WeilConjectures, the project's
  lean/Sheaf and the exact 51-module framework, using IsClassical, classical sheaf,
  classical module and essImage/comparison in both orders. The existing continuity
  module is the owner of classicality. Upstream comparison supplies exactness and
  full faithfulness but no full classical-image theorem. The framework's module
  objects concern condensed coefficients and local finite presentations, not this
  ordinary discrete-ring classical equivalence. The upstream declaration-name
  index has no collision with the theorem name. No matching whole theorem exists.

Mismatches repaired:

- H4: removed the new IsClassicalModuleSheaf predicate; both uses now refer to the
  recorded IsClassical on the underlying set sheaf. Its quantifiers and continuity
  maps are preserved through the source's module/set equivalence.
- H8: replaced the compressed proof paragraph by all five DAG steps, including the
  product/unit/counit linearity argument, arbitrary-coefficient exactness, reflection
  of addition/zero/scalars, filtered-colimit representatives and the actual
  quasi-inverse. Added precise source places and the coefficient-encoding explanation.
- Stage-2 rule 7: added non-public imports for all three stated proof-only dependency
  modules (unit, site abelian exactness, and module-sheaf forgetful colimits).
- Updated lean.statement verbatim and lean.declarations after removing the predicate.
  The natural-language statement, statement dependencies and all other node fields
  remain unchanged.

Validation: scompile.py compiled this sole delivered module cleanly (sandbox 2.3s,
library 2.5s), with no errors or warnings. Every line is at most 100 characters;
there is no local notation, instance, hidden statement let, unbound variable,
hollow definition or proved theorem. The one theorem has exactly `by sorry`.

## Maintainer review correction (cc review service, 2026-10-17)

Imports only; the statement, its declarations and the `lean` record are unchanged.

- The recorded module of `def-weil-pbc-site-comparison-morphism` is now
  `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` (§1(B) repair by Q67, 2026-10-17),
  whose `proEtaleSiteComparisonModules` is exactly `ProEtale.comparisonAdjunction
  (ModuleCat Λ) T` between the `comparisonUpperStar` / `comparisonLowerStar` used here.
  The public import of the retired `ProEtaleSmallModelComparison` is replaced by it.
  The sentence above about the "AsSmall models" of the recorded module is superseded.
- `det-pe-classical-sheaves-image` has since been stated
  (`Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage`, its theorem on
  `proEtaleSiteComparison` and the same `IsClassical`); it is now imported without
  `public` as a proof dependency (stage-2 rule 7).
- The corrected file compiles cleanly with `tools/nt_compile.py --json` (rc 0, no
  errors or warnings).

## Worker report

The module `Sheaf.CategoryTheory.AlgebraSheafQuotientCokernel` states
`CategoryTheory.algebraSheafQuotient_cokernel`. It reuses the landed canonical quotient
construction from `Sheaf.Paper.IdealModuleQuotients` and supplies the remaining algebra-sheaf
structure, restricted ideal inclusion, normalized module-cokernel comparison, local
surjectivity, and algebra universal property. All postponed results have `sorry`; every
definition has real data.

Hypothesis and clause correspondence:

- The space and topology are `{X : Type u} [TopologicalSpace X]`, and the commutative ring
  sheaf is `{O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}`.
- The commutative `O`-algebra sheaf is `B : Under O`; its structure map and ring sheaf are
  `B.hom` and `B.right`.
- The ideal subsheaf is `I : RingedSiteIdeal B.right`, with sections `I.sections U`,
  restriction `I.restriction`, local membership `I.local_mem`, module `I.module`, and
  inclusion `I.inclusion` supplied by `Sheaf.Paper.RingedSiteIdeal`.
- The quotient presheaf, its sectionwise projection, its ring sheafification, and the
  specified ring map are exactly `RingedSiteIdeal.ringQuotientPresheaf I`,
  `RingedSiteIdeal.ringQuotientPresheafProjection I`, `RingedSiteIdeal.ringQuotient I`, and
  `RingedSiteIdeal.ringProjection I` from `Sheaf.Paper.IdealModuleQuotients`. The module does
  not redeclare these constructions. The quotient algebra is
  `algebraSheafQuotient B I := Under.mk (B.hom ≫ RingedSiteIdeal.ringProjection I)` and the
  algebra projection is
  `algebraSheafQuotientMap B I := Under.homMk (RingedSiteIdeal.ringProjection I) rfl`.
- The ideal inclusion as an `O`-module map is
  `algebraSheafIdealInclusion B I`, obtained by restricting scalars along `B.hom` and
  mapping `I.inclusion`. This renders the source inclusion `I ↪ B` in sheaves of
  `O`-modules.
- The first conjunct uses `cokernel (algebraSheafIdealInclusion B I)` and asserts an
  isomorphism to `commAlgebraSheafModule O (algebraSheafQuotient B I)`, normalized by
  `cokernel.π ... ≫ h.hom = (commAlgebraSheafModuleFunctor O).map
  (algebraSheafQuotientMap B I)`. The canonical quotient projection is the same map in the
  ring and algebra clauses.
- The second conjunct is
  `Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
  (RingedSiteIdeal.ringProjection I).hom`; it asserts local, rather than global,
  surjectivity on sections.
- The final conjunct quantifies over every `H : Under O` and every algebra map `χ : B ⟶ H`.
  Its hypothesis is exactly
  `∀ (U : Opens X) (a : I.sections U), χ.right.hom.app (op U) a.val = 0`, and its conclusion
  is the unique `χbar : algebraSheafQuotient B I ⟶ H` satisfying
  `algebraSheafQuotientMap B I ≫ χbar = χ`.

Dependency declarations used:

- `WeilConjectures.CategoryTheory.CommAlgebraSheafModule`: declarations
  `CategoryTheory.commAlgebraSheafModule` and `CategoryTheory.commAlgebraSheafModuleFunctor`.
- `Sheaf.CategoryTheory.RingedSiteModules`: declaration `CategoryTheory.ringedSiteModules`.
- `Sheaf.Paper.RingedSiteIdeal`: declarations `CategoryTheory.RingedSiteIdeal`,
  `sections`, `restriction`, `local_mem`, `module`, and `inclusion`.
- `Sheaf.Paper.IdealModuleQuotients`: declarations
  `CategoryTheory.RingedSiteIdeal.ringQuotientPresheaf`,
  `ringQuotientPresheafProjection`, `ringQuotient`, and `ringProjection` (as well as the
  recorded quotient-module constructions). This is the added statement dependency
  `def-weil-pbc-ideal-module-quotients`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`, and
  `sheafificationAdjunction`; `Mathlib.CategoryTheory.Sites.LocallySurjective` supplies
  `Presheaf.IsLocallySurjective`.
- `WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal` supplies the recorded
  local-section proof interface; the proof also relies on Mathlib's sheafification and
  sheaf-module APIs.

Proof and edge-case notes: the source proof is the quotient sheafification argument from
Stacks Tags 0087, 0089, 00WB, 00WK, 01AG, and 01AH. It transfers local representatives and
local equality to the canonical ring sheafification, descends annihilating module maps by
sheaf gluing, compares the two cokernel maps with both inverse identities, and factors
annihilating algebra maps uniquely. The checks include `I = 0`, `I = B.right`, zero target,
`F = 0`, the empty open, the empty space, and a one-point space. No Noetherian,
quasi-coherent, finite-type, affine, or global-section-surjectivity assumption is added.

Searches made before and during the repair:

- `msearch.py leanfinder` and `leansearch` for a sheaf quotient/module-cokernel theorem:
  results were ordinary module cokernels and sheaf presentations, with no exact theorem.
- `msearch.py loogle` for `Ideal.quotientMap`, `SheafOfModules.restrictScalars`, and
  `cokernel.π`: no exact combined result.
- `msearch.py grep` for quotient/cokernel/ideal terms in Mathlib site algebra sources: no
  matching general theorem.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/nodes` found the landed
  `Sheaf.Paper.IdealModuleQuotients` declarations and no project declaration matching the
  full algebra/module-cokernel theorem. The duplicate quotient helpers in the prior packet
  were therefore deleted and replaced by that dependency's canonical declarations.

No `STATEMENT-DISPUTED` flag or statement correction is required. The repaired module
compiled cleanly with `scompile.py` after importing `Sheaf.Paper.IdealModuleQuotients`.

## Second reading by Q144

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

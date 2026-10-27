## Worker report

The module `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentExtension` states
`AlgebraicGeometry.AlgebraicSpace.isQuasicoherent_of_shortExact`, with its sole proof
`sorry`. It introduces no definitions and changes only the item's `lean` record.
The source read is `literature/stacks-project/spaces-properties.tex`,
`lemma-properties-quasi-coherent`, Tag 03M1, clause (4), and its localization proof
(lines 5441–5540). The node deliberately requests only the extension case of that
source's two-out-of-three assertion. The docstring includes all seven accepted proof
steps and the prerequisites for the future proof.

Hypothesis and clause correspondence:

| Node | Lean |
| --- | --- |
| Work in the chosen universes | Explicit `universe u`, `Scheme.{u}`, and the recorded universe-polymorphic site and module definitions; `set_option autoImplicit false` forbids undeclared variables. |
| S is a scheme | `{S : Scheme.{u}}`. |
| X is an algebraic space over S | `(X : AlgebraicSpace S)`, the recorded full subcategory of fppf sheaves with representable diagonal and an etale surjective atlas. |
| Small etale site and O_X | `X.Modules` unfolds to `ringedSiteModules.{u} X.structureSheaf`, on `X.etaleTopology`. `structureSheaf` is regular functions on each scheme chart. |
| Module sheaves | The recorded `ringedSiteModules` is an abbreviation for Mathlib `SheafOfModules`; no private category is substituted. |
| 0 → M → N → Q → 0 | `(c : ShortComplex X.Modules)` gives M = `c.X₁`, N = `c.X₂`, Q = `c.X₃` and the two arrows with zero composite. `(hc : c.ShortExact)` is categorical exactness plus a monomorphism on the left and epimorphism on the right. |
| M quasi-coherent | `(hM : c.X₁.IsQuasicoherent)`. |
| Q quasi-coherent | `(hQ : c.X₃.IsQuasicoherent)`. |
| N quasi-coherent | Conclusion `c.X₂.IsQuasicoherent`. |
| No quasi-compactness, separation or Noetherian condition | No such binder occurs; S and X are arbitrary. |

Dependency declarations read and used:

- `def-weil-size-convention`: its recorded metatheoretic convention has no declaration;
  explicit universes implement it without an invented object.
- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom` (definition and docstrings read).
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace`, `EtaleSite`, `etaleTopology`,
  `structurePresheaf`, `structureSheaf`, and `Modules`.
- `def-weil-sheaf-of-modules-category`: `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`, transparently Mathlib `SheafOfModules`.
- `def-trf-space-quasi-coherent-module`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`,
  `AlgebraicGeometry.AlgebraicSpace.QCoh` and its public slice-instance theorems.
  QCoh uses exactly Mathlib `SheafOfModules.IsQuasicoherent`, which the statement uses
  directly for the three ambient modules. The full signatures and docstrings of
  `QuasicoherentData` and `IsQuasicoherent` were read in Mathlib's Quasicoherent module.
- `def-weil-pbc-exact-sequence`: `Mathlib.Algebra.Homology.ExactSequence` and
  `Mathlib.Algebra.Homology.ShortComplex.ShortExact`,
  `CategoryTheory.ShortComplex.ShortExact`; its definition is exactness, Mono, Epi.
  Categorical short exactness is appropriate for module *sheaves*: epimorphisms
  are locally surjective, and sectionwise surjectivity is not imposed.

The recorded proof-dependency modules are imported without `public`:
`AlgebraicSpaceRepresentableEtaleSchemeTests`, `LocalizedModuleExactForSystems`,
`SchemeZariskiEtaleQuasiCoherentEquivalence`, `EtaleExtensionFreePresentationsHom`,
`EtaleAffineQcoherentULift`, `ModuleSheavesColimitsForgetful`,
`AlgebraicGeometry.Sites.TorsionAcyclic`, and `Modules.QuasicoherentExtension`
(with their recorded Sheaf/WeilConjectures prefixes). The remaining proof node,
`lem-sfb-scheme-etale-module-exact-finiteness-comparison`, has no recorded Lean module
at this reading, so has no import; it remains named in the proof docstring. It is
not a statement prerequisite. No proof-import cycle was introduced.

Edge cases checked before writing: empty algebraic spaces and empty etale charts
remain allowed; zero outer terms and split extensions remain allowed; arbitrary
non-quasi-compact, non-separated and non-Noetherian spaces are included. The sequence
is in all module sheaves, so the middle term is not already assumed quasi-coherent.
No sectionwise surjectivity, finite presentation or finite rank was introduced.
The existing coefficient universe is retained: sections in u on a site with objects
in u+1, with the recorded slice instances and no new size hypotheses.

Searches actually run on 2026-10-24 using the prescribed msearch wrapper:

- LeanFinder: `An extension of quasi coherent modules on the small etale site of an algebraic space is quasi coherent`.
  Eight hits, all the existing quasi-coherence definitions/presentation data or
  finite-presentation implication; none is the extension result.
- Loogle: `SheafOfModules.IsQuasicoherent`.
  Twelve hits including `IsQuasicoherent`, its constructor, local presentation,
  over-site and pushforward results. None supplies extension closure.
- LeanSearch: `In a short exact sequence of modules on an algebraic space quasi coherence of the outer terms implies quasi coherence of the middle term`.
  Eight hits, including the abstract `ObjectProperty.prop_X₂_of_shortExact`, which
  assumes the desired extension-closure instance, plus free-module and finite-group
  statements. No specialization proving this algebraic-space assertion.
- Mathlib grep: `quasi.?coherent.*(extension|shortExact)|extension.*quasi.?coherent|IsQuasicoherent`
  returned quasi-coherence and tilde API hits. The more targeted
  `quasi.?coherent.*(extension|shortExact)|extension.*quasi.?coherent` returned zero.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf` with those patterns and
  `isQuasicoherent_of_shortExact` found the scheme/Zariski extension theorem
  (`WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension`, read in full),
  which is not the small-etale algebraic-space statement. Algebraic-space coherent
  extension statements require locally Noetherian hypotheses and finite presentation;
  `AlgebraicSpaceQCohTriangulated` mentions extension closure in its proof only.
- `grep -rn 'lem-sfb-space-qcoh-extension-closed' lean/WeilConjectures` returned no match.
  `dag/lean_names_upstream.json` search for `isQuasicoherent_of_shortExact` returned
  no name. The proposed full declaration name is absent from the searched source.

Validation: the prescribed `scompile.py Q88 lem-sfb-space-qcoh-extension-closed`
compiled the delivered file in sandbox and library mode with exit 0 and no errors
or disallowed warnings (reported 14.7 s and 1.5 s). All lines are at most 100 columns.
No statement dispute, correction, missing definition, or dependency repair was needed.

## Second reading by Q88

Author's second reading, under the dispatcher's instruction not to start other agents;
the maintainer supplies the independent review. I reopened the JSON node and Lean
file and matched every row above. `c.X₁` and `c.X₃` are exactly the assumed outer
terms, and `c.X₂` is the asserted middle term; none is bundled in QCoh in advance.
`c.ShortExact` means exactness of sheaves and the end mono/epi conditions, not the
stronger sectionwise-surjective condition. The `X.Modules` abbreviation retains
precisely the small etale structure sheaf and coefficient universe from the dependency.
There is no geometric finiteness hypothesis or exclusion of the empty case. The
source's full two-out-of-three statement was not silently substituted for the item's
extension-only assertion. No mismatch was found and no statement change was made.
The formerly suggested example Sheaf CompactObject module is withdrawn locally;
its recorded upstream `WeilConjectures.CategoryTheory.CompactObject` was read for
module conventions instead. No new or dependency nodes are delivered.

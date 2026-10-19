## Worker report

The delivery states `WeilConjectures.a1FiniteEtaleWeilImage_lisse` in
`Sheaf.Paper.FiniteEtaleLisseWeilImage`. It uses the currently recorded constructible
common-stage category and Frobenius fixed pairs. The natural-language statement is unchanged.
Only `lean` and the addition of two already landed definition nodes to `stmt_deps` change.

Clause audit:

- The finite-field datum, including the actual chosen algebraic closure k, is
  `D : FiniteFieldDatum.{u}`. Every geometric scheme is literally `D.geometricFiber`.
- The prime is `l : ℕ` with `[Fact l.Prime]`, and `hl : l ≠ D.p` is explicit.
  `Ω : Type v`, `[Field Ω]`, `[Algebra ℚ_[l] Ω]`, `[IsAlgClosure ℚ_[l] Ω]`
  give the arbitrary specified coefficient closure. The universes u and v are independent.
- `X₀ Y₀ : Over (Spec (.of D.k₀))` are the two schemes over the given base.
  `[LocallyOfFiniteType ...hom]` and `[QuasiCompact ...hom]` express finite type for
  each, and `[hXsep : IsSeparated X₀.hom]` and `[hYsep : IsSeparated Y₀.hom]`
  express separatedness. The `include hXsep hYsep het in` command retains the two
  separatedness hypotheses and etaleness in the theorem even though the construction
  of proper pushforward itself does not need them.
- `g₀ : Y₀ ⟶ X₀` is a morphism over k₀ by the Over category. `[IsFinite g₀.left]`
  and `[het : Etale g₀.left]` impose exactly finite etale. `zlFiberMap D g₀`
  is its actual geometric base change. Properness needed by the existing construction
  is inferred from finiteness, rather than added as a hypothesis.
- `F : sfCommonStageWeilSheaf D l hl Y₀ Ω` is a constructible Weil fixed pair in
  the constructible heart. `_hF : HasCommonStageLisseLattice ... F.obj.carrier`
  expresses that its underlying geometric sheaf is lisse. This is the already landed
  completed-coefficient presentation of the lisse adic definition; it permits variable
  rank and requires no Frobenius-stable lattice.
- `a1FiniteEtaleWeilImage` is the actual proper direct image lifted by
  `IsoAlgebra.mapOfNatIso (zlProperFrobenius ...)`. The latter is the specified
  counit mate of the normalized inverse-image Frobenius square. The resulting structure
  is exchange followed by the image of F's structure isomorphism. There is no arbitrary
  morphism or isomorphism among the hypotheses.
- The first conclusion, `sfCommonStageHeartProperty ... output.carrier`, states that
  the derived image is a constructible sheaf. The second conclusion,
  `HasCommonStageLisseLattice ... output.carrier`, states lissity on X.
- The third conclusion, `Nonempty (A1FiniteEtaleImageRealization ... F)`, records the
  underived/derived equality in coefficient presentations. Its `stage`, `input`,
  `lattice`, `finiteFree`, `inputDegreeZero`, `inputRealization` realize the input
  as a lisse finite-stage integral lattice followed by rationalization and inclusion.
  `outputDegreeZero` identifies `output.obj` with the single complex on the ACTUAL
  `sfCompletedModuleDirectImage ... lattice`; `outputRealization` identifies its
  rationalization with the carrier of the canonical equivariant image. `product` and
  `derivedImage` retain an instance and the defining `SfIntegralDirectImage` Roos
  triangle for the same input. `derivedEqualsUnderived` identifies that derived-limit
  image with `output.obj`. Thus g_*F and Rg_*F are represented by the same underived
  module image in degree zero; this clause is not merely vanishing of higher cohomology.
  The witness is existential data in the theorem, not an additional hypothesis or a
  definition choosing unconstrained data from a sorry existence statement.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `FiniteFieldDatum.geometricFiber`, reexported by the common-stage operations module.
- The two scheme-convention nodes define no declarations of their own. Their actual
  Mathlib meanings are `Scheme`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`,
  `IsFinite`, `Etale` and `Over`; the full class signatures and docstrings were checked.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilComplex`,
  `sfCommonStageWeilSheaf` and the underlying `.carrier` fixed-pair interface.
- `Sheaf.Paper.LisseIntegralSmallCoefficients`: the recorded lisse integral-system
  interface, publicly imported for the proof route; the already landed
  `Sheaf.Paper.CommonStageLisse` predicate `HasCommonStageLisseLattice` gives its
  completed-coefficient realization, exactly as its owning definition node states.
- `Sheaf.Paper.SfDerivedDirectImage`: `sfCompletedModuleDirectImage`,
  `sfDirectImageTerm`, `SfIntegralDirectImage` (including its actual transition/Roos data).
- `Sheaf.Paper.CommonStageWeilShriek`: `zlCommonStageProperPush`,
  `zlProperFrobeniusMap`, `zlProperFrobenius`; reexports `zlFiberMap` from
  `Sheaf.Paper.WeilIndSheafCategory` and the recorded Frobenius pullback.
- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty`; and
  `Sheaf.Paper.SfRationalizationKaroubi` / `GeneralAlgebraicallyClosedCoefficients`:
  `sfIntegralConstructibleCategory`, `sfRationalConstructibleLocalization`,
  `GeneralAlgebraicallyClosedCoefficients.inclusion` and the canonical small coefficient
  model `AlgebraicallyClosedCoefficients.Coefficient.{u}`.

The module's proof-only imports retain the stated finite-splitting, Galois/lattice,
finite-level, exact-functor, localization and Milnor inputs from the seven proof steps.
Direct-image/constructibility/heart/derived-completeness dependencies already reexported
through these modules need no duplicate import. The old `prop-weil-operations` attachment
was read through `scompile.py --source`: its OtherSections module is in a different
derived-of-Weil-sheaves category and does not supply the required common-stage operation.
Its required proper-image/Frobenius notion is already supplied by the added landed
`def-zl-common-stage-weil-shriek`, so no duplicate construction or partial replacement of
the full six-operation proposition is introduced.

Edge cases: empty schemes and empty fibres, the zero sheaf, finite etale maps that are
not surjective, disconnected bases with varying degrees, and lisse sheaves with varying
finite rank are all allowed. No point, nonempty index set, positive rank, globally
constant degree, global splitting, smoothness, connectedness, or arithmetic Galois
continuity is assumed. The coefficient closure universe is independent of the scheme
universe; completed-module/site universes remain u+1/u as prescribed. Explicit universe
arguments on `IsFiniteLocallyFree` fix its ring/module universe u+1, site Hom universe u
and site object universe u+1, without imposing a new equality on u and v.

Searches performed with the prescribed launcher wrapper (full results in searches.jsonl):

- LeanFinder: `finite etale pushforward of a lisse Weil sheaf is lisse`: eight generic
  etaleness/site/pushforward hits, no exact theorem.
- LeanSearch: `finite etale pushforward of lisse adic sheaves`: eight general sheaf
  pushforward declarations, no matching statement.
- Loogle: `IsLisse, lowerStar`: unknown identifier `IsLisse`.
- Mathlib grep: `(lisse|Lisse).*([Pp]ushforward|lowerStar)`: zero hits.
- Project/source `rg`: lisse/pushforward and `lem-a1-finite-map-lisse` in the named
  source trees and `dag/lean_names_upstream.json`. The previously published
  `Sheaf.DeligneLaumon.Reduction.FiniteMapLisse` module was found and read in full,
  including its current server source. Its theorem uses `WeilComplex.derivedLowerStar`
  on a derived category of Weil sheaves. Its `WeilSheaf` and the fixed canonical
  `PadicAlgCl`/`AlgebraicClosure k₀` are not the literal recorded common-stage fixed-pair
  objects on the arbitrary D.k/Ω used here. In particular the recorded
  `def-weil-weil-sheaf-complex` explicitly excludes that derived-category definition.
  It therefore is not an exact existing match for the present dependency interface.
- Project `rg` for common-stage lisse and proper image found and reused the two
  already landed nodes `def-a1-common-stage-lisse-lattice` and
  `def-zl-common-stage-weil-shriek`; the complete nodes and defining modules were read.
  A read-only traversal checked that neither addition creates a dependency cycle.

Source checks: opened the current blueprint opening sentence and Stacks
`etale-cohomology.tex`, lemma-pushforward-locally-constant (095B), including its proof:
etale-local finite splitting and a finite product of locally constant module sheaves.
The full seven-step node proof is preserved in the theorem docstring. There is one
postponed theorem and no proof work; the two helper declarations have real data.
No statement correction and no STATEMENT-DISPUTED finding.

Validation: the prescribed scompile wrapper compiled both the sandbox file and its
library-path form successfully after the explicit local-freeness universe correction.
Temporary `#check` probes were removed before final compilation and delivery.

## Second reading by N1

Author self-check, not an independent review: reopened the node and complete file and
matched every hypothesis and conclusion as listed above. The initial draft let section
hypotheses disappear when unused by construction; the final theorem explicitly includes
the two separatedness instances and etaleness. The initial local-freeness universe
arguments had site object/Hom universes swapped; compiler output and the full declaration
type identified the order, now explicitly u+1, u, u+1. The output uses the canonical
proper-image Frobenius mate. The additional integral witness binds the same geometric
map, finite coefficient stage and input lattice on both sides of the underived/derived
comparison, with all typeclass data explicit. All sorries are whole theorem proofs.
Independent review is left to the maintainer as required by the dispatcher brief.

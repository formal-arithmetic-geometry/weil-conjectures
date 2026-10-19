## Worker report

The module `Sheaf.Compactification.NagataDensityNormalizationSetup` states
`AlgebraicGeometry.nagataDensityNormalizationSetup`. It imports the recorded compactification
structure, Mathlib's Noetherian, immersion, open/closed immersion, quasi-separated, proper, and
fibre-product interfaces, and the project's canonical open complement of a closed immersion.

The theorem takes `f : X ⟶ S`, a compactification `c : Compactification f`, and
`[IsNoetherian c.Z]`. Its conjunction renders the four source clauses as follows. The first
clause is the canonical image factor `c.i.toImage`, with `IsOpenImmersion c.i.toImage`,
`QuasiCompact c.i.toImage`, `IsSchemeTheoreticallyDominant c.i.toImage`, and the exact
factorization `c.i.toImage ≫ c.i.imageι = c.i`. The second clause is represented by
`CompactSpace c.Z`, `QuasiSeparatedSpace c.Z`, `CompactSpace c.i.image`, and
`QuasiSeparatedSpace c.i.image`; `IsClosedImmersion c.i.imageι` records that the image is a
closed subscheme. The complement is the canonical
`Scheme.openComplementOfIsClosedImmersion c.i.imageι`; its inclusion is open and quasi-compact,
`CompactSpace complement.toScheme` also records quasi-compactness of the open itself,
and its underlying range is disjoint from `Set.range c.i.base`. The third clause is the empty
scheme assertion `IsEmpty (CategoryTheory.Limits.pullback c.i complement.ι : Scheme)`, together
with `IsIso (CategoryTheory.Limits.pullback.fst c.i c.i.imageι)` and the projection formula
`pullback.snd = pullback.fst ≫ c.i.toImage`. The fourth clause is
`IsProper (c.i.imageι ≫ c.g)`.

Dependencies used: `def-nagata-compactification` via
`WeilConjectures.Compactification.Defs`, declaration `AlgebraicGeometry.Compactification`;
`pqf-def-locnoeth` via Mathlib `AlgebraicGeometry.IsLocallyNoetherian`; scheme-theoretic image
via `AlgebraicGeometry.Scheme.Hom.image`, `toImage`, and `imageι`; open and closed immersion
properties via `AlgebraicGeometry.IsOpenImmersion` and `IsClosedImmersion`; quasi-compactness
via `AlgebraicGeometry.QuasiCompact`; quasi-separatedness via `QuasiSeparatedSpace`;
fibre products via `CategoryTheory.Limits.pullback`, `.fst`, and `.snd`; properness via
`AlgebraicGeometry.IsProper`; and the canonical complement via
`AlgebraicGeometry.Scheme.openComplementOfIsClosedImmersion`.

Edge cases checked from the source proof: the empty `X` gives empty image and empty pullback;
the identity open immersion gives the top image and bottom complement; and nonreduced closed
images retain their scheme structure because the complement is built from `imageι`, not from a
reduced replacement. The pullback is stated using the canonical Mathlib pullback and its
universal projections, so the identity and empty cases remain included.

Searches: `msearch.py ... leanfinder "schematic closure of an open immersion in a Noetherian compactification factors as a quasi-compact open immersion"` returned the individual Mathlib declarations `instIsOpenImmersionToImageOfQuasiCompact`, `instQuasiCompactOfIsLocallyNoetherianOfIsOpenImmersion`, and related facts, with no whole-item declaration. `msearch.py ... loogle "Scheme.Hom.toImage, IsOpenImmersion, IsSchemeTheoreticallyDominant, IsProper"` returned no result because `Scheme.Hom.toImage` is not a Loogle identifier. `msearch.py ... grep "toImage|imageι|IsSchemeTheoreticallyDominant" Mathlib/AlgebraicGeometry` returned no grep result in the configured search tree; direct `rg` in the pinned Mathlib and source located the declarations listed above. `rg` over `lean/Sheaf` found the related statement module `Sheaf/Compactification/NagataSketchClosure.lean`, but it states a different theorem and does not cover this four-clause setup. No existing declaration matches the node.

The remaining dependency modules are `Mathlib.AlgebraicGeometry.Noetherian`
(`IsLocallyNoetherian`, `IsNoetherian`), `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
(`Scheme.Hom.image`, `Scheme.Hom.toImage`, `Scheme.Hom.imageι`),
`Mathlib.AlgebraicGeometry.OpenImmersion` (`IsOpenImmersion`),
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` (`IsClosedImmersion`),
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (`LocallyOfFiniteType`; the quasi-compact
part uses `QuasiCompact` from its imported QuasiCompact module),
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` (`QuasiSeparated`, equivalently
`QuasiSeparatedSpace` for the absolute notion),
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback` (`pullback`, `pullback.fst`,
`pullback.snd`), and `Mathlib.AlgebraicGeometry.Morphisms.Proper` (`IsProper`).
The existing complement definition is read from
`WeilConjectures.ConstructibleSheaf.OpenClosedStratification`.
`IsSchemeTheoreticallyDominant` is from Mathlib's Morphisms.SchemeTheoreticallyDominant;
on a quasi-compact factor it says exactly that the scheme-theoretic image fills the target.

Additional required search: `msearch.py ... leansearch "A Noetherian compactification factors
through its scheme theoretic image with quasi-compact dense open factor and proper image
over the base"` returned eight individual image/open-factor and Noetherian facts (including
`Scheme.instQuasiCompactToImage`), with no whole-item statement. Direct `rg` for this node id
and for `nagataDensityNormalizationSetup` over the project Lean trees returned no hit.
The invalid Loogle query and configured-grep zero result are not used as negative evidence;
positive direct source inspection supplies the actual interfaces.

`Compactification` in the upstream source omits a quasi-compactness field for `c.i`; this
causes no loss here because the stipulated locally Noetherian target already makes every
open immersion into it quasi-compact. `IsNoetherian` extends `IsLocallyNoetherian` and
`CompactSpace`, precisely the two hypotheses of this node. No stronger hypothesis on the
base `S`, reducedness, or density of the original compactification is imposed.

No `STATEMENT-DISPUTED` or node fault was found.


## Second reading by Q08

The source statement introduces a morphism `f : X ⟶ S`, a compactification
`c` with ambient scheme `c.Z` (the source's `\overline X`), its open immersion
`c.i` (the source's `j`), and proper map `c.g` (the source's `p`); it assumes
that the ambient scheme is Noetherian, i.e. locally Noetherian and quasi-compact.
It then introduces the scheme-theoretic image `c.i.image` with closed inclusion
`c.i.imageι`, its factor map `c.i.toImage`, and the canonical open complement
`Scheme.openComplementOfIsClosedImmersion c.i.imageι` (the source's `V` and
`j_V`). The four conclusion clauses were matched as follows.

1. `IsOpenImmersion c.i.toImage`, `QuasiCompact c.i.toImage`,
   `IsSchemeTheoreticallyDominant c.i.toImage`, and
   `c.i.toImage ≫ c.i.imageι = c.i` render the factorization
   `j = i ∘ j_Z`, the quasi-compact open immersion, density, and canonical
   factorization. The recorded `Scheme.Hom.toImage`/`imageι` declarations are
   the same scheme-theoretic image objects as the node.
2. `CompactSpace c.Z` and `QuasiSeparatedSpace c.Z` render the ambient qcqs
   assertions. `CompactSpace c.i.image`, `QuasiSeparatedSpace c.i.image`,
   `IsClosedImmersion c.i.imageι`, and the compactness/open/quasi-compactness
   fields for the canonical complement render the qcqs image and the
   quasi-compact open with closed complement `Z`.
3. The range intersection equality renders `j(X) ∩ V = ∅`; `IsEmpty` of the
   pullback with the complement renders the empty fibre product. `IsIso` of
   `pullback.fst c.i c.i.imageι`, together with
   `pullback.snd = pullback.fst ≫ c.i.toImage`, renders the canonical
   `X ×_{\overline X} Z ≅ X` identification via `j_Z`.
4. `IsProper (c.i.imageι ≫ c.g)` is exactly `p ∘ i` proper.

The hypothesis `[IsNoetherian c.Z]` is exactly the source's Noetherian
ambient assumption: Mathlib's class extends `IsLocallyNoetherian` and
`CompactSpace`; no extra hypothesis on `S`, reducedness, characteristic,
finite type, or separatedness is present. The compactification structure in
the current dependency intentionally only assumes an open immersion, matching
the current blueprint; quasi-compactness is concluded from Noetherianity.

Edge cases checked are the empty source (empty image and empty complement
pullback), the identity open immersion (top image and empty complement), and
nonreduced closed images (the given scheme structure is retained by
`imageι`). The pullback statements use the canonical Mathlib pullbacks and
therefore include these cases. Universes are shared by `X`, `S`, and `c.Z`
through the single explicit `universe u`; there is no index type or
characteristic restriction.

Searches were repeated with LeanFinder for the whole factorization statement,
Loogle for image/open/dominance/properness combinations, LeanSearch for the
Noetherian compactification formulation, and direct `rg` searches through the
project, source, and pinned Mathlib trees for
`nagataDensityNormalizationSetup`, `toImage`, `imageι`, and
`IsSchemeTheoreticallyDominant`. They found only the individual Mathlib
interfaces and no declaration of this four-clause theorem. The invalid Loogle
identifier and configured-grep miss were recorded as non-evidence; direct
source inspection supplied the positive interfaces.

No mismatch was found and no Lean or node statement change was necessary.
The module was compiled with `scompile.py` and produced no errors or warnings.

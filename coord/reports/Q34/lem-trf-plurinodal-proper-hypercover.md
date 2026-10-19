## Worker report

The module `Sheaf.Paper.PlurinodalProperHypercover` states
`AlgebraicGeometry.Orgogozo.exists_plurinodal_proper_hypercover`. Its proof is `sorry`;
no mathematical theorem is proved in this delivery. The auxiliary
`SemistableTower.length` is defined by recursion on the existing tower constructors,
with values zero and successor. The only new independent notion is the proper-hypercover
predicate in `Sheaf.AlgebraicGeometry.ProperHypercover`.

I read the complete item, all ten statement-dependency statements and records, the
recorded definitions (including every geometric structure in OrgogozoInductionData),
and all twelve proof steps. I read Orgogozo Proposition 3.3.1 and Lemma 3.3.2 on printed
page 9 of the author PDF, and the surrounding definition of almost plurinodal on
printed pages 8--9. I also read `spaces-simplicial.tex`, section
`section-proper-hypercovering-spaces`, whose scheme version is explicitly authorized.
Its degree-zero, degree-one and coskeleton conditions are the matching conditions used here.

Clause-by-clause translation:

| Node clause | Lean rendering |
| --- | --- |
| Schemes S and X | `{S X : Scheme.{u}}`, with one explicitly bound scheme universe. |
| Both integral | `[IsIntegral S] [IsIntegral X]`. Mathlib integrality includes nonemptiness. |
| Both excellent | `hS : IsExcellentScheme S` and `hX : IsExcellentScheme X`, using the dependency's predicate on every affine coordinate ring. |
| Both Noetherian | `[IsNoetherian S] [IsNoetherian X]`, i.e. locally Noetherian and quasi-compact. |
| Both of finite dimension | `hdimS` and `hdimX`, each `topologicalKrullDim ... < ⊤`. |
| f proper and dominant | `(f : X ⟶ S) [IsProper f] [IsDominant f]`. |
| Existence of integral excellent Noetherian T | Existential `T`, witnesses `IsIntegral T`, `IsNoetherian T`, and conjunct `IsExcellentScheme T`. |
| Alteration a of the base | Existential `(a : T ⟶ S)` and the existing `IsAlteration a`. |
| Augmented simplicial scheme over X times_S T | `Y : SimplicialObject (Over (pullback f a))`; every term has its actual augmentation map as its slice structure map. |
| All matching maps, including degree zero, proper surjective | `IsProperHypercover Y`. This uses the existing proper-face diagram, a universal limit cone, and its unique induced arrow; both `IsProper` and `Surjective` apply to the underlying scheme map. Degree zero is the terminal object of the slice. |
| Degree zero almost plurinodal over T | `D : AlmostPlurinodalDatum T`, an isomorphism `e : Y₀.left ≅ D.source`, and `e.hom ≫ D.morphism = Y₀.hom ≫ pullback.snd f a`. The equation makes this an isomorphism over T. |
| Each term finite type over T | `∀ n`, `LocallyOfFiniteType` and `QuasiCompact` of the composite of its augmentation and `pullback.snd f a`. |
| Each term has a finite fibre-dimension bound | Within the same degree quantifier, `∃ b : ℕ, ∀ t : T`, the dimension of the scheme-theoretic fibre is at most b. There is no uniform bound in n. |
| Each curve factor has a finite closed subscheme containing its nonsmooth locus | Already retained in every `D.towers i` by `SemistableFactor.closed`, `inclusion`, `isClosedImmersion`, `finite`, and `smoothComplement`. The latter gives relative smoothness on the complement, exactly implying the required containment. No replacement notion or extra input is introduced. |
| Every semistable tower has relative dimension equal to the original generic-fibre dimension | `∀ i : Fin D.count`, `(D.towers i).length`, cast to `WithBot ℕ∞`, equals `topologicalKrullDim (f.fiber (genericPoint S))`. Each factor has connected reduced geometric fibres of pure dimension one, so the number of factors expresses the tower's relative dimension, including zero. |
| The other summand has nowhere dense image | Retained by `D.nowhereDense`, with its proper structure map `D.verticalMap` and witness `D.verticalProper`. |
| dim T = dim S | Final equality `topologicalKrullDim T = topologicalKrullDim S`. This also retains finiteness of dim T. |

Dependency declarations reused, without copying their notions:

- `Sheaf.Paper.OrgogozoInductionData`: `IsExcellentScheme`, `IsAlteration`,
  `SemistableTower`, `SemistableFactor`, `AlmostPlurinodalDatum`,
  `AlmostPlurinodalDatum.source`, and `AlmostPlurinodalDatum.morphism`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`,
  `pullback.snd` (the actual fibre product and its structure map).
- `Mathlib.AlgebraicGeometry.Properties`: `IsIntegral` and the scheme's generic point.
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, used through `IsExcellentScheme`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`;
  `Mathlib.Topology.Defs.Filter`: `CompactSpace`, as inherited by `IsNoetherian`.
- The new node reuses `SimplicialObject.properFaceDiagram` and
  `SimplicialObject.properFaceProperty` in
  `Sheaf.CategoryTheory.ProperFaceMatchingObject`, Mathlib's `Over.forgetCocone`,
  `Cocone.whisker`, `Cocone.op`, `Functor.mapCone`, and `IsLimit.lift`.

All proof-dependency modules with recorded Lean modules are imported privately,
except those already imported publicly for the statement. The currently unstated
`lem-trf-closed-dominant-dimension`, `lem-trf-de-jong-geometrically-irreducible-tower`,
and `lem-trf-nodal-family-fitting-singular` have no module to import; the full proof
plan names them. The Mathlib-only geometric-irreducibility, proper/quasi-finite finiteness, and flat
going-down inputs are imported privately from their recorded source modules; the
remaining Mathlib inputs are supplied by the already imported geometry modules.

Edge cases checked before writing: integral hypotheses correctly exclude empty S/X;
proper dominance gives a nonempty generic fibre. A zero-dimensional generic fibre
allows length-zero identity towers. An empty finite set of tower summands is allowed
by `Fin D.count` (surjectivity and the nowhere dense vertical image prevent it from
being an inappropriate solution for the present dominant f). The vertical scheme
and finite singular closed subschemes may be empty, and no reducedness of those
closed subschemes was added. Degree zero of the matching predicate is a terminal
slice limit, degree one is a fibre product over the augmentation target, and all
higher degrees are retained. Every scheme, matching test object and fibre has the
same arbitrary bound universe u; no smaller test universe or extra universe equality
is imposed. Bounds vary with degree. No characteristic restriction is imposed.

Searches were run using msearch.py (actual JSON responses in searches.jsonl):
LeanFinder `proper hypercover of an integral scheme after alteration with almost
plurinodal degree zero` returned quasi-compact covers and ordinary gluing, no
alteration/hypercover theorem. Loogle `SimplicialObject,
AlgebraicGeometry.IsProper, AlgebraicGeometry.Orgogozo.AlmostPlurinodalDatum`
returned zero hits, with an unknown-identifier diagnostic for SimplicialObject.
Mathlib grep `matchingObject|matchingMap|ProperHypercover|AlmostPlurinodal`
returned zero hits. A second LeanFinder query for simplicial matching limits found
`SimplicialObject`, coskeleta and Cech nerves; their sources were read. Further
LeanSearch and LeanFinder proper-hypercover queries found only zero/one-hypercovers,
scheme covers and surjectivity. Exact Mathlib grep
`IsProperHypercover|ProperHypercover|proper hypercover` returned no hit.
Direct rg of WeilConjectures and lean/Sheaf found no proper-hypercover predicate;
rg of the item id in the upstream checkout found no attached theorem. DAG searches
found the existing etale, finite split etale and semi-representable hypercover
notions, whose etaleness/splitting or different objects make them unsuitable here.
The existing generic proper-face diagram is used. `tools/blueprint_refs.py search
'proper hypercover'` returned zero blueprint nodes. No statement correction or
STATEMENT-DISPUTED issue was needed.

## New nodes

`def-trf-proper-hypercover` defines proper hypercovers for arbitrary augmented
simplicial schemes using canonical matching maps in the category of schemes over
the augmentation target. Its source is the proper-hypercover definition preceding
Stacks 0DHL (schemes explicitly allowed), with matching limits from Tag 0186,
and Orgogozo Proposition 3.3.1. The searches above found only etale or truncated
hypercovers, not this predicate. It uses the existing proper-face diagram and the
actual universal-property lift; no arbitrary matching map or hollow data is chosen.
The boundary cone is constructed entirely by existing Mathlib operations.

## Second reading by Q34

Author's final rereading under the dispatcher's single-worker instruction;
independent review is performed by the maintainer. I reopened both modules and
the item and checked the table above against the final signature. In particular,
the degree-zero isomorphism is over T, the Cech augmentation target is X times_S T,
the dimension condition applies to every tower rather than only their union,
and the fibre bound is inside the degree quantifier. The new predicate tests limits
in Over Z, so it retains the augmentation in degree zero. No mathematical mismatch
was found and no node statement was changed. The only sorry is the named item theorem.

Validation: both modules are checked separately, in dependency order, through
scompile.py with the standard 60-second limit. The delivery dry run and final
push are run through deliver2.py.

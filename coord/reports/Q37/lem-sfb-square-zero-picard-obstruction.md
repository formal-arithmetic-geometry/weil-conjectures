## Worker report

This delivery states `AlgebraicGeometry.Scheme.exact_picard_squareZeroPicardObstruction`
and defines its canonical obstruction in the companion definition node. All theorem
proofs are `sorry`; every definition has real data. No statement correction or dependency
repair is required.

Clause-by-clause correspondence:

- Arbitrary schemes Z and Z′: `{Z X : Scheme.{u}}`, with unrestricted universe `u`.
- A first order thickening j: `(j : Z ⟶ X) (hj : IsFirstOrderThickening j)`.
  The recorded definition is exactly `IsClosedImmersion j ∧ j.ker ^ 2 = ⊥`.
- Its defining quasi-coherent ideal: the recorded `j.ker` and `j.ker.toModules`, never
  an arbitrary coefficient sheaf. The ideal on Z is `(Modules.tensorPullback j).obj
  j.ker.toModules`. Affine-locally this is `(R/I) ⊗[R] I = I/I² = I`, with precisely
  the quotient scalar action required by the statement. This works for every ideal,
  without finite generation or Noetherian assumptions.
- Pic(W): the existing `W.Pic`, the isomorphism classes of invertible module sheaves
  under tensor product. `Additive W.Pic` changes notation only, so its zero is the
  class of the unit and its addition is tensor product.
- Restriction: `fun L : Additive X.Pic => Additive.ofMul (Pic.map j L.toMul)`.
  `Pic.map` uses the existing pullback left adjoint; the recorded tensor pullback is
  canonically isomorphic to it by uniqueness of left adjoints. Thus it gives exactly
  restriction of invertible sheaves on Picard classes.
- A canonical group homomorphism: `squareZeroPicardObstruction j hj`, defined from the
  actual units boundary and existing normalized cohomology comparisons. Its additive
  homomorphism type expresses the group homomorphism clause.
- H²(Z,I): the target is `(RingedSpace.moduleCohomology Z.toRingedSpace 2).obj
  ((Modules.tensorPullback j).obj j.ker.toModules)`, the prescribed right derived
  module-valued global sections, not abelian cohomology substituted for module cohomology.
- Exactness at Pic(Z): `Function.Exact` for the restriction function and this specific
  obstruction. It says for every L, δ(L)=0 iff L has a preimage under restriction.
- No Noetherian, proper, reduced, or dimension assumptions occur.

The canonical map is not chosen from existence of a map having the desired kernel.
`squareZeroUnitsSequence` is the categorical kernel sequence of `unitsSheafToPushforward`.
Its short exactness is a named postponed theorem. The only chosen data is an isomorphism
uniquely characterized on every section by a ↦ 1+a; its named existence-and-uniqueness
theorem determines it uniquely, as permitted for universal-property constructions.
The definition then composes Hilbert 90, the inverse canonical units comparison
(using `Function.surjInv` on its proved surjectivity, with bijectivity ensuring uniqueness), the
actual Yoneda boundary `Sheaf.H.δSucc`, the inverse normalized ideal/kernel isomorphism,
the resolution-normalized module/abelian comparison, and the canonical module cohomology
map for the normalized tensor adjunction unit. Since j*I=I/I²=I, this last map is the
canonical cohomology identification with the desired coefficient on Z.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `WeilConjectures.AlgebraicGeometry.Thickening`: `IsFirstOrderThickening`.
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic`: `Scheme.Hom.ker`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`:
  `IdealSheafData.toModules` and `toModulesι`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible`.
- `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`:
  `Modules.tensorPullbackSectionAdjunction` and its public `Modules.tensorPullback`.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `sheafCohomologyAndHigherDirectImages`; cohomology is the public
  `RingedSpace.moduleCohomology` from `WeilConjectures.Topology.RingedSpaceModuleCohomology`.
- `WeilConjectures.AlgebraicGeometry.PicardFunctor`: `Scheme.Pic`, `Pic.map`.
- `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`: `Pic.toH1UnitsAddEquiv`.
- `WeilConjectures.AlgebraicGeometry.ZariskiUnitsRestriction`:
  `unitsSheafToPushforward` and `unitsPushforwardCohomologyComparison`.
- `WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitsCohomologyComparison`:
  `bijective_unitsPushforwardCohomologyComparison_of_isClosedImmersion`.
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`:
  `Sheaf.H.δSucc`, with the `Sheaf.H` and `Sheaf.H.map` definitions from Mathlib.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality`:
  `Modules.moduleCohomologyExtResolutionEquiv`, the explicitly resolution-normalized
  comparison, rather than a choice of an unspecified natural isomorphism.
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`:
  `Modules.moduleCohomologyFMap`.
- The stated proof dependencies `WeilConjectures.Topology.ClosedImmersionPushforwardCohomology`,
  `WeilConjectures.AlgebraicGeometry.ZariskiModuleAbelianCohomologyNatural`, and
  `WeilConjectures.AlgebraicGeometry.PicardH1RestrictionCompatibility` are plain proof imports.

Edge cases checked mathematically: the identity thickening has zero ideal and zero obstruction,
so every Picard class lifts. The empty scheme has trivial Picard and cohomology groups.
The formula (1+a)(1-a)=1 holds in every characteristic, including two. Non-affine opens
require local lifting of units, not surjectivity on global units; the helper theorem asserts
sheaf short exactness only. Arbitrary non-Noetherian and infinite-dimensional schemes are
included. No restriction on characteristic, separation, properness, or affine coverings occurs.

Searches performed with the prescribed msearch wrapper:

- LeanFinder: “For a square zero thickening of schemes the Picard restriction map has
  obstruction homomorphism to second cohomology of the ideal and the sequence is exact”:
  eight cotangent-complex/Jacobi-Zariski hits, no matching scheme theorem.
- Loogle: `"Pic", "Exact"`: three hits, ring-Picard exactness and path homotopy, no match.
- Mathlib grep: `[Pp]icard.*[Tt]hicken|[Pp]icard.*[Oo]bstruction|[Tt]hicken.*[Pp]icard`:
  zero hits.
- LeanSearch: “canonical connecting homomorphism Picard group square zero ideal second
  sheaf cohomology”: eight group-cohomology or homology-sequence hits, no matching map.
- LeanFinder: “The canonical Picard obstruction map is the connecting homomorphism of the
  sequence of units under the identification a maps to one plus a for a square zero ideal”:
  eight cotangent-complex hits, no matching map.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` with Picard/obstruction/thickening
  expressions found only the special split dual-number theorem in Picard/DualNumbers.lean.
  Exact node-id search in WeilConjectures found nothing.
  Additional LeanFinder search for the normalized units sequence returned eight
  algebra-extension/cotangent results; LeanSearch returned generic short-complex
  exactness and no geometric sequence; Mathlib grep returned zero hits.
  Project grep for squareZeroUnitsBoundary and squareZeroIdealUnitsIso returned
  zero hits; blueprint search for “square zero units” returned zero matches. DAG title/content searches found
  the assigned statement but no definition node for its canonical map.
  `tools/blueprint_refs.py search 'Picard obstruction'` returned zero blueprint nodes.

Source read: `literature/stacks-project/more-morphisms.tex`, lines 598–630, Tag 0C6R,
including its entire displayed sequence and proof; the latest unit and chapter section
texts were also read. The unit statement is unchanged. No STATEMENT-DISPUTED issue remains.

## New nodes

`def-sfb-square-zero-picard-obstruction-map` defines the actual canonical homomorphism
used in the item, following Stacks Tag 0C6R. The normalized kernel sequence, its short exactness, the unique section-normalized
ideal/kernel identification, the boundary, and the induced inverse-identification map
are in the additional definition node `def-sfb-square-zero-units-boundary`, module
`Sheaf.AlgebraicGeometry.SquareZeroUnitsBoundary`. Both postponed proof obligations
have a matching statement there and complete natural-language proof docstrings.
The map module defines the composite function first and bundles it using the named
`squareZeroPicardObstructionFun_additive` theorem, whose zero and addition clauses
are explicitly included in its definition node. This additional postponed theorem
has a full proof plan and does not choose any function data.
The map module imports this node; all helpers are listed in the owning `lean.declarations`.
Searches above and their raw responses in `mathlib_searches` establish that this
construction had no existing node or declaration. Existing Picard, ideal, tensor
pullback, cohomology, and comparison definitions are reused.

## Validation

All three delivered files passed scompile.py, both sandbox and module checks,
with no errors or warnings. Module checks: SquareZeroUnitsBoundary 18.1 s,
SquareZeroPicardObstructionMap 52.8 s, SquareZeroPicardObstruction 4.3 s.
No compiler limit was raised. The required deliver2.py dry run passed preflight
and compilation (5ecffd6dd25); nothing was pushed in that dry run.

## Second reading by Q37

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

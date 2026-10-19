## Worker report

The module `Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChangeUnderivedCompatibility`
defines the canonical module mate `chosenSquareEtaleLowerShriekBaseChangeMate`,
its comparison with the recorded standard fiber-product β, and the chosen-square transport
`chosenSquareEtaleLowerShriekBaseChangeMap`, states its invertibility as
`isIso_chosenSquareEtaleLowerShriekBaseChangeMap` (with postponed proof), and states
`AlgebraicGeometry.Etale.derivedExtensionZeroBaseChangeUnderivedCompatibility` with proof
`sorry`, as required for stage 2.  It binds a finite commutative ring `Λ`, four schemes and
four arrows forming `sqdata : OpenImmersionSquare gU j' j g`, and a module sheaf `F` on
`U.smallEtaleTopology`.  The two `letI` binders install the open-immersion instances from
`sqdata`; `sq` is the chosen pullback converted to `IsPullback` by
`IsPullback.of_iso_pullback`.

The first conjunct renders the equality `b_{g,F} = β_F⁻¹`: `b` is the inverse component of
`asIso (isIso_openImmersionLowerShriekBaseChangeMap ... sq)`, while β is the explicitly
transported `chosenSquareEtaleLowerShriekBaseChangeMap`; the right side is its inverse
component using `isIso_chosenSquareEtaleLowerShriekBaseChangeMap`.  The transport composes
κ for `j'`, the open-extension base-change map, and κ for `j`, and `chosenSquareEtaleLowerShriekBaseChangeMap_eq_mate` identifies this transport
with the independently constructed module mate. Its standard fiber-product specialization
is identified with the dependency declaration by
`chosenSquareEtaleLowerShriekBaseChangeMate_pullback`.  The second conjunct is the explicit transpose formula: the unit for `j'`,
followed by the restriction of the base-change map, equals the pullback of the unit for `j`
followed by `squareUpperStarIso ... sq.toCommSq.flip`.  The third conjunct is the requested
restriction normalization: after the cartesian inverse-image identification, the restriction
of `b` and the inverse of the `j'` extension unit compose with the pulled-back `j` unit to
`𝟙` on `gU^*F`.

The declarations used are:

- `AlgebraicGeometry.OpenImmersionSquare` from
  `Sheaf.AlgebraicGeometry.OpenImmersionSquare`;
- `AlgebraicGeometry.Etale.openImmersionToEtaleLowerShriek` and
  `AlgebraicGeometry.Etale.openImmersionToEtaleLowerShriek_adjunction_agreement` from
  `Sheaf.AlgebraicGeometry.Etale.OpenExtensionZeroEtaleAdjunctionAgreement`;
- the new declarations `chosenSquareEtaleLowerShriekBaseChangeMap` and
  `isIso_chosenSquareEtaleLowerShriekBaseChangeMap` in this module, which supply the
  canonical chosen-square transport missing from the strict fiber-product interface;
- `AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap`,
  `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekBaseChangeMap`,
  `AlgebraicGeometry.Etale.unit_map_openImmersionLowerShriekBaseChangeMap_app`, and
  `AlgebraicGeometry.Etale.squareUpperStarIso` from
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare`;
- the recorded dependency `def-weil-pbc-etale-shriek-base-change-map` is the source
  module's standard fiber-product module β; the chosen-square presentation in this module
  is used explicitly by `chosenSquareEtaleLowerShriekBaseChangeMate_pullback`. The
  canonical chosen-square mate extends its formula to the given commutative square;
  `chosenSquareEtaleLowerShriekBaseChangeMap_eq_mate` supplies the previously missing
  comparison with the κ-transported open representative.

I checked the edge cases named by the source and node: the identity square, an empty open,
`F = 0`, a zero finite ring, and `g = 𝟙`.  The formulas remain well-typed; in the empty and
zero cases all relevant maps are the unique zero morphisms, and in the identity case the
cartesian comparison is the identity.

Searches made before writing:

- `msearch.py ... leanfinder "underived open immersion extension by zero base change module sheaf canonical comparison transpose restriction identity"` returned only generic Zariski restriction declarations (`restrictAdjunction_*`,
  `restrictFunctorAdjCounitIso`, `restrictFunctorIsoPullback`), with no small-etale statement.
- `msearch.py ... loogle "AlgebraicGeometry.Etale.openImmersionLowerShriekBaseChangeMap, openImmersionToEtaleLowerShriek, Adjunction"` returned zero hits and reported the queried identifier as unknown to Loogle.
- `msearch.py ... grep "openImmersionLowerShriekBaseChangeMap|openImmersionToEtaleLowerShriek" Mathlib` returned no hits.
- `rg` in `WeilConjectures/` found the canonical open-immersion base-change map and its unit formula in
  `SixFunctors/Etale/LowerShriek/OpenImmersion/BaseChangeSquare.lean`, but no theorem with this node's full compatibility statement.
- `rg` in the project's `lean/Sheaf` found no existing declaration of this item; it found only
  the vertical-pasting sibling and generic base-change uses.
- `grep -rl` over `dag/nodes` found this item, its vertical-pasting and parent corollary, and
  the open/étale adjunction-agreement dependency; no duplicate statement node.
- `blueprint_refs.py search lem-cbc-derived-extension-zero-base-change-underived-compatibility`
  found no blueprint node with this id.

No statement correction or `STATEMENT-DISPUTED` flag is needed.  The module compiles cleanly
through `scompile.py`; all four named theorems have `sorry` proofs, as required for stage 2. Both definitions
have complete data. The two comparison helpers state the identification in this node's
first clause and proof Step 2; they do not introduce independent mathematical assumptions.

## Second reading by Q20

I reread the node and module together.  The ring finiteness, four schemes, four arrows,
open-immersion square, chosen pullback, module sheaf, inverse comparison, transpose equation,
and restriction identity all have explicit Lean counterparts.  The second conjunct is the
source's adjunction-mate formula for the transported β (written through κ as the open
representative), and the third is its unit-normalized restriction formula.
No hypothesis or edge case was dropped.  The module uses the recorded open/étale comparison
rather than introducing a second extension-by-zero construction.

## Repair of returned head 2e771b0a851d

The first saved-packet dry run passed (commit 1de7035736); this did not settle the
independent H3/H4 return. The saved packet constructed its β by conjugating the open
comparison through κ but lacked an identification with the dependency's module mate.
I retained the saved definition, the original theorem signature and all three clauses,
and added the missing canonical construction and comparison in the same owning module.

- `chosenSquareEtaleLowerShriekBaseChangeMate` uses `conjugateEquiv.symm` with
  `(etaleLowerShriekUpperStarAdjunction Λ j).comp (upperStarLowerStarAdjunction Λ g)`
  and `(upperStarLowerStarAdjunction Λ gU).comp
  (etaleLowerShriekUpperStarAdjunction Λ j')`, applied to
  `baseChangeMap (ModuleCat Λ) sq.flip`. Thus it is the module mate itself, independently
  of the open base-change map. No arbitrary map, invertibility assumption or choice is used.
- `chosenSquareEtaleLowerShriekBaseChangeMate_pullback` explicitly equates this definition
  on `(IsPullback.of_hasPullback f j).toCommSq.flip` with the recorded dependency
  `AlgebraicGeometry.Etale.etaleLowerShriekBaseChangeMap Λ f j` from
  `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`. Its source was read
  with `scompile.py --source`; the construction is the same inverse-conjugate expression.
- `chosenSquareEtaleLowerShriekBaseChangeMap_eq_mate` explicitly equates the saved
  κ-transported open representative with the canonical chosen-square module mate.
  Its docstring supplies the proof by substituting the recorded unit/counit agreement
  into the composite-adjunction mate formula. This is precisely the missing comparison
  requested in the return, and is part of this node's first clause and proof Step 2.

The helper definition works on every commutative square with étale vertical arrows;
the comparison theorem uses exactly the open-immersion hypotheses of the item. No
cartesianness is required for that comparison; it is used by the invertibility theorem.
On the standard cartesian square the dependency β is recovered exactly, and on any
chosen cartesian square the same module exchange and adjunctions define β directly.

For the first clause, the κ-transport in `chosenSquareEtaleLowerShriekBaseChangeMap`
and its new equality to the mate now make the meaning of β explicit. The open and étale
functors are definitionally the common Kan-extension/sheafification functors in these
recorded declarations; κ is sheafification of the identity on the common presheaf model.
The displayed equality in the main theorem therefore uses that shared object model,
with the comparison declaration retaining the canonical identification. The second and
third clauses still give the unit transpose and normalized restriction of the same b.
The identity square, empty open, zero module and zero ring introduce no exceptional
choice or missing inverse in the new construction: inverse conjugation exists without
invertibility, and the actual inverses are only taken under the cartesian hypothesis.

Additional source checks: read the full defining formula and docstring of the live
`etaleLowerShriekBaseChangeMap` with `scompile.py --source`, the upstream definitions
of `baseChangeMap`, `squareUpperStarIso`, `etaleLowerShriekUpperStarAdjunction`, and
`openImmersionLowerShriekBaseChangeMap`, and the recorded κ unit/counit agreement.
Read Stacks `etale-cohomology.tex`, `lemma-shriek-base-change` and `lemma-jshriek-open`.
An `rg` search for `chosenSquareEtaleLowerShriekBaseChangeMate` and
`chosenSquareEtaleLowerShriekBaseChangeMap` in the permitted project and upstream
sources found no existing chosen-square interface with these declarations.

## Second reading by Q20 (repair)

I compared the current node and saved packet with the repaired file. All non-lean node
fields match current main, and the principal theorem signature is unchanged. The finite
commutative ring is `Λ` with `[CommRing Λ] [Finite Λ]`; the four schemes and four arrows
are the bound `U', U, X', X, gU, j', j, g`; `sqdata : OpenImmersionSquare` provides both
open immersions and the chosen cartesian comparison; and `F` is a ModuleCat-valued sheaf
on `U.smallEtaleTopology`. Its first conjunct gives b equal to inverse β, interpreted
through κ; the second gives exactly the pulled-back-unit/square-isomorphism transpose;
the third gives the identity after restriction and cancellation of both extension units.
The actual H3/H4 mismatch was the absent connection to the dependency mate. The new
canonical inverse-conjugate definition, pullback specialization equality and κ comparison
equality supply that connection explicitly. Each helper is listed in lean.declarations,
uses the owning node's blueprint tag and has the appropriate source and proof docstring.
No natural statement correction, new DAG notion or dependency replacement is needed.

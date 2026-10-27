## Worker report

The module `Sheaf.AlgebraicGeometry.PointExceptionalIsomorphismNeighbourhood` states
`AlgebraicGeometry.Scheme.point_exceptional_isomorphism_neighbourhood`, with its single
proof left `sorry`. It introduces no definitions. The node is unchanged outside `lean`.

Source read: `literature/stacks-project/resolve.tex`, Tag 0C5R,
`lemma-proper-birational-regular-surfaces`, particularly lines 4929–4964: the
nonconstant exceptional-fibre map, generic isomorphism, conormal comparison,
unramifiedness, quasi-finiteness, and the maximal isomorphism neighbourhood.
Also read the current blueprint under `literature/blueprint/latest/`, unit
`sk-thm-sf-ctf-stability` and `sk-thm-sf-ctf-stability-direct-images.proof.md`.
The item is an auxiliary surface-geometric input, rather than the unit statement.
Its seven inherited proof steps are included in the declaration docstring, with
all cited nodes named and the common-field and generic-local-ring checks retained.

Hypothesis and clause correspondence:

- The two schemes are `(T S : Scheme.{u})`; integrality is `[IsIntegral T]` and
  `[IsIntegral S]`.
- Regularity is `(hT : IsRegularScheme T)` and `(hS : IsRegularScheme S)`. This
  recorded definition includes local Noetherianity and stalkwise regularity.
- Noetherianity is `[IsNoetherian T] [IsNoetherian S]`, Mathlib's locally
  Noetherian plus compact scheme class, exactly the stated quasi-compact convention.
- Global dimension two is `hdimT : topologicalKrullDim T = 2` and its S counterpart.
- The closed points are `(t : T) (s : S)` with `ht : IsClosed ({t} : Set T)` and
  `hs : IsClosed ({s} : Set S)`.
- Only the target point has the additional local dimension hypothesis:
  `hdims : ringKrullDim (S.presheaf.stalk s) = 2`.
- The centres are the actual reduced closed-point ideals
  `IdealSheafData.vanishingIdeal ⟨{t}, ht⟩` and its s counterpart.
  Mathlib documents that the quotient of `vanishingIdeal` is the reduced induced
  scheme structure. Their `.blowup` and `.blowupMap` are the published glued
  blowups and their canonical structure maps. There are no arbitrary replacement
  schemes, centres, maps, or chosen isomorphisms to substitute for these objects.
- E and F are `.blowupMap.fiber t` and `.blowupMap.fiber s`. Their canonical closed
  immersions are `.blowupMap.fiberι t` and `.blowupMap.fiberι s`. The fact that these
  are closed immersions follows from the closed-point hypotheses and is not an
  extra hypothesis on the data.
- The ambient morphism `h` has exactly these two blowups as source and target;
  `[IsProper h]` gives properness.
- `hbirational` explicitly supplies opens V and U, density in their respective
  blowups, and an isomorphism `e : V.toScheme ≅ U.toScheme` satisfying
  `V.ι ≫ h = e.hom ≫ U.ι`. It is birationality of the given h, not merely the
  existence of an unrelated partial isomorphism between its source and target.
- `v` is a morphism of the two actual exceptional fibres. `hcomm` is the stated
  commuting square, in Lean's left-to-right composition order.
- `himage : ∃ e₁ e₂, v e₁ ≠ v e₂` says exactly that the topological image of v
  contains more than one point; the quantifiers range over points of E.
- The first conclusion gives `N` in the opens of the target blowup, the containment
  `Set.range (b.fiberι s) ⊆ N`, and `IsIso (h ∣_ N)`. Mathlib's `morphismRestrict`
  has source `(h ⁻¹ᵁ N).toScheme` and target `N.toScheme`, as required.
- The second conclusion is `IsIso v`.
- The last conclusion is the equality
  `h ⁻¹' Set.range (b.fiberι s) = Set.range (a.fiberι t)`, an equality of subsets
  of the actual source blowup. It does not assert a stronger scheme-theoretic
  equality of closed subschemes.

Recorded statement dependencies used (signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`;
  its body is `IsLocallyNoetherian X ∧ IsRegular X`, using the stalk class in
  `WeilConjectures.AlgebraicGeometry.Regular`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`
  and `AlgebraicGeometry.IsNoetherian`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  used through the standard scheme opens and their inclusions.
- `WeilConjectures.Blowup.Gluing`:
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and `.blowupMap`.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber` and
  `.fiberι`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion`, the standard property of the canonical
  closed-point fibre inclusions, rather than a new predicate.

Additional existing constructions are Mathlib's
`Scheme.IdealSheafData.vanishingIdeal` (IdealSheaf/Basic.lean:561–565) and
`AlgebraicGeometry.morphismRestrict` (Restrict.lean:568–573). All statement
imports are public. All already recorded proof modules are plain imports;
Mathlib's `ZariskisMainTheorem` supplies the closed-immersion/proper input.
The proof dependencies `lem-sfb-conormal-surjection-unramified`,
`lem-sfb-point-blowup-exceptional-conormal`, and
`lem-sfb-projective-line-twist-rigidity` currently have no recorded Lean module,
so there is no module to import for them. They are retained unchanged in the DAG
and named in the proof plan. Their statements are not required to type this item.

Edge cases checked before writing:

- Empty schemes are excluded by integrality and by the supplied points, just as
  in the node; no additional nonemptiness assumptions are introduced.
- A dimension-one local source centre is not silently excluded. The theorem has
  no local-dimension-two hypothesis at t. In this case the nonconstant-image
  condition cannot hold, as the node's proof and source explain.
- A constant map v, an empty exceptional fibre, or a one-point image does not
  satisfy `himage`; two distinct points in the domain with equal images do not
  satisfy it either.
- There is no restriction on characteristic, excellence, algebraic closure, or
  equality of the two residue fields; in particular h and v are absolute scheme
  morphisms. These are essential to the node's stronger generality over a
  single fixed field.
- For identical blowups and identity h and v, the conclusions read as the
  identity isomorphism over the full open and the reflexive subset equality.
- Universes are explicitly bound by `universe u`, and `autoImplicit false` is
  set. There are no test schemes or coefficient types in a smaller independent
  universe, no file-local notation, and no let-bound terms in the signature.

Searches actually run:

- `msearch.py ... leanfinder "proper birational map between blowups of regular
  surfaces is an isomorphism near an exceptional fibre if its image has more
  than one point"`: eight hits, including `IsLocalIso`, properness of an
  isomorphism, normalization and stalkwise isomorphism criteria; none states
  this exceptional-fibre theorem.
- `msearch.py ... leansearch "proper birational morphism of blowups of regular
  surfaces is an isomorphism near a noncontracted exceptional curve"`: eight
  proper-morphism definition and elementary properness results; no match.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.Hom.fiber, IsIso"`: zero hits;
  service reported unknown identifier `IsIso`. This search supplied no evidence
  of an existing exact match.
- `msearch.py ... grep "exceptional|birational.*blowup|blowup.*birational"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` in project `lean/WeilConjectures`, `lean/Sheaf`, and the upstream-name
  index for blowup/point/exceptional/birational terms found the existing
  global blowup construction, `SurfacePointBlowupData`, regular point-blowup
  geometry, point blowdown factorization, and proper birational surface
  factorization; none states this item. The parent factorization only refers
  to this item's name in its proof plan. The exact item-id grep in
  `lean/WeilConjectures` returned no hits.
- Read Mathlib's fibre, vanishing ideal, restriction, integral, Noetherian,
  proper, immersion, and Krull-dimension declarations directly, and the recorded
  scheme-regularity and blowup declarations. The surface-data module's
  `pointIdeal` is just the same vanishing-ideal expression; no second definition
  of that notion is introduced here.

No statement correction, missing notion, dependency-interface repair, or
STATEMENT-DISPUTED issue was needed. The prescribed scompile.py compiled the
module in sandbox and library mode cleanly (2.3 s and 6.0 s respectively).

## Second reading by NM

Author's second pass, not a claim of independent review: re-read the item and
the complete delivered signature after compilation. The independent delivery
review belongs to the maintainer, as specified by the dispatcher brief.
The signature has both global dimensions but only the stated target local
dimension; retains the actual reduced centres and scheme-theoretic fibres;
uses dense opens compatible with h; tests distinct image points rather than
merely distinct domain points; and contains each of the three conclusions.
The preimage equality is topological, and the isomorphism over N uses the full
inverse image of N. No mismatch was found and no statement field was changed.

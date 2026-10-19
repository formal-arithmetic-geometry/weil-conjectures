## Worker report

The repaired module `Sheaf.TraceFormula.SmoothGeometricStalkAlgebra` states
`AlgebraicGeometry.smooth_geometric_stalk_algebra`.  It also supplies the canonical
interfaces needed by the statement: `strictHenselizationLocalRing` chooses the local
structure supplied by `strictHenselizationLocalStructure`,
`strictHenselizationRingMap` transports `Scheme.strictHenselizationMap` through the
`ΓSpecIso` identifications, `strictHenselizationRingMapAlong` transports that map along
`hv`, and `strictHenselizationAffineCoordinate` evaluates the relative affine-space
coordinates in the strict stalk.

The module also defines `strictHenselizationClosedFiberEquiv` and `strictHenselizationAffineClosedFiberEquiv`, canonical `RingEquiv` constructions by ideal equality; the theorem exposes these equivalences through `Nonempty (RingEquiv ...)` conclusions for the ordinary and affine closed fibres.

The theorem renders the hypotheses as a smooth map `f`, local-Noetherian instances for
`S` and `V`, an algebraically closed geometric field `Ω`, compatible points `s`, `v`, and
`hv`.  Its `let` binders set `A` and `B` to the strict henselization rings, install the
canonical local-ring structures, set `φ` to `strictHenselizationRingMapAlong f s v hv`,
and set `mA,mB` to `IsLocalRing.maximalIdeal`.  The first conjunction renders, in order,
Noetherianity of `A` and `B`, their local-ring structures, maximality of `mA,mB`,
flatness and locality of `φ`, and regularity of `B ⧸ Ideal.map φ mA`.  For each
`I ≤ mA`, the displayed `Ideal.quotientMap` is the induced map `A/I → B/(IB)`; the
conjunction states its flatness, locality, and the closed-fibre equivalence
`B/(IB + mA B) ≃ B/mA B`.

The affine clause quantifies `r`, an isomorphism
`e : V ≅ 𝔸(ULift (Fin r); S)`, its over-`S` equation, a finite coordinate subset `K`,
the condition that its selected canonical coordinates lie in `mB`, and `I ≤ mA`.
The coordinate terms are exactly
`strictHenselizationAffineCoordinate v r e i`, i.e. the images of
`AffineSpace.coord S i` under Γ of the structural map followed by `e.hom`.  The clauses
state Noetherianity and locality of `B/(IB+J_K)`, flatness of its displayed canonical
quotient map from `A/I`, regularity of the closed fibre
`B/(mA B+J_K)`, and
`ringKrullDim (B/mA B) = ringKrullDim (B/(mA B+J_K)) + K.card`.

Dependency declarations used are `Smooth` from
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `IsLocallyNoetherian` from
`Mathlib.AlgebraicGeometry.Noetherian`, `RingHom.Flat` from
`Mathlib.RingTheory.RingHom.Flat`, `IsRegularRing` from
`Mathlib.RingTheory.RegularLocalRing.Defs`, `ringKrullDim` from
`Mathlib.RingTheory.KrullDimension.Basic`, and the project's strict henselization
construction and functorial map from `Sheaf.AlgebraicGeometry.StrictHenselization`,
`Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`,
`Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`, and
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`.

Edge cases checked were `I = ⊥`, `I = mA`, `K = ∅`, `K` the full finite index set,
`r = 0`, and coordinates that already vanish in `mB`.  The quotient ideals are written
with `Ideal.map` and `Ideal.span`, so the empty-set cases reduce to the expected bottom
ideal without an extra nonzero-ring assumption.  The dimension formula uses the closed
fibre `B/mA B`, as required by the returned review.

Searches made: `msearch.py leanfinder` for “ring map induced by strictHenselizationMap”
(found no relevant declaration); `msearch.py grep` for `strictHenselization.*Ring`
(found no existing ring-map helper); `rg` over `WeilConjectures/` and `lean/Sheaf/` for
strict-henselization maps, structural maps, maximal ideals, affine coordinates, and
quotient maps (found the canonical scheme map, `ΓSpecIso`, the local-structure theorem,
and `AffineSpace.coord`, but no combined theorem); and `rg` over DAG nodes for existing
copies of this item (only the log-smooth citer).

The previous returned defects are repaired: `φ` is no longer a bare arbitrary map but is
transported from `strictHenselizationMap f v` along `hv`; `mA,mB` are the canonical
maximal ideals; the affine family is induced by `e` and `AffineSpace.coord`; the
closed-fibre dimension is taken over `mA B`; the coordinate regularity clause concerns
`B/(mA B+J_K)`; the affine conclusion additionally contains the canonical quotient RingEquiv identifying the quotient closed fibre with `B/(mA B+J_K)`, while the ordinary clause contains the analogous canonical RingEquiv to `B/mA B`; the quotient map is the explicit `Ideal.quotientMap`; and the affine
quotient includes its `IsLocalRing` clause.  The theorem docstring now has eight numbered
proof steps.  The second reading below records every conclusion clause explicitly.

## Second reading by Q69

I reread the repaired node and module independently.  The smooth and locally Noetherian
hypotheses match the node.  The compatible geometric points and equality `hv` are
explicit.  The ring terms are `Scheme.strictHenselizationRing s` and
`Scheme.strictHenselizationRing v`; the local instances and maximal ideals are the
canonical ones supplied by `strictHenselizationLocalRing`.  The map is the transported
canonical map, so its direction is `A → B`.  The first conjunction matches, clause by
clause, Noetherianity, locality, maximal ideals, flatness, locality, and regularity of
`B/(mA B)`.  The ideal clause uses the induced quotient map, states flatness and
locality, and identifies the fibre with `B/(IB+mA B)` and `B/mA B`.  The affine clause
contains an explicit over-`S` isomorphism, canonical coordinate images, the selected
maximal-ideal hypothesis, Noetherianity and locality of the coordinate quotient, the
canonical quotient-map flatness, regularity of the correct closed fibre, and the corrected
dimension equation.  Empty `K`, full `K`, and `r = 0` remain admitted.  No bare `φ`,
`mA`, `mB`, or arbitrary coordinate family remains.

The citer `lem-trf-log-smooth-log-regular` was audited after the repair.  Its recorded
use relied on the old arbitrary-map interface and therefore does not hold unchanged;
it is named here and was not edited, as required by the return instructions.

## Statement corrected

The old statement left the strict-local map, maximal ideals, and affine coordinates as
bare data, and it used the wrong quotient in the dimension and regularity clauses.  The
source places are Stacks Tags 01VF, 01VB, 05WS, 06LN, 06LK, and 00OR.  The repaired
statement uses the canonical map induced by `strictHenselizationMap f v` transported
along `hv`, `IsLocalRing.maximalIdeal` for both rings, an over-`S` affine-space
identification and its coordinate images, the correct fibre quotient, and the corrected
dimension formula.  Citer `lem-trf-log-smooth-log-regular` holds:false: its recorded
interface consumes the withdrawn arbitrary-map/arbitrary-coordinate statement and must
be repaired by its owner.

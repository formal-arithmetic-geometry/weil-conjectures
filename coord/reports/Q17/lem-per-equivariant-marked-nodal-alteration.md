## Worker report

The module `Sheaf.AlgebraicGeometry.EquivariantMarkedNodalAlteration` states
`AlgebraicGeometry.exists_equivariantMarkedNodalAlteration`, with its sole proof `sorry`.
There are no new definitions or postponed helper theorems. The docstring reproduces all
sixteen natural-language proof steps, including their dependency names. The node's
statement, source, proof and proof_deps are unchanged. Two already-landed definition
nodes are added to stmt_deps: `def-per-admissible-finite-scheme-quotient` and
`def-trf-nodal-geometric-fibres`. No new node or dependency repair is needed.

Source read: the local ILO PDF, PDF pages 137--139 = printed pp. 131--133,
IX Theorem 1.2 (i)--(vi), the definition of a nodal curve immediately below it,
and IX 1.3--1.4 (the affine excellent case and admissible quotients).

Hypothesis and clause correspondence:

| Node phrase | Lean rendering |
| --- | --- |
| Y affine integral excellent Noetherian | `[IsAffine Y] [IsIntegral Y] [IsNoetherian Y]`, `hY : ∀ U : Y.affineOpens, IsExcellent Γ(Y,U)` |
| P integral excellent | `[IsIntegral P]`, `hP` on every affine open; no extra Noetherian hypothesis on P |
| f proper dominant | `(f : P ⟶ Y) [IsProper f] [IsDominant f]` |
| generic fibre | `η : Y`, `hη : IsGenericPoint η Set.univ`, and the canonical `f.fiberToSpecResidueField η` |
| smooth geometrically integral curve | `Smooth`, `GeometricallyIntegral` on that canonical fibre map and `hdim : topologicalKrullDim (f.fiber η) = 1` |
| E effective Cartier divisor | `E : P.IdealSheafData`, `hE : E.IsInvertible` |
| E generic fibre finite étale, possibly empty | `IsFinite` and `Etale` on `(E.subschemeι ≫ f).fiberToSpecResidueField η`; no nonemptiness assumed |
| finite group G | existential `G : Type u`, `Group G`, `Finite G` |
| integral excellent separated Noetherian C,Y' | existential schemes with `IsIntegral`, `IsNoetherian`, `C.IsSeparated`, `Y'.IsSeparated`, and excellence of every affine coordinate ring |
| commutative square | `a ≫ f = f' ≫ b` |
| a,b projective alterations | `IsHProjective`, `IsProper`, `Surjective`, and `IsFinite` over a dense target open, separately for a and b |
| a,b generically étale | `Etale (a ∣_ U)` and `Etale (b ∣_ U)` on those dense opens; intersecting two dense opens in each integral target gives the equivalent common-open form |
| actions, trivial on P,Y | monoid homomorphisms `aC : G →* Aut C`, `aY' : G →* Aut Y'`, with `(aC g).hom ≫ a = a` and `(aY' g).hom ≫ b = b` |
| f' equivariant | `(aC g).hom ≫ f' = f' ≫ (aY' g).hom` for every g |
| f' projective flat finitely presented | `IsHProjective f'`, `Flat f'`, existential `hfp : LocallyOfFinitePresentation f'`; quasi-compactness and quasi-separatedness follow from H-projectivity/properness |
| T' stable nowhere dense closed | `T' : Set Y'`, `hT' : IsClosed T'`, `IsNowhereDense T'`, and stability under each `(aY' g).hom` |
| D stable effective Cartier divisor | `D : C.IdealSheafData`, `D.IsInvertible`, `D.comap (aC g).hom = D` for every g |
| every geometric fibre nonempty connected curve, only ordinary double points | the landed `@HasNodalGeometricFibres _ _ f' hfp`; its definition quantifies over algebraically closed geometric points, uses `ConnectedSpace` (including nonempty), dimension one, and the actual fibre stalk completed at its maximal ideal isomorphic to `Ω[[u,v]]/(uv)` at every nonsmooth point |
| smooth off T' | `Smooth (f' ∣_ ⟨T'ᶜ, hT'.isOpen_compl⟩)` |
| D finite étale over Y' | `IsFinite (D.subschemeι ≫ f')`, `Etale (D.subschemeι ≫ f')` |
| D in smooth locus | `∀ c, c ∈ D.support → c ∈ f'.smoothLocus` |
| inverse-image boundary containment | `a ⁻¹' (E.support : Set P) ⊆ (D.support : Set C) ∪ f' ⁻¹' T'` |
| free action on Y' minus T' | for every algebraically closed Ω and morphism x from Spec Ω into that actual complement open, equality of x with its g-translate implies `g = 1` |
| admissible actions, finite scheme quotients | `IsAdmissibleFiniteSchemeQuotient aC qC` and `IsAdmissibleFiniteSchemeQuotient aY' qY'`; this reuses exactly the affine-orbit condition, finite invariant map, quotient topology, orbit fibres and invariant-sections sheaf |
| Q=C/G and B=Y'/G integral excellent Noetherian | existential Q,B and qC,qY', the quotient predicates, `IsIntegral`, `IsNoetherian`, and excellence on every affine coordinate ring |
| the induced quotient morphisms to P,Y | existential α,β tied to the original arrows by `qC ≫ α = a` and `qY' ≫ β = b` |
| those morphisms proper birational | `IsProper α`, `IsProper β`, dense target opens U on which `IsIso (α ∣_ U)` and `IsIso (β ∣_ U)`; these are isomorphisms from the full inverse-image open, and the source opens are dense since the sources are integral and these maps are surjective |
| generic fibre of f' smooth geometrically integral | existential generic point η' with `Smooth` and `GeometricallyIntegral` of `f'.fiberToSpecResidueField η'` |

Dependency declarations used/read (full signatures and docstrings were checked in their
recorded source modules, with the current Projective module read using `scompile.py --source`):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`.
- `def-pc-reduced-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsReduced`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `def-exc-excellent-ring`: `Sheaf.RingTheory.ExcellentRing`, `IsExcellent`.
- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`.
- `def-trf-strict-normal-crossings-boundary`: `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`, `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
- `def-per-prime-to-ell-alteration-topology`: `Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology`, `AlgebraicGeometry.PrimeToEllAlteration.topology`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, `AlgebraicGeometry.IsHProjective`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`.
- `def-sbc-locally-finite-presentation`: `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`, `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
- `def-weil-geometric-fibre`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`.
- `def-nagata-effective-cartier-ideal`: `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible`, `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible`.
- `def-pc-geometrically-irreducible`: `Mathlib.AlgebraicGeometry.Geometrically.Integral`, `AlgebraicGeometry.GeometricallyIntegral`.
- `def-per-admissible-finite-scheme-quotient`: `Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient`, `AlgebraicGeometry.IsAdmissibleFiniteSchemeQuotient`.
- `def-trf-nodal-geometric-fibres`: `Sheaf.AlgebraicGeometry.NodalGeometricFibres`, `AlgebraicGeometry.HasNodalGeometricFibres`.

The existing normal-crossing boundary and prime-to-ell topology declarations are imported
because they remain recorded convention dependencies, but no regularity, normal-crossing
hypothesis or prime-to-ell degree condition is imposed by this theorem. All recorded
proof-dependency modules available at writing time are private imports unless already
publicly imported for statements; the finite/quasi-finite criterion uses Mathlib's
`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`.

Edge cases checked before writing:

- Empty E and D: the unit ideal is Cartier, its closed subscheme is empty, its generic
  fibre is finite étale, and the smooth-locus and containment conditions allow it.
- Empty T': the complement is all Y', smoothness is global and freeness has its expected
  global meaning. No artificial nonempty bad set is required.
- Empty P or Y: excluded by the node's integrality; geometric fibres of the output are
  nonempty because `ConnectedSpace` contains nonemptiness.
- Trivial group: allowed by `Group` and `Finite`; freeness is satisfied. Nontrivial Galois
  actions on spectra of fields are correctly allowed: geometric, not topological, points
  are used in the free-action condition.
- Reducible nodal special fibres: allowed; only geometric connectedness, dimension one
  and the completed node condition are imposed, not geometric integrality of every fibre.
- Positive characteristic and wild finite groups: no characteristic or group-order
  restriction is imposed. Generic etaleness means separable generic alterations.
- No properness/projectivity hypothesis on the marking beyond its actual Cartier
  inclusion and the specified finite étale generic fibre is added.
- All schemes and geometric test fields are in universe u, as in the existing geometric
  morphism properties; the existential finite group can be realized in any u. There are
  no auto-bound variables, file-local notation, private definitions, or let-bindings in
  the statement.

Searches made for an existing statement:

- msearch LeanFinder: "Galois equivariant marked nodal alteration of a proper relative
  curve with birational scheme quotients" returned eight rational-map and normalization
  declarations; none is this theorem.
- msearch Loogle: "AlgebraicGeometry.Scheme, AlgebraicGeometry.IsHProjective" returned
  zero hits (the upstream-only H-projective identifier is unknown to the Mathlib service).
- msearch grep in Mathlib/AlgebraicGeometry:
  `equivariant.*nodal|marked.*alteration|AdmissibleFiniteSchemeQuotient` returned zero hits.
- msearch LeanSearch: "equivariant marked nodal alteration finite group birational
  quotient" returned orbit quotient and rational-map declarations, no matching theorem.
- rg in upstream WeilConjectures and side lean/Sheaf for
  `equivariant.*nodal|marked.*alteration|lem-per-equivariant-marked-nodal-alteration`
  found related semistable/reduction theorems and this item's mention in a consumer, no
  existing declaration of this theorem. The literal node-id search in upstream had no hit.
- Targeted side/DAG searches found the already-landed finite scheme quotient and nodal
  fibre definitions and reused them rather than creating another notion.
- The exact new declaration name has no prior occurrence in dag/lean_names_upstream.json,
  Mathlib, upstream or side Lean.

No STATEMENT-DISPUTED flag or source correction is needed. The finite scheme quotient
predicate spells out properties of the actual quotient whose existence the source asserts;
it does not substitute an arbitrary map or an abstract quotient of points.

Validation: prescribed scompile.py, both sandbox and destination-library-name checks,
clean (3.1 s and 2.7 s before the final proof-only Mathlib import). The initial compile
found dot notation on a constructed complement open, repaired with explicit
`Scheme.Opens.toScheme` and `Scheme.Opens.ι`; no mathematical clause changed.

## Second reading by Q17

This is the single dispatched worker's second pass, not a separate agent review; the
brief forbids starting other agents, and the maintainer independently reviews delivery.
I reopened the node, source IX 1.2/1.4 and the final signature and compared every row
above. In particular I checked that the same a,b,f',G occur in all clauses; both original
arrows are invariant; the family action is equivariant; the Cartier ideal is preserved
as a closed subscheme, not merely on support; T' is stable; and the quotient maps α,β
are tied to a,b. Both quotient scheme predicates contain invariant sections as well as
orbit topology and affine-orbit admissibility. The nodal definition does include
nonemptiness and connectedness, and the output generic fibre is geometrically integral.
Birationality uses actual dense-open isomorphisms, with no normality assumption. All
finite-presentation, generic-etale and smooth-locus clauses are present. The open-complement
notation issue was the only compile mismatch and was repaired. No statement mismatch or
silent source correction was found. The two definition-node dependencies are already
landed and are the owning declarations, so there are no new or repaired nodes to review.

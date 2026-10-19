## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeMarkedNodalReduction` states
`AlgebraicGeometry.exists_relativeMarkedNodalReduction`, with its proof `sorry`.
Its docstring gives all four DAG proof steps and their dependencies. The node's
statement, proof and proof dependencies are unchanged. The landed nodal-fibre definition is imported unchanged. One new existing-declaration
record supplies the general Cartier notion; it needs no new module. All introduced universes and variables are explicit (`autoImplicit false`).

Clause-by-clause correspondence:

- Proper dominant `f : X ⟶ Y`: `[IsProper f] [IsDominant f]`.
- Integral Noetherian schemes: `[IsIntegral X] [IsIntegral Y] [IsNoetherian X]
  [IsNoetherian Y]`. Excellence is `hX` and `hY`, saying `IsExcellent Γ(X,U)`
  or `IsExcellent Γ(Y,U)` for every affine open. These use the recorded ring
  definition directly, without introducing a competing scheme predicate.
- Projectivity over the spectrum of a Noetherian ring: `R : Type u`,
  `[CommRing R] [IsNoetherianRing R]`, `p : Y ⟶ Spec (.of R)`,
  `[IsHProjective p]`. The morphism is supplied explicitly because its
  projectivity is part of the hypothesis and is used in the proof's composition.
- Generic point: `y : Y` and `hy : IsGenericPoint y Set.univ`.
- Smooth irreducible one-dimensional generic fibre:
  `[Smooth (f.fiberToSpecResidueField y)]`, `[IrreducibleSpace (f.fiber y)]`,
  and `hdim : topologicalKrullDim (f.fiber y) = 1`.
- Nowhere dense closed boundary: `Z : Scheme`, `j : Z ⟶ X`,
  `[IsClosedImmersion j]`, `hZ : IsNowhereDense (Set.range j)`.
  The generic marking hypothesis is `[Etale ((j ≫ f).fiberToSpecResidueField y)]`.
  Thus this is the fibre of the given boundary over Y, without replacing Z by its
  support or imposing reducedness separately.
- The output square quantifies `X',Y',a,b,f'` and states `a ≫ f = f' ≫ b`.
- The two alterations have `IsProper` and `IsDominant`, and each has an open
  dense target subset `U` on which its target restriction is `IsFinite`.
  This renders the node's definition of generically finite literally; there is
  no bound, separability condition or invertibility condition on either degree.
- The base alteration has `IsHProjective b`. No projectivity of a is asserted.
- Excellent integral sources: `IsIntegral X' ∧ IsIntegral Y'` and the two
  all-affine `IsExcellent` clauses, exactly as for the input schemes.
- Projective flat finitely presented family: `IsHProjective f' ∧ Flat f'` and
  the witness `hfp : LocallyOfFinitePresentation f'` in the following existential. H-projectivity implies properness, hence
  quasi-compactness and quasi-separatedness, so the last conjunct means finite
  presentation here, including the global conditions. It is not merely a
  locally finitely presented substitute on an arbitrary non-quasi-compact map.
- Every geometric fibre: `(∃ hfp : LocallyOfFinitePresentation f',
  @HasNodalGeometricFibres _ _ f' hfp)`. This uses exactly the landed
  `AlgebraicGeometry.HasNodalGeometricFibres`, from
  `Sheaf.AlgebraicGeometry.NodalGeometricFibres` (node
  `def-trf-nodal-geometric-fibres`, group Q119). The existential supplies the
  already required finite-presentation hypothesis to its typeclass parameter;
  it adds no condition. The definition tests every algebraically closed field
  in the scheme universe and actual scheme pullbacks, requires nonempty
  connected fibres of dimension one, and gives the completed-ring equation
  `Ω[[u,v]]/(uv)` at every nonsmooth point. In this finite-type nodal setting,
  connectedness and dimension one imply pure dimension one: a zero-dimensional
  irreducible component would be an isolated open-and-closed component, contrary
  to connectedness. A point with that completed ring is closed with residue
  field Ω (its residue field is ring-isomorphic to Ω and the finite-type
  Ω-algebra residue field therefore has transcendence degree zero). Thus the
  definition gives exactly the ordinary-double-point condition in this item.
- Exceptional set: `T : Set Y'`, `hT : IsClosed T`, `IsNowhereDense T`.
- Cartier divisor: `D : Scheme`, `i : D ⟶ X'`, `IsEffectiveCartierCenter i`.
  This existing predicate forces a closed immersion and an invertible defining
  ideal, equivalently a local equation that is a non-zero-divisor.
- Smooth off T: `Smooth (f' ∣_ ⟨Tᶜ, hT.isOpen_compl⟩)`.
- Finite étale marking: `IsFinite (i ≫ f') ∧ Etale (i ≫ f')`.
- Relative smooth locus: for every `d : D`, `(f'.stalkMap (i d)).hom.FormallySmooth`.
  With the asserted local finite presentation this is precisely membership of
  `f'.smoothLocus` (Mathlib Smooth.lean:305--310), not formal smoothness used
  in place of a missing finite-presentation hypothesis.
- Boundary containment: `a ⁻¹' Set.range j ⊆ Set.range i ∪ f' ⁻¹' T`.
- Generic fibre conclusion: there exists `y'` with `IsGenericPoint y' Set.univ`,
  `Smooth (f'.fiberToSpecResidueField y')` and
  `GeometricallyIntegral (f'.fiberToSpecResidueField y')`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`
  (separated, universally closed, locally finite type).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`
  (nonempty and domain section rings).
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, and its quasi-excellent and
  universally catenary constituents, read in full.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`:
  `AlgebraicGeometry.IsHProjective`, read with `scompile.py --source`, since the
  older read-only upstream checkout lacks this module. Its finite coordinate
  embedding matches the DAG convention, including the empty-source convention.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` (the dependency's Mathlib match).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`,
  and the stalkwise smooth-locus criterion.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`,
  `fiberToSpecResidueField`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`,
  using the geometrically integral match recorded by def-pc-geometrically-irreducible.
  The irreducible, reduced and connected variants of that match were also read.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Sheaf.AlgebraicGeometry.NodalGeometricFibres`:
  `AlgebraicGeometry.HasNodalGeometricFibres` (the landed Q119 declaration).
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier`:
  `IsEffectiveCartierCenter`, reused through the new existing-declaration node.
- The nodal definition uses the existing `AdicCompletion`, `MvPowerSeries`,
  `Scheme.residueField`, `ConnectedSpace`, `IsAlgClosed` and actual pullbacks.

The already stated proof dependencies are imported without `public`:
`WeilConjectures.AlgebraicGeometry.Ample`,
`WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible`,
`Sheaf.AlgebraicGeometry.UnramifiedQuasiFinite`, and
`Mathlib.AlgebraicGeometry.ZariskisMainTheorem`. The first ample theorem's live
source was read through `scompile.py --source`. The semistable theorem,
projective-bundle definition, and two projectivity conversion lemmas have no
recorded Lean declarations yet, so no fictitious module imports are added for them.

Edge cases checked before writing: an integral scheme cannot be empty; connected
geometric fibres are nonempty even though pure dimension alone permits an empty
scheme. Empty Z and empty D are allowed. Empty T is allowed. Arbitrary positive
characteristic is allowed, including characteristic two in the nodal equation uv.
The generic fibre is irreducible initially, without a geometric-integrality
hypothesis; geometric integrality occurs only in the output. The two alteration
degrees are unrestricted. All scheme and test-field universes use the same u,
matching Mathlib's geometric-property convention and admitting algebraic closures
of each residue field; there is no independent smaller test-field universe.

Searches: `msearch.py` LeanFinder query "A relative curve admits a marked nodal
reduction by alterations with a finite etale Cartier divisor" returned ordinary
smoothness and Weierstrass-reduction results, no match. Loogle query
"AlgebraicGeometry.Smooth, AlgebraicGeometry.IsProper" returned zero hits.
Mathlib grep `Nodal|GenericallyFinite|EffectiveCartier` returned zero geometric
hits. LeanSearch on excellent schemes, generic finiteness and nodal fibres returned
only elementary Noetherian, affine and finite-morphism APIs. Further LeanSearch,
LeanFinder and grep results are recorded in each new node. Upstream and project
`rg` searches found the existing Cartier predicate but no nodal or marked-reduction
statement. Searching the item id in upstream returned no match. DAG/blueprint
searches found assertions about nodal families and a larger semistable-tower
package, but no standalone definition or usable nodal-fibre interface.

The source ILO Exposé IX p. 131 was read from the local PDF using pdftotext,
including all of Theorem 1.2 and its nodal-curve paragraph. Stacks curves.tex
section-nodal and divisors.tex definition-effective-Cartier-divisor and its
characterization lemma were read locally. No statement dispute or correction.

## New nodes

`def-trf-effective-cartier-center` records `existing: true` for the upstream
`AlgebraicGeometry.IsEffectiveCartierCenter`; no module is written and no
construction is duplicated. Its source is Stacks divisors.tex, definition and
characterization of an effective Cartier divisor. The older
`def-sc-effective-cartier-divisor` concerns curves and records Riemann--Roch
lemmas, so it cannot give the required general predicate on X'. The new node
records the exact existing general scheme notion, allowing an empty divisor.

## Repair of returned delivery

The return on immutable head `84bc1f4c9efd` identified the concurrently landed
`def-trf-nodal-geometric-fibres`. The first required dry run confirmed that the
saved packet tried to modify its existing module and dependency record. Removed
both duplicate files from the packet, retained the landed node in the item's
`stmt_deps`, and changed the theorem to the landed declaration with an explicit
finite-presentation witness. Removed the unused direct pure-dimension dependency.
No existing node or module is overwritten, and the item's natural-language
statement and proof are unchanged.

## Second reading by Q116

Self-check by this repair worker, with the item node and theorem open; no second
agent was started. All input hypotheses and all output clauses are matched in
`Worker report` above. Re-read the landed nodal definition: its finite-presentation
parameter is discharged by the existential witness, its connected dimension-one
nodal condition is equivalent to the item's pure curve condition as explained
above, and no new nodal definition remains. Rechecked the existing Cartier
predicate and its new node: it allows the empty effective Cartier divisor and
adds no regularity or curve restriction. The natural statement, alteration
conditions, exceptional set, boundary containment and generic fibre conclusion
are unchanged. The signature in `lean.statement` was regenerated verbatim.

Validation: compile and delivery preflight are rerun for this repaired packet
using only the prescribed wrappers.

## Worker report

`Sheaf.SixFunctors.BoundaryDualityInput` defines
`AlgebraicGeometry.ProEtale.BoundaryDualityInput`, a proposition packaging exactly the two
assertions of `def-weil-boundary-duality-input`. Its natural-language statement is unchanged.
The saved packet and its initial dry run were inspected first. That run timed out in the
main module. Repair retained the coefficient conventions and the canonical formulas, moved
the long composites into generic categorical coordinates, and fixed a malformed morphism
binder. The saved file's unconstrained `thetaModel` and `tensorModel` fields have been removed:
their replacements are explicitly normalized to the actual composition mate and actual
projection/counit paste. No theorem is proved, no definition contains `sorry`, and no new
axiom or unspecified construction is introduced.

### Hypotheses and coefficient categories

- `D : WeilConjectures.FiniteFieldDatum.{u}` is the recorded global finite field and fixed
  algebraic closure; the characteristic prime is `D.p`.
- `l`, `[Fact l.Prime]`, and `_hl : l ≠ D.p` give the coefficient prime and its distinction
  from the characteristic.
- `E`, `[Field E]`, `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]` give exactly
  a finite extension of Q_l. Its coefficient ring is the existing
  `Padic.coefficientExtensionRing l E (n + 1)`, with the existing chosen uniformizer and
  quotient, and its finiteness instance is `sfPositiveCoefficient_finite` from the recorded
  exceptional-inverse-image module. Index `n : ℕ` denotes level `n+1`, including every
  positive level and level one at `n=0`.
- `Y : Scheme.{u}`, `aY : Y ⟶ Spec (CommRingCat.of D.k)`, and the instances
  `[IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]` are the separated finite-type
  k-scheme. Local Noetherianity, compactness and then Noetherianity are derived inside the
  definition; they are not extra input hypotheses.
- `Piece Y` is a scheme, an inclusion into Y, and `IsImmersion` of that inclusion. Thus it
  includes every locally closed subscheme with its actual map, rather than just an open or
  closed subset. `Piece.structureMap` is that inclusion followed by `aY`.
  `Piece.noetherianSpace` is inherited along the inducing immersion. Its structure morphism
  is compactifiable by the existing Nagata construction, using explicit inherited finite
  type, separation and quasi-compactness; this prevents repeated instance-search loops.
- `Boundary Z T` consists of `map : Z.scheme ⟶ T.scheme`, `IsClosedImmersion map`, and
  `over_eq : map ≫ T.inclusion = Z.inclusion`. Consequently all closed immersions between
  the pieces with the specified equality over Y are quantified over.
- `FixedCategory` is `DerivedCategory (Sheaf (ProEt.topology T) C)`, specialized in the main
  definition to `C = ModuleCat.{u+1} (ULift.{u+1,u} A)`. `FixedEtaleCategory` is the same
  fixed-scalar category on the small etale site. The actual intrinsic constant-ring
  category is related by the recorded `sfIntrinsicDerivedEquivalence`. The predicate
  `ctf l E n T K` is literally the dependency's `WeilConjectures.finiteTorConstructible`
  evaluated on the image of K under that equivalence, at level n+1 with its positivity
  witness. Neither constructibility nor finite Tor amplitude is replaced by a new predicate.

### Canonical operations and clause 1

`Operations` permits the formulas to be elaborated over arbitrary monoidal closed categories.
`Data` then existentially binds an operation record on the *fixed actual* site categories,
requires `CanonicalOperations` for it, and requires `Assertions` with the actual ctf
predicate. Every operation field is fixed by a corresponding `HEq` field, which compares both
its type and its value with the existing construction. These fields do not allow an arbitrary
functor, arbitrary pairing, or mere `Nonempty` isomorphism to replace a canonical map.
There is no existential choice used to *define* data here: the main definition is a proposition
and its coordinate equations are part of that proposition.

The coordinate equations specify the following existing operations:

- `nu`, `nuR`, `adj`: `comparisonUpperStar.mapDerivedCategory`,
  `comparisonLowerStar.rightDerivedFunctor`, and `derivedComparisonAdjunction`.
- `star`, `estar`, `estarLeft`, `estarIso`: the actual pro-etale and etale inverse images,
  their termwise derived functors, and `Etale.leftDerivedUpperStarIsoMapDerivedCategory`.
  Thus the pro-etale `star` is precisely `sfFixedDerivedPullback` at the specialized scalar
  category, not a freely chosen inverse image.
- `eexc`: `Etale.rightDerivedUpperShriek`. Therefore `Operations.exceptional`, defined as
  `nuR ⋙ eexc ⋙ nu`, is exactly the composite defining `sfFiniteExceptionalFixed`, with the
  canonical compactification instance. No ambient pro-etale right adjoint is assumed.
- `eOmega`: `Etale.dualizingComplex` at the actual structure map. `Operations.omega` is its
  comparison pullback. The recorded comparison unit at the constant coefficient identifies
  it with `Ra_T! A` in the node's fixed-scalar presentation.
- `symmetry`, `etaleSymmetry`, `evaluation`: the corresponding data of the dependency's
  `AmbientDualityPairing`. That predicate fixes symmetry to descended Koszul symmetry by
  HEq and evaluation to the tensor-Hom adjunct of the identity. `Operations.delta` is the
  transpose of that same evaluation, exactly the normalization of the dependency's
  `AmbientDualityPairing.bidualityMap`.
- `nuTensor`: `genericComparisonTensor`, assembled from the existing
  `leftDerivedTensorComparison` and `leftDerivedFunctorIsoMapDerivedCategory`.
- `square`: `derivedComparisonPullback`, the mapped actual comparison-site square
  `comparisonUpperStarCompUpperStarIso` with the canonical composition identifications.
- `etau`: the existing `Etale.rightDerivedUpperShriekTensorMap`.
- `ecomp`: `etaleOmegaComposition`, obtained by `Adjunction.comp`,
  `Adjunction.rightAdjointUniq` and `Adjunction.ofNatIsoLeft` from `finiteComposition`.
  The latter uses the existing `Etale.unboundedEtaleLowerShriekCompIso` and
  `Etale.unboundedEtaleLowerShriekCongr` with the actual boundary equality over Y. The landed
  unbounded-comparison node states its normalization on D+; its id is added to stmt_deps.

`Operations.dual` is the actual internal-Hom functor into `Operations.omega`.
`Assertions.preserves` is clause 1, separately requiring that it carry every ctf object on
 every locally closed piece into ctf. The extra generic coefficient typeclass parameters of
helpers are instantiated by the actual finite module category inside the main definition;
none becomes an extra hypothesis of `BoundaryDualityInput`.

### Clause 2 and evaluation compatibility

`Operations.rightTensor` is the lax tensor mate of the two comparison counits.
`Operations.tensorModel` explicitly pastes the actual comparison pullback square, monoidal
comparison inverse, etale symmetry, exact/derived inverse-image identification,
`rightDerivedUpperShriekTensorMap`, and the exceptional image of symmetry followed by that
lax mate. `Assertions.tau_normalization` fixes tau to this paste after precomposition with
ordinary inverse image of the comparison counit in its first factor. For a ctf object that
counit is invertible, because constructible objects have etale origin and the comparison
unit is invertible on D+. Thus the equation determines precisely the canonical tensor-
exceptional map in the node; it is not a vacuous equation against another chosen map.

`Assertions.theta_normalization` uses the comparison *unit* and fixes theta to the right-
adjoint mate of compact-support composition at the coefficient object. This is exactly
`Ri! omega_T ≅ omega_Z`, with the orientation in the node.

`Operations.transpose` curries with the specified symmetry to put the internal-Hom argument
in the right tensor factor. `Operations.exchange` is literally that transpose applied to
tau followed by exceptional evaluation and theta. `Assertions.exchange_isIso` is the
assertion that beta_L is invertible for every ctf L and every boundary. Its ctf witness for
D_T L is supplied by the separate preservation field.

`Assertions.alpha` has type `Ri! D_T K ≅ D_Z i* K`. Its `alpha_normalization` is precisely
the transpose of symmetry, tau with first factor K, exceptional pullback of symmetry
followed by evaluation, and theta. It fixes the canonical comparison described by the
closed-costalk dependency, rather than choosing an arbitrary isomorphism of its endpoints.
Finally `Assertions.compatibility` states the node's equality, in Lean's composition order:

`star.map delta_K ≫ beta_(D_T K) = delta_(star K) ≫ (D_Z).map alpha_K.hom.op`.

The source is `i*K` and the target is `D_Z Ri! D_T K`. The double use of preservation supplies
the finite-Tor witness required to form beta at D_T K. This equality is exactly equivalent
to composing with the inverse of D_Z alpha_K as in the blueprint. There is no assertion
that ordinary and exceptional restriction coincide.

### Dependency declarations read and used

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.coefficientExtensionRing`, `Padic.finite_coefficientExtensionRing`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`, through
  `Sheaf.Paper.FiniteTorAmplitude`: `WeilConjectures.finiteTorConstructible`.
- `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`:
  `sfPositiveCoefficient_finite`, `sfFiniteExceptionalFixed`, `sfFixedDerivedPullback`,
  and `sfDerivedComparisonPullbackIso`; and its imported realization interface
  `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport.sfIntrinsicDerivedEquivalence`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the recorded intrinsic finite pullback, tensor,
  Hom, evaluation and transpose, presented here in their canonically equivalent fixed-
  scalar closed category. The ordinary derived Hom/closed and tensor comparison interfaces
  from the upstream pro-etale derived modules are used for the actual formulas.
- `Sheaf.Paper.DualityPairing`: etale and pro-etale `AmbientDualityPairing`, and the
  normalized `bidualityMap` interface.
- `Sheaf.SixFunctors.ClosedCostalkDuality`:
  `AlgebraicGeometry.Scheme.exceptionalRestrictionVerdierDuality` and its etale version;
  the node's stated normalization specifies their canonical alpha on the chosen coordinates.
- `Sheaf.AlgebraicGeometry.EtaleExceptionalAdjoint` and
  `Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons`: the ambient etale adjoint
  and the D+ support comparison; reexported by the imported unbounded-comparison module.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `unboundedEtaleLowerShriekCompIso`, `unboundedEtaleLowerShriekCongr`, and their canonical
  D+ normalization. An audit found no dependency path from this node back to the item.
- Mathlib: `Adjunction.comp`, `Adjunction.rightAdjointUniq`, `IsImmersion`,
  `IsClosedImmersion`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`.

`Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit` was read but cannot additionally be
imported with the general pro-etale derived-comparison module: its finite-coefficient
comparison import duplicates `AlgebraicGeometry.ProEtale.derivedComparisonAdjunctionPlus`.
The actual unit used here is the general `derivedComparisonAdjunction.unit`, which agrees
with that interface on D+. The unit-invertibility theorem is not assumed by a field of this
definition: it justifies why the normalization determines theta and tau in the indicated
bounded-below/constructible cases. Keep the general module, as required for the generic
coefficient formulas, rather than importing both colliding implementations. No dependency
node record is changed.

### Edge cases, searches and validation

Checked the source and the typing for level one (`n=0`), higher quotient levels without
finite-global-dimension assumptions, the zero complex, the empty piece, identity immersions,
and arbitrary closed boundaries between locally closed pieces. No condition removes any
of these cases. No new bounds, field-coefficient assumption, smoothness, regularity, or
identification `i*=Ri!` is inserted.

The saved searches were retained. Current `msearch.py` LeanFinder query "boundary duality
input Verdier duality closed immersion canonical boundary exchange" returned generic
immersion/coborder and chain-boundary lemmas, no matching record. Loogle query
"CategoryTheory.Adjunction.rightAdjointUniq, CategoryTheory.MonoidalClosed" returned zero
hits. Grep query "BoundaryDualityInput|boundaryDuality|boundary.*exchange" in Mathlib
CategoryTheory returned zero hits. `rg` in upstream WeilConjectures and side lean/Sheaf
found no declaration of this input. The upstream Etale.Derived.BoundaryDuality module was
read: it states etale preservation and existence of an exchange isomorphism, explicitly
without constructing the canonical exchange, so it does not define this pro-etale input or
its required compatibility. The saved LeanSearch query returned only generic closed-
immersion results. The main-20261015 blueprint definition and the recorded dependency
signatures/docstrings were read against the final formulas.

All compilations use the prescribed `scompile.py` wrapper with the unchanged 60-second
limit. Diagnostic heartbeat limits were used only in scratch modules, not in the delivered
file. The long generic composites and the inherited compactification instance were checked
separately during repair. The final module is the sole delivered Lean file; its node lists
all 29 helper/main declarations. There are no new nodes, dependency record repairs,
statement corrections, or statement disputes. The required dry run is rerun after these
repairs before pushing.

## Second reading by Q40

Independent maintainer second reading, 2026-10-18, of immutable delivery
`df55ebd91a5bdb58e09a9446ce7fddd5e9443643`. This section replaces the delivery's
placeholder; it does not claim that a Q40 worker performed the reading.

I read the item node, all sixteen statement-dependency nodes and their declaration
records, the blueprint source at order 2129, the complete delivered module, and the
exact dependency constructions used. The module states the intended input.

- The global datum is `FiniteFieldDatum`; `Fact l.Prime` and `_hl` impose the prime
  and characteristic conditions. `Field E`, `Algebra (Padic l) E`, and
  `FiniteDimensional (Padic l) E` give the finite coefficient extension. The existing
  `coefficientExtensionRing` is used at `n+1`, so `n=0` is exactly level one.
- The explicit structure map `aY` has separatedness, local finite type, and
  quasi-compactness. The definition derives Noetherianity; it does not assume an
  additional geometric condition. `Piece` includes every immersion into Y, and
  `Boundary.over_eq` imposes the equality over Y needed for structure-map composition.
  Compactifiability of each piece follows by the existing Nagata construction.
- `FixedCategory` uses the actual small pro-etale topology. The ctf predicate is
  the recorded intrinsic `finiteTorConstructible`, evaluated through the specified
  `sfIntrinsicDerivedEquivalence`. The coefficient ULift provides the site's value
  universe without equating its object and morphism universes.
- `Operations.exceptional` is precisely comparison direct image, the ordinary
  etale exceptional adjoint, and comparison inverse image. Its constituent
  functors are fixed by `CanonicalOperations`. `omega` is the comparison pullback
  of the etale dualizing complex; the bounded-below comparison unit identifies it
  with the exceptional image of the constant coefficient. `dual` is internal Hom
  into that object, and `Assertions.preserves` separately states clause 1.
- `finiteComposition` uses the actual unbounded compact-support composition and
  congruence along `Boundary.over_eq`. Its restriction to D+ is fixed by the
  dependency's `unboundedEtaleCompactSupport_composition_plus`. The composition
  of adjunctions and `rightAdjointUniq` give `etaleOmegaComposition`.
  `theta_normalization` fixes the requested identification with omega_Z, rather
  than allowing an unrelated isomorphism.
- `rightTensor` is the mate of the two comparison counits. `tensorModel` pastes
  the site square, monoidal comparison, etale symmetry, exact/derived pullback
  identification, and the actual `rightDerivedUpperShriekTensorMap`.
  `tau_normalization` determines tau on ctf first factors: these are of etale
  origin and the comparison counit is invertible there. It does not assume that
  the comparison counit is invertible on every pro-etale complex.
- `exchange` transposes exactly tau followed by exceptional evaluation and theta.
  `exchange_isIso` quantifies over every ctf L. `alpha_normalization` has both
  symmetries and the same tau as in the node's expanded pairing. The compatibility
  equation has source i*K and target D_Z Ri! D_T K; functoriality on alpha.hom.op
  has the correct contravariant direction. `delta` is the same evaluation
  transpose as in `AmbientDualityPairing`. No identification i*=Ri! is asserted.

The normalization fields fix data to real existing constructions; the existential
operation record is not an arbitrary map substitute. The extra typeclass binders
of generic helpers are discharged at the concrete ModuleCat specialization and do
not become hypotheses of the main definition. The closed-costalk theorem concerns
arbitrary ringed coefficients and an assumed adjoint; its canonical comparison is
specified here by the item's explicit alpha pairing, not chosen from its bare
Nonempty conclusion.

I checked the empty scheme and empty piece, zero complexes, identity boundaries,
arbitrary locally closed pieces and closed boundaries, level one and higher
non-field quotient rings, and universes u and u+1. No smoothness, properness of Y,
regularity, finite global dimension, or dimension bound has been inserted.

Independent searches for BoundaryDualityInput, boundary duality and boundary
exchange in side Lean, upstream Lean and Mathlib found no exact replacement.
`Etale.HasBoundaryDuality` was inspected: it is etale-only, asserts existence of
an exchange isomorphism, and explicitly omits the canonical exchange and evaluation
compatibility, so it is not a match. Existing component operations are reused.
All 29 listed declarations are present, with source/blueprint docstrings. The
module has autoImplicit false, no sorry, no axiom, no new theorem proof, and no
line over 100 characters. The small pro-etale categories are retained.

No direct statement dependency occurs on the current route-pivot dropped list.
The current origin/newtargets-dag has no repair note for this item. The module
uses ordinary derived functors, adjunction uniqueness and global compactifications;
it introduces none of the dropped enhancement/rectification machinery.

Findings and repairs: H1/H11, the original second-reading section was only a
placeholder, now replaced by this actual reading. H2, the saved lean.statement
flattened the source signature's whitespace; the accompanying complete lean-record
replacement preserves the signature verbatim, including line breaks. Neither
repair changes a mathematical statement or a Lean declaration. No substantive
H3/H4/H5/H7/H13 defect was found.

Compiler reproduction: invoked
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q40 def-weil-boundary-duality-input snapshot/lean/Sheaf/SixFunctors/BoundaryDualityInput.lean`.
Exit 0, no diagnostics: sandbox `Sheaf/Stage2/Sandbox0.lean` 29.8 s and library
`Sheaf/SixFunctors/BoundaryDualityInput.lean` 28.8 s, each under the 60 s limit.
The installed wrapper is currently server-only and reported its private `.lbuild`
overlay. No direct ssh command, lake build, project edit, live Lean write, delivery,
claim or merge was performed. Only the permitted review/fixes files were written.

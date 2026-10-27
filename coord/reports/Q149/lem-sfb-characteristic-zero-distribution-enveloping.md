## Worker report

Repair of returned immutable head 0ce41f6e0632, point H2. The reviewer accepted the
mathematics but required definition ownership instead of a theorem node added as a
statement dependency. The repaired delivery has the unchanged main theorem signature,
a new definition node/module, and this report. It does not deliver or modify
`lem-sfb-bialgebra-distribution-tangent-calculus` or its Lean record.

H2 repair, checked against the current main node files:

- Created `def-sfb-bialgebra-distribution-algebra`, owning
  `Sheaf.RingTheory.Bialgebra.DistributionAlgebra` and its actual constructions.
- Replaced `lem-sfb-bialgebra-distribution-tangent-calculus` in the item's stmt_deps
  with this new definition node. Kept `def-sfb-rational-highest-weight-data`.
- Preserved the item's proof_deps byte for byte, including the bialgebra calculus
  theorem. That unstated theorem remains a future proof input, not a statement input.
- Removed the delivered theorem-node copy and the old DistributionTangentCalculus
  module. Removed distribution_order_mul, invariant-derivation constructions and
  distribution_tangent_calculus from this delivery. The only postponed helpers in
  the new definition module are the two closure proofs needed by its constructions.
- Changed the main module's public import to the new definition module. Its theorem
  signature, mathematical source, statement, proof and proof_deps are unchanged.

Main module:
`Sheaf.AlgebraicGeometry.GroupScheme.CharacteristicZeroDistributionEnveloping`,
`AlgebraicGeometry.characteristicZero_distribution_enveloping`, with sorry proof.

Every hypothesis and clause of the item, matched with Lean:

- Field and characteristic zero: `(k : Type u) [Field k] [CharZero k]`.
- Group scheme over k: `G : Grp (Over (Spec (.of k)))`, the bundled form of the
  recorded `CategoryTheory.GrpObj` on an object over Spec k.
- Affine: `[IsAffine G.X.left]`.
- Smooth: `[Smooth G.X.hom]`, the recorded Mathlib smooth-morphism notion.
- Finite type: `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`, the Mathlib
  finite-type convention (no scheme `FiniteType` class exists).
- C=k[G]: `RationalHighestWeight.coordinateAlgebra G`, the actual global functions.
- Delta and epsilon: the canonical coordinate Hopf instance `coordinateHopf`,
  ultimately Mathlib Group/Affine. The operations come from multiplication and identity.
- I=ker epsilon: `Bialgebra.augmentationIdeal k C`.
- Dist union: `distributionAlgebra k C` has carrier `exists n,
  HasDistributionOrder k C n a`, precisely vanishing on I^(n+1). The Hom of each
  quotient embeds in Hom(C,k) by precomposition, giving exactly this annihilator union.
- Product: inherited Mathlib convolution, `(a*b)(c)=(a tensor b)(Delta c)`;
  unit is epsilon and scalar map is the scalar multiple of epsilon.
- Tangent vectors: `tangentLieAlgebra k C`, whose carrier is exactly the displayed
  counit-Leibniz identity `IsTangentFunctional`. The bracket is the restricted
  convolution commutator. Its identification with the tangent bracket of invariant
  derivations is the proof input `lem-sfb-bialgebra-distribution-tangent-calculus`;
  the proof docstring records the calculation epsilon(D_v D_w)=v*w.
- U: existing `UniversalEnvelopingAlgebra k L`. Read `Rel` and `ringCon`: this is
  the tensor quotient by xy=yx+[x,y], the stated presentation.
- Unital k-algebra isomorphism: `exists ΘG : ... ≃ₐ[k] distributionAlgebra ...`.
- Generator value: `(ΘG (UniversalEnvelopingAlgebra.ι k v)).val c = v.val c`,
  for every v and c. The image is literally the same functional.
- Naturality: every H with the same geometric hypotheses and every `f : G ⟶ H`.
  ΘH satisfies the same generator law and is selected before f.
- Pushforward: `push : Dist(G) →ₐ[k] Dist(H)` with
  `(push a).val c = a.val (coordinateMap f c)` for every a,c.
- Differential: `df : L(G) →ₗ⁅k⁆ L(H)` with
  `(df v).val c = v.val (coordinateMap f c)` for every v,c.
- Induced tensor-quotient hom: `Udf` is an algebra hom satisfying
  `Udf (ι k v) = ι k (df v)` for every v.
- Natural square: `push.comp ΘG.toAlgHom = ΘH.toAlgHom.comp Udf`.
  Equations on all functionals determine push and df uniquely. The tensor-quotient
  universal property determines Udf and both Θ's on generators. Thus these
  existential characterizations specify the canonical maps, not arbitrary maps.
- Connectedness and semisimplicity do not appear among the hypotheses.

New definition module, clause by clause:

- `(k : Type u) (C : Type v) [Field k] [CommRing C] [Bialgebra k C]` packages
  the field, commutative algebra, Delta, epsilon and their axioms. No antipode,
  cocommutativity, finite generation, smoothness or characteristic is assumed.
- `augmentationIdeal := RingHom.ker (counitAlgHom k C)`.
- `HasDistributionOrder n a` means `forall c, c in I^(n+1) -> a c=0`.
- `distributionFiltration : ℤ → Submodule k (WithConv (C →ₗ[k] k))` uses zero
  for negative degrees, and the dual annihilator pulled back by WithConv.linearEquiv
  otherwise. In particular F_(-1)=0 and all nonnegative F_n have the exact carrier.
- `IsDistribution a := exists n, HasDistributionOrder n a`.
- `distribution_closed` is the named sorry helper asserting zero/addition/unit/
  multiplication/scalar-map closure of that actual carrier. Its proof docstring
  gives the augmentation splitting, decreasing powers and pigeonhole argument.
- `distributionAlgebra : Subalgebra k (WithConv (C →ₗ[k] k))` has this carrier,
  with every proof field supplied by `distribution_closed`. All algebra operations
  are inherited from the actual convolution dual. No data is chosen or postponed.
- `IsTangentFunctional a` is the exact counit-Leibniz identity for all x,y.
- `convolutionLieRing` reuses `LieRing.ofAssociativeRing` on the full dual.
- `tangent_closed` is the named sorry helper for zero/addition/scalar/commutator
  closure, with a full natural-language proof from the invariant derivation formula.
- `tangentLieAlgebra : LieSubalgebra k (WithConv (C →ₗ[k] k))` has this exact
  carrier and inherited convolution commutator. Its proof fields use tangent_closed;
  its Lie structures are the existing Mathlib LieSubalgebra instances.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, its group-hom type.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `.Morphisms.FiniteType`, `.Morphisms.QuasiCompact`: `LocallyOfFiniteType`,
  `QuasiCompact`.
- `Mathlib.Algebra.Lie.Basic`, `.OfAssociative`, `.Subalgebra`: LieRing,
  LieAlgebra, LieRing.ofAssociativeRing, LieAlgebra.ofAssociativeAlgebra,
  LieSubalgebra and its inherited structures.
- `Mathlib.RingTheory.Bialgebra.Basic`: Bialgebra, counitAlgHom; the constructor
  `Bialgebra.ofAlgHom` explicitly packages the two maps and their specified axioms.
- Tensor-product dependencies use Mathlib's actual tensor products, maps and
  commutative algebra tensor product; no second definition is made.
- `Mathlib.RingTheory.Coalgebra.Convolution`: LinearMap.convRing, convAlgebra,
  convMul_apply, convOne_apply, convAlgebraMap_apply; `WithConv.linearEquiv`.
- `Mathlib.LinearAlgebra.Dual.Defs`: Submodule.dualAnnihilator for the filtration.
- `Sheaf.AlgebraicGeometry.GroupScheme.RationalHighestWeightData`: coordinateAlgebra,
  coordinateOverGroup, coordinateHopf, coordinateMap, coordinateMap_commutes.
- `Mathlib.AlgebraicGeometry.Group.Affine`: canonical coordinate Hopf construction.
- `Mathlib.Algebra.Lie.UniversalEnveloping`: UniversalEnvelopingAlgebra, Rel,
  ringCon, ι, lift, lift_unique, hom_ext, with full signatures and docstrings read.
- Proof imports: `Sheaf.RingTheory.HopfAlgebra.AugmentationMonomialPairing`,
  `HopfAlgebra.augmentation_monomial_pairing`, and
  `Sheaf.Algebra.Lie.FieldFilteredPBW`,
  `UniversalEnvelopingAlgebra.exists_field_filtered_pbw_basis`.
- Bialgebra calculus remains in proof_deps. It still has no recorded Lean module
  on the current main branch, so there is no module to import for that proof input.

Edge cases checked:

- C=k: I=0, Dist=k times epsilon, tangent zero, U(0)=k.
- Disconnected finite etale group: identity formal neighbourhood gives Dist=k,
  tangent zero; connectedness cannot be silently required.
- Additive group: factorial comparison with the divided-power functionals.
- Multiplicative group: augmentation ideal at t=1 and tangent dimension one.
- Noncommutative group: no cocommutativity or commutative distribution algebra;
  convolution sign is v*w-w*v, consistent with epsilon(D_v D_w)=v*w.
- Zero dimension, order zero and negative filtration index are included.
- Generic definition works in characteristic 2: v(1)=0 uses subtraction.
  CharZero occurs only in the enveloping comparison.
- Identity, trivial and arbitrary homomorphisms are included by forall f.
- Independent field/algebra universes in the new definition; autoImplicit false
  in both modules, with every variable explicitly bound.

Searches, before introducing the new definition node:

- LeanSearch: "The finite order distributions of a commutative bialgebra form the
  subalgebra of its convolution dual annihilating some power of the augmentation
  ideal". Eight hits, Bialgebra constructors and generic algebra operations; no
  distribution subalgebra. Exact wrapper result is in the new node's mathlib_searches.
- LeanFinder: "The Lie algebra of counit derivations is the Lie subalgebra of the
  convolution dual with commutator bracket". Eight hits, manifold invariant
  derivations and ordinary derivation Lie structures; no bialgebra tangent subalgebra.
- Mathlib grep in RingTheory: distributionAlgebra|tangentLieAlgebra|
  HasDistributionOrder|IsTangentFunctional|augmentationIdeal. Zero hits.
- Project rg for distributionAlgebra, tangentLieAlgebra, HasDistributionOrder,
  IsTangentFunctional and convolutionLieRing: no matching definitions.
- DAG grep and `tools/blueprint_refs.py search distribution`: no blueprint match;
  `ancestor` returns null. Existing theorem node found and deliberately unchanged.
- Existing `def-sfb-affine-group-distribution-calculus` was found. Read its full
  node and fetched its module through `scompile.py --source`. Its finiteOrder and
  tangent are predicates specialized to global functions on affine group schemes
  with Hopf structures; it does not give a subalgebra or tangent Lie subalgebra for
  arbitrary commutative bialgebras (no antipode). The new generic construction is
  therefore needed, as explicitly requested in H2. No coordinate-group construction
  or additive-parameter calculus is copied into the new module.
- Prior searches for the main comparison (LeanFinder, Loogle and Mathlib/project
  grep) found only abstract UEA and manifold APIs; the returned independent review
  confirmed the resulting main theorem is mathematically correct.

Source: Milne Sections 10e/10l, printed pp.195--196 and p.208, read locally, plus
current latest blueprint unit/direct-images proof. Both named closure helpers
include complete proof plans. No mathematical statement change or dispute.

## New nodes

`def-sfb-bialgebra-distribution-algebra`: real-data definitions of the augmentation
ideal, order predicate/filtration, distribution carrier and convolution subalgebra,
and counit derivation carrier and tangent Lie subalgebra, with their necessary
named closure helpers. Source: Milne 10e, Proposition 10.29, and 10l, pp.195--196/208.
The three required search kinds and project/DAG searches are recorded verbatim in
mathlib_searches. The existing affine-group node supplies specialized predicates,
not this generic bialgebra subalgebra/Lie structure. The generic definition has no
antipode or geometric hypothesis. Its owning module is
`Sheaf.RingTheory.Bialgebra.DistributionAlgebra`; every declaration is listed in
lean.declarations and tagged with this new node, and every operation is actual data.
The item directly cites this new node. No dependency-node repair is delivered.

## Second reading by Q149

Reopened the current main item/theorem nodes, the repaired item/new-definition node,
and both Lean modules. H2 is repaired structurally: the added statement prerequisite
is a definition node, the calculus theorem remains a proof prerequisite, and neither
that theorem node nor its Lean record is included in the delivery. The old combined
module and all non-definition results have been removed. The main theorem's signature
is identical to the reviewed version; only its public construction import changed.
The declaration ownership list contains exactly the constructions and two closure
helpers, all tagged with the new definition node. The new node has the required
fields, sources, three kinds of searches and correct ancestry. No proof or statement
of an existing node changes. This is a local second reading; the dispatch brief
prohibits starting another agent. The maintainer's independent review remains required.

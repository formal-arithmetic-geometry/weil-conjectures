## Worker report

This delivery states `lem-sfb-prime-to-ell-derived-invariants-reduction` in
`Sheaf.Paper.PrimeToEllDerivedInvariantsReduction`, with the canonical map built
by an actual derived adjunction transpose. It also supplies the missing
continuous-section realization interface in its own definition node. Every
postponed proof is a named theorem with its source, owning blueprint id, and
natural-language proof. No definition has a sorry body. The choices of maps are
from uniqueness characterizations on all sections, never from bare existence.

Hypotheses and objects, in the main theorem's section and signature:

- `ℓ : ℕ` and `[Fact ℓ.Prime]` mean the specified prime.
- `[NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]`
  mean the algebraic closure with extended norm. There is no completeness
  hypothesis on Ω and no finite-subfield-descent condition on continuous maps.
- `E : IntermediateField ℚ_[ℓ] Ω` with `[FiniteDimensional ℚ_[ℓ] E]`
  is precisely the finite intermediate field, with its inherited norm.
- `B L : ProfiniteGrp.{u}` are the two profinite groups. `_hB` quantifies
  over all open normal subgroups and states `Nat.Coprime` for the order of each
  finite quotient. These are exactly the finite continuous quotients.
- `V : Type (u+1)` with the additive, E-module, finite-dimensional and
  `IsModuleTopology E V` instances is the finite-dimensional norm-topological
  E-vector space. Smaller vector spaces can be lifted to this coefficient size.
- `ρ : Representation E (B × L) V` is the linear action, and `_hρ` is
  continuity of the joint action on `(B × L) × V`.
- `_hfinite` and `_horder` impose finiteness and prime-to-ℓ order on the
  B-image. The image is written as the range in `Module.End`; since a group
  representation takes values in invertible endomorphisms, this has exactly the
  same elements and cardinality as its image in GL(V).
- The final conjunction selects exactly E and Ω. `ReductionIsIso E F ...`
  abbreviates the isomorphism assertion for every realization and invariants
  presentation. `HasReductionRealizations E F ...` abbreviates existence of
  precisely its two realizations. `Extended E F V` has the actual tensor-product module and `moduleTopology F`:
  the finite-dimensional product topology, with no completion.
- `extendedRepresentation` is the scalar-extended action, defined by
  `Module.End.baseChangeHom`. `fixedSpace` is Mathlib's
  `Representation.invariants` for B; `fixedRepresentation` is the actual
  restricted residual L-action. Subspaces carry the inherited topology, and
  scalar extension carries the specified module topology.
- `Realization` identifies every test object's sections with **all** continuous
  functions, including restriction, scalar multiplication and generalized-group
  action. `M` and `W` are presentations of these specified objects, not extra
  representation hypotheses. `reduction_realizations_exist` supplies both from
  `_hρ`, even for noncomplete Ω. The main theorem holds for every presentation.
- `dBL` and `dL` are the existing normalized invariant equalizers, including
  their adjunction, sectionwise image and inclusion characterization. Their
  existence is provided by the recorded product-action/bar theorems. They do
  not posit vanishing or an arbitrary derived functor. `rightDerivedFunctor`
  is the ordinary total derived functor on the recorded module categories.

Clauses and canonical maps:

- `inclusion` is the scalar-extended actual fixed-space inclusion, condensed by
  the unique pointwise section formula. `inflationZero` and `derivedInflation`
  use action restriction along `ContinuousMonoidHom.snd B L` and the normalized
  derived counit/adjunction transpose. `reductionMap` is therefore the actual
  `a_F`, not an unspecified isomorphism. The main theorem says `IsIso` of this
  very map, in `DerivedCategory (Modules (normContinuousRing F))`.
- `reductionMap_h0` states the H⁰ clause directly for `reductionMap`, giving the canonical
  unit square and stating that both unit maps are H⁰ isomorphisms, together
  with the exact inclusion formula for the ordinary transpose. Both invariant
  objects therefore identify with the same fixed sections.
- `realizationMap` is the unique continuous-section realization of the actual
  scalar extension of an equivariant linear map. `fixedMap_equivariant` supplies
  the equivariance of its fixed-space restriction. `reduction_inclusion_natural`
  states their square in the condensed action-module category;
  `reductionMap_natural` states the resulting derived square for `reductionMap`
  itself, for every continuous equivariant E-linear `f`. Neither square is an
  assumption. Zero, identity and noninvertible maps are all included.
- `coefficientRingMap` bundles the recorded continuous-map ring morphism.
  `scalarInsertion` is the actual tensor map induced by E → Ω and identity on
  V; under E tensor V = V its formula is v → 1 tensor v.
  `coefficientContinuity`, `coefficientInsertion_properties` and
  `scalarInsertion_equivariant` supply continuity, semilinearity and equivariance.
  `realizationCoefficientMap` condenses this exact map by its unique section
  formula. The coefficient theorem uses their actual pointwise square, whose commutativity
  follows by tensor functoriality without an extra square hypothesis.
- `coefficientMap` derives the normalized equality of invariants and scalar
  restriction using `ScalarModel`, `scalarInvariantChain` and the inverse of its
  localized quasi-isomorphism. It does not assume that scalar restriction
  preserves injectives. Compatible resolution lifts and their quasi-isomorphisms
  are supplied by `ScalarComputation`, which the recorded derived-bar theorem
  supplies. `scalarInflation_comparison` and `scalarInflationIso` fix the unique
  identity-on-underlying-modules comparison of group and scalar restriction.
  `reductionMap_coefficients` states the precise derived square for `reductionMap`
  itself, with both vertical arrows using `coefficientMap` applied to the actual
  `realizationCoefficientMap`. Their ordinary sectionwise square commutes by tensor functoriality,
  so no commutative-square hypothesis is added. The result holds for
  every compatible injective resolution and lift.
- `reductionMap_trivial_identity` renders the final clause for every
  `[Subsingleton B]`, including any presentation of the one-element group.
  `inclusion_trivial_isIso` identifies the fixed-space realization with the
  original one. `trivialFactorInvariantIso` uniquely identifies ordinary
  invariant equalizers by their actual inclusions; `trivialFactorDerivedIso`
  derives that identification using the upstream canonical comparison.
  The displayed composite of `reductionMap` with these two inverse
  identifications equals the identity. Its comparison is constructed
  independently of `reductionMap`, so this does not identify a map with itself.

Dependencies read and reused:

- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingObjOfUniverse`, its canonical monoid structure and
  commutativity. Its ring is reused by the existing `normContinuousRing`.
- `Sheaf.Topology.ContinuousMapCondensedRingMap`:
  `Profinite.continuousMapRingObjMapOfUniverse` and
  `isMonHom_continuousMapRingObjMapOfUniverse`.
- `Sheaf.Paper.NormContinuousMonodromyData`:
  `AlgebraicGeometry.ProEtale.normContinuousRing` and
  `normContinuousRing_comm`; its representation category does not supply
  internal-action continuous-section realizations.
- `Sheaf.CategoryTheory.CondensedActionModule`: `Modules`, `sectionModule`,
  `ActionModule`, `inflate`, `trivial`, `Invariants`, their normalized adjunctions
  and sectionwise fixed-image formulas. These are the actual internal `Mod`
  categories, not discrete group representations or constant-coefficient
  `CondensedMod` categories.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`, for the
  existence and uniqueness of the section presentations.
- `Sheaf.CategoryTheory.CondensedProductBarComparison`:
  the existing `productBarActionAbelian`, `productBarActionGrothendieck`,
  `productBarModulesGrothendieck` and exact trivial-action instances.
- `Sheaf.CategoryTheory.CondensedEquivariantBarData`: `Ring`, `ActionAbelian`,
  `Model`, `ScalarAction`, `ScalarModel`, `ScalarComputation`,
  `resolutionComparison`, `scalarInvariantChain`, `localizedIso`, and `extend`.
  `Sheaf.CategoryTheory.CondensedDerivedInvariantBar`:
  `condensed_derived_invariant_bar` supplies these normalized models.
- The original `sk-def-sfb-module-objects` and
  `def-weil-abstract-derived-category` are Mathlib matches: `CategoryTheory.Mod`
  and `DerivedCategory`. No parallel definitions are introduced.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction`:
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction`; exact functor
  localization, single-object and composition comparisons are used explicitly.
  Existing `Mod.comap` and its additive/exactness instances give scalar restriction.
- The recorded proof dependencies with modules are imported for stage 3.
  The two unrecorded proof-only analytic/normal-subgroup lemmas are retained as
  the main theorem's named natural-language proof inputs, not silently replaced
  by continuous group cohomology or locally constant coefficients.

Edge cases checked: V = 0 and V^B = 0 use the zero-dimensional tensor space and
empty finite sum; no nonzero or positive-rank hypothesis occurs. Empty profinite
test objects have their unique continuous sections and all realization formulas
remain meaningful. B = 1 is normalized as above; L = 1 is permitted. The finite
B-image may be trivial (cardinality one). ℓ = 2 is permitted. No completeness
or local compactness assumption is imposed on Ω, and no averaging assertion
uses division by ℓ. Product topology is finite dimensional throughout.

Searches for the item: prescribed msearch LeanFinder query "Removing a pro
prime to ell factor from derived invariants of condensed continuous
representations" returned unrelated continuous cohomology/solidification and
profinite-free constructions. Loogle `"Condensed", "invariants"` returned zero
hits. Mathlib grep `(Condensed|profinite).*(invariant|acyclic)|...` returned five
ordinary profinite invariant-ring hits, not the internal derived comparison.
`rg` in `lean/WeilConjectures` and `lean/Sheaf`, including the exact item id,
found no declaration stating this result. New-notion searches are recorded in
its node, including LeanSearch, LeanFinder, Mathlib/source/project grep and the
whole-blueprint search. The previous N9 delivery is a stage-1 split, not a
Lean statement; its reviewed statement and proof are retained verbatim.

No statement correction and no STATEMENT-DISPUTED flag. Added statement
dependencies name the missing realization and the already-landed action/bar
interfaces that the Lean signatures actually use. No shared source was edited
and all compilation uses scompile.py against the live published server build.

## New nodes

`def-sfb-continuous-representation-condensation` specifies the continuous-section
realization of a topological linear representation, its existence, and the
uniquely specified ordinary and scalar-changing maps. It uses the existing
continuous coefficient ring and internal action-module category. Its source is
the same paragraph (3) continuous-representation input; `blueprint_refs ancestor`
returns None, so the inherited null ancestor and full via chain are retained.
LeanSearch and LeanFinder found topological continuous cohomology or
constant-coefficient condensed modules; the project has the norm-continuous
monodromy ring and abstract action modules, but no realization identifying all
sections with C(S,V). The whole-blueprint search found four unrelated
representation nodes. The definition carries real structure data; existence is
a separately named theorem, and no object is chosen from an uncharacterized
existence proof. Maps are chosen only from uniqueness, so their section formulas
fix them completely.

`def-sfb-condensed-derived-inflation-arrows` owns the canonical adjunction-transpose
inflation and the normalized scalar-restriction comparison, including their
normalizations and naturality laws. It is split out of the item's module so each
file remains within the mandatory 60-second per-file limit. The source and
mathematical maps are unchanged. Its three prescribed search kinds returned
ordinary scalar restrictions or constant-coefficient condensed modules, not
these arrows; the existing normalized scalar chain is reused. The blueprint
search returned zero matches for derived inflation. This node introduces real
canonical arrow constructions, with every required proof separately named.

The generic representation helpers (`Extended`, its canonical algebraic/topological
instances, `extendedRepresentation`, `fixedSpace`, `fixedRepresentation`,
`fixedInclusion`, `fixedMap` and `scalarInsertion`) live with the continuous
representation realization definition. They use the actual Mathlib tensor product,
invariant subspace and restricted representation. This also avoids re-elaborating
those constructions in the analytic reduction statement file.

## Repair of returned head 5d0a89048873

H2: Removed `lem-sfb-condensed-derived-invariant-bar` from the item's
`stmt_deps` and from the new arrow node's `stmt_deps` and TeX. Its module
remains a private proof import. The actual signature types `Model`,
`ScalarModel`, and `ScalarComputation` come from
`def-sfb-condensed-equivariant-bar-data`, which remains a statement dependency.
The product-bar theorem remains because its Abelian/Grothendieck instances
are used by the declarations, as the independent return explicitly accepted.

H3(a): Added `reductionMap_h0` in the item module. This states an equation for
`H.map (reductionMap ...)` itself and the actual fixed-space inclusion, using
the canonical unit square and its H⁰ isomorphisms. No H⁰ clause is left
merely as an unstated specialization of a generic arrow lemma.

H3(b): Added `realizationMap`, its actual scalar-extension equivariance lemma,
and `fixedMap_equivariant`; `reduction_inclusion_natural` is the condensed
square, and `reductionMap_natural` is the derived square. Both quantify over
continuous equivariant E-linear `f`, and both use its realization maps.

H3(c): Added `reductionMap_coefficients` with `realizationCoefficientMap` as
both underlying coefficient arrows. It concludes commutativity of the actual
`a_E` / restricted `a_Omega` square without assuming that square.

H3(d): Added an inclusion-normalized, unique fixed-section comparison for
`[Subsingleton B]` and its derived comparison. These implement the group
identification B times L = L; the inverse actual fixed-space inclusion
implements V^B = V. `reductionMap_trivial_identity` states that the transported
`reductionMap` is the identity, and covers all trivial-group presentations.

The saved packet's first dry run was mechanically green, but still had these
semantic omissions from the return. They have been repaired rather than
repushing that unchanged packet. The current main node has no Lean record
and its statement equals this packet's retained statement verbatim; the
wrapper rebases the delivery onto current main. No target or mathematical
statement correction is involved.

## Second reading by Q02

Direct self-check of the revised packet (the independent mathematical reading
is the maintainer's): the prime, algebraic closure, finite intermediate field,
all-continuous coefficients, both profinite groups, pro-prime-to-ell quotient
condition, finite-dimensional topology, continuous action and finite
prime-to-ell B-image hypotheses are retained unchanged in the original
isomorphism theorem. The four new clause theorems state properties of the
same canonical `reductionMap`, with stronger generality only where the
properties are formal for all such actions. Naturality and coefficient squares
use the specified section realization maps rather than arbitrary arrows.
The trivial-group clause uses `[Subsingleton B]`, not a restriction to the
identity homomorphism. The required unique characterization fixes the only
new chosen isomorphism on every section. All new postponed theorems have
same-item blueprint/source tags and natural-language proofs; all definition
bodies construct data, and all variables and universes are explicitly bound.
The zero vector space, zero fixed subspace, zero equivariant map, empty
profinite test object, L trivial and B trivial remain included.

Elaboration diagnosis: profiling showed repeated comparison of the copied tensor
module instances with their original tensor-product instances. Marked the four data-valued
existing `Extended` instance aliases 
`instance_reducible`, preserving their mathematical data and topology. Redundant
linear-only and ordinary coefficient-square preliminary theorems were removed;
the required condensed naturality and actual derived coefficient square remain
explicitly stated. No new module was split off to avoid the compile limit.

The formal inclusion, `reductionMap`, H⁰, naturality and trivial-factor clauses
are parameterized by an independent field E and normed coefficient field F. The analytic theorem
states the conjunction `ReductionIsIso E E ...` and `ReductionIsIso E Ω ...`.
The predicate is defined in full as the original universal assertion over
realizations and normalized invariant equalizers. This replaces the expensive
conditional-field presentation without changing either coefficient object.
The realization-existence theorem likewise gives both exact fields explicitly.
No mathematical statement correction or extra hypothesis is involved.

The coefficient square is likewise formalized for a normed E-algebra F with
continuous `algebraMap E F`. For the node's precise E to Omega inclusion,
instantiate `F := Omega` and `hφ := coefficientContinuity ℓ Ω E`.
That theorem supplies continuity rather than adding it as a hypothesis on the
node. Both vertical arrows are the specified realizations of scalarInsertion.
The analytical isomorphism theorem and its realization-existence theorem still
use the exact original intermediate field and extended norms.

The formal reduction interface only needs `[Field E]`, so it now uses that
instance directly. Source-side V topology is still part of the analytic theorem;
continuity of f is explicitly bound in the naturality theorems. The coefficient
arrow interface still uses the two normed fields, as required for their rings
of continuous functions. These changes avoid forcing definitional comparisons
between the intrinsic intermediate-field structure and inherited normed fields.

Validation: all three owning modules compile cleanly through scompile.py;
the final item compiles in 55.9 seconds as the sandbox module and 52.8 seconds
under its library name, below the unchanged 60-second limit. No diagnostic
commands, reduced-heartbeat setting, profiler setting, or scratch Lean files
are in the delivery. The final self-check verifies exact recorded signatures,
complete declaration registration, removal of the returned unused dependency,
and the 100-column limit.

The final dry run caught and repaired a metadata-only signature extraction
error: the arrow node's signature had stopped at the named argument `(R := R)`.
Its record now contains the complete declaration header, up to the actual body
delimiter. The Lean source and its clean compilation are unchanged.

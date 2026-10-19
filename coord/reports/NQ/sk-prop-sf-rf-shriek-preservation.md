## Worker report

The module `Sheaf.Paper.FiniteLocalizingExceptionalPreservation` states
`AlgebraicGeometry.ProEtale.CondensedRing.localizingExceptionalAdjoint_preserves_finiteConstructible`.
Its proof is `sorry`. It also supplies two transparent helper constructions belonging to
this node: `localizingDctfProperty`, the inverse image of the existing Dctf predicate under
the localizing inclusion, and `finiteShriekProEtaleTateLine`, the specified exact comparison
pullback of the existing etale Tate twist. There are no new independent notions, no new
nodes, no dependency repairs, and no statement correction.

Source read: the current main-20261015 unit's `_section.md`, the complete DAG statement and
its eleven-step proof, and its resolved stage-1 repair note (which requires keeping the
statement and proof route). The upstream etale stability declarations cover pieces of the
argument, not this pro-etale localizing adjoint statement, so no existing match was used.

Hypotheses and conventions, in the order of the mathematical statement:

- A prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`.
- An arbitrary positive-characteristic field k, of characteristic different from ell:
  `(k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]`.
  Characteristic of a field is positive precisely when its ring characteristic is prime.
  No algebraic closure, perfectness, or bound on the field's cohomological dimension is used.
- Separated finite-type schemes over k: the two `Over (Spec (.of k))` structures and,
  for each structure map, `LocallyOfFiniteType`, `QuasiCompact`, and `IsSeparated`.
  These are exactly the recorded finite-type and separatedness definitions.
- A separated finite-type k-morphism: `(f : X ⟶ Y) [f.IsOver (Spec (.of k))]`, followed
  by the same three morphism-property instances for f.
- A finite commutative ring with its discrete topology: `(A : Type u) [CommRing A]
  [Finite A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]`.
  The topology structures state the source's discrete-topological convention explicitly;
  the ring may be zero, and there is no `Nontrivial A` assumption.
- Annihilation by an ell-power: `_hA : ∃ r : ℕ, ((ℓ ^ r : ℕ) : ULift A) = 0`.
  The ring equivalence `ULift.ringEquiv` identifies this with ell^r = 0 in A, equivalently
  annihilation of every A-element by ell^r. The displayed natural-number cast avoids
  conflating a cast of a natural power with a power taken after casting.
- The condensed ring is the actual `Profinite.continuousCoefficientRingObj A`, whose
  sections are continuous maps into A. Its pullback is the recorded `condensedRingObj`.
  The size convention uses `ULift.{u+1} A` only in ordinary fixed-scalar sheaf coordinates;
  schemes have universe u and the pro-etale site keeps object universe u+1, morphism u.
- The chosen compactification, closure preservation proof, right adjoint, and adjunction
  supplied by sk-prop-sf-existence are the binders `c`, `h`, `G`, and `adj`.
  They are data of the “let f^! be the right adjoint” clause, not an additional
  preservation-of-Dctf premise. `localizingLowerShriek ... c.obj.obj h` is the restriction
  of the actual compactification composite used by that dependency, not an arbitrary functor.
  The statement applies to every such adjunction, so it does not depend on selecting a
  particular witness of the existence theorem. No compactification independence is asserted.

Conclusions, clause by clause:

- Dctf is the existing `constantModelBoundedConstructible Λ T` intersected with the
  existing `DerivedCategory.finiteTorAmplitude` predicate, precisely the object property
  underlying `ConstantModelConstructibleFiniteTor`. `localizingDctfProperty` pulls this
  property back along inclusion of `localizingClosureProEtale`; it does not introduce
  another constructibility or Tor test. Its full subcategory is Dctf viewed inside Loc.
  These categories have all ambient morphisms. Every Dctf object lies in its localizing
  closure directly from the latter's intersection definition, so this nested presentation
  excludes no object or morphism and requires no new closure theorem.
- Preservation by the given f^!: the existential `hG` asserts that every Dctf object K of Y
  is taken by G to that same Dctf property on X. No Tor interval or cohomological bound is
  fixed in advance or strengthened uniformly across objects.
- Restriction of the adjunction: `hF` supplies lower-shriek preservation and the two
  `ObjectProperty.lift` expressions restrict the actual two functors. `adjSmall` is an
  adjunction between them; the following equality of `homEquiv` maps identifies it with
  the restriction of the GIVEN `adj`. Thus arbitrary unrelated adjunction structures are
  not substituted. Full-subcategory morphisms forget by `.hom` with no altered maps.
- The smooth clause universally quantifies `(d : ℕ) [SmoothOfRelativeDimension d f]`;
  zero relative dimension is included. It universally quantifies any exponent r and its
  annihilation proof `hAr`. The chosen N is literally `ℓ ^ r`; primality ensures N >= 1.
  Thus the equal-exponent and zero-ring/exponent-zero cases are retained.
- `finiteShriekProEtaleTateLine X A (ℓ ^ r) hAr d` is literally
  `(comparisonUpperStar _ X).obj (finiteEtaleTateTwist X (ℓ ^ r) (ULift A) hAr d)`.
  The comparison inverse image is exact, so this sheaf is the line whose degree-zero
  derived object defines the stated pro-etale twist; no alternative line is chosen.
- Etale-local naturality is one `Scheme.Cover.{u} Scheme.etalePrecoverage X`, followed
  by a statement for every member. This cover is chosen before any input complex.
  The first `Nonempty` gives the actual Tate line's inverse-image trivialization as a
  sheaf of A-modules, not just as an abelian sheaf. The second `Nonempty` is a natural
  isomorphism of functors on ALL Dctf inputs, after restriction to that same member.
  Its left side is G followed by actual internal-module inverse image. Its right side
  is actual inverse image along f, then along the cover map, then `[2d]`.
- This is the local coordinate form of the requested `f^*(-)(d)[2d]`, not a claim that
  the twist is globally trivial. On a cover with the first displayed trivialization,
  tensor by the degree-zero Tate line is naturally tensor by the coefficient unit.
  Its unitors identify that tensor with the identity, giving the second isomorphism
  exactly when the local twist formula holds. Conversely the stated twist formula,
  refined by an etale cover trivializing its Tate line, gives these two clauses. This
  refinement is always available by the recorded finite-etale-twist-line proof dependency.
  The prescribed exact tensor-compatible section-action equivalence transfers the same
  argument between ordinary A_T-modules and the module-object category used here.
  In particular the isomorphism is natural in K, is merely local on X, and constructs no
  canonical global smooth-purity orientation. This equivalent trivialized formulation
  avoids using an arbitrary coefficient comparison map to manufacture a global line.

Dependency interfaces read and used (module, declaration):

- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: `LocallyOfFiniteType`; its imported
  QuasiCompact module: `QuasiCompact`.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: `IsProper`, `IsSeparated`,
  `UniversallyClosed`; here only separatedness is required of f and the structure maps.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: `SmoothOfRelativeDimension`, `Smooth`.
- Sheaf.Paper.LocalizingExceptionalAdjoint:
  `AlgebraicGeometry.ProEtale.CondensedRing.localizingLowerShriek` and
  `exists_localizingExceptionalAdjoint`, including its actual compactification interface.
- Sheaf.Paper.LocalizingAdmissibleCoefficients (reexports Sheaf.Paper.LocalizingClosure):
  `AlgebraicGeometry.ProEtale.localizingClosureProEtale` and
  `CategoryTheory.localizingClosure` (intersection in the unbounded category).
- Sheaf.Paper.CondensedConstantConstructibility (reexported by the closure):
  `constantModelBoundedConstructible` and `ConstantModelConstructibleFiniteTor`.
- Sheaf.Topology.ProfiniteCondensedRing (reexports ContinuousCoefficientCommRing and
  ContinuousCoefficientUniverse): `Profinite.CondensedRing` and
  `Profinite.continuousCoefficientRingObj` with commutativity.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic:
  `coefficientRing`, `condensedRingObj`, `isCommMonObj_condensedRingObj`.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible:
  `compactificationOverField`, the setting's recorded Nagata compactification interface;
  the theorem's explicit scheme binders render the actual setting, not this upstream
  module's different constructibility predicate.
- Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence:
  `CategoryTheory.InternalAbelianSheafModule.sectionModuleEquivalence`; its exact
  section-action identification is the source's coordinate convention. It is imported
  without redefining or assuming an arbitrary replacement equivalence.
- Sheaf.Paper.ProEtaleConstructibleSheaf:
  `Scheme.IsConstructibleProEtaleModuleSheaf`; and
  Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude:
  `Scheme.HasProEtaleTorAmplitude`, `Scheme.HasFiniteProEtaleTorAmplitude`.
  These are the recorded ordinary-module descriptions reexported alongside the actual
  module-object Dctf definition. The statement uses the latter as the source permits.
- Sheaf.AlgebraicGeometry.ProEtaleFiniteModules:
  `finiteCoefficientComparison`, `finiteCoefficientDerivedComparison`; their geometric
  inverse image is the imported `ProEtale.comparisonUpperStar`, used on the Tate line.
- Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist: `Scheme.finiteEtaleTateTwist`, read with
  its scalar extension of roots of unity and zero/nonnegative tensor powers.
- WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs:
  `CondensedRing.upperStar`; its exact `mapDerivedCategory` gives each internal pullback.

Every proof-dependency node with a recorded module is imported nonpublicly unless already
publicly imported as a statement dependency. Nodes without recorded modules are not assigned
invented import paths. These proof modules carry the eleven-step natural-language plan
reproduced in the theorem docstring; the missing proof declarations are not prerequisites
for writing this statement and no downstream lemma is assumed in its hypotheses.

Edge cases checked before writing:

- The zero ring is allowed, including r=0, N=1. All its module categories are zero;
  no nonzero root generator or `Nontrivial A` is required.
- Empty X or Y is allowed. Empty etale covers are permitted by `Scheme.Cover` and the
  memberwise assertions then have no member to check; the zero-category adjunction remains.
- d=0 has shift zero and the existing degree-zero coefficient twist. There is no positive
  dimension requirement and no positive exponent requirement.
- The zero complex belongs to the existing Dctf property and is included in both Hom tests.
- The field is not assumed separably closed, perfect, or of finite cohomological dimension.
- No common Tor/cohomological interval across all objects, fixed affine chart, nonempty
  stratum, derived completion, or smallness equality of site universes was added.

Searches for an existing statement and names:

- `msearch.py ... leanfinder`: “exceptional inverse image preserves bounded constructible
  finite Tor amplitude complexes and smooth local Tate twist formula”; eight hits on
  generic derived-category boundedness/fraction declarations, no exceptional preservation.
- `msearch.py ... loogle`: `constructibleTorAmplitudeIn_rightDerivedUpperShriek,
  localizingExceptionalAdjoint`; zero hits (unknown first identifier).
- `msearch.py ... grep`: `rightDerivedUpperShriek|localizingExceptional`, subdirectory
  CategoryTheory; zero Mathlib hits.
- `rg` of the upstream WeilConjectures tree for the node id and the named etale stability
  declarations found the open, finite-etale, closed, smooth and arbitrary finite-type
  etale statements. Their full relevant signatures are on ordinary etale derived categories,
  not the right adjoint on the module-object pro-etale localizing closure. They do not state
  this whole node, and the smooth preservation result alone is not its natural local formula.
- `rg` of lean/Sheaf found comparison, localizing-existence, etale-transport and chart lemmas,
  but no full declaration of this node. Searches of Mathlib, the upstream Lean tree and
  dag/lean_names_upstream.json found no occurrence of the three new full declaration names.
- Recorded declarations missing from the local checkout were read with the prescribed
  `scompile.py --source`, notably the full section-action equivalence and the finite
  discrete point/scheme ring identifications. Their canonical-map constructions were
  checked before choosing the equivalent common-trivialization formulation above.

No STATEMENT-DISPUTED issue was found. Compilation and delivery results follow below.

## Second reading by NQ

No second reading by a worker: the dispatcher forbids starting other agents. The worker
delivers directly; the maintainer's independent review is the review for this delivery.

Validation: the prescribed `scompile.py NQ sk-prop-sf-rf-shriek-preservation` compiled the
final delivered module both in sandbox coordinates and at its final module path, each in
5.5 seconds, with no errors or warnings. The only postponed proof is the named main theorem.
The node copy differs from the read-only base only in `lean`; its signature was compared
verbatim with the final file. All Lean lines are within 100 characters and `autoImplicit`
is disabled explicitly. No live file, launcher tool, or upstream source was edited.

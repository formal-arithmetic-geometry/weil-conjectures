## Worker report

The module `Sheaf.Paper.GenericRetractSupportGluing` states
`AlgebraicGeometry.ProEtale.genericRetractSupportGluing`, with proof `sorry`.
`GenericRetractSupportGluingAssertions` packages its several conclusions, using actual
existing categories and functors. It introduces no independent mathematical notion:
its local abbreviations expand the objects in this single node's displayed diagrams.
No node statement, dependency list, or proof plan has been changed.

Sources read: the whole item's statement and six proof steps; every statement dependency
and its recorded interface; Stacks `proetale.tex`, Tag 09AH,
`lemma-ses-associated-to-open`, including its quasi-compactness hypothesis; the latest
blueprint `sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraphs (1)--(3).
The blueprint gives the surrounding extension and direct-image argument; the node
explicitly labels its finer support-gluing argument as agent assembly from 09AH.

Hypothesis and clause correspondence:

* The distinct primes are `(p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : p ≠ ℓ)`.
  The base is `{k : Type u} [Field k] [CharP k p]`.
* The finite normed extension is `(E : Type u) [NormedField E]`
  `[NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]`.
  NormedAlgebra specifies the extending norm, rather than an arbitrary topology.
  Its continuous coefficient ring is the existing `(normContinuousRing E).X`, whose
  body is exactly `Profinite.continuousMapRingObjOfUniverse.{u,u} E` with the recorded
  canonical pointwise ring-object structure. The valuation ring is background notation
  in this node: no asserted object or arrow uses integral coefficients.
* `U S : Over (Spec (.of k))` with the three structure-morphism classes
  `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated` expresses separated finite type
  over the same field. `a : S ⟶ U` is a k-morphism; `[IsImmersion a.left]` is locally
  closed immersion, and `[IsIntegral S.left]` includes nonemptiness, reducedness and
  irreducibility. Opens and closed subschemes inherit the same base morphism, finite
  type and separatedness, so arbitrary `S₀` and `B` with the displayed immersions lose
  no k-scheme condition.
* `v : S₀ ⟶ S.left`, `[IsOpenImmersion v]`, `[Nonempty S₀]`, and `_hv : DenseRange v`
  give exactly the nonempty dense open. `z : B ⟶ S.left`, `[IsClosedImmersion z]`,
  `[IsReduced B]`, `_hz : Set.range z = (Set.range v)ᶜ` specify the reduced closed
  complement. This is the reduced induced closed structure, characterized equivalently
  by these conditions; no possibly nonreduced thickening is admitted.
* `D Λ T` expands to the ordinary unbounded derived category of
  `Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u+1}) (condensedRingObj Λ T)`.
  Thus these are the specified internal modules with coefficients pulled back from
  the point. `constantModelBoundedConstructible Λ S.left M` and the same for N use
  precisely bounded cohomology and the recorded finite constant scalar models on
  constructible stratifications, rather than arbitrary finite-presentation models.
  Lisse is background terminology and is not added as an assumption on M or N.
* In the assertion definition, `F := closure (Set.range (z ≫ a.left))` and
  `closure (Set.range a.left)` are exactly F and Z. The first conclusion is their
  strict inclusion `F ⊂ closure (Set.range a.left)`. Both are closed by construction.
* `e := support Λ a.left` and `e₀ := support Λ (v ≫ a.left)` reuse the canonical exact
  closure-factorization extension. `r := pull Λ v` is the exact termwise derived
  inverse image. The given arrows `ι`, `ρ` have source and target `r.obj M`, `r.obj N`,
  and `ι ≫ ρ = 𝟙 (r.obj M)` uses Lean's left-to-right composition convention.
* `o K := e₀.obj (r.obj K)` is `(av)_!v^*K`;
  `c K := e.obj ((closed Λ z).obj ((pull Λ z).obj K))` is `a_!z_*z^*K`.
  The universal clause restricted by `K = M ∨ K = N` states both displayed triangles
  using three existential arrows and `Triangle.mk f g h ∈ distTriang (D Λ U.left)`.
  The last arrow has codomain `(o K)⟦(1 : ℤ)⟧`, exactly the shift in the node.
* That same clause says `constantModelBoundedConstructible Λ U.left (c K)` and
  `IsZero ((pull Λ w.ι).obj (c K))`, where `w` is the open with underlying set Fᶜ.
  This renders both the constructibility and the specified meaning of support on F.
* `e₀.map ι ≫ e₀.map ρ = 𝟙 (o M)` uses exactly the images of the supplied maps.
  It therefore exhibits the requested retract, without replacing it by unrelated maps.
* A full thick subcategory is represented by `P : ObjectProperty (D Λ U.left)`;
  `P.IsTriangulated`, `P.IsClosedUnderIsomorphisms`, `P.IsStableUnderRetracts` give
  zero, shifts, cones, repleteness and retract closure. Finite sums follow from the
  split distinguished triangle. The assumptions are `P (e.obj N)` and membership
  of every bounded constant-model constructible K whose restriction to w is zero.
  The conclusion is `P (o N) ∧ P (o M) ∧ P (e.obj M)`, in the node's order.
* `Set.range v = Set.univ → IsZero (c M) ∧ IsZero (c N)` is the S₀=S case, allowing
  any presentation of the open immersion rather than requiring definitional equality
  of schemes. An open immersion with full image is an isomorphism.
  There is no hypothesis supplying or extending a projector on `a_!N`.

Dependency declarations read and reused (module, names):

* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, publicly reexporting
  `Padic.coefficientExtensionAbsoluteValue` and `coefficientExtensionIntegers` and
  their finite-extension data; Mathlib's `NormedAlgebra` expresses the unique extending
  norm on E directly. The ring of integers does not occur in the conclusions.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
  `AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField`: the setting
  is rendered by the explicit Over, finite-type and separated binders, as its record
  prescribes. No compactification choice is needed for an exact immersion extension.
* `Sheaf.Topology.ContinuousMapCondensedRing`,
  `Profinite.continuousMapRingObjOfUniverse`, its canonical MonObj and commutativity;
  the existing `Sheaf.Paper.NormContinuousMonodromyData.normContinuousRing` bundles
  precisely this construction and is not a new coefficient ring.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`: actual point pullback.
* `Mathlib.CategoryTheory.Monoidal.Mod`, `CategoryTheory.Mod`: actual internal modules.
* `Sheaf.Paper.CondensedModuleDerivedPushpull`,
  `moduleObjectDerivedPullback` and `moduleObjectDerivedPushforward` retain the total
  derived interfaces. Here exact inverse image and exact closed pushforward are written
  with the existing equivalent termwise `mapDerivedCategory` interface.
* `Sheaf.Paper.CondensedConstantConstructibility`,
  `constantModelBoundedConstructible`, with its full definition read through
  `IsConstantModelConstructible`, `IsFiniteConstantStratified`,
  `HasFiniteConstantLocalModel`.
* `Sheaf.Paper.CoefficientHeartStratificationDefs`, `IsLisseCoefficientModule`, read
  but not imposed as a hypothesis, since this node allows all M,N in Dbc.
* Mathlib `CategoryTheory.Pretriangulated`, `ObjectProperty.IsTriangulated`,
  `ObjectProperty.IsStableUnderRetracts`: distinguished triangles and full thick
  subcategories. `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
* `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`,
  `AlgebraicGeometry.Scheme.LocallyClosedExtensionData.DerivedCoherence` and
  `locallyClosedExtensionCoherence`: the recorded exact normalized composition laws
  used by the proof. Its section-module system is not copied or selected arbitrarily.
  For actual internal-module terms, the existing
  `Sheaf.Paper.NormalizedInternalSupportScalars` declarations
  `SupportedCommonField.support`, `closed`, `pull`, `D` implement the same exact
  functors with the canonical `coefficientHeartLocallyClosedExtension` factorization:
  open extension into the scheme-theoretic closure followed by closed direct image.
  Their bodies and the owning `CoefficientHeartFiltration` definition were read.

The remaining imports record every already-stated proof dependency: complementary
stratifications, Cartesian coefficients, ringed open/closed localization, internal-module
transport, the short-exact-complex triangle, constant-model pullback, scalar-model immersion
extension, and reduced scheme image. Exact-functor localization is publicly available
through the support interface. There are no added proofs or hollow definitions.

Edge cases checked: M=0, N=0 (a generic retract of zero need only have boundary support),
S₀=S and empty B, zero-dimensional integral S, and a nontrivial boundary in A¹.
The helper's strict support inclusion precedes quantification over M,N and their arrows,
so it does not become conditional on a retract existing. There is no positive-rank
hypothesis, no proper-open hypothesis and no nonempty-boundary hypothesis. The full norm
coefficient construction allows E in Type u with schemes in universe u; this includes
arbitrary coefficient size by choosing a sufficiently large common universe.

Searches run:

* msearch LeanFinder: `Open closed localization triangles glue a retract on a dense open
  modulo bounded constructible complexes supported on the boundary`. Eight results:
  bounded-derived representative lemmas, triangulated-localization infrastructure and
  T-structures; none states the node.
* msearch Loogle: `CategoryTheory.ObjectProperty.IsThick, CategoryTheory.Retract`.
  Zero hits, unknown identifier IsThick. Direct source search found the correct existing
  `ObjectProperty.IsTriangulated` and `IsStableUnderRetracts` encodings instead.
* msearch grep: `IsThick|triangEnvelope` in CategoryTheory. Five hits in
  `Triangulated/Generators.lean`, general thick envelopes, not this statement.
* msearch LeanSearch: `Open closed localization distinguished triangles and generic
  retract imply thick subcategory membership`. Eight results on triangulated
  subcategories/localization/T-structures and `DerivedCategory.mem_distTriang_iff`;
  none is the coefficient-specific support-gluing theorem.
* Direct rg of `generic.retract|GenericRetract|lem-sfb-generic-retract-support-gluing`
  over project Sheaf, WeilConjectures and upstream name records found only an unrelated
  generic retraction of condensed affine generators. The new declaration name is absent.
* Direct project/Mathlib searches for `coefficientHeartLocallyClosedExtension`, `support`,
  `IsStableUnderRetracts`, `IsTriangulated`, `continuousMapRingObjOfUniverse` located
  precisely the reused canonical constructions above. No duplicate notion was written.

Validation: scompile.py checked this module as a sandbox and under its real library
name, both clean (21.8 s and 15.5 s). The initial compile identified the missing
`CategoryTheory.Pretriangulated` namespace opening for `Triangle.mk`; that was repaired.
No warning other than the stage-2 sorry warning remains. The node's lean.statement is
extracted verbatim from the final theorem signature.

## Second reading by Q99

This is a second pass by the same dispatcher-started worker; the human brief forbids
starting another agent, so no independent second-reader claim is made. The maintainer's
independent review remains the independent reading required by this workflow.

I reopened the node and the completed module and checked each clause against the mapping
above. In particular the two triangles are not replaced by a membership-only consequence;
the two third terms, not their generic parts, carry constructibility and vanishing;
the retract equation uses the images of the original generic arrows; and membership
includes all three required objects. The boundary is allowed empty, the generic open
is allowed all of S, and integrality carries nonemptiness. The assertion definition
quantifies all thick P rather than fixing one in advance. The helper definitions contain
real constructions; the only theorem proof is sorry. No mismatch or statement correction
was found during this pass. No new nodes or dependency repairs were needed.

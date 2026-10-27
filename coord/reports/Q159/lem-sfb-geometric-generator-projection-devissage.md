## Worker report

Item: lem-sfb-geometric-generator-projection-devissage. Group Q159, stage 2.
The module states geometric constructibility, finite supported-lattice generation, and
invertibility of the specified norm coefficient projection. Its sole theorem is postponed
with `sorry`; the helpers have actual data. No statement correction is made.

Source read: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3),
and sk-lem-integral-models/sk-lem-integral-models-generators.md, clause (1), together
with the item's six-step agent proof. The blueprint paragraph supplies the six-functor
context; the norm comparison is the explicitly agent-extracted obligation, whose exact
literature reference the node labels WANTED. It is not asserted to be a literal theorem
of that paragraph. The theorem docstring retains the full six-step proof plan.

Hypotheses, objects, and conclusions matched individually:

* Distinct primes: `p ℓ : ℕ`, `[Fact p.Prime]`, `[Fact ℓ.Prime]`, `_hpℓ : p ≠ ℓ`.
* The characteristic-p field and specified separable closure: `k ks : Type u`, their
  `Field` instances, `[Algebra k ks]`, `[IsSepClosure k ks]`, and `[CharP k p]`.
* A separated finite-type k-scheme: `X`, its structure map `a : X ⟶ Spec (.of k)`,
  `[LocallyOfFiniteType a]`, `[QuasiCompact a]`, `[IsSeparated a]`.
  These are precisely finite type and separatedness, without an assumption on u.
* The actual geometric scheme and projection are the existing `geometricScheme k ks X a`
  and `geometricProjection k ks X a`. The second projection is bundled directly as `Over.mk (pullback.snd ...)` for the
  existing lattice API.
* A normed algebraic closure of Q_ell: `Ω`, `[NormedField Ω]`,
  `[NormedAlgebra ℚ_[ℓ] Ω]`, `[IsAlgClosure ℚ_[ℓ] Ω]`. There is no `CompleteSpace Ω`.
  The embedded finite field is `E : IntermediateField ℚ_[ℓ] Ω` with
  `[FiniteDimensional ℚ_[ℓ] E]`; its norm is the inherited subfield norm.
* A and B are `normCoefficients E` and `normCoefficients Ω`. Their underlying objects
  are `Profinite.continuousMapRingObjOfUniverse`: all continuous functions with
  pointwise operations, not a colimit of finite-subextension-valued functions.
  `supportedLatticeNormInclusion ℓ E` is postcomposition by the actual inclusion E to Ω.
* Internal coefficient modules are `CondensedGalois.Modules R.toMon X`, an abbreviation
  for Mathlib `Mod` on the existing pulled-back ring object `coefficientRing X R`.
* `V : DerivedCategory.{u + 2} ...` is an ordinary unbounded derived object.
  `_hV : constantModelBoundedConstructible ... V` supplies bounded cohomology and
  exactly the node's finite constant local models, rather than arbitrary local matrices.
* V^s is `(CondensedRing.moduleObjectDerivedPullback ... (geometricProjection ...)).obj V`,
  the recorded total left-derived composite. Exactness identifies this with the
  termwise pullback in the proof, but the stated object remains the total-derived one.
* The first conjunct is `constantModelBoundedConstructible ... V^s` on the actual T,
  using the same finite constant local model convention as the input.
* Finite cone-and-integer-shift generation is expressed by membership in every
  `ObjectProperty P` which is triangulated, closed under isomorphisms, and contains
  the displayed supported lattices. This is the intersection definition of the
  smallest triangulated subcategory, as in the recorded integral-generator theorem.
  It does not take closure under arbitrary coproducts or retracts.
* Each generator quantifies a scheme S, `i : S ⟶ T`, `hi : IsImmersion i`,
  `Topology.IsConstructible (Set.range i)`, and a module L0 over
  `supportedLatticeIntegralRing ℓ E` with `IsLisseCoefficientModule ... L0`.
  That lisse predicate uses finite free modules with locally varying rank, including zero.
* `supportedRationalizedLattice ℓ E ... i hi L₀` is exactly the recorded
  degree-zero ordinary scalar extension of `coefficientHeartLocallyClosedExtension`.
  It uses open extension into the scheme-theoretic closure followed by closed direct
  image, and the integral ring `C(P, Padic.coefficientExtensionIntegers ℓ E)`.
  The latter is the dependency's valuation ring; uniqueness of the extending absolute
  value identifies it with the unit ball for the restricted norm.
* The third conjunct is `IsIso (pointProjection ... (canonicalPointScalar ...) V^s)`.
  Its source is ordinary K-flat condensed extension applied to the derived point
  direct image; its target is derived point direct image after K-flat extension on T.
  `source` and `target` are only transparent abbreviations for these two composites.
* The map is fixed: `canonicalPointScalar` is the existing uniquely normalized square
  of scalar adjunctions. Its restriction is the derived ordinary mapMod/comap square,
  and its `AdjunctionSquare.transpose` equation fixes every Hom transpose. Thus its
  counit-adjoint `pointProjection` equals the scalar-unit transpose specified in the
  node; no arbitrary isomorphism, comparison, or existence-only choice is substituted.
* Naturality is the final existential natural transformation π, with its component
  on EVERY N constrained to equal that same `pointProjection`. This quantifies the
  packaging of a fixed family, not a free choice of map.
* `NatTrans.CommShift π ℤ` states compatibility with all canonical integer shifts.
  Condensed scalar shifts are obtained directly from the existing scalar adjunction
  and exact restriction, in `condensedExtensionCommShift`; on T they are the existing
  `derivedExtendCommShift`. Point direct images have their total-derived shifts.
* For each distinguished `Triangle Δ`, both mapped triangles are distinguished and
  the existential triangle morphism has components exactly π on its three vertices.
  Its `comm₃` is the connecting-arrow square, which would not follow from ordinary
  naturality alone. This explicitly covers the node's final compatibility clause.

Dependency declarations read and used (modules listed without the common prefix when clear):

* Sheaf.Topology.ContinuousMapCondensedRing:
  Profinite.continuousMapRingObjOfUniverse and its canonical monoid/commutativity instances.
* Sheaf.Paper.CondensedConstantConstructibility:
  AlgebraicGeometry.ProEtale.constantModelBoundedConstructible and
  IsConstantModelConstructible, with their finite-scalar presentation definition.
* Sheaf.Paper.CondensedModuleDerivedPushpull:
  AlgebraicGeometry.ProEtale.CondensedRing.moduleObjectDerivedPullback, defined as
  the generic total left-derived functor of the full underived module pullback.
* Sheaf.Paper.CondensedOpenClosedRecollement:
  CondensedRing.condensed_open_closed_recollement, the exact support functors and
  their bounded-below distinguished triangles.
* WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic:
  coefficientRing, condensedRingObj, upperStarFromPoint and coefficient transport.
* Mathlib.CategoryTheory.Monoidal.Mod: CategoryTheory.Mod and its module actions/morphisms.
* Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions:
  Functor.rightDerivedFunctorOfQuasiIsoResolutions, the recorded total-derived convention.
  The actual point direct images use its already published K-injective specialization.
* WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom:
  CondensedRing.derivedHom, derivedTensor, and the relative K-flat derived monoidal structure.
* Sheaf.NumberTheory.Padics.CoefficientExtensionFinite and its public CoefficientExtension:
  Padic.coefficientExtensionIntegers, the valuation-ring construction.
* Sheaf.Paper.CoefficientHeartStratificationDefs:
  IsLisseCoefficientModule (and upstream Mod.IsFree, explicitly finite rank).
* Sheaf.AlgebraicGeometry.ProEtalePointPullback: sfbPullbackFromPoint and its right adjoint.
* Sheaf.Paper.SupportedLatticeNormProjection: supportedLatticeIntegralRing,
  supportedLatticeNormInclusion, supportedRationalizedLattice, and its isomorphism theorem.
* Sheaf.Paper.CanonicalPointScalarComparison: canonicalPointScalar, uniquely normalized.
* Sheaf.AlgebraicGeometry.FieldActionGeometricTransportData:
  pointProjection and normCoefficients, with the actual canonical-transpose construction.
* Sheaf.AlgebraicGeometry.FieldActionTransportData: derivedExtend,
  condensedDerivedExtend, condensedScalarAdjunction and canonical derived scalar shifts.
* Sheaf.Paper.NormContinuousMonodromyData: normContinuousRing, the all-continuous ring.
* Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent:
  Modules, Coefficients, geometricScheme, geometricProjection and pointModules.

The item retains its original eleven statement dependencies and adds only the two
new definition nodes described below. The six previously appended existing nodes
are removed from its direct stmt_deps. In particular neither enclosing theorem is
a statement prerequisite; lem-sfb-supported-lattice-norm-projection remains in
proof_deps. Existing definition interfaces are reused through their owning nodes;
no dependency module or mathematical definition is reimplemented.
Every recorded proof dependency with a module is imported. Mathlib proof inputs are
imported from FiniteType, Separated, Noetherian, NoetherianSpace and Pretriangulated;
exact derived factorization is already publicly available through the derived framework.

Edge cases checked: empty X, V = 0, empty supports, rank zero, varying local ranks,
nonconnected schemes, arbitrary bounded cohomological interval, every integer shift,
and an incomplete Ω. Triangulated predicates contain zero. Empty/zero input is not
excluded by any nonemptiness hypothesis. No flatness of A to B is assumed. The actual
small pro-etale sites keep object universe u+1 and morphism universe u; module groups
are in u+1 and derived localization is in u+2, consistently with the dependencies.
All variables and universes are explicitly bound; autoImplicit is disabled.

Searches actually run through msearch.py:

* LeanSearch, `Bounded constructible complexes satisfy norm coefficient projection by
  integral lattice generation`: eight hits on ZLattice norm bounds and unrelated
  projections, no match.
* LeanFinder, `Bounded constructible pro etale complexes are generated by supported
  integral lattices and satisfy norm coefficient projection`: eight hits including
  BDeRham, Chevalley, Nobeling and Condensed.profiniteSolid, no matching assertion.
* Loogle, `"DerivedCategory", "Condensed"`: zero hits.
* Mathlib grep, `geometric.*projection|supported.*lattice`: one unrelated graph-subgraph
  bounded-lattice docstring. No matching theorem.
* rg on lean/WeilConjectures and lean/Sheaf for geometric projection/devissage and the
  item id: geometric base changes and the supported-lattice/field-action interfaces
  were found and reused; no combined statement. A literal item-id search in the
  upstream WeilConjectures tree returned no declaration.

No dependency modules or statement correction are needed. The two new metadata-only
definition nodes below own existing helper notions. The helpers in the item module only name the already specified source, target,
canonical shift structure and the existing base-change property instances. The latter
are direct applications of Mathlib `MorphismProperty.pullback_snd` at
LocallyOfFiniteType and QuasiCompact. None introduces an independent notion or a
postponed auxiliary assertion.

## Second reading by Q159

Performed a separate second pass with the node and module open, by this same worker;
no other agent was started, in accordance with the dispatcher's instruction. The
maintainer's independent review remains the delivery review.

Rechecked the primes, characteristic, specified separable closure, finite-type separated
structure morphism, normed incomplete algebraic closure, embedded finite E, and bounded
constant-model input against the binders. Rechecked the first conjunct against Dbc on T;
the universal triangulated predicate against finite cone-and-shift generation with exactly
the constructible supported integral lisse leaves; and IsIso against the actual normalized
pointProjection at the actual total-derived geometric pullback. The final natural
transformation has fixed components for every object, and the triangle-morphism clause
retains the third connecting square. No unmentioned flatness, completeness, chosen
isomorphism of source and target, or nonempty-scheme assumption appears. The compilation
pass prompted an explicit triangle namespace, public base-change imports and direct
use of the second pullback projection, without changing any mathematical clause.

Validation: scompile.py completed with exit 0 for the full delivered module, including
both the sandbox elaboration and library-name artifact compilation, with no errors or
warnings. The explicit base-change instances resolved the only remaining elaboration
fault, without extra hypotheses. Final signature equality, explicit binders, source
docstrings, 100-character line width and the sole requested theorem sorry were checked.


## New nodes

Repair of the independent immutable-head review at 121e7b78597f, point H2:

* `def-sfb-condensed-point-modules-geometric-base-change` owns the existing
  `CondensedGalois.Modules`, `pointAdjunction`, `pointModules`, `Coefficients`,
  `geometricScheme` and `geometricProjection` in
  `Sheaf.AlgebraicGeometry.CondensedGaloisGlobalDescent`. Its `existing: true`
  record binds the primary signature of `pointModules` verbatim. Condensed
  coefficients are commutative ring objects; Modules is exactly the internal
  module category over the pulled-back ring. Point direct image is mapMod
  followed by comap along the actual composite adjunction unit, not an arbitrary
  scalar action. Geometric base change is exactly the specified pullback along
  Spec of the field algebra map, with its first projection. The node owns no
  assertion of condensed Galois global descent.
* `def-sfb-supported-lattice-norm-coefficients` owns the existing
  `supportedLatticeIntegralRing`, `supportedLatticeRationalization`,
  `supportedLatticeNormInclusion`, and `supportedRationalizedLattice` in
  `Sheaf.Paper.SupportedLatticeNormProjection`. Its `existing: true` record binds
  the last signature verbatim. The integral coefficient object is all continuous
  functions into the recorded valuation ring, rationalization and norm inclusion
  are postcomposition with the actual inclusions, and Q is ordinary scalar
  extension of the actual locally closed extension, then the degree-zero derived
  embedding. Its parameters are exactly a prime, a normed Q_ell algebra field,
  finite intermediate E, finite-type K-scheme T, immersion a and arbitrary L0;
  no lisse condition is needed to define Q. The generator specialization in the
  item adds the recorded lisse and constructible-support conditions. This node
  owns no projection-isomorphism theorem.

Both nodes use existing definitions, so no additional Lean module or sorry is
introduced. Their statements cite their exact definition dependencies. The first
is directly cited by the second as well as by the item. The existing fixed
PadicAlgCl integral-model-generator definition is not the same interface as the
arbitrary normed Omega definitions here, so no duplicate mathematical construction
is written. No field except lean and stmt_deps of the existing item is changed;
the current shared base was compared with the retained delivery and all other
fields are preserved verbatim as JSON values. The proof and proof_deps, including
supported lattice norm projection, are unchanged.

Additional searches actually run for these nodes:

* LeanSearch: `internal condensed coefficient modules point direct image and
  geometric base change` gave eight general CondensedMod/base-change hits; none
  gives the specified point module direct image together with this geometric base
  change. LeanFinder: `module objects over a pulled back condensed ring and direct
  image to the condensed point` gave general module/locally constant hits, with
  no exact match.
* LeanSearch: `supported integral lisse lattice rationalization and continuous norm
  coefficient inclusion` gave eight ordinary lattice hits, no exact match.
  LeanFinder: `continuous functions into integral coefficients rationalization
  supported lattice extension by zero` gave eight Mahler/polynomial-function and
  Nobeling hits, no exact match.
* Mathlib grep through msearch for
  `pointModules|geometricScheme|supportedRationalizedLattice|supportedLatticeIntegralRing`
  returned no hit. The exact raw msearch result records are retained in each
  node's mathlib_searches, with the actual query, timestamp and digest.
* The same rg search in lean/WeilConjectures and lean/Sheaf found the existing
  helpers in the two owning modules and their consumers, with no upstream
  alternative. Scanning the definition-node lean.declaration/declarations fields
  found no node owning these exact helpers. blueprint_refs.py searches for
  `geometric sections`, `supported lattice`, `condensed point` and
  `integral generators` found no matching definition unit.

Re-read both existing construction bodies, their signatures and docstrings.
Empty schemes, empty support, zero modules and rank zero are still admitted;
all scalar maps and support functors have real data. The new nodes make no
claim about an isomorphism and add no hypotheses to the accepted item theorem.
The new records are existing bindings, with no copied definition. The item Lean
is byte-for-byte unchanged from the reviewed delivery (SHA256
`a24eafd8477fb4e72aeb036fe78a17c465b8a82dcef52e367ab3fba3bf9d122a`).

## Repair second reading by Q159

Checked H2 against the final JSON: exactly the original eleven statement
prerequisites and two new definition nodes; neither enclosing theorem appears
in stmt_deps; the supported-lattice theorem remains in proof_deps; all six prior
extra direct prerequisites are removed. The two new nodes own exactly the plain
constructions requested by the reviewer and introduce no theorem conclusions.
Reviewed the new node statements against every listed declaration body and its
implicit section parameters. No item statement, Lean source, or proof plan has
changed. No statement is disputed.

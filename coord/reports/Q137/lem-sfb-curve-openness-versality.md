## Worker report

Q137 states `lem-sfb-curve-openness-versality` in
`Sheaf.AlgebraicGeometry.ProperCurveOpennessVersality`, declaration
`AlgebraicGeometry.ProperCurveFamily.exists_open_isVersalAt`.
Its only theorem proof is `sorry`. The new module
`Sheaf.AlgebraicGeometry.ProperCurveVersality` defines the missing Artinian
lifting predicate with real data (a proposition expressed by quantification).
No definitions or proofs in the shared checkout were edited.

The node's mathematical statement, proof and proof dependencies are unchanged.
Its statement dependencies gain the already published
`def-sfb-proper-curve-moduli` and the new definition node
`def-sfb-proper-curve-versality`. The existing family declaration is reused;
there is no dependency repair and no second definition of curve families.

Clause-by-clause match:

- Schemes over Spec Z: `T : Over (Spec (.of (ULift.{u} ℤ)))`. The universe lift
  represents the same integer ring in the universe of the big site. No
  characteristic is fixed.
- U locally of finite type over Z: `[LocallyOfFiniteType T.hom]`. There is no
  quasi-compactness, separatedness or finite-type assumption on all of U.
- The object x of the groupoid C(U): `x : ProperCurveFamily T`. Its `space`
  is the recorded algebraic space, not a scheme or a set of isomorphism classes.
  Its `projection` is a natural transformation to the represented base.
- Flat: `x.isCurve.1`, namely `MapToSchemeIsLocally (@Flat)` on all representable
  etale scheme charts. The project's family predicate uses the recorded
  Mathlib scheme Flat class.
- Proper: in the same `isCurve` conjunction, separatedness is representability
  of the relative diagonal by closed immersions; quasi-compactness is compactness
  of the point space after each affine scheme test; locally finite type is
  tested on etale charts; universal closedness is closedness of point maps after
  every scheme base change. Scheme testing is equivalent to all algebraic-space
  base changes by etale descent of closed subsets. Thus this is the node's
  separated, finite type, universally closed condition.
- Finitely presented: quasi-compactness above, quasi-compact diagonal, and
  `MapToSchemeIsLocally (@LocallyOfFinitePresentation)` in `isCurve`.
- All geometric fibres of dimension at most one: the last clause of `isCurve`
  quantifies over all `Ω : Type u` with `[Field Ω] [IsAlgClosed Ω]` and all maps
  `Spec Ω → T.left`, and bounds `topologicalKrullDim` of the actual presheaf
  fibre product's algebraic-space point space by 1. No dimension equality,
  nonemptiness, connectedness, reducedness or nodality is imposed.
- Arrows and cartesian pullback: the published `ProperCurveModuli.Hom` uses
  precisely `IsPullback` squares of the presheaves. The versality predicate
  uses the same cartesian maps directly; a cartesian map over a fixed base
  map is the specified isomorphism to the fibre product.
- The starting point: `u₀ : T.left` and
  `hft : LocallyOfFiniteType (T.left.fromSpecResidueField u₀)`.
  In Stacks morphisms.tex `definition-finite-type-point`, finite type means
  locally finite type plus quasi-compact. Here the canonical map has a singleton
  source, so every inverse image of an affine open is empty or a singleton,
  hence quasi-compact. Thus the Lean condition is exactly finite type, not a
  stronger closed-point or rational-point requirement.
- Versality at u₀: `hx : x.IsVersalAt u₀` is the lifting condition expanded below.
- The conclusion's open neighbourhood: `∃ V : T.left.Opens, u₀ ∈ V ∧ ...`.
- Every finite type point: `∀ u₁ : T.left, u₁ ∈ V →
  LocallyOfFiniteType (T.left.fromSpecResidueField u₁) → x.IsVersalAt u₁`.
  The conclusion uses versality of x at points in V, as the source's
  definition-openness-versality does. It equals versality of x restricted to V:
  each Artinian local test spectrum has one point, so maps reducing to a point
  of V factor uniquely through V, and the specified cartesian isomorphisms
  are unchanged. This avoids constructing a second restriction interface.

Expansion of each part of the versality definition:

- `A' A : CommRingCat.{u}` with both Artinian and local instances gives exactly
  commutative Artinian local test rings in the big site's universe.
- `q : A' ⟶ A`, `Function.Surjective q.hom`, and
  `IsNilpotent (RingHom.ker q.hom)` express the nilpotent thickening.
- `r : A ⟶ T.left.residueField u₀` with surjective underlying ring map identifies
  A's residue field with κ(u₀), since A is local and the target is a field.
  The composite `q ≫ r` is surjective and identifies A' with the same residue
  field, compatibly with q. Conversely every common-residue-field diagram
  supplies these data. There is no assumption of a field section κ(u₀) → A
  or κ(u₀) → A', so mixed-characteristic tests are retained.
- `s' : Spec A' ⟶ S` and `a : Over.mk (Spec.map q ≫ s') ⟶ T` are the test base
  and the specified S-map Spec A → U. The equation
  `Spec.map r ≫ a.left = T.left.fromSpecResidueField u₀` fixes the reduction,
  including its residue-field map, rather than merely its topological image.
- `Y` is any proper curve family on Spec A'. `Z` is its specified reduction
  on Spec A and `j` with its cartesian square supplies the reduction map.
  `z` with its cartesian square over a is the specified isomorphism of that
  reduction with the pulled-back family x. This is equivalent to giving an
  isomorphism of the two canonical pullbacks: the pullback universal property
  converts either description into the other without losing the isomorphism.
  Y is automatically a deformation of x_u because these cartesian squares
  identify its residue fibre with x_u. No further choice of a marking of that
  residue fibre is needed; every marking compatible with z is retained.
- The witness `b : Over.mk s' ⟶ T` satisfies
  `Spec.map q ≫ b.left = a.left`, so it lifts the original map.
  `w : Y.space.obj.obj ⟶ x.space.obj.obj` with its cartesian square over b
  specifies the required isomorphism of Y with b's pullback of x.
  Finally `j ≫ w = z` is exactly extension of the supplied isomorphism over A.
  It is stronger than merely asking for an arbitrary isomorphism class, as the
  node requires. Changing the chosen representative Z does not change the
  predicate, by the unique pullback isomorphism.

Dependency declarations read and used (including transitive public imports):

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`; the scheme structure and locally ringed space morphisms.
- `def-weil-affine-spectrum`: the same module, `AlgebraicGeometry.Spec` and
  `Spec.map`; these are the actual affine schemes and contravariant ring maps.
- `def-weil-geometric-fibre` and `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`; the published family predicate uses the
  fibre product with every geometric point. Cartesian squares use Mathlib's
  `CategoryTheory.IsPullback`, expressing that same universal property.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`,
  `topologicalKrullDim`, with values in `WithBot ℕ∞` and empty dimension ⊥.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace` (full subcategory of fppf sheaves),
  `AlgebraicSpace.IsRepresentableWith` and `IsEtale`. The full definition and
  its scheme-test and atlas conditions were read.
- `def-weil-size-convention`: metatheoretic convention, not a declaration.
  Explicit `universe u`, `Scheme.{u}`, `CommRingCat.{u}` and the existing
  `Type u` presheaf convention keep test objects in the site's universe.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`,
  `AlgebraicGeometry.Flat`; scheme chart property in the family predicate.
- `def-sbc-locally-finite-presentation`:
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`,
  `AlgebraicGeometry.LocallyOfFinitePresentation`; same use.
- `def-weil-proper-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`,
  `IsSeparated`, `UniversallyClosed`. The family predicate specializes their
  definition to algebraic spaces using representable diagonals and point maps;
  it cannot apply the scheme-only IsProper directly to a space's projection.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType`, and the QuasiCompact class;
  LocallyOfFiniteType appears directly in the theorem and the family predicate.
- Added published dependency `def-sfb-proper-curve-moduli`:
  `Sheaf.AlgebraicGeometry.ProperCurveModuli`, `ProperCurveFamily`,
  `AlgebraicSpace.IsProperCurveFamily`, and its chart, separatedness,
  quasi-compactness and universal closedness predicates. The complete module
  and the node statement and lean record were read before using the interface.
- The new predicate also uses `def-weil-residue-field`:
  `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.residueField` and
  `Scheme.fromSpecResidueField`; the recorded residueField and residueFieldMap
  signatures/docstrings were checked. Mathlib's `IsArtinianRing`, `IsLocalRing`
  and `IsNilpotent` are reused directly, never replaced by private copies.
- Proof-only import: `Sheaf.AlgebraicGeometry.AffineClosedPinchingPushout`,
  `AlgebraicGeometry.isPushout_spec_pullbackCone_of_surjective`.
  The other five proof dependencies had no recorded Lean module in the read
  DAG at preparation, so no invented imports were added. They are unnecessary
  to type this statement. Their precise proof roles remain in the docstring.

Edge cases checked before writing:

- Empty U admits no u₀; the theorem is correctly conditional on a point.
- Empty curve families and zero-dimensional fibres satisfy the existing ≤ 1
  condition, and are not excluded. No stability, smoothness or nodality added.
- q may be the identity (zero kernel is nilpotent); the prescribed map and
  cartesian square themselves solve this test. No nonzero thickening is required.
- A and A' may be fields. No nonzero maximal ideal is required.
- Every characteristic and mixed-characteristic Artinian thickening is allowed.
  Only a residue quotient, not an algebra structure over κ(u), is specified.
- Nontrivial automorphisms of the reduced family are retained: z ranges over
  every cartesian map and `j ≫ w = z` retains the supplied identification.
- Non-quasi-compact locally finite type U is allowed, since there is no
  `[QuasiCompact T.hom]` hypothesis. Finite type points need not be assumed
  rational; the actual residue field of each point is used.
- No independent smaller test-ring universe, no algebraically closed residue
  field assumption, and no restriction on nilpotence exponent is present.

Searches made:

- `msearch.py leanfinder`: “Openness of versality for flat proper finitely
  presented families of algebraic space curves” returned scheme universal
  openness results, including UniversallyOpen.of_flat; none assert versality.
- `msearch.py loogle`: `AlgebraicGeometry.IsVersalAt,
  AlgebraicGeometry.AlgebraicSpace` returned no hits (unknown IsVersalAt).
- `msearch.py grep`: whole-word Versal/IsVersalAt/CurveFamily in
  AlgebraicGeometry returned zero hits.
- `msearch.py leansearch`: Artinian infinitesimal lifting query initially
  rate-limited. A subsequent exact versality query succeeded and returned
  formal-etale/unramified/smooth ring results, not a family versality predicate.
- `msearch.py leanfinder`: the exact versality query returned scheme
  formally-unramified/etale, residue-morphism and local formal-smoothness
  results, not the required moduli lifting condition.
- `msearch.py grep`: whole-word IsVersalAt/Versality/Versal/versal returned
  three unrelated prose hits in Mathlib's cotangent and weak-limit modules.
- `msearch.py leansearch`: finite type point / canonical residue map returned
  Scheme.fromSpecResidueField and its related residue field declarations;
  these are reused. `loogle` with LocallyOfFiniteType and fromSpecResidueField
  returned isClosed_singleton_iff_locallyOfFiniteType (requiring JacobsonSpace)
  and two algebraically closed base lemmas; no extra hypothesis was imported.
- `rg` over `lean/WeilConjectures`, `lean/Sheaf` and upstream-name JSON for
  IsVersalAt, finite type point and curve-family names found ProperCurveModuli
  and no versality definition. The mandated node-id grep in WeilConjectures
  found no declaration. Whole-word versal found only a prose citation.
- DAG definition/title scans and `tools/blueprint_refs.py search versality`
  found no definition node for this notion; the latter returned an unrelated
  universal-property assertion. `blueprint_refs.py ancestor` reports ancestor
  None for this supplemental item, matching the item's recorded blueprint.
- Exact output from the three successful versality-definition searches is
  retained in the new node's mathlib_searches, along with source/DAG searches.

No STATEMENT-DISPUTED issue or source correction was found. The apparently
scheme-only records for properness and geometric fibres are used through the
already published algebraic-space family definition, which supplies the exact
specialization and avoids any dependency repair.

Validation: both delivered files were compiled separately in dependency order
using `scompile.py Q137 lem-sfb-curve-openness-versality <both files>`.
Both compiled with no errors and no unexpected warnings. No global or local
Lake build was run. The dry run and final push results follow from deliver2.py.

## New nodes

`def-sfb-proper-curve-versality`, in the item's chapter and unit, defines
`AlgebraicGeometry.ProperCurveFamily.IsVersalAt` in
`Sheaf.AlgebraicGeometry.ProperCurveVersality`. The source is Stacks artin.tex
`definition-versal` and `equation-hat-x`, with the smooth-morphism lifting
condition of formal-defos.tex specialized to the curve groupoid. Its six
statement dependencies are exactly the ids cited in its self-contained TeX
statement. The LeanSearch, LeanFinder and Mathlib/source/DAG grep checks above
found no reusable predicate. There is no `sorry`, choice from existence, or
unconstrained replacement for a canonical map in the definition.

## Second reading by Q137

I reread the node, the complete proper-family interface, the source definition
of finite type points, artin.tex's versality and openness definitions, and both
delivered modules. Every hypothesis and conclusion clause is matched above.
In particular, I checked the two places where a superficially similar statement
would be wrong: the residue data must be quotient maps rather than chosen
coefficient subfields, and the isomorphism on the reduction must extend
literally, not just up to a freely chosen automorphism. The definition handles
these with surjective r and q and the equality `j ≫ w = z`.

I also checked that using x at points of V is equivalent to using x restricted
to V (one-point Artinian spectra), and that locally finite type of the canonical
residue morphism is finite type because it is automatically quasi-compact.
The added family dependency is already published and its mathematical objects
agree with the entire preamble of the item. The new definition uses those same
objects and no duplicate family construction. No changes were needed on this
second pass; the maintainer's independent delivery review remains required.

## Returned-delivery self-check (2026-10-23)

The required first dry run of the retained packet passed: deliver2.py reported
`OK (dry run): commit 67f5eed99fa passes the preflight and compiles; nothing pushed`.
Both saved Lean files compiled separately against the current server library.
The mathematical statements and definitions are retained without modification.
The delivery wrapper rebases the packet on current sheaf-dag; no direct Git
operation or shared-checkout edit was performed.

The return at immutable head 544cd60ac61b listed five incremental reachability
findings. I checked each against the current read-only DAG and this packet:

- `def-sf-constructible-exceptional-coefficient-construction-data` is absent
  from the current DAG and is not a file of this packet.
- `def-sfb-algebraic-moduli-stack` now has `unreachable` in its `import_flags`;
  its current record is retained and is not a file of this packet.
- `def-sfb-marked-curve-deformations` is absent from the current DAG and is
  not a file of this packet.
- `def-sfb-proper-curve-versality` is explicitly in this packet's item's
  `stmt_deps`. The current graph reaches the item from former target
  `thm-weil-final` (which has `target_former: true`) through
  `thm-weil-final-rh`, `prop-arithmetic-roots`, the smooth-proper purity
  hypotheses, the six-functors package, constructible direct-image stability,
  and its alteration/stable-curve prerequisites, ending in
  `lem-sfb-unpointed-stable-coarse-projective`,
  `lem-sfb-nodal-curve-stack-smooth`, then this item and its new definition.
  Thus the definition is reached under the validator's former-target rule;
  an `unreachable` flag would be incorrect. The item gains precisely the
  existing proper-family dependency and this new definition dependency.
- `def-trf-implicit-transverse-coefficient` is absent from the current DAG
  and is not a file of this packet.

I reread both delivered modules, the complete public proper-curve-family
interface, Stacks quot.tex lemma-curves-defo-thy, artin.tex definition-versal
and definition-openness-versality, and morphisms.tex
 definition-finite-type-point. The saved clause matching remains valid.
Both modules explicitly disable auto-implicit variables, bind their universe,
have no lines over 100 characters, and contain respectively zero and one
`sorry` (the latter is the complete proof of the item's named theorem).
Both node signatures occur verbatim in their recorded modules. No additional
mathematical repair was required by the passing dry run or this self-check.

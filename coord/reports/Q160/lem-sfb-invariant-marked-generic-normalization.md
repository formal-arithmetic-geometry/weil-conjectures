## Worker report

The module `Sheaf.AlgebraicGeometry.InvariantMarkedGenericNormalization` states
`AlgebraicGeometry.exists_invariant_marked_generic_normalization`, with one `sorry`.
Its `InvariantMarkedGenericNormalization.Data` packages the witnesses, not an extra
hypothesis. The three genericTensor helpers construct the actual tensor algebra and
its two standard inclusions. They have real data and no postponed proofs. There are
no new independent notions, dependency repairs, or statement corrections.

Hypotheses and clauses, in the order of the node:

- A field K is `(K : Type u) [Field K]`. A K-scheme is `X : Scheme.{u}` with explicit
  structure map `f`. `[IsIntegral X]` supplies its integral function-field interface;
  `[GeometricallyIntegral f]` is the node's full geometric integrality. Integrality
  follows from that condition over a field, so this spelling restricts no input.
- Properness and finite type are `[IsProper f]`: this includes locally finite type,
  and universal closedness supplies quasi-compactness. `hdim` says exactly
  `topologicalKrullDim X = 1`.
- The marking is `Z : TopologicalSpace.Closeds X`, with `hZ : Z ≠ ⊤`. Bottom is
  allowed, so an empty marking is included. No subscheme structure on Z is assumed.
- H has `[Group H] [Finite H]`, in independent universe v. Its actions are the
  monoid homomorphisms `aK : H →* Aut (Spec (.of K))` and `aX : H →* Aut X`.
  A field action by ring automorphisms corresponds bijectively to this spectrum
  action by sending h to Spec of the inverse ring automorphism. Using the inverse
  corrects contravariance. `hcompat` is the semilinear structural square and
  `hmark` says precisely that every automorphism preserves the closed set.
  There is no faithfulness assumption and no hypothesis that constants are fixed.
- The existential K₀ has Field and Algebra structures. Data.finiteConstants and
  inseparableConstants are `Module.Finite K K₀` and `IsPurelyInseparable K K₀`.
  These are the recorded field-tower notions, with the standard p-power meaning.
  Data.constantsAction and constants_equivariant extend the given action on K.
- Data.N, integral, ν, normalizationIso, normalization_map identify N, over the
  exact chosen base change X_K₀, with that scheme's `reducedNormalization`.
  For this geometrically integral input X_K₀ is integral and reduced, so the
  existing componentwise reduced normalization is canonically the normalization
  of (X_K₀)_red. No arbitrary smooth model replaces that normalization.
- Data.smooth, proper, geometricallyIntegral and dimension assert all four curve
  properties over K₀. Normality is already part of being the specified normalization:
  its local rings are integrally closed domains.
- Data.D and i are a reduced closed immersion with marking_support equal to the
  inverse image of Z under N → X. The reduced induced structure on a closed subset
  is unique, so these conditions express exactly the reduced inverse image.
  finiteMarking and etaleMarking assert finite étale over K₀.
- Data.curveAction, original_equivariant and field_equivariant give the lifted H
  action commuting with both N → X and N → Spec K₀. marking_invariant preserves D.
  An automorphism preserving its support preserves the unique reduced induced
  closed structure, so this includes the asserted scheme-theoretic preservation.
- genericTensor is literally X.functionField ⊗[K] K₀, with the scalar map constructed
  as `Spec.preimage (X.fromSpecFunctionField ≫ f)`. tensorIsField is `IsField` of
  this algebra; genericComparison identifies it with N.functionField.
  generic_original and generic_constants impose the two equations on generic
  spectra for the canonical tensor inclusions. Hence the isomorphism induces
  precisely the embeddings coming from N → X and N → Spec K₀. It cannot be an
  unrelated abstract field isomorphism; the inclusions generate the tensor ring.
- further_extension quantifies over every K'/K₀ and compatible K-algebra tower.
  This does not assume K'/K₀ finite, algebraic or separable. Its e identifies
  N ×_K₀ K' with the chosen reduced normalization of X_K'; both projection
  equations fix that comparison over X and Spec K'. The map j has the two
  projection equations of the base change of i, so is the actual canonical map
  D ×_K₀ K' → N ×_K₀ K'. Its reducedness, closed immersion and support condition
  state that it is the reduced inverse image of Z in the displayed normalization.
- The final clause `∀ [CharZero K], Function.Surjective (algebraMap K K₀)` expresses
  the node's stipulated equality of extensions in characteristic zero. Since a
  field map is injective this is an isomorphism; transporting the displayed data
  along it gives the literal choice K₀ = K. Characteristic p is unrestricted.
- The background sentence about schematic closure introduces no additional
  closure object in this statement; no closure operation is needed for its Lean.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `['Field']`.
- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`, `AlgebraicGeometry.IsProper`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-pc-geometrically-irreducible`: `Mathlib.AlgebraicGeometry.Geometrically.Integral`, `AlgebraicGeometry.GeometricallyIntegral`.
- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`.
- `def-sc-function-field`: `WeilConjectures.AlgebraicGeometry.FunctionField`, `AlgebraicGeometry.Scheme.functionFieldOfComponents`; the integral clause is Mathlib `Scheme.functionField`, as its module explicitly documents.
- `def-pc-field-extension`: `Mathlib.Algebra.Algebra.Defs`, `Algebra`.
- `def-pc-field-tower`: `Sheaf.FieldTheory.FieldTower`, `FieldExtension.degree`; its docstring explicitly delegates finite and purely inseparable extensions to `Module.Finite` and `IsPurelyInseparable`.
- `def-weil-pbc-reduced-normalization`: `Sheaf.AlgebraicGeometry.ReducedNormalization`, `AlgebraicGeometry.Scheme.reducedNormalization`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, `CategoryTheory.Limits.pullback`.

All recorded proof-dependency modules are imported privately. Mathlib proof leaves
are imported from Artinian, UniversallyInjective, Immersion, FinitePresentation,
Flat.Basic, PerfectClosure and AlgebraicClosure. Four proof nodes have no Lean
record yet and therefore have no import: lem-sfb-finite-georeduced-etale,
lem-sfb-finite-normalization-model-functoriality,
lem-sfb-flat-curve-pullback-function-field,
lem-sfb-integral-closure-geonormal-scalar-extension. They are proof prerequisites,
not missing definitions needed to type this statement. The complete eight-step
DAG proof, including its cited node ids, is in the theorem's docstring.

Sources read: Stacks varieties.tex, finite-extension-geometrically-normal
(0BXT), finite-extension-geometrically-reduced (04KT) and
normalization-and-change-of-fields (0C3N); the current blueprint's direct-images
proof (3). The assertion is the agent-written assembly in the node, not a claim
that de Jong gives all of these clauses as one printed lemma.

Edge cases checked before writing: Z = ∅ (D and every further marking may be
empty); trivial/nonfaithful H; nontrivial action on constants; K₀ = K;
characteristic zero; arbitrary positive characteristic; identity further extension;
inseparable, separable and transcendental further extensions. The empty curve is
already excluded by the node's geometric integrality and dimension one, while
an empty marking is never excluded. Same-universe field extensions are the usual
size convention for Scheme.{u}; u is arbitrary. All variables and universes are
explicitly bound. No disputed statement or node fault was found.

Searches for an existing statement:

- msearch.py leanfinder, query: “A proper geometrically integral curve with a finite
  semilinear group action has invariant finite purely inseparable constants with
  smooth normalization and finite etale marking”. Eight hits concerning invariant
  integral extensions and fraction fields (IsArithFrobAt.exists_of_isInvariant,
  IsGaloisGroup.iff_isFractionRing, Algebra.IsInvariant.isIntegral, etc.); none
  constructs this equivariant normalization or supplies its marking/base changes.
- msearch.py loogle, `IsPurelyInseparable, AlgebraicGeometry.Smooth`: zero hits.
- msearch.py grep, `normalization|PurelyInseparable`, AlgebraicGeometry: fourteen
  hits in ZariskisMainTheorem, UniversallyInjective and Normalization; relative
  normalization exists but not this smooth marked semilinear construction.
- rg in lean/WeilConjectures and lean/Sheaf for semilinear/markedGeneric/
  reducedInverseImage, and for invariant-normalization in either order: only
  unrelated linear/derived normalization statements. Search by the exact node id
  in lean/WeilConjectures found nothing. dag/lean_names_upstream.json was checked
  for normalization names. FunctionField, ReducedNormalization and FieldTower
  were opened rather than replaced by duplicate definitions.

Validation: scompile.py compiled both sandbox and intended library module cleanly,
with no warnings or errors. A first compiler pass exposed missing tensor notation
scope, tensor-inclusion inference and one extra closing parenthesis; these were
repaired before the clean compile. The only postponed proof is the main theorem.

## Second reading by Q160

No independent worker reading is claimed. Per the dispatcher brief, this worker
delivers directly; the maintainer performs the independent review. A self-check
matched each clause above to the node and file, including both generic spectrum
equations and both projections for the further marking comparison.

## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.space_relative_spec_correspondence`
in `Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativeSpecCorrespondence`. Its proof is `sorry`.
The original mathematical statement, proof, and proof dependency list are unchanged.
The statement dependency list gains the new algebra-sheaf definition node and the already
landed `def-sfb-space-morphism-properties`, whose chart-local finite-presentation and
quasi-compactness interfaces are used verbatim. No dependency record is replaced.

Hypotheses and clauses, in the order of the node:

- A scheme S and an algebraic space X over S: `S : Scheme.{u}` and
  `X : AlgebraicSpace S`, with the existing full subcategory of fppf sheaves.
  The theorem chooses the correspondence simultaneously for every X so that its
  base-change clause uses that same family, including identity base changes.
- Size convention: explicit universe `u`; schemes and ring/module carriers remain in
  u and small-etale-site objects in u+1. No new essential-smallness, nonemptiness,
  atlas, separatedness, flatness, or universe-equality hypothesis is imposed.
- QCAlg(X) consists of commutative algebra sheaves on X_et: `CommAlgebraSheaf X`
  is `Under X.commStructureSheaf`. Its arrows are exactly algebra maps.
  `CommAlgebraSheaf.toModule` restricts the unit module along the structure map.
  `QCAlg X` is the full subcategory for the dependency's Mathlib
  `SheafOfModules.IsQuasicoherent` predicate, using its existing slice instances.
- Integral, finite, and finitely presented algebras: respectively
  `CommAlgebraSheaf.IsIntegral`, `.IsFinite`, and `.IsFinitePresentation` quantify over
  EVERY `V : X.EtaleSite` with `IsAffine (X.etaleForget.obj V)` and apply the ring-map
  predicates to `(A.hom.hom.app (op V)).hom`. RingHom finite presentation is the
  finitely generated polynomial algebra quotient predicate; it is not module finite
  presentation. No chart is required to be surjective.
- Spaces affine over X: `AffineOver X` is the full subcategory of `Over X` defined by
  `IsRepresentableWith (fun _ _ p => IsAffineHom p.left)` of the underlying map.
  Finite and integral morphisms use the same scheme-test definition with `IsFinite`
  and `IsIntegralHom`. These are the recorded Mathlib scheme predicates.
- Finite presentation of the affine morphism is the triple in
  `RelativeSpecData.finitePresentation_iff`: `MapIsQuasiCompact` of the morphism,
  `MapIsQuasiCompact` of its relative diagonal, and the existing
  `MapIsLocallyOfFinitePresentation` (all compatible etale scheme-chart tests).
- Anti-equivalence: `RelativeSpecData.equivalence : (AffineOver X)ᵒᵖ ≌ X.QCAlg`.
  Its object values are identified with `directImage` by `directImageIso`.
  `StructureAlgebraModel.underlying` is an isomorphism to the EXACT existing
  `moduleDirectImage f` of `SheafOfModules.unit Z.structureSheaf`.
  Its ring projections equal EVERY specified chart-limit projection after this iso;
  `projection_structure` fixes pullback of regular functions. Thus the algebra really
  has sections Γ(Z ×_X V,O), including its ring operations, rather than being an
  arbitrary quasi-coherent algebra equivalent to it. The dependency's limit is
  precisely compatible regular functions on charts of this fibre product.
- On arrows, `RelativeSpecData.map_projection` says that the equivalence's map is
  pullback of functions on every compatible chart pair. The two triangle equations
  specify the map over Z and the map over V; there is no arbitrary Hom bijection.
- Inverse relative Spec: `RelativeSpecData.relativeSpec` is the inverse equivalence,
  unopped. `counitAlgebra` is the equivalence counit followed by `directImageIso`,
  giving A ≅ q_*O for precisely that inverse object.
- Affine etale chart formula: `chartMap` is the canonical map into Spec(A(V)), built
  from that counit, the ring restriction projection, and `Scheme.toSpecΓ`.
  `HasChartFormula` asserts it is an isomorphism for every chart representing the
  fibre product. Such charts exist by the affineness already built into the inverse
  object, and their maps to the relative spectrum are etale since V -> X is etale.
  The chart comparison is over V because `projection_structure` gives its structure
  ring-map equation. Its second conjunct says an algebra arrow φ induces
  `Spec.map (φ.hom.right.hom.app (op V))`, with the correct reversed direction.
- Arbitrary base change: the theorem quantifies over ALL `g : X' ⟶ X` and A, produces
  a quasi-coherent algebra B and an iso e of its underlying module with the EXISTING
  `(moduleTensorPullback g).obj A.obj.toModule`. `IsTensorAlgebraPullback` fixes its
  unit and multiplication on the actual `moduleTensorSection` tensors. Linearity of
  e then fixes its O_X' structure map too. Thus B is tensor pullback as an algebra.
  The unique h satisfying `IsRelativeSpecBaseChangeArrow` has the cartesian square
  with g and the two inverse-equivalence spectra, and on every compatible chart it
  sends b tensor s to b times the pullback of s. This normalization fixes the
  comparison, hence its compatibility with algebra arrows and successive base
  changes by uniqueness, including identity and arbitrary choices of tensor models.
- Property preservation in both directions: `integral_iff`, `finite_iff`, and
  `finitePresentation_iff` in the SAME `RelativeSpecData` use the direct-image algebra,
  not an unrelated ring. The counit carries these tests to any input A.

Definitions have real data. The supporting theorem
`commStructurePresheaf_isSheaf` has `sorry`, a source/proof docstring and is explicitly
part of the new definition node's regular-functions sheaf assertion. The main theorem
has the complete eight-step natural-language proof in its docstring. No theorem is proved.

Dependency declarations read and reused:

- Mathlib.AlgebraicGeometry.Scheme: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- Sheaf.AlgebraicGeometry.AlgebraicSpace: `AlgebraicSpace`, `IsRepresentableWith`,
  `IsEtale`, `EtaleSite`, `etaleForget`, `structureSheaf`, and `Modules`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule: `QCoh` and the existing
  slice sheafification/locally-bijective instances, with Mathlib's
  `SheafOfModules.IsQuasicoherent`, unchanged.
- Mathlib.AlgebraicGeometry.Morphisms.Affine: `IsAffineHom`.
- Mathlib.AlgebraicGeometry.Morphisms.Finite and Integral: `IsFinite`, `IsIntegralHom`.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation: `LocallyOfFinitePresentation`.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations: `ModuleChart`,
  `moduleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`, and
  `moduleTensorSection`; their full signatures and normalization docstrings were read.
- Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties:
  `MapIsLocallyOfFinitePresentation`, with its `MapIsLocally` chart test;
  its imported ProperCurveModuli interface supplies `MapIsQuasiCompact`.
- Sheaf.CategoryTheory.CochainCoefficientUniverseTransport:
  `SheafOfModules.CochainUniverseTransport.liftedRingForgetHasSheafCompose` supports
  forgetting commutativity on this large-object/small-coefficient site. An explicit
  public import was required: the algebraic-space module's private proof import does
  not expose this general sheaf-composition instance to consumers.
- def-weil-size-convention is metatheoretic, so has no declaration to import.

The module imports every available recorded proof-dependency module, with plain imports.
The already imported Mathlib Affine/Finite/Integral/FinitePresentation/Separated modules
also supply the mathlib-match proof dependencies (affine-cover criteria, locality,
permanence and finitePresentation_appLE). The proof-only nodes currently without Lean
records are not restated: lem-sfb-space-qcoh-groupoid-equivalence,
lem-sfb-space-affine-locality, lem-sfb-space-integral-finite-etale-locality,
and lem-sfb-space-local-properties-chart-test. They are only used in the postponed
natural-language proof, not to define any statement object.

Edge cases checked before writing and on rereading:

- Empty X, empty atlas and zero algebra are allowed. The zero algebra's spectrum is
  empty; there is no Nonempty, nonzero-ring, or nonempty-chart binder.
- O_X corresponds to the identity, and identity base change is included.
- A polynomial algebra k[T] is algebra-finitely-presented but not module-finite;
  the two tests are explicitly different.
- An infinite integral field extension satisfies the integral test without being
  finite; no finiteness conclusion is extracted from integrality.
- Finite algebras over a non-coherent ring need not have finite algebra presentation;
  no implication between the two fields is asserted.
- The chart tests include non-surjective affine etale charts. Arbitrary g need not
  be etale, affine, flat, representable or surjective.
- No equality of site object, site arrow, or coefficient universes is added.

Searches: `msearch.py` LeanFinder queried "Relative Spec anti equivalence affine
algebraic spaces quasi coherent algebras": eight scheme-Spec/affine-scheme hits, no
algebraic-space correspondence. Loogle `"relativeSpec"`: zero hits. Mathlib grep
`AlgebraicSpace|relativeSpec.*[Ee]quiv|[Ee]quiv.*relativeSpec` in AlgebraicGeometry:
zero hits. LeanSearch "Sheaves of commutative algebras on a ringed site underlying
module": eight generic scheme/module/sheaf hits. LeanFinder "Quasi coherent
commutative algebra sheaves on an algebraic space small etale site": eight generic
quasi-coherent module hits. Mathlib grep `CommAlgebraSheaf|QCAlg|AlgebraicSpace`:
zero hits. Raw response records are retained in the new node's mathlib_searches.
Local rg of `lean/WeilConjectures` and `lean/Sheaf` found scheme/Zariski algebra sheaves
but no small-etale algebraic-space algebra sheaf; the blueprint-id search in
WeilConjectures had no hit. DAG grep and `tools/blueprint_refs.py search` found no
existing definition node for this notion. The stack big-fppf algebra node is a
different site and cannot replace the small-etale notion without a site comparison.
`CategoryTheory.commAlgebraSheafModule` is specialized to topological spaces, so its
signature also cannot be applied to X_et.

No statement dispute, counterexample, statement correction, or dependency repair.

## New nodes

`def-sfb-space-quasi-coherent-algebra` defines the missing small-etale commutative
algebra sheaves and their underlying modules, QCAlg, and its three affine-chart ring
properties in `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra`. It is based
on the existing space structure presheaf, Mathlib's Under category and restriction of
scalars, and the dependency's quasi-coherence predicate. Source: Stacks 081V/081W,
03G7, 03ZQ and 0410. The searches above and the raw responses in the node show why
neither scheme/Zariski algebra sheaves nor stack big-fppf algebra sheaves is the same
notion. The named supporting sheaf-condition theorem states the regular-functions
assertion in this node; only its proof is postponed. The module carries no second
module quasi-coherence definition and no choices of arbitrary algebra structures.

## Second reading by Q44

The dispatcher brief prohibits starting other agents and assigns independent review to
the maintainer. This section records my second pass with both the node and Lean files
open; it does not claim an independent worker read.

I checked every clause against the mapping above. The ring maps for the three tests
are structure maps on every affine etale object. I checked opposition twice: an
algebra map A -> B induces the morphism Spec B -> Spec A and the chart formula uses
Spec.map of precisely the component of that same map. I checked that the direct image
uses all existing module projections, so its algebra structure is determined. I
checked the arbitrary-base-change equation and pure tensor normalization against the
source's last sentence, and the use of the dependency's actual adjunction unit in
moduleTensorSection. I checked that finite presentation uses a quasi-compact relative
diagonal, not an absolute diagonal or module-finite-presentation condition.

The first compiler passes found that a private proof import did not expose the small
coefficient sheaf-composition instance and that Lean needed ring-typed annotations for
the underlying module's unit/product expressions. The explicit public import, explicit
universe arguments, and `@id` ring casts repair elaboration without changing the site,
coefficients or statement. No notation, private definition or local instance is used.

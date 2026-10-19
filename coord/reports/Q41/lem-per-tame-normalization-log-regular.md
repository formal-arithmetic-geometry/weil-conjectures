## Worker report

This is the stage-2 statement of `lem-per-tame-normalization-log-regular`, not a new
stage-1 split. The Q73 merge supplied the reviewed six-step DAG proof and three smaller
logarithmic statement nodes; it supplied no Lean statement for this item. No repair note
exists at `coord/repair-notes/lem-per-tame-normalization-log-regular.json`.

The delivery adds `lean/Sheaf/AlgebraicGeometry/TameNormalizationLogRegular.lean`, with
`AlgebraicGeometry.Scheme.tame_normalization_log_regular`, whose entire proof is `sorry`.
The item's JSON changes only in `lean`. No definitions or dependency records change.
No new nodes and no dependency modules are needed. No statement correction or dispute.

Source read: the local PDF `literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`,
Exposé IX Proposition 2.1(i)--(iii), proof and paragraph 2.2, printed pp. 133--134;
Exposé VI 1.1--1.8 and 2.1--2.3, printed pp. 69--73. IX 2.1 extends tame covers of the
regular strict-normal-crossings complement to Kummer étale covers on their normalization;
IX 2.2 concludes that the normalization and inverse-image boundary form a log regular
pair. VI 2.3 explicitly gives log regularity of the source over a log regular target.
The invertible-order torsor in this node is a special case of the tame cover input.

### Every hypothesis

* `Y : Scheme.{u}`, `[IsIntegral Y]`: the integral base scheme. The Mathlib class includes
  nonemptiness and domain section rings on every nonempty open, agreeing with the node.
* `[IsNoetherian Y]`: Noetherian scheme, including local Noetherianity and quasi-compactness.
* `hExcellent : ∀ W : Y.affineOpens, IsExcellent Γ(Y, W)`: excellence on all affine coordinate
  rings, using the recorded excellent-ring definition, without a finite-type-over-field
  restriction or a restriction to stalkwise excellence.
* `hRegular : IsRegularScheme Y`: the recorded scheme predicate, local Noetherianity and
  regularity at every stalk, including mixed characteristic.
* `T : Y.IdealSheafData`, `hT : IsStrictNormalCrossingsBoundary T`: exactly the recorded
  effective Cartier, reduced, finite regular-component and regular-intersection boundary
  notion. Its `support.compl` is the node's open V; the empty boundary is permitted.
* `G : Type v`, `[Group G]`, `[Finite G]`: an arbitrary finite group, with universe v
  independent of the scheme universe u. No enumeration or additional group property.
* `hG : IsUnit (Nat.card G : Γ(Y, ⊤))`: order invertible on Y. An integer is a unit globally
  if and only if it is a unit locally everywhere; local inverses glue uniquely, so this
  does not restrict the intended scheme-theoretic invertibility hypothesis.
* `C : Scheme.GaloisCoverAction G (Scheme.Opens.toScheme T.support.compl)`: the recorded
  Galois-cover/torsor declaration. Its total space is `C.Z`, its map is `C.π`, and its
  fields state finiteness, étaleness, surjectivity, action over V, action laws, simple
  transitivity on geometric fibres and the scheme quotient. This uses the node's own
  dependency interface, not a second torsor definition. For a finite étale torsor these
  quotient and action clauses are the same Galois-cover notion in the dependency node.
* `[ConnectedSpace C.Z]`: connected cover V'. `ConnectedSpace` includes nonemptiness;
  that is already forced here by the torsor over V, since the Cartier boundary misses
  the generic point of the nonempty integral base.

### Every conclusion and the objects used

* `∃ (_ : IsIntegral C.Z)`: exposes the derived integral structure of the connected normal
  cover, so that its actual function field `C.Z.functionField` can be used. This is a
  consequence in the statement, not an added integral-cover hypothesis.
* `∃ (_ : Algebra Y.functionField C.Z.functionField)`, followed by
  `Y.fromSpecOfAlgebraFunctionField C.Z.functionField =
  C.Z.fromSpecFunctionField ≫ C.π ≫ Scheme.Opens.ι T.support.compl`: specifies exactly the
  function-field extension induced by the cover. It does not quantify over an arbitrary
  unconstrained extension. For fields, equality of the resulting generic morphisms
  determines the field map. This dependent existential is the same presentation used
  by the existing `normalizationIn_functionField_extends_cover` interface; no object is
  selected from an unrelated mere existence theorem.
* `Y.normalizationIn C.Z.functionField` and `Y.fromNormalizationIn C.Z.functionField`:
  the dependency's real normalization in that extension field and its canonical map.
  Its source code identifies this with gluing the integral closures of affine coordinate
  rings in the extension. The original function-field normalization is not substituted.
* `IsFinite (Y.fromNormalizationIn C.Z.functionField)`: b is finite.
* `IsIntegral (Y.normalizationIn C.Z.functionField)`: Y' is integral.
* `∀ W : (Y.normalizationIn C.Z.functionField).affineOpens,
  IsExcellent Γ(Y.normalizationIn C.Z.functionField, W)`: Y' is excellent.
* `∃ (_ : IsNoetherian (Y.normalizationIn C.Z.functionField))`: Y' is Noetherian. Its
  witness supplies the local-Noetherian instance required by the recorded pair predicate;
  this is why this conclusion is dependent rather than an ordinary separate conjunct.
* `hU : DenseRange (Scheme.Opens.ι
  ((Y.fromNormalizationIn C.Z.functionField) ⁻¹ᵁ T.support.compl))`: the dense open
  complement needed by the definition of a log regular pair. The open is the actual
  inverse image of Y minus |T|, and hence its closed complement is exactly b⁻¹|T|.
* `IsDivisorialFineSaturatedLogRegularPair` applied to this normalization, this open
  subscheme and this inclusion: precisely (Y', b⁻¹|T|) is log regular. The dependency
  predicate contains the small-étale divisorial sheaf, fs charts, exact triviality locus,
  regular strict-local quotient and characteristic-group rank dimension formula.
  No arbitrary log structure or a weaker ordinary regularity assertion replaces it.

### Dependency declarations read and used

I opened every statement dependency's full node and its recorded declaration/docstring:

* `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
* `Sheaf.RingTheory.ExcellentRing`: `IsExcellent` and the definitions it unfolds to.
* `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
* `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`; scheme Noetherianity is
  `AlgebraicGeometry.IsNoetherian` in `Mathlib.AlgebraicGeometry.Noetherian`.
* `Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary`:
  `AlgebraicGeometry.IsStrictNormalCrossingsBoundary`.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`, carried in C.
* `Sheaf.AlgebraicGeometry.NormalScheme`: `AlgebraicGeometry.Scheme.GaloisCoverAction`.
  The other notions of that dependency are not redefined or unnecessarily assumed.
* `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `AlgebraicGeometry.Scheme.normalizationIn`, `fromNormalizationIn`, and
  `fromSpecOfAlgebraFunctionField`. Read the entire finite-extension definition section.
* `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
* `Sheaf.AlgebraicGeometry.LogRegularPair`:
  `AlgebraicGeometry.IsDivisorialFineSaturatedLogRegularPair`; read its divisorial
  constructions, chart definitions and strict-local rank/dimension clause.

The statement modules publicly import the dependencies that expose these declarations.
All already stated proof dependencies are available by proof-only imports:
`RegularNormalDecomposition.regular_normal_and_normal_decomposition` (namespace
`AlgebraicGeometry`), `EtaleNormalComponents.Etale.exists_clopen_normal_integral_components`,
`UnramifiedFieldFibreDecomposition.unramified_iff_exists_iso_coproduct_spec_finite_separable`,
`FiniteEtaleDescentDataExistence.finiteEtaleDescent_data`,
`IsExcellentFiniteTypeLocalization.isExcellent_finiteType_localization`,
`LogRegularDivisorialStructure.logRegular_divisorialStructure`, and
`WeilPbcNormalizationInResidueFieldExtension.normalization_in_finite_residue_field_extension`.
Here the capitalized prefixes identify their modules, not extra Lean namespaces.
I read the missing-local-checkout normalization-residue module using
`scompile.py --source WeilConjectures.AlgebraicGeometry.WeilPbcNormalizationInResidueFieldExtension`.
Mathlib's `IsIntegralClosure.finite` is imported from
`Mathlib.RingTheory.DedekindDomain.IntegralClosure`; finite-type Noetherian permanence
is already available from `Mathlib.AlgebraicGeometry.Noetherian`.

Three proof-only nodes have no Lean declaration yet:
`lem-per-regular-boundary-divisorial-chart`,
`lem-per-prime-to-order-snc-kummer-charts`,
`lem-per-invertible-kummer-chart-log-regular`. They are used only in the proof plan,
not to define anything in this signature, so no missing statement notion is hidden and
no module is invented for them in this delivery. Their later statements can be imported
by the maintainer under the stage-2 proof-dependency import rule. The theorem docstring
contains all six original proof steps with the relevant node names.

### Searches performed

All remote search calls used the prescribed msearch.py wrapper for Q41 and this item:

* LeanFinder: `Normalization of a regular excellent scheme in a finite etale torsor of
  invertible order is log regular`: 8 ordinary normalization hits, including
  `Scheme.Hom.normalization`, `instIsIntegralNormalization`, `instIsReducedNormalization`,
  `normalizationDesc`, `toNormalization`, `instIsIntegralHomFromNormalization`,
  `normalizationDiagram`, `normalization.hom_ext`. None states the logarithmic theorem.
* Loogle: `AlgebraicGeometry.Scheme.normalizationIn,
  AlgebraicGeometry.IsStrictNormalCrossingsBoundary,
  AlgebraicGeometry.IsDivisorialFineSaturatedLogRegularPair`: 0 hits, with the explicit
  note `unknown identifier 'AlgebraicGeometry.Scheme.normalizationIn'`. These are project
  declarations, not indexed Mathlib declarations; I read their source directly.
* Mathlib grep: `LogRegular|log.regular|[Tt]ame.*[Nn]ormalization|[Nn]ormalization.*[Tt]ame`
  in `AlgebraicGeometry`: 0 hits.
* LeanSearch: `The normalization of a regular scheme along a strict normal crossings
  divisor under a tame finite cover is log regular`: 8 ordinary normalization hits,
  including `normalizationDesc`, `toNormalization`, `instIsIsoToNormalizationOfIsIntegralHom`,
  `normalization`, `ι_toNormalization_assoc`, `toNormalization_normalizationDesc`,
  `normalizationDesc.congr_simp`, `instIsIntegralNormalization`. No log-regular match.
* Direct rg/grep searches of the read-only upstream `WeilConjectures` and side `lean/Sheaf`
  trees by the item id, `LogRegular`, `log.regular`, `Kummer`, `tame`,
  `tame_normalization`, `normalization.*log_regular`, `log_regular.*normalization` found
  the recorded definitions, the strict-henselian one-divisor tame normalization module,
  and proof tools; no theorem for an arbitrary regular excellent SNC pair.
* Exact-id searches in the DAG and coordination reports located Q73's already reviewed
  split. That report explicitly records that no Lean statement was supplied. Searching
  existing function-field-normalization users found `NormalizationExtendsCover`, which
  supplies an applicable dependent-existential pattern but assumes finite type over a
  field and concludes extension over an open, not this theorem. It is not duplicated.

### Edge cases and validation

Empty boundary: `support.compl = ⊤`; neither the signature nor its boundary predicate
requires a component, a positive rank, or nonempty closed support. The pullback open is
all of the normalization and the log regular pair is the trivial-boundary pair.
Identity torsor/trivial group: `Nat.card G = 1` is invertible, and connectedness allows
this cover. No nontrivial ramification assumption appears.
One tame root t=sⁿ with n invertible: the conclusion is log regularity, and the proof
plan allows finite torsion group cokernel. Two crossing branches, such as zⁿ=xy, need
not have a regular normalization; ordinary regularity is deliberately not a conclusion.
The zero-dimensional field base, arithmetic regular traits and mixed-characteristic
regular bases are included. Integral Y excludes the empty base exactly as the node does;
there is no new nonempty-open hypothesis. Dropping invertibility would allow wild
ramification and is not asserted. Scheme universe u and finite-group universe v are
explicit and independent.

`scompile.py Q41 lem-per-tame-normalization-log-regular
lean/Sheaf/AlgebraicGeometry/TameNormalizationLogRegular.lean` succeeded in both sandbox
mode (3.0 s) and library import mode (2.4 s), with no diagnostics. An earlier elaboration
attempt exposed field-notation ambiguity for `T.support.compl`; using the explicit
`Scheme.Opens.toScheme` and `Scheme.Opens.ι` names fixed it without changing the objects.
Every universe and variable is explicitly bound, no local notation or instance is added,
there are no let/have binders in the signature, and every line is at most 100 characters.

## Second reading by Q41

I reread the node, the source places and the complete Lean file after the clean compile.
This is the dispatcher-authorized direct-delivery self-check; no second worker or
independent review is claimed. The maintainer supplies the independent review.

The base hypotheses match: integral and Noetherian instances; excellence on all affine
opens; the exact recorded regular-scheme predicate; the exact recorded SNC predicate,
including the empty family. The finite group is not restricted in universe or structure.
Its order is a global unit, the equivalent form of invertibility on every point. The
cover uses the recorded `GaloisCoverAction` fields for finite étaleness and simple
transitivity, over precisely the specified complement, and `ConnectedSpace` supplies the
stated connectedness and the already implied nonemptiness.

I checked the two dependent existentials carefully: cover integrality is concluded,
not assumed, and the function-field algebra is constrained by the generic-morphism
equality. Thus the normalization uses the cover's induced extension, rather than the
original field or an arbitrary algebra map. The explicit finite/integral/excellent
clauses and the dependent Noetherian witness give every property of b and Y' in the node.
The final pair uses the inverse-image open and its literal inclusion; the complement is
b⁻¹|T|. Density and local Noetherianity supply only premises of that exact pair predicate,
not additional assumptions on the input. I checked that regularity of the underlying
normalization and étaleness of b have not been inserted as conclusions.

No mathematical mismatch was found and no node statement was changed. The only edit
during elaboration was resolving the open-subscheme field notation explicitly. I checked
all proof-only imports against the recorded proof dependencies; the three unstated
logarithmic nodes are listed above instead of being silently replaced by stronger or
unrelated assumptions. No new node or dependency repair is present.

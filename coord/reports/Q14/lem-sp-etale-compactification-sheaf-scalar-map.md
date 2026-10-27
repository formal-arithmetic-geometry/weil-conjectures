## Worker report

The module `Sheaf.EtaleCohomology.Purity.Smooth.EtaleCompactificationSheafScalarMap`
states `AlgebraicGeometry.Etale.etaleCompactificationSheafScalarMap`, with its entire
proof postponed. No definition contains postponed data. The three helpers are part of
this node's specified construction: `compactificationOrdinaryScalarMate` is the ordinary
geometric counit mate, `compactificationCoefficientPullbackIso` is the canonical
constant-coefficient inverse-image identification, and
`compactificationScalarTensorSection` is the image of a local pure tensor under the
existing balancing map. They are listed in `lean.declarations` and have source docstrings.

Hypothesis and clause correspondence:

- Schemes U,V are `Scheme.{u}`. Noetherianity (finite affine covers by Noetherian
  rings) is `[IsLocallyNoetherian U] [CompactSpace U]` and the analogous V instances.
  This is the same encoding used by the normalization dependency.
- A separated étale finite-type e is `(e : U ⟶ V) [Etale e] [IsSeparated e]
  [LocallyOfFiniteType e] [QuasiCompact e]`. There is no flatness assumption on
  coefficients or modules. Finite type is local finite type plus quasi-compactness.
- `(c : Compactification e)` supplies W as `c.Z`, j as `c.i`, r as `c.g`, the
  factorization `c.comm`, and the open/proper instances. No compactification is chosen
  by a mere existence theorem.
- Finite commutative unital coefficients are `{A B : Type (u + 1)} [CommRing A]
  [CommRing B] [Finite A] [Finite B] (φ : A →+* B)`. Module sheaves are arbitrary
  `Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)`; they are not assumed locally
  constant, finite, constructible, or flat.
- Ordinary scalar extension is `ProEtale.etaleSheafExtendScalars φ T`, the existing
  sheafification of sectionwise extension of scalars. Its conventional B tensor M
  orientation is identified with M tensor B by the existing `scalarSheafTensorMap`.
  Every tensor in this statement is an ordinary tensor; no derived object occurs.
- The degree-zero comparisons νA and νB are natural isomorphisms with exactly the
  source `openImmersionLowerShriek ... c.i ⋙ lowerStar ... c.g` and the target
  `etaleLowerShriek ... e inferInstance`. Their inverse equations fix them to
  `etaleCompactificationGraphMap A e c` and its B analogue. This is the explicit
  extension-by-zero graph normalization used by the dependency, and fixes the
  sheet-component direction of ν. The existential isomorphisms are normalized,
  rather than arbitrary comparison data.
- C = j!M is inserted directly as the argument of
  `compactificationOrdinaryScalarMate φ c.g`. This helper uses `mateEquiv` on the
  ordinary A and B inverse/direct-image adjunctions and the forward
  `scalarSheafPullbackIso`. Its transpose is precisely that comparison followed by
  scalar extension of the A counit, so it is the specified pi_C.
- `openScalarExtensionZero φ c.i` is the existing canonical ordinary open/scalar
  isomorphism o_M. Its adjoint-uniqueness construction fixes the restriction to the
  identity. It is not replaced by a chosen isomorphism.
- The first conjunct is exactly scalar extension of νA inverse, then pi_C, then
  `lowerStar B c.g` of o_M, then νB, equal to `ρ.app M`. Lean composition `≫`
  runs left to right, so this has the displayed node's order.
- Rho has the B-valued natural-transformation type
  `etaleLowerShriek A e ⋙ extendScalars φ V ⟶ extendScalars φ U ⋙ etaleLowerShriek B e`.
  Its components are therefore B-linear sheaf morphisms. Its natural-transformation
  naturality is exactly naturality in every module map M → M'; each component is a
  sheaf morphism, so it commutes with every étale restriction.
- A test object on U, `S : U.Etale`, records a test scheme over V together with its
  lift s. Its V-test object is `(MorphismProperty.Over.map ⊤ inferInstance).obj S`.
  The section x is in M(S,s), and `etaleSumSection` inserts it into the actual
  lift-indexed Kan-extension/sheafification generator.
- The last clause fixes rho on every pure tensor of every individual lift generator.
  This is the finite-sum formula by additivity: a finite-support family is a finite
  sum of its single-lift insertions, and tensoring and every displayed map are
  additive. Tensor sheafification uniqueness extends the formula to all sections.
- The binder b is a section of `scalarCoefficientSheaf φ V` at the V-test object;
  it is NOT restricted to a ring element b : B. This sheaf is B_V with its A-action.
  `etaleLiftSection` pulls b back by the inverse-image unit and restricts along the
  same lift; `compactificationCoefficientPullbackIso` identifies it with B_U.
  Thus the right side is exactly the same lift with x tensor b_s.

Dependency declarations read and used (public imports are statement interfaces;
ordinary imports are proof-plan inputs):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, via the standard
  `IsLocallyNoetherian` scheme interface and quasi-compactness.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, `QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`, `IsSeparated`.
- `WeilConjectures.Compactification.RefinementCategory`: `Compactification`, with its
  data/signature read in `WeilConjectures.Compactification.Defs`; refinements are not
  an extra hypothesis of this node.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the existing `Sheaf`/`ModuleCat`
  small-étale encoding; no second constant module-sheaf category is introduced.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, the ring-sheaf tensor interface;
  constant-coefficient calculations use the existing equivalent ModuleCat-valued
  sheaf tensor `etaleSheafTensor` and its local tensor pairing.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `openImmersionLowerShriek`, its ordinary adjunction.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `lowerStar`, `upperStar`,
  `upperStarLowerStarAdjunction`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`: `etaleLowerShriek`.
- `Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalization`:
  `EtaleCompactSupportNormalization`, `nonempty_etaleCompactSupportNormalization`;
  its underlying explicit graph map is used directly, without selecting a
  non-unique structure from Nonempty. Read the data module and graph construction.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `etaleInverseImageModulesExact`, the fixed constant-ring inverse-image normalization.
- `Sheaf.SixFunctors.EtaleOpenTensor`: `EtaleOpenTensorComparisons`,
  `etaleOpenTensorComparisons`, and the exported ordinary `openScalarExtensionZero`.
- `Sheaf.Paper.RingedTopoiInverseImageTensorComparison`:
  `SheafOfModules.RingedTensor.exists_inverseImageTensorComparison`.
- `Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafProjectionMap`:
  `etaleLowerShriekProjectionMap`, with the exported `etaleSumSection`,
  `etaleLiftSection`, and `etaleSheafTensorSection` read in its data module.
- `Sheaf.CategoryTheory.Sites.InverseImageBilinearAdjunction`:
  `CategoryTheory.site_inverse_image_bilinear_adjunction`.
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`:
  `PresheafOfModules.exists_sheafificationTensorIso`,
  `PresheafOfModules.nonempty_sheafTensorSheafificationIso`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction` (already imported by the preceding interfaces).
- Additional canonical constructions reused from
  `Sheaf.Paper.ScalarPullbackRepresentativeData`: `scalarSheafPullbackIso`;
  `Sheaf.Paper.EtaleDerivedScalarTensor`: `scalarCoefficientSheaf`,
  `scalarSheafTensorMap`; `WeilConjectures.SixFunctors.ProEtale.ScalarExtension`:
  `etaleSheafExtendScalars`, `etaleSheafExtendScalarsAdjunction`.

Source reading: local Stacks more-etale.tex, lemma-f-shriek-projection (0GKF),
remark-Rf-lower-shriek-change-of-rings (0GL6), and etale-cohomology.tex,
proposition-describe-jshriek (03S5), lemma-shriek-into-star-separated-etale (0F4L).
These specify pure tensors, graph extension and sheafification. The docstring gives
all six steps of the DAG proof and names their dependency nodes.

Edge cases checked before writing: identity e and identity compactification reduce
to the scalar unit/counit triangle and the identity sheet; two split sheets give
componentwise tensoring; arbitrary nonsplit covers require only individual lifts,
not a splitting of all sheets. Empty supports give the empty sum, so the formula
extends as zero; the empty source scheme and zero sheaf impose no inhabitance
condition. The zero coefficient ring is allowed by CommRing and Finite, and no
Nontrivial instance is requested. A = 0 with a unital map forces B = 0. Non-flat
Z/4 → Z/2 is allowed. Neither an inverse of pi_C nor tensor exactness is asserted.
Source schemes live in u and coefficient modules in u+1, matching all dependencies;
there is no new equality of independently varying site universes.

Searches (msearch.py, group Q14, this item):

- LeanFinder: "Ordinary compactified etale scalar extension counit mate acts by
  tensoring each local sheet component". Eight hits, principally ModuleCat scalar
  unit/counit formulas, unrelated coalgebra counits and affine Spec adjunctions.
  None gives this compactification/sheaf-sheet compatibility.
- Loogle: "SheafOfModules.pullbackPushforwardAdjunction,
  AlgebraicGeometry.Etale.etaleLowerShriek". Zero hits; unknown identifier for the
  project's etaleLowerShriek, which is not a Mathlib declaration.
- Mathlib grep through msearch: "scalar.*mate|compactification.*scalar",
  Algebra/Category. Zero hits.
- Project rg in both lean/WeilConjectures and lean/Sheaf for scalar mates,
  compactification scalar maps and sheet scalar formulas. Found and reused the
  graph map, scalarSheafPullbackIso, openScalarExtensionZero and the local sum and
  tensor sections. Derived scalarMate statements are about derived objects, not
  this ordinary sheaf morphism. Exact item-id search in WeilConjectures found none.
  No existing declaration states this item's equality and arbitrary-local-section
  formula together. Search records are also in the sandbox searches.jsonl.

No node correction, missing notion, dependency repair, or disputed statement.

Validation: scompile.py compiled the sandbox and the actual library module separately
against the live published library, cleanly (5.7 s and 9.7 s). No error or unexpected
warning. Only the named owning theorem uses sorry. No local build was run.

## Second reading by Q14

The dispatched worker reread the node and complete module after compiling. This is
a self-check; no separate agent was started, as the dispatch explicitly forbids one.
The maintainer's independent delivery review remains the independent reading.

Rechecked the crucial distinctions against the node: b ranges over local sections,
not global ring elements; the mate uses the ordinary geometric adjunctions; ν is
fixed to the actual graph extension, not any isomorphism; o is the published open
scalar map; the equality has the node's exact order. Rho has B-linear components
and its natural-transformation type includes naturality in M; component naturality
includes restriction. Individual generators imply the finite-support-family rule
by additivity, including merging lifts and empty sums. No proof, flatness,
constructibility, globally split cover, or nonzero-ring assumption was introduced.
No mismatch or statement change was found in this rereading.

## Worker report

Repair of the return for immutable head `0a2015113bff` (H3, H11, H9).
The retained packet was inspected first and its prescribed initial dry run passed:
`OK (dry run): commit 73f3e4049f passes the preflight and compiles; nothing pushed`.
That mechanical result did not resolve the mathematical review, so the module has
been substantively repaired. The node's natural statement and proof are unchanged.
Only its `lean` record and the already required additions to `stmt_deps` are delivered.

The module is `Sheaf.AlgebraicGeometry.AffineRelativeDualizingComparison`; its
main theorem is `AlgebraicGeometry.affine_relativeDualizing_comparison`. The
only postponed proof is that theorem. Every definition has real data. The added
helpers expose the canonical constructions needed for this node's final clause;
they are recorded in `lean.declarations`, with source and blueprint docstrings.

Hypotheses, checked against the node:

* `{X S : Scheme.{u}} (f : X ⟶ S)` supplies the schemes and the given morphism.
* `[IsSeparated f] [Flat f] [LocallyOfFinitePresentation f]` are exactly the
  three morphism hypotheses. `[IsLocallyNoetherian S]` is the base hypothesis.
* `K : schemeDerivedCategory X` and the binder `ξ` use the recorded degree-zero
  ordinary diagonal direct image and the first derived pullback. No derived
  diagonal pushforward replaces the node's ordinary diagonal pushforward.
* `hKξ : IsCoherentRelativeDualizingPair f K ξ` unfolds to precisely the
  supplied pair's three conditions: `Scheme.IsPseudoCoherent X K`, pointwise
  open neighborhoods with `Scheme.HasFiniteTorDimensionOver`, and `IsIso` of
  the multiplication-induced `relativeDualizingClassMap f K ξ`. The relative
  Tor predicate uses modules over the inverse-image base structure sheaf.
* `(R A : Type u) [CommRing R] [CommRing A] [Algebra R A]` supplies the actual
  chart rings and induced homomorphism. `jA`, `jR` with the two open-immersion
  instances are arbitrary specified affine charts; `h` says their square
  commutes. Neither a shrinking of the specified charts nor properness is assumed.
* The derived-category instance binders select the localizations. Ring derived
  categories use their native morphism universe `u`; scheme derived categories
  retain the independent universe `w`. Every variable and universe is explicit,
  with `autoImplicit false`. No equality of those universes is imposed.

Conclusions, checked clause by clause:

* `(algebraMap R A).Flat`, `Algebra.FinitePresentation R A`,
  `IsNoetherianRing R`, and `IsNoetherianRing A` are the four ring conclusions.
* `∃ M : DerivedCategory (ModuleCat A)` with
  `DerivedCategory.IsPseudoCoherent M` is the bounded-above finite-free model
  condition, and the displayed `Nonempty` isomorphism identifies tilde M with
  the restriction of this given K. `relativeDualizingAffineTilde` uses the
  existing affine equivalence, normalized by its termwise tilde comparison.
* `∃ a b : ℤ, a ≤ b ∧ ∀ N i, ...` states one finite interval for every R-module
  in degree zero. M is first restricted from A to R, and the tensor is the
  existing derived tensor over R. `i < a ∨ b < i` is exactly outside `[a,b]`.
* `A ⊗[R] A` is B. `relativeDualizingModuleFirstPullback R A M` is K-flat
  extension along `includeLeft`, hence the specified M₁. The order B tensor_A M
  is canonically the displayed M tensor_A B. No new derived-tensor notion is used.
* `relativeDualizingProductChart f R A jA jR h` uses `pullbackSpecIso` and the
  actual chart square; its derived pullback restricts to U times_V U.
* `relativeDualizingModuleDiagonal R A` is A[0] with B-action through
  `Algebra.TensorProduct.lmul'`. The three existential isomorphisms `eD`, `eM`,
  `eH` compare the restricted diagonal, first pullback, and derived sheaf Hom
  with their affine module constructions. `relativeDualizingModuleHom` is
  `(ihom (relativeDualizingModuleDiagonal R A)).obj M₁` in D(B).
* `ξU` is a map from that diagonal module to that M₁. The first square identifies
  it with the restriction of the specified ξ. The second square identifies the
  given sheaf class map with `relativeDualizingModuleClassMap R A M₁ ξU`.
  That map is defined by transposing ordinary diagonal multiplication, after
  canonical monoidal localization, followed by ξU. Its `IsIso` is precisely
  the algebraic relative-dualizing condition.
* For every `a : A` the three `schemeDerivedScalar` equations express scalar
  compatibility on the diagonal, M₁, and Hom. The local-section family is fixed
  at the top by `ΓSpecIso.inv` applied to `includeLeft a`. The B-linear Hom
  action also equals precomposition with that scalar on the diagonal.
* The final quantifiers range over EVERY affine open `Spec C → Spec B`, encoded
  by `φ` and its open-immersion instance. This includes identity, empty, basic,
  and non-principal affine opens. `relativeDualizingDerivedExtension φ` computes
  restriction by the actual scalar extension, on K-flat representatives.
* The final tensor family `τ` is normalized, not arbitrary:
  `IsRelativeDualizingExtensionTensorComparison φ τ` states naturality and the
  counit equation on ALL homotopy complexes. Its right side is the existing
  ordinary scalar-extension oplax tensor comparison localized by Qh; its left
  side is the derived comparison followed by the two K-flat counits and the
  canonical lax monoidal Qh map. On K-flat representatives these maps are
  invertible, which determines the comparison. The native universes are retained.
* `relativeDualizingHomLocalization φ τ D M₁` is defined by transposing extended
  evaluation. Its target is the independently recomputed
  `RHom_C(C tensor_B^L D, C tensor_B^L M₁)`. The new `IsIso` clause asserts
  the genuine Hom localization comparison, not a transported identity square.
* `relativeDualizingLocalizedClassMap` independently transposes localized
  diagonal multiplication followed by the localized ξU. The new algebraic
  equality identifies extension of the original transpose, followed by the
  canonical Hom localization map, with this recomputed local transpose.
* `ρ` compares tilde followed by open pullback with scalar extension followed
  by tilde on Spec C. The final sheaf square now ends in the tilde of the
  RECOMPUTED Hom over C, using the canonical evaluation comparison; the other
  square still identifies the localized ξU with the restricted given ξ.
  Thus the conclusion includes actual constructions on the smaller chart.
  If the open is the product chart from U'=Spec A', V'=Spec R', take
  C=A' tensor_{R'} A'. The canonical ordinary identification
  C tensor_B A ≅ A' and tensor associativity identify the two scalar-extended
  objects with the smaller-chart diagonal and first pullback. The recomputed
  Hom and multiplication transpose are therefore exactly the constructions
  on that chart. This uses no arbitrary replacement map.

Dependencies used (recorded declarations, not private copies):

* `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`;
  `Morphisms.Proper`: `IsSeparated`; `Morphisms.Flat`: `Flat`;
  `Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`.
* `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `schemeDerivedCategory`, `schemeDerivedQCohProperty`.
* `Sheaf.AlgebraicGeometry.PseudoCoherentComplex`:
  `Scheme.IsPseudoCoherent`; `FiniteTorDimensionOver`:
  `Scheme.HasFiniteTorDimensionOver`, through the recorded pair predicate.
* `Sheaf.AlgebraicGeometry.DerivedPullback`: `derivedPullback`;
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: retained
  `derivedInternalHom`, used by the recorded canonical class map.
* `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`;
  `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation`;
  `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
* `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`:
  `exists_affineQCohDerivedEquivalence`;
  `Sheaf.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`.
* `Sheaf.AlgebraicGeometry.RelativeDualizingPair`:
  `IsCoherentRelativeDualizingPair`, `relativeDualizingDiagonalComplex`,
  `relativeDualizingClassMap` and their canonical multiplication construction.
* `Sheaf.AlgebraicGeometry.DerivedGlobalScalar`: `schemeDerivedScalar`.
* `Sheaf.Algebra.Homology.ExtensionKFlatQuasiIso`:
  `ModuleCat.extendScalars_preservesKFlatQuasiIso`;
  `WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs`:
  `Functor.leftDerivedFunctor`, `Functor.leftDerivedFunctorCounit`.
* `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`:
  module derived tensor and closed structures;
  `Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction`:
  canonical monoidal extension of scalars;
  `WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal`:
  `Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans`.
* `Mathlib.AlgebraicGeometry.Pullbacks`: `pullbackSpecIso`.

All stated proof-dependency modules remain non-public imports. The relative
Tor-criterion node still has no recorded Lean module in the read base, so has
no proof import yet. No import cycle was introduced.

Source reread: Stacks `duality.tex`, Tags 0E2T and 0E2U,
`lemma-relative-dualizing-complex-algebra`, including the proof, and the algebraic
relative-dualizing definition in `dualizing.tex`. The last proof step of the DAG
explicitly requires localization of diagonal, tensor, Hom, multiplication and
class. The repair spells out this clause; no natural statement correction or
statement dispute is needed.

Edge cases: zero rings and empty affine charts remain permitted; the identity
open map is quantified over; a=b and zero M are permitted; non-principal affine
open immersions are included. No perfect, smooth, regular, finite-dimensional,
proper, connected or nonempty assumption has been inserted. For a singular
diagonal its finite-free resolution may extend arbitrarily far left. The
bounded-below M₁ model ensures finitely many Hom factors in each degree, which
is why the canonical Hom localization map is invertible without a perfect
hypothesis. Scalar naturality applies after every φ, including base-chart changes.

Searches for existing declarations:

* `msearch.py ... leanfinder "Affine comparison of a coherent relative dualizing
  pair with diagonal pushforward derived pullback and derived Hom over A tensor
  R A"`: 8 ordinary sheaf-pullback/adjunction hits, no relative-dualizing comparison.
* `msearch.py ... loogle "DerivedCategory, Algebra.TensorProduct"`: 0 hits with
  unknown-identifier note for `Algebra.TensorProduct`; this failed query alone was
  not used as evidence of absence.
* Valid Loogle follow-up `AlgebraicGeometry.Scheme.Modules, DerivedCategory`:
  successful query with zero hits.
* `msearch.py ... grep "relative.dualizing|RelativeDualizing|diagonal.*RHom"
  AlgebraicGeometry`: 0 Mathlib matches.
* `msearch.py ... leansearch "affine relative dualizing complex diagonal derived
  Hom comparison"`: 8 unrelated short-complex homology/general diagonal results.
* `rg` over upstream `WeilConjectures` and shared `lean/Sheaf` for relative
  dualizing, diagonal multiplication, and the item id; `grep -rn` for the item id
  upstream: no exact comparison. The later shared search found Q80's pair API,
  which is used here. Existing etale relative dualizing declarations concern a
  different coefficient/site theory and do not state the coherent comparison.
* Helper search `leanfinder "Multiplication on the pushforward of the structure
  sheaf as a sheaf of modules for a scheme morphism"`: ordinary pushforward hits;
  `loogle "SheafOfModules, multiplication"`: unknown multiplication identifier;
  `grep "pushforward.*(mul|algebra)|diagonal.*multiplication" AlgebraicGeometry`:
  four unrelated stalk/cohomology-cycle hits; `leansearch "The direct image of the
  structure sheaf has a canonical multiplication as a module sheaf"`: ordinary
  module/section actions. `tools/blueprint_refs.py search 'pushforward structure
  algebra'`: zero results. These initially motivated a helper draft, removed when
  the newly landed Q80 module was found. No duplicate helper module is delivered.

Repair searches (2026-10-17 UTC):

* `msearch.py ... leanfinder "Canonical localization map from derived Hom over B
  tensored with C to derived Hom over C, defined as transpose of extended
  evaluation"`: eight hits, ordinary localization tensor maps, Tor, Ext,
  ordinary module evaluation and localization linearity; no derived Hom
  localization declaration for this affine comparison.
* `msearch.py ... loogle "MonoidalClosed.curry"`: unknown short identifier;
  this failed query is not absence evidence. The full definition is read in
  Mathlib's `CategoryTheory/Monoidal/Closed/Basic.lean` and reused.
* `msearch.py ... grep "HomLocalization|HomBaseChange|ExtensionTensorComparison"
  CategoryTheory`: zero matches. Source `rg` found the generic
  `Functor.leftDerivedTensorComparison` in the upstream LeftDerivedFunctor/Monoidal
  module. It fixes hom universes to successors and cannot specialize to native
  ModuleCat.{u} universes here. The helper states its exact counit normalization
  directly using the recorded extension functor and ordinary tensor comparison;
  it introduces no different tensor or Hom object.

Validation: the repaired module compiled through the prescribed `scompile.py`
as both a sandbox module and at its library path, exit 0, with no errors or
unexpected warnings. The subsequent exact-module `deliver2.py --no-push`
finished `OK (dry run): commit 74b3aafa17 passes the preflight and compiles;
nothing pushed`. It staged only this module, the item node, and this report.
The final delivery wrapper reruns the same compilation and preflight before push.

## Second reading by Q68

This is a fresh, explicit second pass by the repair worker with the node and
repaired file open; the dispatcher forbids starting another agent. It does not
claim an independent reviewer. The maintainer's independent immutable-head
review remains the independent reading.

H3 found in the returned file: its last two equations used only r.map of the
original ξ and transpose squares and naturality of ρ. Their targets were still
extension of the OLD Hom. They did not assert the comparison with the Hom or
multiplication transpose recomputed over C. The repair adds the evaluation-defined
Hom localization map, requires its invertibility, defines the local class from
localized multiplication, and compares that class with extension of the original
transpose. The final sheaf equation now includes that Hom comparison. This is a
substantive new condition on the smaller-open constructions. Reading the helper
bodies confirms neither map is defined by transporting the old class square.
The tensor-comparison normalization fixes evaluation on representatives, so an
arbitrary isomorphism cannot stand in for the canonical map.

H9 found in the returned file: B, W, jB, res, D, M₁, T, H, r and T' were
statement-local `let` bindings. All are removed from the theorem signature.
The first-pullback and Hom expressions are named public definitions; all other
terms are explicit. The signature has no `let`, `show`, auto-bound variable,
local notation or extra universe equality.

H11 found in the returned report: there was no actual second-reading section.
This pass checked each binder and each conclusion against the node, as detailed
above. In particular: the three pair hypotheses use the supplied-pair predicate;
the source and base charts are the specified arbitrary open immersions; the Tor
interval is uniform over all R-modules; the diagonal module is A via μ, not B;
ξU is tied to the supplied ξ; the algebraic isomorphism is its multiplication
transpose; scalar compatibility has all three objects; restriction now includes
independent local Hom and class constructions. Empty/identity cases and the
bounded-above/bounded-below Hom argument were checked. No mismatch remains in
these clauses. Every added helper has real definitional data and its source;
no extra `sorry`, new independent notion or dependency module was added.

## New nodes

None. All new helpers are intrinsic components or characterizations of this
item's canonical comparison, not separate mathematical notions.

## Dependency modules

None. The existing dependencies are reused at their recorded universes.

## Worker report

The module `Sheaf.Paper.LocalizedDirectImageComparison` states
`AlgebraicGeometry.ProEtale.CondensedRing.localizedDirectImageComparison_isIso`.
Its only postponed proof is this named theorem, with the complete seven-step node
proof in its docstring. The helper `localizedDirectImageComparison` specializes the
existing canonical `derivedPushHom`; it introduces no independent notion and has
real data. The item node changes only in `lean`. No dependency node is changed,
no new node is needed, and no statement correction or dispute is present.

### Clause-by-clause statement reading

- The fixed prime is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- A finite subextension of the fixed algebraic closure of Q_ℓ is
  `(E : PadicAlgCl.FiniteIntermediateField ℓ)`. This is the published subtype of
  intermediate fields with `FiniteDimensional ℚ_[ℓ] E.1`; its embedding, restricted
  norm and topology are the published ones, not independently supplied structures.
- A morphism of arbitrary schemes is `{X Y : Scheme.{u}} (f : X ⟶ Y)`.
  Quasi-compactness and quasi-separatedness are exactly `[QuasiCompact f]` and
  `[QuasiSeparated f]`, with Mathlib's affine-preimage and diagonal meanings.
  There is no properness, finite-type, field-of-definition, characteristic or
  invertibility-of-ℓ-on-X hypothesis.
- A = O_E is `Profinite.padicIntegersRingObj ℓ E.1`, defined using continuous
  functions with values in `PadicAlgCl.integers ℓ E.1`. E is
  `Profinite.continuousMapRingObj E.1`. For Z = X,Y their pulled-back ring objects
  are the existing `condensedRingObj ... Z`, equivalently the underlying objects
  of the recorded `coefficientRing Z (Mon.mk ...)`. The latter construction is
  `(upperStarFromPoint Z).mapMon.obj` with the canonical transported operations.
- The arbitrary ambient object is
  `C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))`.
  Bounded below is precisely `hC : DerivedCategory.TStructure.t.plus C`, namely
  existence of an integer lower cohomological bound. This is not a bounded
  constructible category or a category of complete objects.
- The helper's source is the left derived extension
  `(Mod.extendScalars (padicIntegersToPadicSubfield Y ℓ E)).leftDerivedFunctor`
  applied to `moduleObjectDerivedPushforward` with integral coefficients and C.
  This is E_Y tensor^L over A_Y with Rf_{*,A} C.
- Its target is `moduleObjectDerivedPushforward` with E coefficients applied to
  `(Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.obj C`.
  This is Rf_{*,E}(E_X tensor^L over A_X with C).
- These direct images are the recorded definitions in
  `Sheaf.Paper.CondensedModuleDerivedPushpull`: exactly the generic
  `rightDerivedFunctor` of the entire `lowerStar` module functor. No completed
  or constructible direct image appears.
- The map is the component of the existing `CondensedRing.derivedPushHom` at C,
  with the existing point inclusion `padicIntegersRingObjToContinuousMapRingObj`.
  Its sheaf inclusion is definitionally `padicIntegersToPadicSubfield`.
  `derivedPushHom` is `Adjunction.pushHomOfComapIso` of the normalized
  `derivedComapLowerStarIso`. The companion `derivedPullIso` is the conjugate of
  this SAME right-adjoint comparison under the two geometric adjunctions and
  scalar adjunctions. Therefore the push mate is equivalently adjoint to extension
  of the A-counit after the pull/tensor comparison. The ordinary comparison is
  the identity on underlying pushed-forward sheaves, and its derived comparison
  is fixed by the right-derived universal transformations. It is not an arbitrary
  map or a choice of an isomorphism. The recorded tensor-pullback theorem is
  publicly imported; it and the section normalization proof dependencies give
  the K-flat pure-tensor/unit normalization required in the node's proof.
- `IsIso (localizedDirectImageComparison ℓ E f C)` is exactly invertibility of
  that specified arrow. There is no extra conjunct and no additional assumption
  about C's completeness, constructibility or Tor amplitude.

The helper supplies the existing flatness argument required by `derivedPushHom`
from the final assertion of `padicIntegers_invertEll Z ℓ E` for every Z. The
projection through its existential witnesses extracts only a proposition about
the fixed existing scalar-extension functor. It does not choose the coefficient
ring, a comparison morphism or any undetermined object. The local `letI` is in
this helper's body, not in a theorem statement.

### Dependency declarations read and used

All six statement dependencies were read, including the convention node and its
referenced Mathlib leaves. Their signatures and docstrings were opened.

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`, with the
  public continuous-function coefficient constructors. It is the abbreviation
  for ring objects of abelian sheaves on the coherent profinite site.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `coefficientRing_X`, `condensedRingObj`,
  `upperStarFromPoint`, `condensedPullbackHom` and their monoidal structures.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `Functor.rightDerivedFunctorOfQuasiIsoResolutions`; this convention module
  exposes generic total right derivation on arbitrary K-injective resolutions.
  For the present Grothendieck module categories the recorded geometric
  specialization is the existing generic `rightDerivedFunctor` as below.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `CondensedRing.moduleObjectDerivedPushforward` is used in BOTH source and target.
  Its definition is exactly `(lowerStar Λ f).rightDerivedFunctor`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.ringedTopoiCanonicalDerivedTensorPullback`.
  The signature retains independent object/morphism site universes, the genuine
  module pullback, and the uniquely normalized representative square. It is
  imported for the canonical tensor identification, not replaced by a supplied map.
- `def-weil-pbc-scheme-conventions` explicitly has no new notion. Its recorded
  Mathlib meanings `AlgebraicGeometry.Scheme`, `QuasiCompact`, `QuasiSeparated`
  are used directly. Their source signatures were read.

The canonical maps also use the existing
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients`
(`coefficientMap`, `derivedComapLowerStarIso`, `derivedPushHom`, `derivedPullIso`)
and `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization`
(`padicIntegersRingObjToContinuousMapRingObj`, `padicIntegersToPadicSubfield`).
`Sheaf.Paper.PadicIntegersInvertEll` supplies `padicIntegers_invertEll` and
publicly exports the latter module. Every already stated proof dependency is
imported, privately when used only by the proof plan, including section
push/pull and tensor normalization, scalar adjunction, qcqs continuity, exact
functor derivation, ring-sheaf change adjunction, scalar localization on complexes,
modules and sheaves, cohomological detection, and Cartesian coefficients.

### Sources and edge cases

Read the local HRS PDF with pdftotext: Lemma 5.3(1), comparison (5.4), says precisely
that arbitrary qcqs pushforward commutes with filtered colimits with one common
lower bound; its proof reduces by good truncation to a single degree and evaluates
on weakly contractible affine tests. Lemma 5.6 identifies the coefficient colimit.
Read the current main-20261015 blueprint's `lem-sfb-dc-lower-star-preserves` and its
unit context. The consumer's constructibility assumption does not belong in this
auxiliary bounded-below localization theorem.

Checked: the zero complex; a complex in any single degree, including negative
degrees; a complex unbounded above; the empty source or target scheme whenever
a morphism exists; the identity morphism; the degree-one subextension Q_ℓ itself;
ramified finite E; schemes in characteristic ℓ; absence of a uniform bound on
Rf_* cohomological dimension. None is excluded by a binder. For the identity,
the mate specializes to the canonical scalar comparison and is invertible.
The lower bound is existential and may depend on C. Scheme universe u is arbitrary;
its small pro-etale site has object universe u+1 and morphism universe u, and
coefficients remain Ab.{u+1}. No site-universe equality or smaller test universe
is imposed. The scalar telescope is the nonempty sequence of natural numbers.

### Searches

Executed the prescribed msearch wrapper, group O1, item
lem-sfb-localized-direct-image-comparison:

- LeanFinder: “For a quasi compact quasi separated morphism of schemes, extension
  of scalars from the integers of a finite p-adic field to the field commutes with
  bounded below derived pushforward”. Eight hits, ordinary scheme/module
  pushforwards and their right-adjoint structures, no matching theorem.
- Loogle: `"SheafOfModules", "IsLocalization"`. One hit, categorical sheafification
  localization, not coefficient localization and derived direct image.
- grep Mathlib: `(pushforward|rightDerived).*(localization|IsLocalization)|
  (localization|IsLocalization).*(pushforward|rightDerived)`. Nine hits, generic
  right-derived localization interfaces and a stalk-localization comment, no match.
- LeanSearch: “Extension of coefficients from the ring of integers of a p-adic
  field to the field commutes with bounded below derived direct image for quasi
  compact quasi separated scheme morphisms”. Eight hits, p-adic integer coercions,
  their fraction field and unrelated integral bases, no matching theorem.
- rg over `lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject` and
  `lean/Sheaf/Paper`, `lean/Sheaf/CategoryTheory` for coefficient-change, localization
  and pushforward combinations: found the canonical `derivedPushHom`, which is
  reused. Existing finite-extension change-of-field isomorphisms invert different
  coefficient maps. `ContinuousIntegralPushComparison.integralScalarPushHom_isIso`
  takes `K : integralConstructible ℓ E X` and thus does not state the arbitrary
  bounded-below result. No copy of its constructible notion or theorem is made.
- rg for the exact node id in `lean/WeilConjectures`: no existing declaration.
  Searches for both new fully qualified declaration suffixes found no collision.

### Validation

Only scompile.py is used. Initial compile exposed a privately imported upstream
canonical-map module and a typeclass search limit. The public import was made
explicit, and the instance-search option was scoped to the two declarations.
No time limit was increased. The final sandbox compile and actual library-artifact
compile both succeeded without warnings (45.2 and 52.6 seconds). All Lean lines
are at most 100 characters. `autoImplicit false` is explicit and universe u and
all binders are named. The theorem proof is exactly `by sorry`.

No second-reader claim is made: the dispatcher brief forbids starting another
agent and assigns independent review to the maintainer.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

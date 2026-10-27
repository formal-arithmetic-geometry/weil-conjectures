## Worker report

Q103, stage 2, item lem-pur-compact-support-strict-scalar-composition.

Delivery: `Sheaf.Paper.CompactSupportStrictScalarComposition`, namespace
`WeilConjectures.PurStrictScalar`. The node statement is unchanged. There are no new
nodes or dependency repairs. The module states the strict composition equation,
the proper/open factor equations, the identity equation, quotient coefficient
compatibility, the Roos-limit equation, and the completed-coefficient equation.
All newly stated theorems have `sorry` as their entire proof. Definitions contain
actual functor, adjunction, localization or uniquely normalized comparison data.
Each declaration has the source/node docstring; each theorem includes its proof plan.

The natural-language auxiliary is agent-written: it is not asserted to be a single
Stacks theorem. I read the full node proof and Stacks sites-cohomology.tex,
lemma-adjoint (07A6), lemma-derived-limit-is-ok (0941), and sites-modules.tex,
lemma-j-shriek-and-tensor (0E8I), and the current blueprint
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/`
`sk-thm-purity-transport.proof.md`. The imported auxiliary's proof is the detailed
composition calculation used here. The current blueprint discusses coefficient
transport as a whole; it does not itself define another strict scalar mate.

### Hypotheses and objects

* The prime ell is `l : ℕ` with `[Fact l.Prime]`. The global finite-field datum is
  `D : FiniteFieldDatum` and the different-characteristic requirement is `hl : l ≠ D.p`.
  This uses the underlying datum of the recorded `PurityFiniteSetting`; its finite
  level is not fixed because the statement concerns the entire positive tower.
* The coefficient fields are `E F L : Type u`, each with `Field`,
  `Algebra ℚ_[l]`, and `FiniteDimensional ℚ_[l]`. The inclusions are the algebra
  homomorphisms `i : E →ₐ[ℚ_[l]] F` and `j : F →ₐ[ℚ_[l]] L`.
  Field homomorphisms are injective, so these represent the inclusions in the node.
* Valuation rings, chosen uniformizers, and positive quotient rings are exactly
  `Padic.coefficientExtensionIntegers`, `Padic.coefficientExtensionUniformizer`
  and `Padic.coefficientExtensionRing`; they are never redefined in this file.
* The positive ramification indices are `e h : ℕ`, with `hepos : 1 ≤ e`,
  `hhpos : 1 ≤ h`, and the actual ideal equalities
  `he : PurCompactSupport.Ramification l E F i e` and the analogous `hh`.
  `compositionRamification` obtains the composite equality at `h * e` from these;
  there is no additional ramification hypothesis for the composite extension.
  It identifies ideals, allowing unit multiples of the chosen uniformizers.
* `X Y : Scheme.{u}` have the specified `Over (Spec (.of D.k))` structures.
  `LocallyOfFiniteType` and `QuasiCompact` of both structure maps say finite type,
  and `IsSeparated` of both structure maps says separated over k.
* `f : X ⟶ Y` has `f.IsOver`, `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact`.
  The fixed `c : Compactification f` contains its open immersion, proper map and
  factorization identity. All three coefficient fields use this same `c`.
* `M : DerivedCategory (scalarReductionSource l E X)` and
  `hM : finiteTorConstructibleIntegral l E X M` are the actual completed-coefficient
  derived category and its bounded constructible, derived-complete, uniform finite
  Tor interval condition. No hypothesis about merely discrete integral modules replaces it.
* `SE SF SL : CoefficientDerivedSystemCalculus ...` specify the published universal
  quotient-reduction calculi. They are presentation choices of the recorded derived
  reductions, with their whole-system adjunctions and evaluation normalizations,
  not arbitrary towers or independently chosen maps. The equations hold for every
  choice of these calculi.
* `support l E c SE` is the native separately derived proper/open reduction system
  followed by exact restriction to constant integral scalars. This is the strict
  tower `𝒯_E^c` of the node. `T` is the existing exact constant scalar extension
  on `D(ℕᵒᵖ ⥤ Mod(constant O_E))`, not the category of towers in a derived category.
  `subsequence l L W e` is exact arithmetic selection with composite transitions.
  Index n in Lean denotes positive exponent n+1. Thus the three simultaneous
  levels are n+1, e(n+1), and h e(n+1), covering every requested positive level.
* `scalarSupport` is the existing total derived inverse limit of the native finite
  proper/open system over completed coefficients, namely the node's `P_H^c`.
  `pbcDerivedExtend (completedCoefficientMap ...)` is ordinary derived scalar
  extension along the actual completed coefficient sheaf map, namely `C_{J/H}`.

### Every conclusion

1. `compactSupportStrictScalarComposition` is the first displayed equation. Its
   left side is `compositionTower.hom ≫ arrow_(L/E)`. Lean composes arrows from
   left to right, so this is q_(L/E) after alpha^Y in the node's convention.
   Its right side is T_(L/F)(q_(F/E)), then the canonical interchange of tensor
   and selection, then selection by e of q_(L/F) at C_(F/E)(M), then
   `compositionRetained`, then selection by h*e of support applied to alpha^X.
   The common target is therefore exactly the retained L support tower at the
   direct extension of M. The equality is between actual derived strict-tower
   morphisms and is natural in M since its factors are natural transformations.
2. `compositionOrdinary` is the ordinary balancing associator defined by the
   tensor-unit normalized scalar adjunctions and the recorded identity-on-sections
   restriction compositor `pbcRestrictComp`. `compositionTowerOrdinary`,
   `compositionTower`, and `compositionBase` only whisker/localize that same map.
   These are specializations of the existing scalar constructions, not a second
   tensor functor. The formula multiplies the two scalar factors; Mathlib writes
   a sheafified pure tensor in scalar-first order.
3. `compositionProper` gives the proper factor equality on the actual
   `proper` maps; its docstring describes pasting the pulled-back scalar squares
   on flat-term K-flat diagram representatives and applying mate pasting.
   `compositionOpen` gives the identical equation for `openTensor`. This uses
   precisely the multiplication associator, zero off the open, and no sign.
4. `compositionSelectionOrdinary` and `compositionRetained` give the required
   reassociation of nested retained towers. The ordinary equality includes
   transitions, since it is equality of functors, not a list of level equalities.
5. Coefficient actions are retained by the types: all strict morphisms are in
   `D(ℕᵒᵖ ⥤ Mod(constant O_L))`, and completed morphisms are completed O_L-linear.
   The equalities can be precomposed with every strict augmentation and then
   realized. They therefore retain augmentations as actual morphisms, with no
   inference from faithfulness of finite evaluations. The existing definitions
   of `arrow`, `reductionBalancing`, and `scalarLimitArrow` already fix the
   augmentation by their ordinary tensor formulas and whole-complex counits.
   The imported `scalarRoosNormalization`, `scalarRoosTensorNormalization`, and
   `scalarLimitArrow_augmentation` fix the zero shifted-product coordinate too.
6. `compactSupportStrictScalarIdentity` says q_(E/E) becomes tensor multiplication
   after the canonical e=1 selection and input multiplication maps.
   `compositionUnitOrdinary`, `compositionUnitTower`, `compositionUnitCompleted`
   and `compositionSelectionOne` are the actual unit comparisons, defined from
   the existing scalar adjunctions and restriction comparison; no arbitrary unit
   is supplied. `compositionRamificationOne` derives the ramification hypothesis.
7. The completed ring maps already satisfy
   `PurCompactSupport.completedMap_composition` and `completedMap_identity`.
   `compositionCompleted` uses the former equation in the existing normalized
   `PurCompactSupport.tensorComposition`; `compositionUnitCompleted` uses the
   latter in `tensorIdentity`. `compositionFiniteCoefficients` states equality
   of the actual quotient sheaf ring maps induced by the inclusions. Its sole
   target transport is the explicit arithmetic equality h*(e*n)=(h*e)*n.
   `identityFiniteCoefficients` is the same identity assertion at every positive
   quotient. The imported `arrow_transition` and finite coefficient square
   normalization supply compatibility with all longer quotient transitions.
8. `compactSupportScalarLimitComposition` is the same composition equation for
   the existing `scalarLimitArrow`, whose definition is exactly tau, R(q), then
   the inverse of the canonical cofinal restriction. This uses the specified
   Roos product comparison and cofinal block/selection maps, not chosen isos.
9. `completedArrow_existsUnique` fixes the actual completed-linear gamma by the
   normalization equation from the recorded scalar-limit-reduction theorem.
   `completedArrow` chooses that uniquely determined arrow, rather than choosing
   an arbitrary object or map. Its source and target are exactly C(P_E M) and
   P_F(C M). Uniqueness uses the full derived-completion/restriction interface,
   not faithfulness of evaluation of derived towers at finite levels.
10. `compactSupportCompletedScalarComposition` is the second displayed equation,
    using the ordinary completed associator `compositionCompleted` at X and Y.
    The intermediate finite-Tor witness comes directly from the existing
    `PurCompactSupport.integralCoefficientComparison`, adding no hypothesis.
    `compactSupportCompletedScalarIdentity` is gamma_(E/E)=1 under the ordinary
    tensor units. `completedArrow_naturality` explicitly states naturality on
    the full finite-Tor subcategory, including every derived morphism.

### Recorded dependency interfaces read and used

* `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and its
  underlying `FiniteFieldDatum` convention.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the imported integer rings,
  uniformizers and positive quotient constructions.
* `def-weil-scheme-morphism-properties` is explicitly a convention-only node with
  no declaration. Its named Mathlib classes are the hypothesis classes above.
* `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement` and the existing `Compactification`.
* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and `ProEt.topology`. Its object and morphism universes remain the small-site ones.
* `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses` and the existing completed coefficient sheaf.
* `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`:
  `ModuleCat.nonempty_ordinaryDerivedChangeOfRings`. For sheaves the actual node's
  scalar interface already uses `pbcDerivedExtend`, with its normalized universal
  counit and scalar adjunction; no ordinary module category is substituted for sheaves.
* `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`.
* `Sheaf.Paper.FiniteTorAmplitudeSites`: `finiteTorConstructibleEtale`, importing
  the same node's `finiteTorConstructibleIntegral` used by this item.
* `Sheaf.Paper.QcqsCompactSupportRealization`: `sfQcqsCompactSupportRealization`.
  Here the recorded scalar-limit interface presents the integral support directly
  as the native finite-image total limit `scalarSupport`, as required by the node.
* `Sheaf.Paper.CompactSupportReductionTower`:
  `exists_compactSupportReductionTower`. Its native normalized whole-ringed-diagram
  presentation is the `support` interface used by the recorded strict scalar mate.
* `Mathlib.CategoryTheory.Functor.OfSequence`: `Functor.ofOpSequence` and the
  actual functor-category towers `ℕᵒᵖ ⥤ ...`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  the exact abbreviation of Mathlib `SheafOfModules`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`.
* `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`; the native support and constant restriction
  use this same definition.
* `Sheaf.Paper.CompactSupportStrictScalarMate`:
  `compactSupportStrictScalarMate`, `arrow`, `proper`, `openTensor`, `baseTensor`,
  `support`, the evaluation maps and `arrow_transition`.
* `Sheaf.Paper.CompactSupportScalarLimitReduction`:
  `compactSupportScalarLimitReduction`, `scalarLimitArrow`, `scalarSupport`,
  `scalarCompletion`, `scalarSupportLimit`, and all recorded Roos normalizations.

Proof-only recorded modules are imported for ideal-quotient associativity,
diagram K-flat replacements, extension by zero, horizontal Roos coherence, Roos
cofinality (already public through scalar-limit reduction), and scalar completion
associativity. `lem-weil-pbc-mate-pasting` is a Mathlib leaf, whose listed
`mateEquiv_vcomp`, `mateEquiv_hcomp`, conjugation and identity statements are
already imported by the native scalar-mate modules. Its Mathlib declaration was
read in Mathlib/CategoryTheory/Adjunction/Mates.lean. The proof-only node
`lem-pur-compact-support-coefficient-models` has no lean record or Mathlib match
in the read DAG; there is no module to import for that proof-only dependency.
This does not prevent stating this item on the recorded statement dependencies.

### Searches and edge cases

The prescribed msearch commands ran under this item:

* leanfinder: "Composition of scalar extension proper open mates on strict compact
  support reduction towers before derived inverse limit". Eight results concerned
  condensed solidification, adic completion, and module scalar adjunctions; no match.
* loogle: "CategoryTheory.conjugateEquiv, TensorProduct.assoc". Zero hits.
* grep: `mate.*(comp|pasting)|extendScalarsComp`, Mathlib CategoryTheory. Hits include
  `mateEquiv_vcomp` and generic mate conjugation; these are the proof tools,
  not the strict compact-support result.
* leansearch: "Composition of extension of scalars adjunction mates derived categories".
  Results include `ModuleCat.homEquiv_extendScalarsComp`, module adjunctions,
  and `Adjunction.derivedε`; no compact-support theorem.
* Project source rg and the required blueprint-id grep in `lean/WeilConjectures`
  found no declaration for this item. Targeted searches in `lean/Sheaf` found the
  native strict mate and scalar-limit reduction, plus the generic completed
  scalar associator. These are reused. Broader scalar-composition searches found
  `PurCompactSupport.tensorComposition`, `tensorIdentity`, and completed ring map
  composition/identity; these exact declarations are used rather than restated.

The zero object and empty schemes are allowed; no nonemptiness or positive rank
is assumed. The identity inclusion E=F=L is permitted, with explicit unit laws.
Unramified extensions e=1 or h=1 are covered by the composition and unit comparisons.
The first finite exponent n=1 is covered; the positive tower is encoded by n+1,
so no exponent zero is silently used as the first level. The quotient compatibility
is for every positive n, and direct and nested levels are explicitly reassociated.
Arbitrary uniformizer units cause no problem because Ramification equates ideals.
All cochain and derived categories are unbounded ambient categories; boundedness
and uniform Tor amplitude occur only in the node's specified object predicate.
No hypothesis forces the small pro-etale site's object and morphism universes equal.

No STATEMENT-DISPUTED issue or statement correction was found.

## Second reading by Q103

I reopened the unchanged node and the completed Lean file for a separate second pass.
This is a second reading by the same dispatcher-started worker; no other agent was
started, in accordance with the brief. The maintainer's independent review remains.

The strict equation has the same endpoints after multiplying by alpha at the source
and applying the retained input alpha at the target. In particular, the order of
nested selection is h then e, giving h*e, and tensor must be moved past e-selection
before applying the second arrow. Both maps use the actual strict mate `arrow`.
The integral equation has the completed P^c values as endpoints, not merely their
restrictions to constant coefficients. Its gamma is pinned down by the published
chi/support-limit normalization, and its intermediate finite-Tor proof is derived
from the existing theorem rather than postulated. The two identity equations use
the same reduction calculus SE at source and target. Quotient ring maps have the
necessary arithmetic transport, and do not identify two nondefinitionally equal
uniformizer exponents silently. All geometric hypotheses and l != p are included
in the theorem signatures via explicit `include` directives.

During this pass I removed a proposition-valued helper definition that produced a
defProp linter warning; its use now directly projects the existing theorem. Every
remaining theorem proof is exactly `by sorry`, and every definition constructs its
data using existing functors or a uniquely normalized theorem. No private notion,
file-local notation, proof of the requested assertions, or source modification was used.

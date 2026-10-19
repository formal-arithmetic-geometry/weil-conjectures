## Worker report

`Sheaf.AlgebraicGeometry.PunctualPurityTwoOfThree` states only
`AlgebraicGeometry.Etale.punctual_purity_two_of_three`, with proof `sorry`.
The saved packet was retained and checked first by the prescribed dry run. Its
previously copied Tate-pullback dependency was redundant: the current published
source has the structured interface. That copy and its node rewrite have been
removed from the packet and retained in scratchpad for history.

Current published `Sheaf.AlgebraicGeometry.PunctualPurity` already owns the
canonical class map and the punctual-purity predicates. The saved packet's five
helpers duplicated those notions, so they have been removed. The statement now
uses these published declarations directly and cites the landed definition node
`def-per-punctual-purity`. No mathematical statement changes and no new nodes.

Source checked: ILO, Exposé XVI, Definitions 3.1.4 and 3.2.1--3.2.2 and
Proposition 3.2.3 with proof, printed pp.243--244. The saved PDF extraction
`ilo.txt`, lines 12286--12381, gives exactly the assertion that the number of true
conditions cannot be two. Its nontrivial implication uses induction on the local
dimension and the cone supported at the closed point. The theorem docstring
retains all eight DAG proof steps and their dependencies.

Hypotheses and clauses, matched individually:

* Prime and coefficients: `(ℓ : ℕ) (hℓ : ℓ.Prime)`, with coefficients
  `regularClassCoefficients ℓ 1 = ULift (ZMod (ℓ ^ 1))` in the published map.
  This is F_ell at the required coefficient universe u+1.
* Categories and twists: `punctualPurityClassMap` is a morphism in ordinary small
  etale `DerivedCategory.Plus` of sheaves of modules, using the published roots
  of unity Tate sheaf `regularClassTwist`. It transposes the n=1, a=0 supported
  Ext class via `closedSupportPlusAdjunction`, the exact direct-image comparison
  and the fully faithful inclusion D+ -> D. Both displayed objects belong to D+;
  its full inclusion reflects invertibility. The twist-shift inside i^! agrees
  canonically with the displayed shifted exceptional inverse image.
* Regular Noetherian schemes: `{Z X : Scheme.{u}} [IsNoetherian Z]
  [IsNoetherian X] (hZ : IsRegularScheme Z) (hX : IsRegularScheme X)`.
  `IsRegularScheme` includes local Noetherianity and regular local stalks.
* Closed immersion: `(i : Z ⟶ X) [IsClosedImmersion i]`.
* Codimension: `(c : ℕ) (hi : IsStalkRegularClosedImmersion i c)` uses the
  published length-c regular sequence generating the kernel of every stalk map
  at a point of Z. For closed immersions of regular Noetherian schemes this
  is the constant-codimension condition. Locally constant codimension is handled
  on its constant regions, as in the node's first proof step.
* Invertibility: `(hℓX : IsUnit ((ℓ ^ 1 : ℕ) : Γ(X, ⊤)))` means ell invertible
  on X; invertibility on Z and all local spectra follows under the structure
  ring homomorphisms. No further invertibility hypothesis is imposed.
* Condition (a) is exactly `IsIso (punctualPurityClassMap ℓ hℓ i c hi hℓX)`.
  The class family is determined by the dependency's unique characterization;
  the map uses the actual adjunction, with no arbitrary map or isomorphism.
* Condition (b) is `IsPunctuallyPure ℓ hℓ Z`, the published universal predicate
  over all points z. Its local predicate uses the actual stalk spectrum,
  `Spec.map (W.residue w)`, residue field, and the equation
  `ringKrullDim (W.presheaf.stalk w) = (d : WithBot ℕ∞)`.
  Its existential Noetherianity, finite dimension, regular-sequence and unit
  witnesses always exist on the regular Noetherian schemes under consideration.
* Condition (c) is `∀ z : Z, IsPunctuallyPureAt ℓ hℓ X (i z)`, precisely all
  points of the set-theoretic image i(Z), including points not closed in X.
* The conclusion is `(a → b → c) ∧ (a → c → b) ∧ (b → c → a)` with each
  occurrence written out. All three implications appear. Arbitrary regular
  Noetherian pairs include their localizations; no global finite-dimension,
  excellence, finite-type, constructibility, connectedness or nonemptiness
  assumption is present.

Dependency declarations read and reused:

* `Sheaf.AlgebraicGeometry.PunctualPurity`: `punctualPurityClassMap`,
  `IsPunctuallyPureAt`, `IsPunctuallyPure`, and its `regularImmersionClasses`.
* `Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus`:
  `regular_immersion_class_calculus`, `RegularImmersionClassFamily`,
  `regularClassCoefficients`, `regularClassTwist`.
* `Sheaf.AlgebraicGeometry.IsRegularScheme`: `AlgebraicGeometry.IsRegularScheme`.
* `Sheaf.AlgebraicGeometry.StalkRegularClosedImmersion`:
  `AlgebraicGeometry.IsStalkRegularClosedImmersion`.
* `Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange`:
  `closedSupportPlus`, `closedSupportPlusAdjunction`, `closedSupportPlusCommShift`.
* `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its coefficient source:
  `AlgebraicGeometry.Etale.DerivedCategoryModule`; Mathlib `DerivedCategory.Plus`.
* `Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist`:
  `AlgebraicGeometry.Scheme.finiteEtaleTateTwist`, through `regularClassTwist`.
* Mathlib `AlgebraicGeometry.Scheme.residueField`, `Scheme.residue`,
  `AlgebraicGeometry.Spec`, `Spec.map`, `IsClosedImmersion`, and `ringKrullDim`.

All declaration names above that are not explicitly qualified are in
`AlgebraicGeometry.Etale`. Already stated proof-dependency modules remain imported
without `public`; the eight-step proof plan is unchanged.

Edge cases checked: empty Z has vacuous (b) and (c) and the unique zero-category
map in (a); codimension zero includes clopen and identity immersions; local
dimension zero retains d=0 and the empty punctured spectrum; a trait's closed
point gives (a) equivalent to (c) since its residue field is punctually pure.
The scheme universe u is arbitrary, with coefficients at u+1 as in the dependency.
No equality of independent universes is imposed.

Searches made for an existing statement and the names used:

* `msearch.py leanfinder`: "Punctual purity of regular closed pairs two of three with
  supported Kummer class maps". Eight hits were unrelated simplicial regularity,
  radicial maps and regular-sequence localization; none is this purity criterion.
* `msearch.py loogle`: `"IsIso", "Ext"`. Twelve generic Kan extension and cone
  isomorphism hits; no cohomological purity statement.
* `msearch.py leansearch`: "Punctual cohomological purity regular schemes two out of
  three for a closed immersion". Eight generic scheme closed-immersion hits, no match.
* `msearch.py grep`: `punctual.*pur|PunctuallyPure|punctually_pure|Gysin`. No relevant
  cohomological-purity assertion; the general Mathlib sheaf-topology hits do not match.
* `rg` over `WeilConjectures` for punctual-purity and regular-class names found only
  Weil/Frobenius weight purity, a different notion. The exact blueprint-ID grep found
  no upstream declaration. The project `lean/Sheaf` search found the class calculus
  and unrelated punctual base-change modules but no existing two-of-three criterion.
* Searches of `dag/lean_names_upstream.json`, Mathlib, upstream WeilConjectures and
  `lean/Sheaf` for all six chosen declaration names found no collisions.


A current project search additionally finds `PunctualPurity.lean` and its landed
`def-per-punctual-purity` node. Reading the full signatures and docstrings showed
that its map and predicates are exactly those needed here. They replace the
saved private copies. Searches of upstream WeilConjectures still find only
Frobenius-weight purity; no existing two-of-three criterion was found.

The item node differs from the shared node only in lean and additions to
stmt_deps of three already landed definitions: def-per-stalk-regular-closed-immersion,
def-per-closed-support-plus-adjunction, and def-per-punctual-purity. No dependency
node is changed. The pre-existing class-calculus docstring disputes whether its
laws establish uniqueness; this packet uses that published dependency unchanged.
There is no dispute or correction of this item's statement.

## Second reading by Q48

This is the dispatcher's required self-check, not an independent second worker;
the brief explicitly prohibits starting agents and reserves independent review
for the maintainer. With the node, its eight proof steps, source excerpt and
module open, checked prime, coefficient field, regularity, Noetherianity,
closed immersion, codimension, invertibility, all three purity conditions and
all three implications as matched above. The mismatch found was duplicate
punctual-purity helpers after Q03's definition landed; repaired by reusing the
published declarations. No case or mathematical hypothesis changed. The theorem
signature equals lean.statement verbatim; autoImplicit is false; universes and
variables are bound; every line is at most 100 characters; the sole sorry is the
named theorem. No fabricated independent review is claimed.

## Validation

The initial saved-packet dry run compiled its redundant Tate overlay, then
reported a 60-second timeout in the automatically compiled
RegularImmersionClassCalculus prerequisite, confirmed on the server. Removing
the redundant overlay permits normal use of the published compiled dependencies.
After replacing the duplicate helpers, prescribed scompile.py succeeds for the
actual final module in both sandbox and library names, without diagnostics:
5.8 seconds and 5.2 seconds, respectively. Required deliver2.py preflight follows.

The final deliver2.py --no-push completed after the shared-fetch wait and printed
OK: commit 0379e1ebd3 passes preflight and compiles, with nothing pushed. The packet
contains just the item module, its node, and this report. No dependency source or
node is republished.

## Worker report

The module `Sheaf.Paper.WeilPullbackLocalFrobenius` states
`WeilConjectures.fdWeilPullbackLocalFrobenius` with a `sorry` proof. Its sole
helper, `fdWeilLocalEigenvalues`, constructs the ordinary multiset of roots of
the characteristic polynomial of the recorded degree-zero local Frobenius.
Its finite-dimensionality instance comes from the recorded point category;
there is no additional finiteness hypothesis and no postponed data construction.

Hypothesis and clause audit:

- The finite field, its positive prime-power cardinality, and chosen algebraic
  closure are `D : FiniteFieldDatum`. The distinct coefficient prime and fixed
  algebraic closure of Q_l are `c : D.CoefficientDatum`. These are the recorded
  coefficient and size conventions, with all universes explicitly bound.
- `X₀ Y₀ : Over (Spec (.of D.k₀))` are schemes over the same finite field.
  The two `LocallyOfFiniteType`, two `QuasiCompact`, and two `IsSeparated`
  instances say exactly separated finite type for each model.
- `f₀ : X₀ ⟶ Y₀` is a morphism over k₀. `zlFiberMap D f₀` is its actual base
  change to k; `zlPull` is exactly common-stage derived inverse image along it.
- `F : sfCommonStageWeilSheaf ...` means a common-stage fixed pair whose
  underlying constructible complex is in the recorded standard heart.
  The first conjunct asserts `sfCommonStageHeartProperty` on the actual
  `zlPull` image of `F.obj.carrier`. `zlWeilPull` equips this same carrier
  with the induced Weil structure using the normalized Frobenius square.
- `z : {z : X₀.left // z ∈ closedPoints X₀.left}` quantifies over every closed
  point. The witness `hx` states its image is closed. The finite-extension
  clause is `(f₀.left.residueFieldMap z.val).hom.Finite`, which uses the
  actual residue-field embedding. The positive degree is Mathlib's
  `f₀.left.residueDegree z.val`, with the explicit inequality `1 ≤ ...`.
  `Nat.card κ(z) = Nat.card κ(x) ^ residueDegree` is precisely q_z = q_x^e.
- `ιz`, `ιx` are residue-field embeddings into the fixed k, with `hz`, `hxι`
  requiring their k₀ compatibility. The subsequent implication assumes
  exactly compatibility of their geometric points: zbar followed by the
  base-changed map is xbar. No geometric point or return is postulated to
  be fixed by Frobenius as a scheme morphism.
- `comparison` is a natural isomorphism of Qbar-linear fibre functors from
  the existing Weil heart to `ModuleCat c.Qbar`, directed from the pulled
  back fibre at zbar to the original fibre at xbar. Its components are
  automatically Qbar-linear. Naturality is encoded by `NatIso` itself.
- The equation is written in categorical composition order as
  `F_z ≫ comparison = comparison ≫ ModuleCat.ofHom (F_x.hom ^ e)`.
  This is exactly c F_z = F_x^e c, with the existing geometric local
  Frobenius convention. The right power is in the endomorphism algebra
  of the coefficient module, not an iterate of a scheme morphism.
- The final equality maps `fun α ↦ α ^ e` over the characteristic-polynomial
  root multiset. It retains algebraic multiplicities, including collisions
  of powers; it does not replace the multiset by a set.

Dependency declarations used (full signatures and docstrings read):

- `Sheaf.Paper.SfWeilSheafComplex`: `sfCommonStageWeilSheaf`,
  `sfCommonStageWeilForget`, `sfWeilPrimeInvertible` and finite-stage pairs.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `commonStageDerivedPullback`
  and its unique object/representative-map characterization.
- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty`.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localClosedPoint`, its residue-field
  compatibility, degree and return, and the finite-stage local operators.
- `Sheaf.Paper.WeilIndSheafCategory`: `zlFiberMap`, `zlPull`,
  `zlFrobeniusSquare`, `zlWeilPull`. The square uses the uniquely normalized
  integral composition comparison; the heart functor has this actual
  derived carrier. Its owning landed node `def-zl-weil-ind-sheaf-category`
  was added to stmt_deps to cite the reusable canonical construction.
- `Sheaf.Paper.RationalStalkExact`: `wfPointFunctor`, `wfSheafFibre`,
  `wfSheafClosedFrobenius` and their explicit common-stage point transports.
  Its owning landed node `lem-wf-rational-stalk-exact` was added to stmt_deps.
  The exact-sequence theorem is not used as a pullback theorem.
- `Sheaf.Paper.CoefficientCohomologyModules`:
  `DerivedCategory.coefficientQbarCohomology_finite` supplies the finite
  vector space instance used by the eigenvalue helper.
- Mathlib `AlgebraicGeometry.Scheme.Hom.residueDegree`,
  `Scheme.Hom.residueFieldMap`, `RingHom.Finite`, `LinearMap.charpoly`,
  and `Polynomial.roots` are reused, without duplicate definitions.
- All already stated proof dependencies are imported directly:
  GeneralAlgebraicallyClosedCoefficients, ConstructiblePullbackTExact,
  ClosedPointField, PointSectionsScalarExtension, and the derived/local
  dependencies above. The three currently unrecorded proof-interface nodes
  (integral-pullback-comparison-realization, local-frobenius-transport-
  normalization, frobenius-point-transport-natural) have no module to import.
  They are not required to type this statement; the proof docstring retains
  their precise roles and does not replace them by hypotheses.

Edge cases checked: the empty source has no closed points, but still has the
heart-preservation clause; the zero sheaf has the empty characteristic-root
multiset; residue degree one includes identity maps without restriction;
positive e excludes only the impossible zero degree of a finite field
extension. Powers may merge distinct eigenvalues and the multiset preserves
both occurrences. Non-dominant, non-proper and non-smooth morphisms are allowed.
No finite Tor-amplitude assumption or finite-ring substitute is introduced.
The common-stage fibre has actual finite-dimensional scalar extension, rather
than the unrelated stalk of a pro-etale Qbar sheaf.

Searches performed:

- `msearch.py ... leanfinder`: "Pullback of a constructible rational Weil
  sheaf identifies local Frobenius with the residue degree power on stalks".
  Eight hits concerned scheme residue-field maps and pullback carriers;
  none states the rational Weil-sheaf assertion.
- `msearch.py ... loogle`: "LinearMap.charpoly, Multiset.map,
  Scheme.Hom.residueFieldMap" returned zero hits, unknown unqualified
  `Scheme.Hom.residueFieldMap`. Its fully qualified Mathlib source was
  subsequently read in AlgebraicGeometry/ResidueField.lean.
- `msearch.py ... grep`: `stalk.*[Ff]robenius|[Ff]robenius.*stalk` returned no hits.
- `msearch.py ... leansearch`: "Natural local Frobenius stalk isomorphism for
  inverse image of constructible rational Weil sheaves" returned eight generic
  stalk-pullback comparisons; none states this coefficient-specific theorem.
- `rg` of WeilConjectures found the concrete upstream category in
  WeilSheaf/StalkUpperStar.lean and StalkCharpoly.lean. The source's cited
  ranges were read: they concern concrete adic Weil sheaves, not the actual
  common-stage heart. No equivalence with this category is assumed.
- The exact node-id search in WeilConjectures returned no match. Searches of
  lean/Sheaf found and reused SfWeilSheafComplex, RationalStalkExact,
  WeilIndSheafCategory, and the local Frobenius/point cohomology modules.
- `rg` of Mathlib ResidueField.lean found the exact residue degree already
  defined; an initial degree wrapper was discarded before delivery.
  Existing finite ring-homomorphism and characteristic-root constructions
  are used directly. Searches of dag/lean_names_upstream.json, the project
  modules and upstream source found no collision with the two new names.

The blueprint Step 2 source and its concrete upstream comparison were read.
No statement fault, correction or STATEMENT-DISPUTED remains. No new DAG node
or dependency repair is needed.

## Second reading by Q40

Author self-check, not an independent agent review: compared the final
signature clause by clause with the item and all four recorded dependencies.
The two additional landed interfaces supply canonical constructions only;
the statement still concerns every separated finite-type model morphism and
every constructible rational Weil sheaf. The natural isomorphism is on the
actual fibres; its operator equation uses the exact residue degree and the
root equality keeps multiplicity. All data definitions are explicit and the
only new theorem has proof `sorry`. The first compile exposed the need to
name the finite-dimensional instance at the fibre's exact type and to take
powers in its linear endomorphism algebra; both were corrected without any
new hypothesis or mathematical change. The maintainer supplies the independent
review required by the dispatcher brief.

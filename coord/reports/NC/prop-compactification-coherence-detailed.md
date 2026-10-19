## Worker report

The module `Sheaf.Paper.CompactificationCoherence` states
`AlgebraicGeometry.ProEtale.compactification_coherence`, with one `sorry` and no
proofs of mathematical assertions. Its real-data helper
`AlgebraicGeometry.ProEtale.compactificationOriginCandidate` restricts the existing
compactification candidate to the existing witnessed etale-origin category, using
exactly the inverse coefficient realization from the recorded comparison definition.
It defines no alternative proper-open map, direct image, extension by zero, or
coefficient ring. No new DAG nodes and no statement corrections are needed.

The node and source read were
`literature/blueprint/master/blueprint/sec-smooth-purity/sk-def-sf-operations/prop-compactification-coherence.md`,
order 1485, statement and entire proof. All ten statement-dependency nodes were
read, including their Lean records and the source signatures/docstrings. The
proof-dependency records were also checked to assemble the proof imports and the
nine-step proof docstring.

Hypothesis-by-hypothesis correspondence:

| Node hypothesis | Lean rendering |
| --- | --- |
| A field K0 | `(K₀ : Type u) [Field K₀]` |
| X and Y are K0-schemes | `{X Y : Scheme.{u}}`, their two `Over (Spec (.of K₀))` instances |
| Both structure maps are of finite type | `LocallyOfFiniteType` and `QuasiCompact` on each structure map |
| f is a K0-morphism | `(f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]` |
| f is separated and of finite type | `[IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]` |
| l is prime | `(l : ℕ) [Fact l.Prime]` |
| Its image in K0 is invertible | `(hl : IsUnit (l : K₀))` |
| E is a finite extension of Q_l | `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` |
| n is a positive integer | `(n : ℕ) (hn : 1 ≤ n)` |
| A is A_(E,n) | `Padic.coefficientExtensionRing l E n` everywhere, with the recorded `ULift` to the coefficient universe |
| Finite-torsion coefficient convention | `Padic.finite_coefficientExtensionRing l E n hn` supplies finiteness; the discrete topology is explicitly bottom, exactly as in `RefinementFiniteLevelOrigin` |
| Objects and arrows of Comp(f) | `Compactification f` and its recorded refinement category `c₁ ⟶ c₂` |

The finite-torsion constructibility sentence fixes the coefficient convention; it
does not impose constructibility on every input K. The source explicitly claims
the comparison on the whole bounded-below etale-origin category, which includes
more than bounded constructible objects. Accordingly there is no added
constructibility, finite Tor dimension, or bounded-above hypothesis.

Clause-by-clause correspondence:

| Node clause | Lean rendering |
| --- | --- |
| The functors are R p_* after exact j_!, restricted to the declared domain | `compactificationOriginCandidate` is the existing `etaleOriginForgetful`, then the inverse `refinementCoefficientEquivalence`, then `rightDerivedLowerShriekOfCompactification` |
| Each refinement has a canonical natural isomorphism of these candidates | The existential `theta`, whose values have type `compactificationOriginCandidate ... c₁ ≅ compactificationOriginCandidate ... c₂` |
| This is the proper-composition isomorphism followed by R p₂_* of the inverse proper-open isomorphism | The first conjunct fixes every component to `refinementComparisonIsomorphism K₀ l hl E n hn f r O`, whose full definition was read: equality transport by `r.hom_g`, `finiteDirectImageComposition` at j₁!K, and proper direct image of `refinementProperOpenIso ... r O` inverse |
| The intermediate proper-open isomorphism is in the ambient derived category | `refinementProperOpenIso` and the normalized comparison component live in the ordinary unbounded derived category of fixed-scalar module sheaves; its inputs retain a bounded-below origin witness |
| Identity refinements give identities | `∀ c, theta c c (𝟙 c) = Iso.refl _` |
| Refinements compose transitively | `theta c₁ c₃ (r ≫ s) = theta c₁ c₂ r ≪≫ theta c₂ c₃ s` |
| Every finite collection has a common refinement | `∀ (m : ℕ) (c : Fin m → Compactification f), ∃ d, ∀ i, Nonempty (d ⟶ c i)`; enumeration by `Fin m` represents every finite family |
| Any pair of candidates has a natural comparison isomorphism | The existential `comparison : ∀ c₁ c₂, candidate c₁ ≅ candidate c₂` |
| It is obtained through a common refinement | For EVERY `d`, `r₁ : d ⟶ c₁`, `r₂ : d ⟶ c₂`, `comparison c₁ c₂ = (theta d c₁ r₁).symm ≪≫ theta d c₂ r₂` |
| It is independent of common refinement and its arrows | The same universal equation holds for every d and both arrows, so all choices give the same `comparison`; no equality or uniqueness of refinement arrows is assumed |
| The triple cocycle | `comparison c₁ c₂ ≪≫ comparison c₂ c₃ = comparison c₁ c₃` |
| The domain has an etale-origin witness, rather than arbitrary pro-etale complexes | The input category is exactly `RefinementFiniteLevelOrigin l E n hn X`, the coefficient specialization of recorded `EtaleOriginDerivedCategory`; its objects retain `(K,L,alpha)` and its Homs are ALL ambient morphisms of K |

The helper's object at O is definitionally the fixed-scalar object used by
`refinementFiniteLevelFixedObject`, followed by the recorded candidate. This was
checked by elaboration of the component-normalization equality, without casts or
extra equality hypotheses. The helper acts on every ambient morphism using the
same inverse coefficient-equivalence functor. It does not retain only those maps
that have already been presented as etale pullbacks. Naturality therefore includes
the identity map between two witnesses for the same K; the expected independence
of witnesses follows as explained in proof step 4.

Dependency declarations used (signatures and docstrings read):

- `WeilConjectures.Compactification.Refinement`:
  `AlgebraicGeometry.Compactification.Refinement` and its `category`, with
  `hom`, `i_hom`, `hom_g`, identity and composition. Properness of a refinement
  is its existing instance.
- `Sheaf.Paper.RefinementComparisonIsomorphism`:
  `AlgebraicGeometry.ProEtale.refinementComparisonIsomorphism`,
  `RefinementFiniteLevelOrigin`, `refinementFiniteLevelFixedObject`,
  `refinementCoefficientEquivalence`, and the constituent
  `refinementComparisonAtWitness`/`refinementProperOpenIso`.
- `Sheaf.Paper.EtaleOriginDerivedCategory`:
  `AlgebraicGeometry.ProEtale.EtaleOriginDerivedCategory` and
  `etaleOriginForgetful`; both are publicly imported by the comparison module.
- `Sheaf.Paper.RingedEtaleOriginWitness`:
  `AlgebraicGeometry.Scheme.EtaleOriginWitness` is an abbreviation for the same
  `AlgebraicGeometry.ProEtale.EtaleOriginWitness` defined in
  `Sheaf.Paper.EtaleOriginWitness` and used by the recorded category. The latter
  module is already publicly imported. The larger ringed wrapper is not needed
  for this abbreviation and is not imported, avoiding its conflicting framework.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, together with
  `Padic.coefficientExtensionRing` from `CoefficientExtension`; both come through
  the recorded comparison dependency. The full coefficient construction was read.
- `WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek`:
  `AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification`, the
  existing fixed-scalar candidate (see dependency-record repair below).
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`:
  the recorded `Scheme.sfIntrinsicExtensionByZero` is the upstream
  `ProEtale.openImmersionLowerShriek` conjugated by its specified intrinsic
  coefficient equivalences. Its body and docstring were read. We use that same
  upstream functor in the fixed-scalar presentation, not a private definition.
- `Sheaf.Paper.SfDerivedDirectImage`:
  the finite-level part is the canonical `proEtaleConstantDerivedDirectImage`,
  the right derived intrinsic direct image. The integral tower is irrelevant to
  this finite-level assertion. Here its fixed-scalar presentation is the existing
  `(ProEtale.lowerStar ... c.g).rightDerivedFunctor` inside the candidate and
  `finiteDirectImageComposition`, exactly as in the recorded refinement comparison.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible` was read. Its predicate is not a
  hypothesis or conclusion of this coherence assertion. Thus that larger module
  is not an unused import; its coefficient ring and finiteness declaration above
  are used instead.
- `def-weil-scheme-morphism-properties` is explicitly a convention node without
  a module or declaration. The actual properties are Mathlib's `IsSeparated`,
  `LocallyOfFiniteType`, and `QuasiCompact` exported by the recorded modules.

The proof docstring follows all nine DAG proof steps. In particular it does not
assume the refinement square Cartesian, infer naturality merely from objectwise
invertibility, infer uniqueness of refinement arrows, or omit the two successive
parallel-arrow equalizations. The proof imports include the etale proper-open
construction, derived open restriction, derived extension-zero base change,
clopen-section direct image, extension-zero site comparison, fixed-scalar derived
comparison pullback, global comparison module, and the recorded cofilteredness
module. The recorded proper-open and finite-direct-image-composition modules are
already public imports of `RefinementComparisonIsomorphism`.

Import-conflict check: a wrapper compile importing the recorded refinement module
along with `AmbientExceptionalRightAdjoint`, `IntrinsicFiniteTorsionConstructibility`,
`RingedEtaleOriginWitness`, and `SfDerivedDirectImage` failed with the duplicate
`AlgebraicGeometry.ProEtale.«term(_)_*[_]»` between the general upstream
`UpperLowerStar.Defs` and `FiniteCoefficient.UpperLowerStar.Defs`. The server
confirmed the same failure. The recorded proof-only
`Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived` import causes the same
collision and is omitted for this reason. The mathematical full-faithfulness
step remains in the proof plan; no full-faithfulness hypothesis is added. All
other used constructions have their existing fixed-scalar declarations through
the comparison dependency. This follows the explicit instruction to import only
the required side and prefer the general upstream modules for duplicates.

Edge cases checked:

- `m = 0` is permitted and requires a compactification even for the empty family;
  there is no nonempty-family hypothesis. Cofilteredness over the field supplies it.
- `m = 1`, repeated compactifications, and identity refinements are included.
  Setting the common refinement to the compactification itself makes the pair
  comparison identity; reversing the two arrows yields the inverse comparison.
- Distinct arrows from the same common refinement, as well as unrelated choices
  of common refinement, are covered by the universal normalization equation.
- No density, scheme-theoretic dominance, or Cartesian square condition is added
  to a refinement. Extra components outside X are permitted.
- Empty schemes and zero derived objects are not excluded.
- The source requires `n ≥ 1`; `n = 1` is included, and `n = 0` is deliberately
  excluded by exactly that source hypothesis. No `Nontrivial` assumption on
  module sheaves or complexes is introduced.
- The scheme universe is u; fixed module coefficients and module sheaves use
  u+1 via `ULift`, exactly as in the recorded comparison. No independent lower
  test-scheme universe or extra equality of site universes is imposed.
- The statement is bounded below only via the retained origin category. It adds
  neither boundedness above nor a claim about arbitrary unbounded-origin objects.

Searches actually run:

- `msearch.py ... leanfinder`: “Natural isomorphisms between compact support
  functors from refinements are coherent and independent of a common
  compactification on etale-origin complexes”. Eight unrelated compact/profinite
  hits (including `Profinite.NobelingProof.spanFunctorIsoIndexFunctor` and
  `CompHausLike.LocallyConstant.functorIso`); no matching assertion.
- `msearch.py ... loogle`: `CategoryTheory.NatTrans, CategoryTheory.IsCofiltered`.
  Successful query, zero hits.
- `msearch.py ... grep`: `compactification|properOpen|proper_open|LowerShriek`.
  Twenty-five topology/compactification hits in the broad Mathlib search; none
  concerns algebraic compactifications and derived compact support.
- `msearch.py ... grep` under `AlgebraicGeometry`:
  `properOpen|proper_open|LowerShriek|compactification`. Successful, zero hits.
- `msearch.py ... leansearch`: “Coherence and independence of compactification of
  the derived direct image with compact support on bounded below etale origin pro
  etale complexes”. Eight hits on etale morphisms/sites and condensed categories;
  none is this coherence theorem.
- `rg` of the upstream project and `lean/Sheaf` for
  `compactification.*coher|refinementComparison|commonRefinement|common_refinement`
  found the recorded objectwise comparison and the general compact-support
  formalism. The latter's refinement interface requires an `IsPullback` argument;
  it does not state this assertion for arbitrary proper refinements on witnessed
  pro-etale objects. The etale coherence theorem is a different site/interface.
- `rg` of upstream for the exact node id returned no declaration. `rg` of
  Mathlib, upstream and `lean/Sheaf` for `compactificationOriginCandidate` and
  `compactification_coherence` returned no prior declaration.

No `STATEMENT-DISPUTED` issue was found. The original statement, dependencies,
proof and proof-dependency lists are unchanged. Only Lean records are changed.

Validation: `scompile.py NC prop-compactification-coherence-detailed` compiled
`CompactificationCoherence.lean` at both its sandbox and library module paths
cleanly (2.3 s and 2.5 s). There is exactly one postponed theorem, and its
complete proof plan is in its docstring. The required delivery dry run is the
last worker check; the independent second reader supplies the second-reading
section and performs delivery.

## Dependency modules

`def-weil-compact-support-candidate`: lean-only attachment repair to the EXISTING
`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactification` in
`WeilConjectures.SixFunctors.ProEtale.Derived.LowerShriek`. No dependency module
and no additional theorem are written. The old recorded intrinsic wrapper cannot
be imported with the recorded refinement-comparison dependency because it brings
in the colliding finite-coefficient notation declarations described above. The
existing upstream definition, specialized to `ModuleCat (ULift A_(E,n))`, is the
same termwise exact extension by zero followed by K-injective proper derived
direct image. Its full signature and docstring, and the old wrapper's full body,
were read. The intrinsic wrapper itself is formed from these functors by the
specified coefficient equivalences. The consumer now uses this same fixed-scalar
presentation, transported from the recorded origin category by exactly the
comparison dependency's `refinementCoefficientEquivalence`. Only this dependency's
`lean` field changes, with the required explanatory note. No node statements or
other dependencies are restated.

## Second reading by NC

I independently read the node's statement and all nine proof steps, the complete
blueprint source `sec-smooth-purity/sk-def-sf-operations/prop-compactification-coherence.md`
(order 1485), the delivered Lean file, and the ten statement-dependency records.
The immediate source is this blueprint proposition, rather than a single Stacks
lemma. Its proof explicitly specifies bounded-below etale antecedents; its final
paragraph explicitly limits the assertion to the witnessed origin domain. The
finite-torsion sentence specifies the coefficient convention, not an additional
constructibility hypothesis on every input. No statement correction is needed.

My object/hypothesis/conclusion checklist, with verdicts:

| Source item | Lean rendering and verdict |
| --- | --- |
| Field K0 | `K₀ : Type u`, `[Field K₀]`; exact. |
| Finite-type K0-schemes X,Y | `X Y : Scheme.{u}`, two `Over` structures, and `LocallyOfFiniteType` plus `QuasiCompact` on both structure morphisms; exact finite type, without a separatedness assumption on either structure morphism. |
| Separated finite-type K0-morphism f | `f : X ⟶ Y`, `f.IsOver`, `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f`; exact. |
| Prime l invertible in K0 | `l : ℕ`, `Fact l.Prime`, `hl : IsUnit (l : K₀)`; exact, not an extra characteristic-zero assumption. |
| Finite extension E/Q_l | `E : Type u`, `Field E`, `Algebra ℚ_[l] E`, `FiniteDimensional ℚ_[l] E`; exact. |
| Positive level n and coefficient A | `n : ℕ`, `hn : 1 ≤ n`, `Padic.coefficientExtensionRing l E n`; exact. I opened the coefficient definitions: the ring is the quotient of the recorded valuation ring by the nth power of the ideal generated by its recorded uniformizer. |
| Finite discrete coefficients | `finite_coefficientExtensionRing` supplies `Finite`; the helper sets the topology to bottom and uses `ULift` for the coefficient universe, exactly as the recorded comparison specialization; exact. |
| Compactifications c_i and proper refinements u | `Compactification f` and its category Homs `c₁ ⟶ c₂`; exact. I opened `Compactification` and `Refinement`: the latter retains both `i_hom` and `hom_g`, and properness follows from its existing instance. No density or Cartesian-square restriction is present. |
| Domain of the comparison | `RefinementFiniteLevelOrigin l E n hn X`; exact. I opened its abbreviation and `EtaleOriginDerivedCategory`, `EtaleOriginWitness`, and `etaleOriginForgetful`: the sigma retains the bounded-below K, L and alpha, the induced category has every ambient morphism of K, and the forgetful functor includes K into the unbounded category. |
| Candidates R p_* j_! | `compactificationOriginCandidate`; exact. Its body is the recorded forgetful functor, the inverse recorded coefficient equivalence, and `rightDerivedLowerShriekOfCompactification`. I opened that last abbreviation: it is the exact termwise j_! followed by the total right-derived p_*, in that order. |
| Canonical natural comparison along each refinement | The outer `∃ theta` has functor-isomorphism values; its first conjunct fixes `(theta c₁ c₂ r).app O` to `refinementComparisonIsomorphism ... r O` for every O; exact. This supplies naturality rather than just pointwise isomorphisms. |
| Proper-composition followed by R p₂_* of inverse proper-open comparison | I opened `refinementComparisonAtWitness`, `refinementProperOpenIso`, `properOpenProEtaleIso`, and `finiteDirectImageComposition`. The normalization is equality transport along `r.hom_g`, the canonical direct-image compositor at j₁!K, then direct image of the inverse witnessed proper-open isomorphism; exact orientation and canonical map. |
| Proper-open comparison in ambient derived category | Those normalized components use the unbounded fixed-scalar derived category, after the bounded-below witness inclusion; exact. It makes no claim for pro-etale inputs lacking an etale origin. |
| Identity and transitivity for refinements | `theta c c (𝟙 c) = Iso.refl _` and `theta c₁ c₃ (r ≫ s) = theta c₁ c₂ r ≪≫ theta c₂ c₃ s`; exact order. |
| Common refinement for every finite collection | `∀ m : ℕ, ∀ c : Fin m → Compactification f, ∃ d, ∀ i, Nonempty (d ⟶ c i)`; exact, since every finite family can be enumerated and repetitions are allowed. |
| Natural comparison for each pair | The inner `∃ comparison` has functor-isomorphism values for every ordered pair; exact. |
| Construction through a common refinement and independence | Its normalization holds for every d and every pair of arrows `r₁ : d ⟶ c₁`, `r₂ : d ⟶ c₂`, and identifies comparison with `(theta d c₁ r₁).symm ≪≫ theta d c₂ r₂`; exact. The universal equation handles different arrows as well as different common objects; it assumes no uniqueness of refinement arrows. |
| Cocycle for triples | The final equality `comparison c₁ c₂ ≪≫ comparison c₂ c₃ = comparison c₁ c₃`; exact. |

Dependency-record repair: I separately checked the delivered copy of
`def-weil-compact-support-candidate` against its full node statement and its
blueprint definition (order 1472). Only its `lean` field differs from the shared
base. I opened the old recorded `sfAmbientCompactSupportCandidate` and
`sfIntrinsicExtensionByZero`, and the proposed existing upstream abbreviation.
The former is intrinsic exact extension by zero followed by intrinsic derived
direct image; its extension by zero is explicitly conjugated from the same
fixed-scalar upstream functor by the coefficient realization equivalences. The
new record selects that existing fixed-scalar construction, which is also the
one used by the already recorded refinement comparison. Thus the import-conflict
repair changes the presentation, not the candidate or its domain. Its explanatory
`lean.note` is appropriate; no dependency module or new node is needed. I also
opened `Scheme.EtaleOriginWitness`: it is an abbreviation of precisely the
`ProEtale.EtaleOriginWitness` used here, not a different origin notion. The
recorded intrinsic constructibility predicate and integral direct-image tower
were inspected; neither imposes an additional hypothesis on this finite-level
coherence statement.

Edge cases: `m = 0` requires a compactification through the displayed existential,
so the finite-family clause does not become vacuous. Singleton families, repeated
objects, identity refinements and parallel arrows are included. In particular,
the common-refinement normalization with both identity arrows gives comparison
of an object with itself equal to the identity, and naturality includes the
identity ambient map between two different witnesses for the same K. The empty
scheme, zero complex, and refinements with extra components outside X are not
excluded. `n = 1` is included; `n = 0` is excluded by exactly the source's
positive-level assumption. All characteristics with l invertible are included.
The scheme/site universe remains u, with module coefficients in u+1 through
ULift; no equation between site object and morphism universes or independent
smaller test universe is imposed. There is no constructibility, upper-boundedness,
finite-Tor-dimension, or extra Noetherian hypothesis.

Independent searches, using different queries from the first worker:

- `msearch.py ... leanfinder`: "Independence of derived compact support from
  compactification, natural refinement isomorphisms with identity composition and
  cocycle laws"; eight hits, all on compactly supported continuous maps and related
  topology, no match.
- `msearch.py ... loogle`: `CategoryTheory.Iso, CategoryTheory.IsCofiltered`;
  successful query, no hits.
- `msearch.py ... grep`:
  `rightDerivedLowerShriek.*(Iso|iso)|refinement.*(coher|trans)|compactification.*(independ|cocycle)`;
  two open-cover refinement hits in Mathlib, no matching theorem.
- Independent `rg` of Mathlib's algebraic geometry/category theory, upstream
  `WeilConjectures`, side `lean/WeilConjectures`, and `lean/Sheaf` for independence,
  coherence, refinement naturality/transitivity and compactification isomorphisms.
  I opened the closest side/upstream declarations in
  `ProEtale/Derived/LowerShriekIndependence.lean` and
  `Etale/Derived/LowerShriekCoherence.lean`.
  `rightDerivedLowerShriekOfCompactificationOriginIso` and its `_trans` lemma are
  comparisons after precomposition by nu^* on the category of bounded-below etale
  complexes. They do not state the present normalization to the recorded
  proper-open comparison on every witnessed object and every ambient morphism,
  nor independence of all common-refinement arrows. The etale refinement laws
  concern another site. Thus neither is an exact existing attachment for this
  node; the delivered statement does not duplicate an existing statement.
  Exact searches for the two delivered declaration names found no prior match.

H5/H6/H8/H9 checks: the helper contains only the three specified real functors
and the already recorded coefficient instances; it has no sorry data. The only
postponed theorem is `compactification_coherence`, with proof `sorry`. Its
nine-step docstring follows the node, including actual naturality, full
faithfulness for arbitrary ambient maps, and successive equalization of the two
parallel pairs. Both declarations and the module have source/blueprint
docstrings. There is no file-local notation, private definition, local instance,
or implicit variable/universe; no Lean line exceeds 100 characters. A direct
text comparison confirms the item's `lean.statement` equals the entire signature
verbatim. Both node copies change only `lean` relative to the shared base.

Findings and changes: no mathematical or Lean mismatch was found; no Lean source,
node signature, dependency statement, or target was changed by the second reader.
I appended this independent reading and its additional search evidence only.
The prescribed `scompile.py` compilation passed without warnings at both the
sandbox and library module paths (2.7 seconds each), compiling its required
overlay dependencies separately. An initial compile invocation used a path
relative to the read-only checkout; rerunning with the absolute sandbox path
resolved that invocation error. The delivery dry run and delivery follow below.

Delivery validation: `deliver2.py NC prop-compactification-coherence-detailed
--no-push` returned `OK`: the module and existing-declaration probe compiled and
the server preflight passed. No mathematical fixes were required.

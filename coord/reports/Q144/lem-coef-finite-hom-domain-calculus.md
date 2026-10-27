## Worker report

The module `Sheaf.Paper.FiniteHomDomainCalculus` states the clauses of
`lem-coef-finite-hom-domain-calculus` as separate named theorems. All theorem
proofs are `sorry`; definitions contain explicit data. The node statement and
proof are unchanged. The additional statement dependencies are already-landed
nodes supplying the canonical scalar/pullback comparison, the normalized identity
scalar comparison, and the existing all-complex tensor-normalization predicate.
No new DAG node or dependency repair is needed.

Hypotheses and conventions:

- `D : FiniteFieldDatum.{u}` supplies the finite field and its algebraic closure
  `D.k`, of characteristic `D.p`. `[Fact l.Prime]` and `hl : l ≠ D.p` give the
  prime and invertibility convention. `E : Type u`, `[Field E]`,
  `[Algebra (Padic l) E]`, and `[FiniteDimensional (Padic l) E]` give the finite
  coefficient extension. These geometric hypotheses are explicitly retained by
  `include` on each geometric/ambient theorem.
- `finiteHomDomainCoeff l E n` abbreviates the existing positive coefficient ring
  `ULift (Padic.coefficientExtensionRing l E (n + 1))`.
  `finiteHomDomainCoeffFinite` transports the recorded finiteness theorem along
  `Equiv.ulift`. This is only a universe lift, with the actual quotient maps
  `finiteHomQuotient l E h`. As in the recorded arrow, indices `n,m,r : ℕ`
  mean exponents `n+1,m+1,r+1`; `h : m ≤ n`, `k : r ≤ m` cover exactly all
  positive exponents and all allowed towers.
- `X : Scheme.{u}`, `[X.Over (Spec (.of D.k))]`, separation, local finite type,
  and quasi-compactness of the structure morphism express separated finite type
  over the specified field. The pullback theorem has the same assumptions for
  `Y`, and `(f : Y ⟶ X) [f.IsOver (Spec (.of D.k))]`.
- `finiteHomEtale` is the recorded ordinary unbounded small-etale derived
  category of `ModuleCat.{u+1}`-valued sheaves. `finiteHomEtaleReduction` is its
  published scalar extension, and `finiteHomEtaleInternalHom` the published
  derived internal Hom. There is no alternate ringed-site encoding.
- `Etale.DerivedCategory.isBoundedConstructible` is the dependency's exact
  finite-value constructible-cohomology predicate. The Tor condition is
  `hasTorAmplitudeIn ... a b`, which tests every degree-zero module sheaf.
  Finite Tor amplitude is written `∃ a b : ℤ, a ≤ b ∧ hasTorAmplitudeIn ...`.

Clause correspondence:

- `finiteHomDomain_flatModel` first asserts `IsNoetherian X`. Its existential
  cochain complex `P` has `Etale.IsBoundedFlatComplex ... a b P`, constructible
  terms, and `Nonempty (T ≅ DerivedCategory.Q.obj P)`. Bounded-flat means flat
  terms and zero terms outside exactly the given interval. The theorem also
  states K-flatness with `(HomologicalComplex.quasiIso _ (.up ℤ)).kFlat`.
  The reduced complex is the actual termwise
  `ProEtale.etaleSheafExtendScalars (finiteHomQuotient ...) X`; it is bounded
  flat, termwise constructible, K-flat, and represents the actual derived
  reduction of `T`. The final two conjuncts give bounded constructibility and
  the same Tor interval for that reduction.
- `finiteHomDomain_pullback` states exactness of `Etale.upperStar`, bounded
  constructibility of its left-derived image, and preservation of the identical
  Tor interval. Its last conjunct, independently of any constructibility or Tor
  hypotheses, gives the representative-normalization
  equation for the recorded `Etale.scalarPullbackIso`. That existing natural
  isomorphism is between the two actual composite functors, in the derived
  category of B-module sheaves, hence is B-linear. No extra boundedness is
  imposed on its K-flat representatives.
- `finiteHomDomain_monoidal` asserts strong monoidality for the fixed canonical
  `ExceptionalCoefficients.tensorIso` and `unitIso`, with Koszul symmetry.
  `FiniteHomDomainMonoidal` spells out a `Functor.CoreMonoidal` whose
  inverse unit and tensor isomorphisms are precisely those maps (using `HEq`
  to avoid repeated elaboration of equivalent derived monoidal structures),
  together with the Koszul symmetry square for the ordinary etale categories.
  These helper predicates only group this node's equations;
  they do not replace the monoidal structure or choose maps. `HEq` identifies
  the published finite-Hom tensor comparison with this canonical comparison.
  Unit normalization is the recorded `UnitNormalization`. The final conjunct uses
  the owning definition node's
  `Etale.ExceptionalCoefficients.TensorNormalization` directly on its canonical
  `tensorIso`. Its equation is the localization tensorator followed by the ordinary
  scalar balancing comparison, for every pair of cochain complexes; in particular
  it gives the required normalization on flat-term K-flat models. The equation's
  tensor comparison points from F(U tensor V) to F(U) tensor F(V), so this is the
  same normalization with the equality reversed, without the former inverse-family
  wrapper. Both scalar actions are retained.
- `finiteHomDomain_scalarCoherence` states the tensor and unit squares for
  `finiteHomEtaleAssoc`, the actual normalized successive-extension comparison.
  `FiniteHomDomainScalarComposition` groups exactly those two squares. Its
  component and unit families are fixed by `HEq` to the supplied canonical
  maps, avoiding repeated conversion of specialized monoidal structures.
  `FiniteHomDomainScalarIdentity` gives the tensor and unit squares for the
  identity quotient, using the same tensor bifunctor. `finiteHomDomain_quotient_id` identifies the actual quotient ring
  homomorphism with the identity; its proof is postponed. `finiteHomDomainUnit`
  is real data obtained from the recorded `normalizedOriginScalarUnit` and that
  equality. The normalized comparison is the adjunction mate of restriction's
  identity, not an unspecified isomorphism.
- `finiteHomDomain_transpose` expresses the two ambient adjunctions by unique
  evaluation transposes for every `U,K,M` and every map `U tensor K → M` at
  both coefficient levels. The adjunction and counit themselves are the
  dependency's `finiteHomEtaleClosed` data. Its third conjunct characterizes
  the unique transpose of inverse tensor comparison followed by reduced
  evaluation as exactly `etaleFiniteHomCanonical`. Its fourth conjunct is the
  naturality square in both variables (contravariant in K, covariant in M).
- `finiteHomDomain_endpoints` assumes bounded constructibility and finite Tor
  intervals for K and M and concludes those same two membership conditions for
  both `F H_A(K,M)` and `H_B(F K,F M)`. It asserts no invertibility of their map.

Recorded dependency declarations used:

| Node / module | Declaration used |
| --- | --- |
| `def-weil-finite-field-fiber` / `Sheaf.Paper.FiniteFieldFiber` | `WeilConjectures.FiniteFieldDatum` |
| `def-weil-l-adic-coefficient-extension` / `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` | `Padic.finite_coefficientExtensionRing`, existing `Padic.coefficientExtensionRing` |
| `def-weil-scheme-morphism-properties` (convention, Mathlib) | `Scheme`, `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` |
| `def-weil-pbc-derived-categories` / `WeilConjectures.AlgebraicGeometry.DerivedCategories` | `Etale.DerivedCategoryModule` |
| `lem-pur-derived-change-of-rings` / `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel` | recorded cochain-model interface; actual ordinary-etale `Etale.scalarExtension` through the arrow module |
| `def-pur-derived-internal-hom` / `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses` | publicly exposed `Etale.derivedHom`, `Etale.derivedTensorHomAdjunction` |
| `def-weil-pbc-constructible-complexes` / `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes` | `Etale.DerivedCategory.isBoundedConstructible` |
| `def-kun-tor-amplitude` / `Sheaf.AlgebraicGeometry.EtaleTorAmplitude` | `Etale.DerivedCategory.hasTorAmplitudeIn` |
| `def-sf-etale-finite-coefficient-hom-arrow` / `Sheaf.Paper.EtaleFiniteCoefficientHomArrow` | `finiteHomEtale`, `finiteHomQuotient`, `finiteHomEtaleReduction`, `finiteHomEtaleInternalHom`, `finiteHomEtaleClosed`, `finiteHomEtaleTensor`, `finiteHomKoszulIso`, `finiteHomEtaleAssoc`, `etaleFiniteHomCanonical` |
| `def-pc-kflat-complex` / `Sheaf.Algebra.Homology.KFlatIndependentCoefficients` | publicly exposed `MorphismProperty.kFlat` for ordinary sheaf complexes |
| `def-pc-flat-sheaf-modules` / `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite` | `exactFunctor`; existing `ObjectProperty.flat` used by `Etale.IsBoundedFlatComplex` |
| `def-sfb-strong-monoidal-functor` / `Mathlib.CategoryTheory.Monoidal.Functor` | `Functor.CoreMonoidal` |
| `def-pur-etale-scalar-pullback-iso` / `Sheaf.Paper.PurEtaleScalarMateProjection` | `Etale.scalarPullbackIso` and publicly exposed representative comparisons |
| `def-weil-pbc-normalized-origin-scalar-comparisons` / `Sheaf.Paper.NormalizedOriginScalarComparisons` | `ProEtale.normalizedOriginScalarUnit` |
| `def-pur-exceptional-coefficient-normalizations` / `Sheaf.Paper.ExceptionalCoefficientMaps` | `Etale.ExceptionalCoefficients.TensorNormalization`, `tensorIso`, `unitIso`, `UnitNormalization` |
| `def-weil-pbc-etale-constructible-sheaf` / `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` | `Scheme.IsConstructibleEtaleModuleSheaf` |
| `def-weil-pbc-inverse-image` / `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` | `Etale.upperStar` |
| `def-kun-derived-tensor` / `WeilConjectures.SixFunctors.Etale.Derived.Tensor` | `Etale.derivedTensor` |

All already-stated proof-dependency modules are imported as plain imports. The
unstated proof dependency `lem-sp-etale-scalar-flat-model` is named in the proof
plan; the statement requires no construction from it and does not assume its
conclusion as a hypothesis. Each postponed theorem has its own source, blueprint
identifier, and natural-language proof plan in its docstring.

Edge cases checked against the formulas: the empty scheme (no nonempty or
connectedness hypothesis, dimension bound can be zero); the zero object; `a=b`;
negative and shifted Tor intervals; exponent one (`n=0` in this module's indexing);
identity quotients (`m=n`); and the nonflat tower Z/8 → Z/4 → Z/2. There is no
flatness hypothesis on the quotient rings. Arbitrary unbounded objects are
allowed in all ambient tensor and transpose formulas. The finite-value
constructibility predicate, rather than the other upstream finite-generation
predicate, is used throughout.

Searches for an existing complete statement (no match):

- `msearch.py ... leanfinder` with “Derived coefficient reduction preserves
  bounded constructible finite Tor amplitude complexes and is symmetric monoidal;
  reduced evaluation transpose”: eight hits, including `CategoryTheory.Tor'`,
  `Tor`, and derived-category factorization lemmas; none states this result.
- `msearch.py ... loogle "Functor.CoreMonoidal, Functor.Braided"`: zero hits,
  with an unknown-identifier diagnostic for that short name. Direct source search
  found the fully qualified Mathlib `CategoryTheory.Functor.CoreMonoidal` and its
  complete signature was read.
- `msearch.py ... grep "CoreMonoidal|Symmetric|Braided"
  CategoryTheory/Monoidal/Functor`: zero hits for that supplied subdirectory.
  Direct `rg` in the actual `Mathlib/CategoryTheory/Monoidal/Functor.lean` located
  the structure and its unit, tensor, naturality, associativity and unitor fields.
- `msearch.py ... leanfinder` with “bounded constructible finite Tor amplitude
  etale coefficient extension tensor Hom”: eight ordinary etale-algebra hits,
  including `Algebra.Etale.baseChange`; no sheaf-derived statement.
- Direct `rg` for this node id, `finiteHom.*(Domain|Calculus)`, and the proposed
  declaration names in `lean/WeilConjectures`, `lean/Sheaf`, and the upstream-name
  index found no existing declaration of this item. The prescribed
  `grep -rn "lem-coef-finite-hom-domain-calculus" lean/WeilConjectures` also found
  no occurrence. Searches for scalar extension, derived tensor, Tor amplitude,
  normalized comparisons and CoreMonoidal located the reused interfaces above.

No statement correction, disputed assertion, or unresolved node fault is reported.

## Returned delivery repair

The return at immutable head `5f5aafb105ff` identifies a theorem dependency used
only for a plain predicate. Removed `FiniteHomDomainNormalization` and the public
import of `Sheaf.CategoryTheory.DerivedTensorRightExact`; removed
`lem-derived-right-exact-tensor-comparison` from `stmt_deps`. The monoidal theorem
now states `ExceptionalCoefficients.TensorNormalization` directly. Its owning
node `def-pur-exceptional-coefficient-normalizations` is cited and its module is
publicly imported, also accounting for `tensorIso`, `unitIso`, and
`UnitNormalization`. No conclusion of the removed theorem is assumed or used.

Addressed the advisory owner citations for constructible sheaves, inverse image,
and derived tensor, with explicit public imports. Also moved the T, interval,
constructibility and Tor hypotheses into the preservation conjunct of
`finiteHomDomain_pullback`; exactness and the all-K-flat representative comparison
now have no such hypotheses. `Etale.IsBoundedFlatComplex` is the existing upstream
predicate (FlatModel.lean:47), used verbatim rather than copied; its full definition
was checked: zero terms outside [a,b] and flat terms. The existing
`Etale.scalarExtensionRepresentative` is the real derived-adjunction counit in
`Sheaf.Paper.EtaleDerivedScalarTensor`, documented there under the already cited
`lem-pur-derived-change-of-rings`; no new notion is introduced.

Compared the saved packet with current read-only main by JSON fields: only
`lean` and the authorized added `stmt_deps` differ. The mathematical node
statement, proof and proof dependencies remain unchanged. Rechecked identity
quotients, empty schemes, zero objects, shifted intervals and nonflat towers;
the replacement normalization quantifies over all complexes, including those
flat-term K-flat models, with the same representative maps and tensor orientation.

Self-check after the repair: the primary `lean.statement` is byte-for-byte the
module signature; every recorded declaration exists; the removed theorem node
and predicate do not occur in the module or statement-dependency list; all Lean
lines are at most 100 characters, with `autoImplicit false` retained. Local
transparency settings keep `upperStar` and `derivedTensor` abstract and apply the
normal transparency policy inside the pullback section, so its repeated canonical
maps can be elaborated without expanding their constructions. No mathematical
hypothesis or map is changed by these elaboration settings.

Validation: the prescribed `scompile.py Q144 lem-coef-finite-hom-domain-calculus`
completed successfully for the final module, both the sandbox module (30.9 seconds)
and the library module (21.1 seconds), with no compiler errors or warnings.

## Second reading by Q144

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

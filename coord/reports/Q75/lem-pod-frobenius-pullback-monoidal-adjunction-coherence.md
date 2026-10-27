## Worker report

Item: lem-pod-frobenius-pullback-monoidal-adjunction-coherence.
Module: Sheaf.Paper.FrobeniusPullbackMonoidalAdjunctionCoherence.
Namespace: WeilConjectures.PodFrobeniusCoherence.

The module states the actual rational and common-stage Frobenius comparison equations,
and the ordinary adjunction coherence with the original unit and counit. Every theorem
has proof `sorry`: `comparison_lifts`, `ordinary_adjunction_coherent`, and
`frobeniusPullbackMonoidalAdjunctionCoherence`. Their docstrings give respectively
node step 6, steps 7--9, and steps 1--6 plus the ordinary-adjunction application.
All other declarations are real comparison constructions or predicates packaging the
item's clauses. No new independent notion, new DAG node, or dependency module is needed.
The statement, proof, and proof_deps are unchanged.

Sources read: the current `literature/blueprint/latest/blueprint/sec-poincare-duality/
sk-thm-frobenius/prop-weil-operations.proof.md`, and the current
`sec-six-functors/sk-rem-sf-pf-done/lem-fix-weil-operations.proof.md` in the same blueprint.
The latter explicitly defines the ordinary direct-image lift with Ex_*, uses the
pullback Frobenius square, the standard tensor/Hom identifications, and says the
ordinary adjunction assertion is the definition of Ex_*. The item's accepted nine-step
proof supplies the explicit coherence calculations. I did not use the older snapshot
path in the historical source record as the blueprint text.

Hypotheses and context, clause by clause:

- The fixed prime p, a >= 1, q = p^a, finite field k_0 of cardinality q, and chosen
  algebraic closure k are exactly `D : FiniteFieldDatum.{u}`, with the existing
  `prime`, `exponent_pos`, `cardinality_eq`, `card_base`, and closure fields.
- The coefficient prime and inequality are `(l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)`.
  The fixed coefficient closure is `(Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]`. The finite field inside it is
  `(E : AlgebraicallyClosedCoefficients.Index l Ω)`. The rational clause uses the
  dependency's `AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω E`, its canonical
  Shrink transport of the literal finite subfield. Thus E really is inside the fixed
  closure, while the coefficient closure's universe v is independent of the site u.
- Finite-type k_0-schemes are `X₀ Y₀ Z₀ : Over (Spec (.of D.k₀))`, each with
  `LocallyOfFiniteType` and `QuasiCompact` on its structure morphism. There is no
  `IsSeparated` hypothesis on any of these structure morphisms.
- The two separated finite-type maps are `f₀ : X₀ ⟶ Y₀`, `h₀ : Y₀ ⟶ Z₀`, with
  `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact` on their `.left` maps.
- Their geometric maps are the recorded `FrobeniusExchange.fiberMap D f₀` and the
  corresponding map for h₀. This is the existing actual Over.pullback map, not a new
  arbitrary morphism. Geometric schemes are `(D.geometricFiber W₀).left`, and g_W is
  `(D.geometricFrobenius W₀).hom`. The Frobenius is geometric and semilinear, not an
  absolute Frobenius or an assumed k-linear map.
- Prime invertibility is supplied inside the predicate/construction bodies by the
  existing `sfWeilPrimeInvertible D l hl W₀`. It is not an additional hypothesis.
- The two categories are precisely `sfRationalConstructibleCategory` and
  `generalAlgebraicallyClosedConstructibleCategory`; no étale-module or arbitrary
  substitute category is used in these two conclusions.
- Frobenius pullbacks are `sfWeilFrobeniusPullback` and
  `sfCommonStageWeilFrobeniusPullback`. Weil pairs and their arrows use the existing
  `IsoAlgebra`, via its `mapOfNatIso`, carrier, and `str` interfaces. This is the same
  fixed-pair construction as `sfWeilComplex`/`sfCommonStageWeilComplex`.
- Standard lifted structures are the existing `IsoAlgebra.mapOfNatIso`: its structure
  is the comparison followed by the underlying functor's image of theta. Tensor and
  the partial internal Hom retain their existing operations and permitted-pair domains
  from `DerivedPullbackTensorHom` and `SemilinearFieldOperationLifts`; this item does
  not assert a larger internal-Hom domain or a new internal-Hom result.

Conclusions, clause by clause:

- `RationalCoherent` and `CommonCoherent` each quantify natural isomorphisms sF, sH,
  sHF. Their first three conjuncts fix EVERY component to `rationalSquare` or
  `commonSquare`. Those constructions are the dependency's
  `podRationalSquarePullbackComponent` and `podCommonSquarePullbackComponent`, using
  the actual geometric square equality. Hence the existential quantifiers do not
  permit a different Frobenius comparison.
- `rationalComposition` and `commonComposition` are the dependency's canonical
  `pullbackTensorRationalComposition`/`pullbackTensorCommonComposition`, preceded
  only by the equality transport for base change preserving f₀ ≫ h₀. Their integral
  normalization is that of `integralPullbackComposition`; the common-stage map is
  specified at every larger finite coefficient field by the existing dependency.
  Their definitions contain no sorry or arbitrary isomorphism choice.
- The next conjunct is, in diagrammatic order,
  `sHF_K ≫ d_(P_Z K) = P_X(d_K) ≫ sF_(Lh*K) ≫ Lf*(sH_K)`.
  This is exactly `d_P c_H = c_J P(d)` for the pullback compositor, with the prescribed
  comparison for applying the two lifts successively.
- The tensor conjunct spells out the full two-variable equation. Its left route is
  `sF_(M⊗N) ≫ Lf*(mu_gY) ≫ mu_f_(P_Y M,P_Y N)`; its right route is
  `P_X(mu_f) ≫ mu_gX_(Lf*M,Lf*N) ≫ (sF_M ⊗ sF_N)`.
  Every mu is `canonicalRationalPullbackTensor` or
  `canonicalCommonStagePullbackTensor`, never an arbitrary tensor comparison.
- The last three groups of conjuncts use the actual
  `canonicalRationalPullbackTensor_associative`, `_braiding`, `_unit` predicates,
  and their common-stage counterparts, at g_X, g_Y, g_Z. I read their definitions:
  associativity gives the two three-input routes; braiding is the signed derived
  braiding; `_unit` supplies the canonically normalized unit comparison and BOTH
  the left- and right-unitor equations. Thus the tensor associator, signed symmetry,
  and both unit comparisons have precisely their multivariable Frobenius equations.
- `ComparisonEquation` is the one-variable equation in the item.
  `comparison_lifts` states that its specified underlying natural isomorphism lifts
  between the STANDARD lifted functors, with both hom and inverse carrier components
  unchanged. This formal clause is node step 6; applying it with product categories
  handles the multivariable equations. It records the isomorphism-of-Weil-pairs
  assertion as well as the stronger explicitly requested comparison equations.
- In EACH actual coefficient predicate, the ordinary clause quantifies `R` together
  with `adj : actualDerivedPullback f ⊣ R`, and applies
  `OrdinaryAdjunctionCoherent` to THIS adjunction and the normalized sF above.
  The universal statement includes the supplied ordinary Rf_* with its original
  adjunction. It neither chooses a replacement right adjoint nor assumes the
  coherence to be proved. Giving adj as data preserves its actual unit and counit.
- `OrdinaryAdjunctionCoherent` fixes the direct-image comparison t by
  `t.hom = (mateEquiv adj adj s.inv).natTrans`. Its next conjunct spells out
  `eta_(P R M) ≫ R(s inverse_(R M)) ≫ R(P_X(epsilon_M))`, term for term the
  unit--square--counit definition of Ex_* in the supplied-domain exchange dependency.
- Its next two conjuncts are exactly
  `P_Y(eta_K) ≫ theta_RLK = theta_K ≫ eta_K` and
  `theta_LRM ≫ epsilon_M = P_X(epsilon_M) ≫ theta_M`.
  Here theta_RLK and theta_LRM are the actual structures obtained by applying the
  two existing `mapOfNatIso` lifts in the indicated orders.
- Its final conjunct supplies the lifted adjunction, fixes its unit/counit carriers
  to `adj.unit`/`adj.counit`, and states both lifted triangle equations explicitly.
  No exceptional adjunction, compactification, or exceptional admissibility is a
  hypothesis of this assertion.
- `ordinary_adjunction_coherent` states the same formal calculation on ANY supplied
  closed full domains with the Frobenius equivalences and original adjunction.
  Thus restrictions of the actual categories to the domains specified in the node
  are included, without asserting extension of R or Hom to a larger domain. The
  canonical coefficient operations keep their inherited finite-Tor, integral
  presentation, and witnessed-origin restrictions; the theorem never changes those
  definitions or removes their witnesses.

Dependency declarations used (modules and names):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `.geometricFiber`, through the public dependency imports.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: `.geometricFrobenius`.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilPrimeInvertible`,
  `sfWeilFrobeniusPullback`, `sfCommonStageWeilFrobeniusPullback`, and the recorded
  fixed-pair category interpretation.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `rationalDerivedPullback`,
  `rationalDerivedTensor`, `commonStageDerivedPullback`, `commonStageDerivedTensor`.
- `Sheaf.Paper.DerivedPullbackTensorIso`: both field-stage composition components,
  both canonical pullback/tensor components, and their associative/braiding/unit
  predicates. Its full relevant signatures and normalization docstrings were read.
- `Sheaf.Paper.IntegralPullbackComposition`: `integralPullbackComposition` and
  `IntegralPullbackCompositionFamily` (proof dependency; the canonical composition
  helpers already use this family).
- `Sheaf.Paper.PullbackIdentitiesScalarExtension`: `pullbackIdentities_scalarExtension`
  (proof dependency for the coefficient-stage coherence).
- `Sheaf.Paper.SemilinearFieldOperationLifts`: `podRationalSquarePullbackComponent`
  and `podCommonSquarePullbackComponent`, owned by `def-pod-weil-lift-interfaces`,
  are statement dependencies. `pod_actual_pullback_field_lifts` and
  `semilinearFieldOperationLifts` remain proof dependencies.
- `Sheaf.Paper.FrobeniusSquareExchange`: `FrobeniusExchange.fiberMap`, the recorded
  `zlFiberMap` alias. Its underlying definition is the actual Over.pullback map.
- `Sheaf.SixFunctors.FrobeniusSquareCartesian`:
  `FiniteFieldDatum.frobenius_square_cartesian`, specifically its square equality.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`:
  `ExchangeProjectionStage.exchange`; I read its definition as the original square
  mate, which the displayed t formula uses verbatim in the identical-square case.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv` and its
  component formula (the mathlib_match of def-weil-pbc-adjunction-mate).
- `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`: `IsoAlgebra` and
  `IsoAlgebra.mapOfNatIso` in the statement, via the fixed-pair definition node.
- `WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraAdjunction`:
  `IsoAlgebra.mapOfNatIsoAdjunction`, its unit/counit carrier equations, and
  `IsoAlgebra.mateIso`, as proof dependencies only; its import is plain.
- `Sheaf.Paper.CompletedPullbackTensorComparison`:
  `canonicalRationalPullbackTensor` and `canonicalCommonStagePullbackTensor`,
  owned by `def-pur-completed-pullback-tensor-comparison`, in the statement.
- `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`: the recorded ordinary
  adjunction and pasted-adjunction interfaces, imported as a proof dependency.
  The theorem preserves the supplied original adjunction; it does not rebind a
  finite-étale adjunction as a rational pro-etale one.
- Scheme properties use Mathlib `IsSeparated`, `LocallyOfFiniteType`, and
  `QuasiCompact`, as collected by def-weil-scheme-morphism-properties.

Four already recorded nodes were added to stmt_deps because their public interfaces
occur in the signatures or comparison constructions: def-weil-operation-exchange-
coefficient-descent, lem-weil-frobenius-square-cartesian,
def-pod-weil-lift-interfaces, def-pur-completed-pullback-tensor-comparison.
This uses the standing authorization for gaining already landed statement dependencies.
No dependency node file is changed.

Edge cases checked before and during the statement audit:

- Empty geometric schemes and zero complexes: no nonempty/connectedness condition or
  invertibility of an object is assumed; the existing constructions still type.
- Identity f₀ or h₀: map_comp transport stays present and the same canonical
  comparisons are used. No identity or arbitrary coefficient stage is discarded.
- Non-separated finite-type models (e.g. a line with doubled origin): no separatedness
  of W₀ over k₀ is inferred or assumed. Only the two specified relative maps are
  required separated.
- Arbitrary rational theta, including multiplication by l without a stable lattice:
  theta is an arbitrary IsoAlgebra structure in the rational category, not an
  integral automorphism. Common-stage arrows may move to any larger finite field.
- Shifted complexes: `_braiding` refers to the dependency's derived signed braiding,
  not the unsigned exchange of graded terms.
- Coefficient closure in another universe: `Coefficient.{u}` transports only each
  finite subfield. It does not force u = v or alter the small pro-etale site.
- The adjunction result only claims a lifted adjunction from a given ordinary
  adjunction, and uses its original unit/counit; no exceptional existence is needed.

Searches actually run with msearch.py:

- leanfinder: `Frobenius pullback composition tensor comparisons equivariant ordinary
  adjunction lifts Weil fixed pairs`: 8 hits, on generic Frobenius reciprocity,
  module-sheaf pullback compositors and conjugate comparisons. None states this item.
- loogle: `CategoryTheory.mateEquiv, CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoAdjunction`:
  returned zero hits with unknown identifier for the project-only IsoAlgebra declaration.
  This was a search-index limitation, not evidence that the project declaration is absent.
- loogle: `CategoryTheory.mateEquiv`: 12 hits, including mateEquiv, its component,
  unit/counit equations, and pasting. Exact match for the existing mate notion, reused.
- grep: `mapOfNatIsoAdjunction|pullbackComp|Frobenius` under Mathlib/CategoryTheory:
  25 hits, generic pullback composition and Frobenius reciprocity, no full item.
- leansearch: `Geometric Frobenius pullback composition tensor comparisons equivariant
  unit counit Weil complexes`: 8 hits, including generic Frobenius reciprocity,
  module pullback/unit comparisons and field Frobenius. No full item.
- rg over lean/WeilConjectures and lean/Sheaf for the item id,
  `frobeniusPullbackMonoidalAdjunction`, and `Frobenius.*[Cc]oherence`: found the
  downstream ConstructibleMateCoherence proof docstring citing this item and distinct
  coefficient-reduction coherence; no existing statement. The existing generic
  IsoAlgebraAdjunction module was read and reused, not duplicated as a construction.
- The prescribed grep of the item id in lean/WeilConjectures and rg of the proposed
  namespace/main name in dag/lean_names_upstream.json had no match.

Validation: scompile.py compiled the complete delivered file cleanly under its normal
60-second limit, both sandbox and actual library-module checks (38.4 s and 8.1 s in
that successful invocation). Earlier failures were repaired: public access to the
actual geometry and explicit fibre parameters for instance inference. No increased
limits or additional mathematical assumptions were used. No STATEMENT-DISPUTED flag
and no source correction is needed.

## Second reading by Q75

This is a fresh second pass by this dispatched worker; the dispatcher explicitly
prohibits starting other agents, so I do not claim an independent reviewer wrote it.
I reread the node and complete Lean file side by side. The maintainer's independent
review remains the delivery review stipulated by the brief.

The second pass found and repaired two formulation omissions before the clean compile:
the coefficient E is now a finite subfield of the fixed Ω, rather than an unrelated
abstract finite extension; and each actual coefficient-stage predicate now includes
the ordinary adjunction clause, rather than leaving it only in the generic helper.
The ordinary clause binds an actual adjunction with the actual pullback, fixes the
right comparison by the mate of sF inverse, and spells out both carrier maps and
both triangles. Thus it cannot be satisfied by choosing a different unit or counit.

I checked the composition equation's direction: the source is P_X L(hf)*, and both
routes finish at Lf* Lh* P_Z. The tensor equation starts at P_X Lf*(M⊗N) and ends at
Lf* P_Y M ⊗ Lf* P_Y N, in precisely the order in proof step 4. I reread the reused
associativity, braiding and unit predicates rather than checking their names only;
their components give the exact source equations, including the right unit and the
Koszul sign. The ComparisonEquation/standard-lift theorem explains the passage to
Weil morphisms with the same components and inverses.

I also checked all three finite-type structure maps, both relative separatedness
hypotheses, the independent coefficient universe, full-domain interpretation,
arbitrary rational theta, and the absence of any exceptional-adjoint hypothesis.
The helper definitions have actual data and all three postponed theorems correspond
to explicitly identified portions of this node's nine-step proof. There are no new
nodes or dependency modules to audit. The final node record lists every declaration
and copies the main signature verbatim.

## Repair of returned head e4076e79a87b

The retained packet first passed deliver2.py --no-push (commit d75d4122439).
The maintainer's two content findings were then repaired explicitly:

- F1: replaced lem-pod-semilinear-field-operation-lifts in stmt_deps with the
  already-landed existing:true owner def-pod-weil-lift-interfaces. The two square
  component definitions have the exact canonical compositor signatures required
  here. The semilinear-lift theorem remains in proof_deps; its module remains a
  public import because the same module supplies those definition declarations.
- F2: removed lem-sf-fixed-pair-adjunction-lift from stmt_deps and retained it in
  proof_deps. Its module now has a plain import. Added explicit public imports of
  the upstream fixed-pair definitions and Mathlib mates, whose declarations occur
  in the signatures; no IsoAlgebraAdjunction declaration occurs in a signature.
- Advisory: added def-pur-completed-pullback-tensor-comparison to stmt_deps and
  its module as a public import for the two canonical tensor comparisons used.
  The explicit triangle clauses are retained as part of the accepted formulation.

Self-check against the retained file: only imports changed in Lean. All predicates,
constructions, theorem signatures and sorry proofs are unchanged. Against the
current shared main node, only lean and stmt_deps differ; proof_deps, statement,
proof, and all other fields are identical. Both proof-only theorem nodes remain
in proof_deps. No statement correction or dependency-module repair is involved.

Repair validation: scompile.py compiled the repaired sandbox and library module
cleanly (8.2 s each). The verbatim signature record, 100-character line width,
explicit autoImplicit=false setting, definition ownership, public/plain imports,
and three sorry-only theorem bodies were checked again.

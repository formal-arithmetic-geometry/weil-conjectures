## Worker report

Repair of returned delivery 096df19850cc. The retained packet was inspected and
`deliver2.py Q59 thm-coef-finite-hom --no-push` was run first. I retained its
substantive repair: the target now uses evaluation-defined arrows and actual
compatibility equations. Subsequent file-only compilation found unresolved
universe metavariables in the site's K-flat binders. Their `EssentiallySmall`
arguments are now explicit `essentiallySmallSelf.{0, u, u + 1}` through the
`finiteHomKFlat` abbreviation; the site still has objects in u+1 and morphisms
in u. The ordinary chain-tensor construction
is isolated in its own definition module so each file can be checked under
the fixed 60-second limit. This repair removes repeated universe elaboration in
`FiniteCoefficientSiteHomArrow` while leaving its representative square and
pure-tensor normalization unchanged.

The theorem is `WeilConjectures.finiteCoefficient_derivedHom_change` in
`Sheaf.Paper.FiniteCoefficientHomChange`. The mathematical statement, proof
plan and proof dependencies are unchanged. Only `lean` and the additional
canonical-definition `stmt_deps` differ from the current target node. No
STATEMENT-DISPUTED issue or source correction is asserted.

Hypotheses, individually:

- `D : FiniteFieldDatum` supplies p, q, the finite field and its algebraic closure k.
  `[Fact l.Prime]` and `_hl : l ≠ D.p` are exactly the coefficient prime condition.
- `E`, `[Field E]`, `[Algebra ℚ_[l] E]`, and `[FiniteDimensional ℚ_[l] E]`
  give the finite coefficient extension. The rings and chosen uniformizer are
  the recorded `Padic.coefficientExtensionRing` construction.
- `X : Scheme`, `[X.Over (Spec (.of D.k))]`, `[IsSeparated ...]`,
  `[LocallyOfFiniteType ...]`, and `[QuasiCompact ...]` say separated finite
  type over k. They impose no smoothness, properness or nonemptiness.
- `(n m : ℕ) (h : m ≤ n)` denotes the exponents n+1 and m+1. This parametrizes
  every n_paper≥m_paper≥1, including the residue field and identity quotient.
- Each finite assertion binds ambient `K M` and assumes respectively
  `finiteTorConstructibleEtale ... K/M` or `finiteTorConstructible ... K/M`.
  These are bounded finite-value constructibility and finite Tor amplitude
  against every degree-zero module sheaf, not just boundedness.

Conclusion, clause by clause:

1. The étale arrow's body is the explicit term `coefficientBaseChangeHom`
   with `finiteHomEtaleClosed`, `finiteHomEtaleReduction`, and
   `finiteHomEtaleTensor`. Those are normalized by the published derived Hom,
   Koszul right-tensor adjunction, actual quotient and scalar tensor comparison.
   The pro-étale arrow is `finiteIntrinsicReductionHom`, using the published
   `finiteIntrinsicClosed` and quotient calculus. No existence theorem selects
   the arrow itself.
2. In each site's finite-pair clause, the first membership conjunct is
   `F(H_A(K,M)) ∈ D^b_ctf(B)`; the second is
   `H_B(FK,FM) ∈ D^b_ctf(B)`; the third is `IsIso` of that specific arrow.
   Because the subcategories are full, these express an isomorphism in the
   specified finite-Tor constructible subcategory.
3. `FiniteHomEvaluation` says
   `tensor_B.map(v,1) ≫ ev_B = μ.inv ≫ F.map(ev_A)`, and every arrow satisfying
   this equation equals `coefficientBaseChangeHom ...`. It states both the
   evaluation identity and uniqueness of its tensor-Hom transpose.
4. `CoefficientEvaluationCompatible` is the recorded structure of actual
   equations, instantiated on those same closed records and quotient functors.
   Its `naturality` compares `F(H_A(f,g)) ≫ v` with
   `v ≫ H_B((F f).op,F g)` for all maps in both variables. Its `transpose`
   compares `F(transpose_A f) ≫ v` with the B-transpose of `μ.inv ≫ F(f)`
   for every `f : T⊗P ⟶ Q`. Its `composition` compares
   `F(comp_A) ≫ v` with `μ.hom ≫ tensor_B(v,v) ≫ comp_B`, on the tensor
   of two internal-Hom objects. Thus it states internal-Hom composition,
   rather than composition only on external Hom sets.
5. `FiniteHomEtaleCocycle` and `FiniteHomIntrinsicCocycle` bind every
   `(r : ℕ) (k : r ≤ m)`, denoting every positive third exponent r+1.
   The equation is
   `α.hom(H_A(K,M)) ≫ v_AC = G.map(v_AB) ≫ v_BC ≫ H_C(α.inv_K,α.hom_M)`.
   `α` is the canonical scalar-extension associator; its inverse in the first
   Hom argument is forced by contravariance. The intrinsic associator uses
   `Adjunction.leftAdjointCompIso` and the actual restriction composition;
   the étale associator uses `pbcFixedScalarExtensionComp` and quotient-factor
   equality. This is precisely the node's A→B→C equation after identifications.
6. `FiniteHomSiteFormula.square` uses actual `finiteHomNu` at levels n and m,
   the canonical scalar beta `finiteHomSiteBeta`, both canonical quotient
   arrows and both evaluation-defined site-Hom comparisons. Its equation is
   `β(H_A) ≫ ν_B(v_et) ≫ s_B = F_pro(s_A) ≫ v_pro ≫ H_pro(β_K⁻¹,β_M)`.
   Both paths start at `F_pro(ν_A H_A(K,M))` and end at
   `H_pro(ν_B F_et K,ν_B F_et M)`. Inverting the finite-domain site-Hom
   comparisons gives the familiar beta/ν_X^* transport formula. The scalar
   beta is the mate of the section-normalized restriction isomorphism.
   The site-Hom comparison is the transpose of ν of evaluation under the
   tensor comparison fixed on local pure tensors and K-flat localization.

Dependency declarations read and used:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` and its public
  coefficient imports: `Padic.coefficientExtensionRing`,
  `Padic.finite_coefficientExtensionRing`.
- `Sheaf.Paper.FiniteCoefficientReductionFlatModel`:
  `Scheme.flatModelReductionCoefficientMap`, the actual quotient factor map.
- `Sheaf.Paper.FiniteTorAmplitude` and `FiniteTorAmplitudeSites`:
  `finiteTorConstructible`, `finiteTorConstructibleEtale`; their bodies use
  `Scheme.intrinsicFiniteTorsionConstructible`,
  `Etale.DerivedCategory.isBoundedConstructible`,
  `HasFiniteProEtaleTorAmplitude`, and `Etale.DerivedCategory.hasTorAmplitudeIn`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: `finiteIntrinsicClosed`,
  `finiteIntrinsicTensorModels`, `finiteIntrinsicReductionHom`.
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`:
  `coefficientBaseChangeHom`, `CoefficientEvaluationCompatible`,
  `coefficientDerivedSystemEvaluationCalculus`, `coefficientFiniteInternalHom`,
  `coefficientFiniteQuotientDerived`.
- Published étale imports: `Etale.derivedHom`, `Etale.scalarExtension`,
  `Etale.ExceptionalCoefficients.tensorIso`, `DerivedMonoidal.braiding`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`:
  `ProEtale.finiteCoefficientIntrinsicComparison` and its coefficient unit.
  Its exact derived descent defines ν; the older fixed-coefficient pro-étale
  category is not substituted for the intrinsic constant-ring category.
- Mathlib adjunction, mate, currying, signed total tensor and exact derived
  descent interfaces are reused. The recorded generic change-of-rings node
  supplies its universal K-flat computation; no coefficient-flatness
  hypothesis is imposed.

Edge cases read against the formulas: n=m, m=0 (paper exponent 1), r=m,
all three levels equal, empty X, zero K or M, and rank-zero local finite-free
models. Successor indices exclude only the forbidden zero exponent. The
contravariant inverses in cocycle and site formulas have the required source
and target in all identity cases. No nonempty site or stratum is assumed.

Search evidence: the retained `mathlib_searches` contain raw `msearch.py`
LeanFinder, Loogle and Mathlib grep results for each definition. A fresh real
LeanSearch on "canonical finite coefficient internal Hom comparison and site
scalar transport" returned eight ordinary sheaf-Hom/light-condensed hits,
none the theorem. This replaces inherited placeholder search metadata.
Upstream and `lean/Sheaf` regex searches locate the generic canonical Hom
comparison and intrinsic consumer used here, with no existing full theorem.
For the extracted chain interface, `blueprint_refs.py search 'inverse image
 tensor'` returned zero blueprint nodes; DAG regex candidates concern generic
ringed comparisons or other coefficient/site encodings. Source regex searches
found no specialized `finiteHomNuChainTensor`. The fresh chain-specific
LeanSearch returned eight ordinary module pullback/sheafification hits;
Loogle reported unknown `Functor.mapHomologicalComplex`; Mathlib grep on
`finiteHomNuChainTensor|finiteCoefficientIntrinsic.*[Tt]ensor|[Tt]ensor.*finiteCoefficientIntrinsic`
returned zero. All raw search records are preserved in the definition nodes.

## Second reading by Q59

This is a separate clause-by-clause rereading in the same worker session;
the dispatch brief prohibits spawning another agent. I opened the target,
its retained new nodes and every delivered module, rather than treating a
clean compile as a mathematical review.

H5/H3: I followed `etaleFiniteHomCanonical` to the explicit
`coefficientBaseChangeHom` body and `proEtaleFiniteHomCanonical` to
`finiteIntrinsicReductionHom`. Their Hom bifunctors, closed adjunctions,
quotient functors and tensor comparisons are the same ones used by the
conclusion. Auxiliary choices are from unique specifications: every closed
record and tensor family is fixed by equality/HEq to the published data;
site restriction and chain tensor maps are fixed on local generators;
the derived site tensor is fixed by the localization square. No bare
`Nonempty.some` chooses a Hom arrow.

H3/H6: I expanded `FiniteHomEvaluation`, `CoefficientEvaluationCompatible`,
the cocycle predicates and `FiniteHomSiteSquareAux`. Each compares two
specified composed paths. The deleted reflexive naturality/transpose/site/spec
predicates have no replacement tautological clauses. Evaluation and uniqueness,
arbitrary input-map naturality, arbitrary tensor-Hom transposes and internal
composition occur exactly as described in clauses 3–4 above.

H3, successive quotients: both cocycles quantify r≤m. I checked the Hom of
`α.inv.app K` against the first contravariant input and `α.hom.app M`
against the second input. Both paths have common endpoints; the associator
comes from the specified quotient maps and adjunctions.

H3, site comparison: I checked beta's source `ν_A ⋙ F_pro` and target
`F_et ⋙ ν_B`, and both Hom comparison endpoints in the displayed square.
The contravariant beta is inverted; the scalar and site maps are not identities.
The ordinary chain comparison fixes every local total-summand pure tensor,
and the derived normalization compares it with the exact-descent factor
isomorphism and `finiteIntrinsicTensorModels.comparison.inv`.

H11, complete statement: each hypothesis above matches a binder, each finite
site has both endpoint membership claims and the particular `IsIso`, and both
site compatibility structures and cocycles are present. Positive levels,
identity quotients, zero objects and empty schemes are retained. The second
reading also identified the K-flat binders' inferred smallness universes as
the source of the compiler failure; explicit instance arguments repair that
interface without adding a mathematical assumption. All postponed proofs
remain named `sorry` theorems with source and natural-language proof docstrings.

## New nodes

`def-sf-etale-finite-coefficient-hom-arrow`, module
`Sheaf.Paper.EtaleFiniteCoefficientHomArrow`, owns the missing specialized
étale quotient diagram. It reuses the published Hom, scalar extension, tensor
comparison and Koszul symmetry, constructs v by evaluation transpose, and
supplies the actual quotient associator and normalized tensor representatives.
Its source is the opening evaluation paragraph of the current blueprint proof.
The retained searches found the generic canonical-map API and intrinsic
consumer, which are reused, but no specialized étale record. The rereading
matched all positive levels, arbitrary X, tensor order, quotient associator,
ordinary generators and localization tensorator to the new node.

`def-sf-finite-coefficient-site-scalar-arrow`, module
`Sheaf.Paper.FiniteCoefficientSiteScalarArrow`, owns the published ordinary
inverse image, its exact derived descent, the unique identity-on-local-sections
restriction comparison, and its scalar-extension adjunction mate beta.
Source: the final site-transport paragraph. Its retained searches found the
general mate/descent constructions, but no specialized intrinsic scalar/site
map. The rereading checked the actual restricted actions, both section units,
every positive quotient, mate direction and beta's endpoint functors.

`def-sf-finite-coefficient-site-chain-tensor`, module
`Sheaf.Paper.FiniteCoefficientSiteChainTensor`, extracts the ordinary chain
comparison and exact-descent localization isomorphism. Source: the same final
paragraph's termwise tensor reassociation. Its fresh searches are listed above
and stored verbatim in its node. The comparison sends each local pure tensor
in a specified signed-total summand to that of its two comparison-unit images;
this unique normalization determines the chosen isomorphism for all complexes.
The rereading checked the total degree p+q=k, both section carriers, all
complexes and the unchanged u+1/u site universes.

`def-sf-finite-coefficient-site-hom-arrow`, module
`Sheaf.Paper.FiniteCoefficientSiteHomArrow`, owns the derived tensor comparison
fixed on flat K-flat representatives and the evaluation-transpose site-Hom map.
Source: the final site-transport paragraph, with the ordinary chain interface
now cited from its own node. Its retained searches found no specialized ambient
canonical map. The rereading checked the complete localization square, flat
K-flat source conditions, explicit intrinsic K-flat witnesses, and the
`coefficientBaseChangeHom` body. Invertibility of internal Hom on finite
constructible pairs remains the target theorem's assertion, not a premise
used to define the comparison. No downstream dependency wait is introduced.

The ordinary chain normalization uses explicitly typed section carriers for the
source total complex and both factor complexes. Each carrier value is pinned
by HEq to the prescribed comparison-unit image; the final equation compares
the chain map applied to that source value with the intrinsic pure tensor of
the pinned factor values. These are dependent transports of the original
three sections, not arbitrary choices or an additional hypothesis. This
avoids repeated kernel reduction through termwise derived comparison data.


## Returned-head ownership repair

The return on immutable head `452ae2b401b7` identified a missing owning node,
not a defect in the independently verified mathematical statement. The saved
packet already contains
`dag/nodes/sec-six-functors/def-sf-finite-coefficient-site-chain-tensor.json`.
I retained and checked this complete new-definition record: it owns
`Sheaf.Paper.FiniteCoefficientSiteChainTensor` and lists `finiteHomNuComplex`,
`finiteHomNuFactors`, `FiniteHomNuChainTensorNormalization`,
`finiteHomNuChainTensor_existsUnique`, and `finiteHomNuChainTensor`.
Its self-contained statement specifies every signed-total local pure tensor
and the exact-descent localization isomorphism; its source is the final
site-transport paragraph and Stacks 00YV/06YN/07A4. The three search kinds,
creation record, blueprint origin, empty audits, chapter and unit are present.
The site-Hom node cites it in both its statement and `stmt_deps`, so the target
reaches it through that definition. The blueprint ancestor command confirms
`thm-coef-finite-hom` as its origin.

I added the omitted `WeilConjectures.finiteHomKFlat` to the site-Hom node's
`lean.declarations`. A sandbox self-check finds exactly one owning node for
every delivered module, every top-level declaration listed, all recorded
primary signatures verbatim in their source, and no line over 100 characters.
The target differs from the current shared node only in `lean` and the
permitted canonical-definition additions to `stmt_deps`. Its statement,
hypotheses, universes and canonical maps are retained as independently reviewed.

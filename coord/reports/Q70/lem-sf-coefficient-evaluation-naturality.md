## Worker report

The delivery states `WeilConjectures.sfCoefficientEvaluationNaturality` in
`Sheaf.Paper.CoefficientEvaluationNaturality`. The theorem has `sorry`; its auxiliary
predicates and theta and line constructions have real data. A dependency-interface repair
states `sfTwistTensorHomMap_isIso` with `sorry` in
`Sheaf.Paper.CoefficientTwistInterchange`. No proof is supplied in this stage.

Sources read: main-20261015, `sk-thm-sf-dual-perfect/_section.md` and its proof,
sentences 1–3, and `sk-lem-sf-twist-interchange` statement and proof, all three paragraphs.
I also read the item's four expanded proof steps and every statement dependency's
statement, Lean record, and recorded signatures and docstrings. The source theorem
uses Dctf. The fixed datum in this item's first paragraph is explicitly defined on
D^b_ctf in `def-sf-datum`; the four `SixFunctorClosedDomain` presentations are precisely
these categories. In particular the finite and integral inputs below have the datum's
finite-Tor membership, and the field domains are the full recorded constructible
categories. This delivery does not reinterpret E or Qbar as discrete-field sheaves.

Hypotheses and clauses, in the order of the node:

- `D : FiniteFieldDatum.{u}` contains p prime, a positive, q=p^a, the field k0 of
  cardinality q, and its algebraic closure k. `C : D.CoefficientDatum` contains the
  prime ell, ell distinct from p, and Qbar. `E : Type u` with `Field E`,
  `Algebra (Padic C.l) E`, and `FiniteDimensional (Padic C.l) E` is the finite
  coefficient extension. The actual valuation ring, uniformizer and quotients are
  those of these dependencies, not independent rings.
- The positive finite level is `n + 1` with `Nat.succ_le_succ (Nat.zero_le n)`.
  This covers every level at least one, including the first and ramified quotients.
- `S : SixFunctorDatum ...` is exactly the fixed datum. `X : SixFunctorSpace D`
  is a finite-type k-scheme. There is no separatedness, smoothness, orientation,
  exceptional-inverse-image existence, or purity hypothesis in the new theorem.
- The four coefficient choices are the first four conjuncts, respectively
  `(S.finiteClosed X)`, `(S.integralClosed X)`, `(S.rationalClosed X)`, and
  `(S.commonClosed X)`. Their `.closed` and `.symmetric` retain the actual tensor,
  internal Hom, unit, and signed symmetry. The integral closed presentation is
  the completed one, with the normalized ambient comparison of the datum.
- In `SfCoefficientEvaluationLaws`, the internal Hom is the existing bifunctor H,
  the unit is `S.monoidal.tensorUnit`, and P dual is `H.obj (op P, unit)`.
  Evaluation is the existing `S.evaluation P unit`, its adjunction counit.
- The comparison c is the existing `ringedSiteDualEvaluationLeft S s unit
  (Iso.refl _) P M`. The predicate's first clause explicitly identifies it with
  `S.transpose` of associator, identity tensor signed interchange, inverse
  associator, coefficient evaluation tensor identity, and the left unitor.
  Thus the map is pinned to the exact arrow in the node, including constraints.
- The second clause quantifies over P,P',M,M', `u : P ⟶ P'`, `v : M ⟶ M'`,
  and says `c(P',M) ≫ H.map (u.op,v) = tensor.map (H.map (u.op,id),v) ≫ c(P,M')`.
  Composition `≫` is in the reverse written order from the node's functional
  composition. Both contravariant and covariant variables are unrestricted
  within their coefficient category.
- The third clause quantifies over every `J : ObjectProperty B`, arbitrary L,W,
  and `gamma : L ≅ W`. Its sole extra premise is exactly
  `hc : ∀ P : J.FullSubcategory, IsIso c(P.obj,L)`.
  Empty subcategories are included. No condition of dualizability is inserted here.
- `sfCoefficientTheta` is `H.mapIso (id,gamma.symm)` composed with `(asIso c).symm`.
  It therefore has precisely the specified hom and inverse, and is never selected
  from an unnormalized existence assertion.
- The first part of that third clause is theta's contravariant naturality on
  every morphism of J. The second part is the equality
  `tensor.map (theta.inv,id) ≫ S.evaluation P W = ... ≫ gamma.hom`.
  The right hand side spells out the same associators, signed symmetry,
  coefficient evaluation and unitor as in the node.
- The last four theorem conjuncts quantify over every `m t : ℤ` and instantiate
  `SfCoefficientTwistEvaluation`. The completed line is the recorded
  `sfIntegralTwistingCoefficient`, shifted by t, in `sfEvaluationIntegralLine`.
  Its finite line is actual `sixFunctorIntegralReduction` of that line; the
  rational line is `sfRationalTwistingCoefficient`, shifted by t (its definition
  is the actual raw rationalization of the integral line);
  the common-stage line is the existing `sfQbarTwistingCoefficient` shifted by t.
  These are the signed Tate lines of `def-coefficient-twists-detailed`, including
  negative m, not newly chosen rank-one objects.
- `SfCoefficientTwistEvaluation` asserts the line belongs to the given domain
  and is tensor-invertible; those are conclusions, not new hypotheses.
  For every dualizable K it asserts `IsIso c` and literal equality
  `(asIso c).symm = sfCoefficientTwistIso ...`.
  The latter is the repaired dependency's canonical tensor-Hom interchange
  with M=unit, preceded by H of the inverse left unitor. Its target is
  K dual tensor Lambda(m)[t], the node's K dual(m)[t] with the specified
  tensor/shift constraints understood. It is not a bare Nonempty isomorphism.

Dependency declarations used:

- `Sheaf.Paper.SixFunctorDatum`: `SixFunctorDatum`, `SixFunctorClosedDomain`,
  `sixFunctorDomainHom` and the four `.finiteClosed/.integralClosed/.rationalClosed/
  .commonClosed` fields. This publicly imports the recorded
  `Sheaf.Paper.SixFunctorOperationDatum` and its actual operations, including
  `sixFunctorIntegralReduction`.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`:
  `sfIntegralTwistingCoefficient`, `sfQbarTwistingCoefficient`, and the reexported
  signed finite/integral/rational twist constructions.
- `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic`:
  `CategoryTheory.IsDualizable` (Nonempty of a right dual) and `IsInvertible`.
  These are reexported by the repaired twist dependency's upstream import.
- `Sheaf.CategoryTheory.RingedSiteDualityMaps`:
  `ringedSiteDualEvaluationLeft` (its definition and underlying right-order
  evaluation were read), imported by the datum. The new definition owner
  `def-sf-coefficient-evaluation-transpose` records both existing maps; the theorem
  `lem-sfb-ringed-site-duality-maps` is not a statement dependency.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`:
  `CoefficientClosedStructure`, `.tensor`, `.evaluation`, `.transpose`.
  Its already landed owning node `def-coef-ringed-tensor-hom-model` is added.
- `Sheaf.Paper.DlLocallyConstructibleAdicHeart`:
  `dlAdicGeometricResidueInvertible` transports the prime unit along k0→k→kappa(x).
  Its owning landed definition node is added to stmt_deps; no residue-invertibility
  assumption is imposed on X. This is the same helper used by the sibling
  `lem-sf-oriented-double-hom-cancellation`.
- The repaired `sk-lem-sf-twist-interchange` module, described below, supplies
  `sfTwistTensorHomMap`, its canonical iso and its unit case.
- Proof-only `Mathlib.CategoryTheory.Monoidal.Closed.Basic` provides the recorded
  `lem-pod-closed-uncurry-laws` match: `uncurry_curry`, `uncurry_natural_left`,
  and `uncurry_eq`, read with `ihom.ev` as adjunction counit.

Edge cases checked before writing and again against the final signatures:
P=0 and M=0 give zero evaluation composites and no exceptional assumption;
P=unit gives the ordinary scalar action with its unitors; identity u,v give
identity naturality; J empty is permitted and its universal claims are vacuous;
J the whole category is permitted when every c is invertible. L,W,gamma are
arbitrary; gamma=id is included, as are zero L,W when the stated invertibility
premise holds. No equality with an oriented purity line is required. The empty
scheme is permitted by SixFunctorSpace and prime-unit transport. Level one and
nontrivially ramified quotient coefficients are included. Negative m, m=0,
t=0 and odd/negative t are all included by the integer quantifiers and actual
signed symmetry. Universes a,b are independent for the categorical predicates;
the actual small-site object/morphism universe convention is inherited unchanged.

Searches actually run through `msearch.py`, recorded in sandbox `searches.jsonl`:

- LeanFinder: “The canonical map from coefficient dual tensor M to internal Hom P M
  is natural in P and M and transports evaluation along an isomorphism L to W”.
  Eight hits, including `ModuleCat.ihom_ev_app`, `dualTensorHom`,
  `dualTensorHomEquiv`; none states the four-stage assertion.
- Loogle: `CategoryTheory.MonoidalClosed.uncurry, CategoryTheory.ihom`.
  Twelve hits including `uncurry`, `uncurry_injective`, `uncurry_natural_left`,
  `uncurry_natural_right`; these are adjunction ingredients only.
- Grep: `ihomUnitTensorToIhom|ev_naturality|uncurry_natural` in
  `CategoryTheory/Monoidal`: twenty hits, including the existing evaluation and
  uncurry identities in `Closed/Basic.lean`.
- LeanSearch: “Naturality of internal Hom evaluation and the canonical map from
  dual tensor to internal Hom”. Eight hits, notably `ihom.ev_naturality` and
  `Module.Dual.eval_naturality`; none includes theta, arbitrary J, canonical
  shifted twists, and all four coefficient stages.
- Direct rg of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for comparison, evaluation/naturality, and the
  chosen declaration names. The node-id grep of `lean/WeilConjectures` has no
  match. Existing `ihomUnitTensorToIhom`, `ringedSiteDualEvaluationLeft`,
  `SfOrientedPerfectDuality`, and `SfPackagePerfectEvaluation` were inspected.
  The first two supply the comparison notion; the latter two require a supplied
  orientation/perfectness and do not state the general two-variable and arbitrary
  full-subcategory laws. Their map construction is reused through the existing
  ringed-site comparison; no second coefficient category or tensor is defined.

Compilation: both delivered modules were compiled separately, in dependency order,
using scompile.py on the server. The final run returned exit 0 for both modules in
sandbox and library module mode, with no errors or non-sorry warnings. Earlier
compilation caught a missing public import of the residue-invertibility helper and
an unused existential proof name; both were repaired and the successful run includes
those repairs. No existing node statement is disputed or corrected. The new definition node
owning the existing evaluation maps is described below.

## Dependency modules

`sk-lem-sf-twist-interchange`: its recorded declarations are specialized to
`DerivedCategory (Sheaf X.smallEtaleTopology A)`. They cannot be instantiated at
the actual completed integral, raw rationalization or common-stage categories.
The new module publicly imports the entire old module, retaining all its recorded
ordinary-etale clauses, and supplies the same evaluation-defined map through
`CoefficientClosedStructure` for the other coefficient presentations. Its definition
uses the actual adjunction, associator and symmetry. Its one postponed theorem has
exactly perfect P, invertible T, arbitrary M and invertibility of that canonical map;
its docstring gives the source's autoequivalence/Yoneda proof. The canonical inverse
is `asIso` of that map using the named theorem, not a choice of iso; the unit case
uses H of the inverse unitor. Every helper is listed in lean.declarations. The
consumer supplies the recorded signed shifted Tate lines, rather than assuming
unspecified invertible coefficients. The dependency node changes only in lean,
with a note explaining this interface repair.

## Second reading by Q70

This is a self-rereading, not a claim that a separate worker was started; the
brief forbids subagents and assigns independent review to the maintainer.
I reopened the node and final two source files and compared each hypothesis and
clause above. I checked composition directions: u.op points from op P' to op P;
`c(P',M) ≫ H(u,v)` and `(u dual tensor v) ≫ c(P,M')` have identical endpoints.
Theta's map starts at H(P,W), passes through H(P,L), and ends at P dual tensor L.
Its inverse is the comparison followed by H(P,gamma), so the tensor-evaluation
composite has precisely the node's domain and codomain. The theta naturality
formula has P' on the right and P on the left, as contravariance requires.
The transpose clause contains both associators in the correct directions and the
left unitor after e tensor identity. I checked the repaired dependency's unit
normalization: inverse unitor first under H, then inverse of the evaluation-transpose
map, so equality with c inverse fixes the canonical isomorphism, including signs.
No mismatch was found in this rereading; the compilation import and unused-name
repairs described above are included. There are no hidden proofs in definitions
or arbitrary isomorphism choices. The theorem docstring contains all four proof
steps, and each postponed theorem is owned by its delivered DAG node.


## New nodes

`def-sf-coefficient-evaluation-transpose` owns the existing definitions
`CategoryTheory.ringedSiteDualEvaluation` and `CategoryTheory.ringedSiteDualEvaluationLeft`
in `Sheaf.CategoryTheory.RingedSiteDualityMaps`, with `existing: true`; no module or
second evaluation construction is added. Its self-contained statement gives arbitrary
category B and bifunctor H, the recorded closed structure S, symmetry s, arbitrary
O and unit identification u, and arbitrary P,N. The first arrow transposes associator,
evaluation, inverse unit identification, and right unitor. The second arrow braids
before that first arrow. The item takes O=unit and u=identity. This is precisely the
source's evaluation-defined second arrow, with the clause-1 coherence equation still
asserted by the item rather than assumed by the definition. The new node cites only
`def-coef-ringed-tensor-hom-model`. It has empty proof and proof_deps and no theorem
premise. Searches of every definition-node Lean record found no existing owner;
`def-per-ringed-site-bidual-transpose` owns only biduality. LeanSearch on the evaluation
transpose returned eight ordinary evaluation/linear-dual hits; Loogle on
`CategoryTheory.ihom.ev` returned twelve evaluation and uncurry hits; Mathlib grep on
`ihomUnitTensorToIhom|dualTensorHom|ihomTensorToIhom` returned zero monoidal hits.
Project rg found the exact two reused definitions, while upstream rg found specialized
ordinary module comparisons. `blueprint_refs.py search 'coefficient evaluation'`
found two blueprint nodes, neither owning these definitions. The exact tool records
are retained in the new node's mathlib_searches. P=0, N=0, P=unit, O=unit and u=id
require no additional hypothesis; independent object/morphism universes are retained.

## Returned-review repair

The returned immutable head was d51f2efaf68a. The initial saved packet passed a fresh
dry run (cce25e9dad7) before repairs; that mechanical pass did not address the review's
H2 finding. The repair replaces the added theorem dependency
`lem-sfb-ringed-site-duality-maps` by the definition owner above and uses its existing module through
the already public SixFunctorDatum import. Neither comparison is a choose from the theorem.
All hypotheses and all four coefficient stages of the accepted statement remain.

The ND interface declarations in `sk-lem-sf-twist-interchange` are now all retained
in lean.declarations along with the four new generalized declarations, and the original
module is still publicly imported. The rational clause now uses the existing
`sfRationalTwistingCoefficient` with its shift, rather than expanding its underlying
localization construction.

For the theta advisory I read `def-sf-perfect-evaluation-comparisons` and
`sfPerfectThetaInverse` in `Sheaf.Paper.OrientedPerfectDuality`. The present theta is
an isomorphism, while that existing definition is its inverse arrow: its body is
braiding, tensor(gamma,id), and the right-order evaluation at W. Naturality of
braiding and of the right-order comparison identifies this body with
`ringedSiteDualEvaluationLeft S s unit (Iso.refl _) P L` followed by `H(P,gamma)`;
this is exactly the inverse of sfCoefficientTheta. Thus this report links the two
interfaces explicitly; no second inverse-arrow definition or additional theorem is
introduced, and no orientation or perfectness restriction is added to arbitrary J.

For the repair self-check, I reopened the new node and both existing map bodies:
right-order d has N first and uses u.inv before the right unitor, while left-order c
has the dual first and braids to d. The verbatim signature in the new record is the
existing ringedSiteDualEvaluationLeft signature with its ambient arguments recorded
in lean.note. I compared the final main signature against the node: the only source
expression change uses the named rational Tate line with the same arbitrary integer
shift. The report continues to identify the second reading as self-rereading; the
independent review is the maintainer's. No new proof or hollow definition is added.


Validation repair: the first repaired dry run rejected a redundant direct import of
`Sheaf.CategoryTheory.RingedSiteDualityMaps`, because the route-pivot table associates
that module with a dropped bidual node. I removed this redundant import; the same
existing definitions remain available through the original public SixFunctorDatum
import, as in the already compiled saved packet. The new definition ownership record
and the removal of the theorem dependency remain intact. The subsequent dry run
compiles the final files and the existing-definition reference probe again.

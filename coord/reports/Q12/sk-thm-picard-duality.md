## Worker report

States `sk-thm-picard-duality` in
`Sheaf.AlgebraicGeometry.Curve.PicardDuality`. There are four postponed theorems:
`AlgebraicGeometry.Scheme.picard_duality_zero`, `picard_duality_one`,
`picard_duality_structureSheaf`, and `picard_duality_genus`. Their joint content
is the node, with separate dimension-zero and dimension-one cases. Every theorem
has proof `sorry`. The six helper definitions have actual data and no `sorry`.
The natural-language node and proof are unchanged. The returned dependency fault
is repaired by recording the existing resolution comparison on a new definition
node, as detailed below. The six local helpers assemble the maps and conventions
of this same statement using the recorded objects.

Hypothesis and clause correspondence:

- Field k and scheme X: explicit `{k : Type u} [Field k] {X : Scheme.{u}}`.
  `[X.Over (Spec (.of k))]` fixes the structure morphism throughout. There is no
  perfection or algebraic-closedness hypothesis in either duality theorem.
- Smooth proper curve of pure dimension n in {0,1}: the two cases use
  `[SmoothOfRelativeDimension 0 (X ↘ Spec (.of k))]` and the corresponding
  dimension-one instance, each with `[IsProper (X ↘ Spec (.of k))]`.
  Over a field this is precisely smoothness with all nonempty components of
  dimension n. Properness supplies separatedness and quasi-compactness, and
  smoothness supplies local finite type, so these are curves in the recorded
  `IsCurve` sense. No connectedness, integrality or nonemptiness is imposed on X.
  The relative-dimension formulation also admits the empty scheme in both cases.
- F finite locally free: `IsPicardTraceDuality` quantifies over every `F : X.Modules`
  with `[F.IsFiniteLocallyFree]`, the recorded variable-rank predicate. Naturality
  quantifies over F and G with that same predicate and every morphism `φ : F ⟶ G`.
- Canonical module: in dimension zero it is `SheafOfModules.unit X.ringCatSheaf`;
  in dimension one it is `(X ↘ Spec (.of k)).relativeDifferentials`.
  These are exactly Ω⁰ and Ω¹, without choosing an abstract dualizing object.
- Cohomology: nonnegative degrees use `scalarCohomology`, whose carrier is the
  recorded `RingedSpace.moduleCohomology`, and whose scalar action is restricted
  along the structure map. `picardCohomologyZ` uses it at `q.toNat` for q ≥ 0 and
  the actual zero k-module `ModuleCat.of k PUnit` for q < 0. Both sides of duality
  use this convention, for every `q : ℤ`. No negative degree or q > n is omitted.
- Dimension-zero trace: `picard_duality_zero` asserts existence of one k-linear t
  on H⁰(O_X), and its first conjunct fixes t on every class as
  `Algebra.trace k Γ(X, ⊤)` of `scalarGlobalSectionsEquiv` of that class.
  The explicit algebra argument is `(globalSectionsRingHom k).toAlgebra`.
  Smooth proper relative dimension zero implies X = Spec A with A finite étale;
  using A = Γ(X,O_X) gives exactly the specified trace, including the zero algebra.
  There is no arbitrary trace supplied as a hypothesis.
- Integral dimension-one trace: the reused `Scheme.residueTrace k Y` is defined
  in `WeilConjectures.AlgebraicGeometry.Curve.ResidueTrace` as the quotient of
  `residueSum` through `differentialsH1Equiv`. Its source is the existing
  abelian-sheaf H¹. We feed it the *canonical* module/abelian comparison
  `moduleCohomologyExtResolutionEquiv Y Ω¹ 1`, with no chosen equivalence.
  The existing `residueTrace_symm_mk_eq_residueSum` and
  `residueTrace_symm_mk` identify its value with the sum of Tate local residues.
  The existing `residueSum_differentialsPrincipalPartsMap` is precisely the
  residue-theorem descent condition. The finite-locally-free principal-parts
  dependency supplies the stated exact flasque sequence and canonical connecting
  map on module cohomology. These constructions are reused, not copied.
- Local residue normalization, including imperfect fields: the reused residue
  is `TateResidue.localRes` on the actual local subalgebra in the function field.
  `TateResidue.dvr_residue_calculus` in the recorded dependency states that regular
  differentials have residue zero and gives the uniformizer/residue-field-trace
  formula. Its separable-residue-field clause is the Laurent coefficient formula
  for every k-algebra coefficient-field coordinate. Thus no inseparable point
  is discarded or assigned the naive field-trace formula. The integral trace
  reused here is built from the same `localRes`, not from classical coefficients.
- Disconnected dimension-one trace: the first conjunct of `picard_duality_one`
  quantifies over every finite family Y of integral components and its open
  immersions j into X, with `IsColimit (Cofan.mk X j)` expressing the actual
  disjoint-union identification. It requires `t z = ∑ i, residueTrace k (Y i) ...`.
  The entries are the restrictions of z by `scalarCohomologyPullback` followed by
  `picardDifferentialPullback`, the adjoint of the universal differential map.
  Its coefficient comparison uses the equality h that j is over k. This is
  the actual restriction, not an arbitrary comparison or an unconstrained map.
  The integral/function-field compatibility instances on Y are universally
  quantified *inside this normalization conclusion*, not assumptions on X.
  The chosen field-algebra structures are required to be the compatible ones
  by `IsFunctionFieldAlgebra`, exactly as in the recorded principal-parts API.
- Empty X: the finite presentation above includes `I = Empty`. Its residue sum
  is zero and `IsColimit (Cofan.mk X j)` identifies X with the empty coproduct.
  Consequently the normalization explicitly fixes the trace to zero. The
  dimension-zero normalization is also zero for the zero global-section algebra.
- Exact trace pairing: `picardTracePairing` applies `scalarCohomologyCup` with
  coefficients F and `dual F ⊗ ω`, then the recorded coefficient cohomology map
  of `evalTensor F ω`, then t. The only degree transport is the equality
  `q.toNat + (n-q).toNat = n` in the nonnegative case. When either degree is
  negative the function is zero. The casts and arithmetic are actual data;
  no theorem or placeholder is used to manufacture a pairing.
- Perfection and displayed isomorphism: for every F and integer q the first
  conjunct of `IsPicardTraceDuality` supplies a `LinearEquiv` from H^(n-q)(Fᵛ⊗ω)
  to the k-linear dual of H^q(F), together with `∀ b a, e b a = ...` fixing
  the equivalence to this exact trace pairing. Its inverse is the displayed
  isomorphism H^q(F)^∨ ≅ H^(n-q)(Fᵛ⊗ω). This is not a bare existence of an
  unrelated isomorphism.
- Naturality: the second conjunct is exactly
  `pairing G (H(φ) a) b = pairing F a (H(dualMap φ ▷ ω) b)`, with the actual
  recorded coefficient maps, extended by zero in negative degrees.
- Specialization F = O_X, n = q = 1: `picard_duality_structureSheaf` states the
  linear equivalence between H¹(O_X)^∨ and H⁰(Ω¹), for every proper smooth curve
  of pure dimension one, including disconnected and empty curves.
- Genus: `picard_duality_genus` uses the recorded `IsConnectedCurve`, Smooth and
  IsProper assumptions and concludes, when `IsAlgClosed k`, the equality between
  the recorded structure morphism's `.genus` and `Module.finrank k` of the
  recorded scalar-restricted module H¹(O_X). Connectedness is needed only for
  this final genus clause, not for either duality case.

Dependency declarations used (their signatures and docstrings were opened):

- `Sheaf.AlgebraicGeometry.CurveGenus`: `AlgebraicGeometry.IsCurve`,
  `IsConnectedCurve`, `Scheme.Hom.genus`, `Scheme.Hom.genus_baseChange_of_isAlgClosed`
  (the first three are re-exported from `WeilConjectures.AlgebraicGeometry.Curve`).
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`:
  `SheafOfModules.IsFiniteLocallyFree` (varying rank).
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsHomEquiv`,
  `pushforwardDerivation`, and `relativeDifferentialsCongr`.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: `Scheme.functionFieldOfComponents`;
  the integral components use Mathlib's re-exported `Scheme.functionField`.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `sheafCohomologyAndHigherDirectImages`, re-exporting `RingedSpace.moduleCohomology`.
- `WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`:
  `scalarCohomology`, `scalarCohomologyCup`, `scalarCohomologyMap`,
  `scalarCohomologyPullback`, and the recorded `exists_tensorPullbackAdjunction`.
- `Sheaf.AlgebraicGeometry.Curve.VectorBundlePrincipalParts`:
  `finiteLocallyFree_principalParts_resolution`, its cohomology and naturality
  declarations, and `finiteLocallyFree_principalParts_differentials`.
- `Sheaf.RingTheory.TateResidue.DVRResidueCalculus`:
  `TateResidue.dvr_residue_calculus`, with the existing `localRes` construction.
- `WeilConjectures.AlgebraicGeometry.Curve.ResidueTrace`:
  `residueTrace` and its residue-sum normalization. `Modules.dual`, `dualMap`,
  and `evalTensor` are reused from its public module imports.
- Added already-landed statement dependency
  `def-sc-scalar-global-sections-comparison`, module
  `WeilConjectures.AlgebraicGeometry.ScalarGlobalSectionsComparison`:
  `Scheme.Modules.scalarGlobalSectionsEquiv`.
- Added definition-node statement dependency
  `def-pc-module-cohomology-ext-resolution-equiv`, module
  `WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality`:
  `Scheme.Modules.moduleCohomologyExtResolutionEquiv`. The node and full
  construction/signature were read, not just the declaration's name.

The stated proof dependencies are imported as the stage-3 plan. The as-yet
unrecorded `lem-pc-tate-adelic-reciprocity` has no module to import; its existing
upstream implementation is already available through ResidueTrace's public
import `WeilConjectures.RingTheory.TateResidue.ResidueTheorem`. No import cycle
is introduced, and no proof dependency is removed.

Edge checks: both n = 0 and n = 1; arbitrary imperfect k; inseparable residue
extensions; q negative, q = 0, q = 1, q > n; empty X; disconnected X; finite
locally free rank zero and ranks varying between components; zero coefficient
morphisms; empty and singleton component presentations. In negative degrees
`picardCohomologyZ` is the actual zero module, not an unconstrained object.
For q > n its duality with the negative complementary degree asserts the
needed positive-degree vanishing, rather than assuming it. No statement fault
or disputed clause was found.

Searches for an existing complete statement:

- `msearch.py`, leanfinder, query `Serre duality for smooth proper curves with
  trace pairing from residues`: eight algebraic trace/trace-dual hits
  (`map_equiv_traceDual`, `FractionalIdeal.trace_mem_dual_one`,
  `isIntegral_discr_mul_of_mem_traceDual`, `LinearMap.trace_eq_contract'`,
  `ClassGroup.fintypeOfAdmissibleOfFinite`, `traceForm_dualSubmodule_adjoin`,
  `Module.Basis.traceDual`, `Module.Basis.trace_traceDual_mul`); no curve duality.
- `msearch.py`, loogle, query `"serreDuality"`: zero hits.
- `msearch.py`, grep, query `serreDuality|residueTrace|picardDuality`: zero Mathlib hits.
- `msearch.py`, leansearch, query `Serre duality trace pairing on smooth proper curves`:
  eight trace-related hits (`LinearMap.trace_eq_contract'`, `Algebra.traceForm`,
  `Algebra.trace`, `Submodule.mem_traceDual`, `LinearMap.trace_eq_contract_apply`,
  `Submodule.traceDual`, `traceForm_nondegenerate`, `Module.Basis.traceDual`);
  no complete duality statement.
- `rg` in WeilConjectures and Sheaf for `serreDuality|residueTrace|picardDuality|tracePairing`,
  and for the node id: the upstream integral residueTrace and integral q = 1
  `serreDuality_residueTrace` are genuine reusable constructions, but do not
  include the whole node. RiemannRoch has abstract dimension-one isomorphisms,
  finite-étale degree-zero trace duality and genus results for its abelian H.
  None states the complete module-derived, normalized disconnected pairing in
  every integer degree. We reuse these constructions and state the remaining
  joint module-cohomology interface, rather than rebinding a partial result.
- `rg` in Mathlib, WeilConjectures, Sheaf, and `dag/lean_names_upstream.json`
  for every proposed helper/theorem prefix: no declaration-name collisions.

Validation: server-only `scompile.py` compiled the module cleanly in its sandbox
and at its final module name; no warnings, errors, or added theorem proofs.


## Repair of returned delivery

The independent return at immutable head `7c4db1762aec` identified one H2 fault:
`new-module-cohomology-ext-resolution-naturality` was added to `stmt_deps`, but
only its plain definition `moduleCohomologyExtResolutionEquiv` occurs in the
statement. The theorem's conclusion supplies no object needed to state duality.
Replaced that added dependency with the new definition node
`def-pc-module-cohomology-ext-resolution-equiv`. The theorem node and every
existing dependency node are unchanged. The Lean file is unchanged. The initial
saved packet passed the required dry run at `ece81f4014b`; that success alone did
not address the independent mathematical return.

Compared the saved item with current main through the delivery wrapper and direct
JSON comparison: only `lean` and the added statement dependencies differed. The
repair retains the reviewed statement, proof plan, declarations and signatures.
The return's residueTrace/IsFunctionFieldAlgebra observation was advisory; the
requested repair concerns only the resolution-comparison definition ownership.

## New nodes

`def-pc-module-cohomology-ext-resolution-equiv` records the existing definitions
in `WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality`,
with `existing: true`. For every scheme X, module F and q ≥ 0 its main declaration
is `moduleCohomologyExtResolutionEquiv X F q`, with source exactly
`(RingedSpace.moduleCohomology X.toRingedSpace q).obj F` and target `H F q`.
The record also lists `moduleCohomologyExtResolutionNatIso` and the public
`ExtEdgeResolution` definitions assembling the specified composite. Their source
signatures, docstrings and actual constructions were read. The composite uses
standard module resolutions, exact forgetting of homology, the identity between
section complexes, the inverse acyclic-resolution comparison, inverse
Ext/derived-sections identification, then inverse terminal-source precomposition.
No equivalence is selected from a bare existence theorem. The Stacks source is
Tag 03FD (sites-cohomology.tex, lemma-cohomology-modules-abelian-agree); the
Hom-complex and acyclic-resolution ingredients are the cited 06XR and 015E.
This definition is the normalization needed to feed module-derived H¹ into the
existing residueTrace in the blueprint's residue-sequence construction.

The node's q : ℕ includes zero, and X and F are unrestricted, including empty X
and zero F. Its natural-isomorphism packaging is the existing construction, not
an added naturality axiom. Searches are recorded in `mathlib_searches`: LeanSearch
and LeanFinder returned the generic injective-resolution/Ext primitives,
Mathlib grep returned zero matches, project rg found the adopted source owner
and its consumers, and blueprint search and the complete definition-node scan
found no existing definition node for this composite. The existing theorem node
lists these definitions as helpers but states coefficient naturality; the new
node owns the construction needed in a statement. No Lean module is added or
copied, and no existing theorem or definition is edited.

## Self-check by Q12

Reread the returned point against the unchanged Lean file and new node: the only
use is `moduleCohomologyExtResolutionEquiv (Y i) Ω¹ 1` inside the componentwise
residue normalization. The new definition record has exactly that scheme/module/
natural-degree signature and the canonical resolution-normalized construction;
it covers empty schemes, zero modules and degree zero. The former theorem
stmt_dep is absent. The import of its source module still supplies the same
plain definition and needs no change. The independent return already verified
every hypothesis and clause of the unchanged Picard duality Lean module. No new
independent reader was started, per the dispatcher's instruction.

Repair validation (2026-10-21): explicit `scompile.py` passed both sandbox and
final module-name compiles (9.1 s and 9.0 s). Revised `deliver2.py --no-push`
passed preflight and all per-file checks at `c906b72a7a0`. Verified the new
record signature verbatim and every listed construction declaration as an
existing `def` in the adopted upstream source. No Lean source changed.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Worker report

Item: lem-weil-isomorphism-scalar-quotient-chain-squares. The module
`Sheaf.Paper.IsomorphismScalarQuotientChainSquares` states
`AlgebraicGeometry.ProEtale.ScalarQuotientChain.scalar_quotient_chain_squares`.
This is the only postponed theorem, with proof `sorry`. Every auxiliary definition
has real data: abbreviations specialize existing constructions, structures bundle
exactly the hypotheses, and formula predicates spell out generator equations.
There is no statement correction and no disputed statement.

Source read: `literature/stacks-project/sites-modules.tex`,
`section-tensor-product`, lines 3550–3640 (Tag 03EK, tensor construction,
sheafification compatibility, and bilinear universal property). The coefficient
calculation is the agent argument recorded in this node, not a quoted Stacks theorem.
All seven proof steps are copied as a mathematical proof in the theorem docstring.

### Hypotheses and clauses

- Scheme isomorphism: `{X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]`.
- The small sites are the original `W.ProEt` and `ProEt.topology W`, with object
  universe t+1 and morphism universe t. `Coeff.{t,r} W` uses commutative rings
  in `max r (t+1)`; the module universe is the same. No equality between site
  object, site morphism or independent coefficient universes is assumed.
- The size convention is implemented by explicit universes. Existing
  `EssentiallySmall` instances for these sites are used, without adding a size
  hypothesis. The sectionwise model retains every site object, so it does not
  discard identity cases or require an arbitrarily selected skeleton.
- F is `inverseRing g` on commutative ring sheaves, the recorded
  `isoSectionwiseInverseImage`. On modules it is `inverseModules g c`, using
  `isoSectionwiseModuleInverseImage` with the commutativity-forgetting image of c.
  Thus the action is transported by c inverse. On cochains it is `inverseComplex`.
  Evaluation at `op ((proEtaleIsoPostcompose g).obj U)` implements precisely the
  node's identification of corresponding Y sections. This is the canonical
  sectionwise inverse-image model from the recorded isomorphism lemma.
- For each W, `Tower W` fields R, S, A, B, j, i, piA, piB, qA, qB are exactly
  the two coefficient rings, towers and maps in the node. An index n : ℕ means
  positive level m=n+1, including m=1. No level is omitted.
- `Tower.transition_i` is i_(m+1) followed by qB = qA followed by i_m.
  `projection_A` and `projection_B` state compatibility of both projections
  with transitions. `projection_i` is j followed by piB = piA followed by i.
- `Transport g DX DY` fields cR, cS, cA, cB are the four specified ring-sheaf
  isomorphisms. `j_comm`, `i_comm`, `piA_comm`, `piB_comm`, `qA_comm`, `qB_comm`
  give each of the six stipulated compatibility families. No compatibility
  is replaced by an unconstrained scalar map.
- `ringedSiteModules` is the recorded general-site category of module sheaves.
  `moduleComplex W R` is its unbounded integer cochain category. `scalarExtend`
  is the existing `CochainPullback.extend` on that site: ordinary sheafified
  balanced change of rings, applied to terms and differentials. This is the
  usual model of total tensor with the coefficient ring concentrated in degree
  zero (exactly one nonzero summand in each degree, even for unbounded P).
  The existing API places the scalar first: s tensor p represents p tensor s.
  `pure` specializes `extensionTmul`, the actual sheafification-unit tensor.
- `left g d` is G_R followed by extension along j_X; `right g d` is extension
  along j_Y followed by G_S. The given b is an isomorphism of these functors.
  `hb : UpperFormula g d b` says in every degree, on every corresponding object,
  b(Fp tensor cS(Fs)) = F(p tensor s), the exact required normalization.
  Using a natural isomorphism packages the canonical natural family b_P.
- `finiteLeft g d n` is extension along piA_Y, then G_A,m, then extension
  along i_X,m. `finiteRight g d n` is extension along j_Y followed by piB_Y,m,
  then G_B,m. `Tower.projection_i` identifies this latter ring map with i piA.
- The witness `bfin : ∀ n, finiteLeft ... n ≅ finiteRight ... n` consists of
  natural B_X,m-linear isomorphisms of complexes, not merely homology isomorphisms.
- The first conjunct of `FiniteFormulas` says on `doublePure ... a s p`:
  bfin sends F(p tensor a) tensor s to
  F(p tensor (i_Y,m(a) * cB,m.inverse(s))). The explicit `@id` only fixes the
  already definitionally corresponding Y section type; it adds no object/map.
- The second conjunct gives the inverse rule on every `finitePure ... s p`:
  F(p tensor s) goes to F(p tensor 1) tensor cB,m(Fs).
  Since bfin is an actual Iso, mutual inverseness holds on all sections.
- `restrictedLeft` and `restrictedRight` apply the existing `restrictComplex`
  along piB_X,m. They preserve the exact underlying complexes and maps.
- The witnesses v and w are natural transformations of these cochain-valued
  functors. `QuotientFormulas` gives both stated coefficient rules, respectively
  on all X scalars s and on corresponding Y scalars s0. In particular the left
  rule uses piB_X,m(s), and the right rule uses piB_Y,m(s0), not substitute maps.
- The first natural-transformation square in the conclusion is
  v ≫ restricted(bfin.hom) = b.hom ≫ w, exactly b_(P,m) v_m = w_m b_P
  in the node's right-to-left composition convention.
- vtrans and wtrans are natural transformations from level n+1 to level n
  after restriction to S_X. `TransitionFormulas` gives the induced qA/qB
  rule on the nested source and qB rule on the target. Both factors of the
  source transition are specified, not just its outer B factor.
- The second square is vtrans ≫ restricted(bfin_n) =
  restricted(bfin_(n+1)) ≫ wtrans, exactly the requested transition identity.
- All witnesses are morphisms/isomorphisms in cochain categories, so commutation
  with all differentials is part of their types. All are natural transformations
  or natural isomorphisms over the entire source cochain category, so naturality
  includes every chain map P → P'. No boundedness, K-flatness, flatness,
  surjectivity, nonzero-ring or nonzero-complex hypothesis occurs anywhere.

### Dependency declarations used

Read every original stmt_dep statement and lean/mathlib record, and the following
recorded source declarations/docstrings:

- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`.
  Scheme morphism properties and size convention are convention-only DAG nodes,
  with no declaration to import; `Scheme`, `IsIso`, and explicit universes render them.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleSheafInverseImage`,
  base change, the module construction, and its size conventions. Publicly
  reexported through the isomorphism-model import.
- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`:
  `isoSectionwiseInverseImage`, `isoSectionwiseModuleInverseImage`, and its
  additive instance. Its public predecessor exposes `proEtaleIsoPostcompose`
  and the canonical comma-normalized section identification. The new definition node
  `def-weil-proetale-iso-sectionwise-inverse-image` owns the model actually used;
  the isomorphism inverse-image theorem remains in proof_deps only.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`; publicly available through imports.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal` and the existing sheafified tensor
  interface, with independent site object/morphism universes.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`,
  the recorded direct-sum total convention. Here coefficients are in degree
  zero; the already existing `extend` is its termwise scalar-extension model.
- `Sheaf.SecSmoothPurity.CochainCoefficientArrows`:
  `CochainPullback.extensionFunctor`, `extensionTmul`, `extend`,
  `restrictComplex`, `extensionFunctorAdditive`, and the underlying Modules/
  Complex aliases. The owning landed node `def-pur-cochain-coefficient-arrows`
  is added to stmt_deps; these constructions are reused, never copied.
- Proof-only imports: `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
  (`PresheafOfModules.sheafification`),
  `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`
  (`PresheafOfModules.existsUnique_bilinear_sheafification_extension`), and
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`
  (`SheafOfModules.tensor_bilinear_universal`). The recorded inverse-image and
  tensor proof dependencies are also statement dependencies and public imports.

### Searches and edge cases

- msearch.py leanfinder: "Inverse image tensor scalar extension comparison
  commutes with coefficient quotient and transition maps": 8 hits, algebraic
  presentations and tensor quotient facts, no site/cochain statement matching this node.
- msearch.py loogle: "SheafOfModules.changeOfRings, CochainComplex": zero hits,
  unknown project identifier. Follow-up "TensorProduct.assoc": 12 hits including
  TensorProduct.assoc/assoc_tmul, all algebraic fixed-ring associators; none states
  these two tower squares with inverse-image coefficient transport.
- msearch.py grep: "changeOfRings|extendScalars" in
  Algebra/Category/ModuleCat/Sheaf: the Mathlib ChangeOfRings import/interface;
  Mathlib does not supply the present statement.
- rg in lean/WeilConjectures for the exact item id: no match. Concept search
  for changeOfRings in that source found existing TensorProduct construction,
  which is reused through CochainCoefficientArrows. Search in lean/Sheaf found
  IsomorphismScalarTensorKFlatModel and related scalar interfaces. Read that
  specialized theorem: it assumes finite padic field extensions and good
  K-flat complexes, so it does not state this arbitrary-coefficient, arbitrary-
  complex node. Its double-pure and formula organization informs this module,
  without copying any coefficient notion or adding its hypotheses.
- rg in dag/lean_names_upstream.json for ScalarQuotientChain: no name clash.
- Read the exact TensorProduct, change-of-rings, sheafification, ringed-site
  modules, total bifunctor, and sectionwise inverse-image signatures and docs.
- Checked zero rings (where they occur in a compatible diagram), zero terms and
  zero complexes; no cancellation by a scalar is used. Arbitrary maps such as
  an identity, a nonflat quotient, or an injective nonsurjective coefficient
  transition remain allowed. Index n=0 gives m=1 and its transition from m=2.
  Negative complex degrees and complexes unbounded in both directions remain
  allowed. The identity scheme isomorphism and empty schemes impose no extra
  hypotheses. No assertion identifies all sheaf-tensor sections with pure
  tensors: generator formulas use the genuine sheafification units, and the
  proof explicitly uses bilinear-extension uniqueness for nested sheafification.

Validation: scompile.py compiled both the sandbox and library module cleanly
(15.4 s and 14.6 s), within the fixed 60-second limits. An early error exposed
an implicit site/size inference ambiguity; explicit universes and site arguments
resolved it without changing any universe or mathematical hypothesis. Another
elaboration cost in componentwise square notation was removed by stating the
same square as equality of natural transformations (its component equations
are definitionally the requested equations).

## Second reading by Q15

A separate clause-by-clause reread of the node and the final file by this worker
checked the complete Tower and Transport fields, both forward/inverse rules,
both coefficient rules, both transition rules, scalar restriction, both square
orientations, chain-map typing and naturality. In particular the inverse rule
uses cB.hom and the forward rule uses cB.inv; the transition square uses bfin at
level n+1 on the source-side path. Positive indexing includes m=1; P ranges over
all unbounded complexes. Every auxiliary declaration has source/blueprint docs;
the only theorem has exactly `sorry`. No statement mismatch was found. This is
a second pass by the same worker, not a claimed independent agent review: the
dispatcher explicitly forbids starting another agent, and the maintainer's
independent delivery review is the independent reading.

## New nodes

`def-weil-proetale-iso-sectionwise-inverse-image` records the already published
sectionwise inverse image and module action transport in
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage` with `existing: true`.
Its primary declaration is `AlgebraicGeometry.Scheme.isoSectionwiseInverseImage`;
its declarations also name `isoSectionwiseModuleInverseImage`, the reexported
`proEtaleIsoPostcompose`, its continuity instance, and module additivity for cochains.
The source is Stacks 09A5 (proetale.tex, section-morphism), 00WX
(sites.tex, lemma-adjoint-sheaves), and 03D2 (sites-modules.tex,
lemma-pullback-module). For arbitrary coefficient categories the sheaf is evaluated
on corresponding objects; for module sheaves the specified inverse coefficient
map gives the scalar action. The source declarations have exactly those signatures,
including arbitrary sheaf Hom size and module size max r (t+1).
LeanSearch and LeanFinder with query "Sheaf inverse image along scheme isomorphism
by precomposition and module scalar transport" each gave 8 related scheme/sheaf
facts, rather than these pro-etale definitions. Mathlib grep for
"sheafPushforwardContinuous|def pushforward" in Algebra/Category/ModuleCat/Sheaf
gave 17 hits, including the generic pushforward reused by the project definition.
Project rg found the exact existing declarations in the two published Sheaf modules
and no duplicate in WeilConjectures. DAG textual search and a definition-node audit
found only the theorem attachment and unrelated point/adic/constant specializations;
`tools/blueprint_refs.py search 'sectionwise inverse image'` returned 0 blueprint
nodes. The new node's mathlib_searches records these results, and its blueprint
ancestor/via and chapter/unit are inherited from the item.

## Returned delivery repair

The independent review of immutable head ea3f49d03a43 found one defect, H2:
plain sectionwise definitions were attributed to the theorem
`lem-weil-proetale-isomorphism-inverse-image` as a statement dependency.
Added the definition node above and replaced that theorem in the saved item's
stmt_deps with the new definition node. The theorem stays in proof_deps.
`def-pur-cochain-coefficient-arrows` remains a statement dependency, as accepted
by the return. The item's mathematical statement, proof, proof_deps and Lean
source are unchanged. The current main copy still has lean:null and the original
seven statement dependencies, so the repair preserves all current-main fields
other than the authorized lean record and two added definition dependencies.
The saved packet's initial dry run passed (d638b208416); that structural success
did not resolve the independent H2 finding, which is repaired here.

### Second reading of the repair by Q15

Read the new node against the complete existing definitions and docstrings:
Phi_g changes only the structure map; F_g is literal precomposition with its
opposite, using the existing continuity instance; G_c uses module pushforward
along inv c, so its scalar action is c inverse. The primary recorded signature
is verbatim from the published module. The node adds no equivalence assertion,
flatness, nonzero condition or surjectivity requirement. Identity isomorphisms,
empty schemes, zero coefficient rings and independent universes remain allowed.
Checked that the item cites this definition node, while the theorem is a proof
dependency only. No Lean source changed and no new theorem or sorry was added.
This is a second reading by this worker; no other agent was started.

Final repair validation: scompile.py reports clean sandbox/library compilation
(15.4 s / 14.6 s). The repaired deliver2.py --no-push passes server preflight
and compilation, including the existing-definition record (commit 719cf8ec607).
Self-check confirms the new node cites exactly its declared dependencies, its
record is existing:true with no duplicate file, the consumer's theorem signature
is verbatim, the sole postponed proof is sorry, and the consumer contains no
choice of the isomorphism inverse-image theorem.

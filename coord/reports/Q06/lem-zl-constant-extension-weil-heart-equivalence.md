## Worker report

The module `Sheaf.Paper.ConstantExtensionWeilHeartEquivalence` states
`WeilConjectures.constantExtensionWeilHeartEquivalence`, together with the explicit
geometric cyclic-sheet statement `constantExtensionCyclicSheets`. All theorem
proofs are `sorry`. Definitions have real data: the existing unique finite
subfield, actual categorical pullbacks, universal pullback lifts, the canonical
fibre isomorphism, and composites of the published normalized pullback comparisons.
The equivalence itself is asserted, with its underlying natural transformation
and Weil structure characterized by `ConstantExtensionSheetSpec`; no arbitrary
map or choice from a mere existence statement defines a functor.

The previous BLOCKED report mistook NU's stage-1 completion for a stage-2 landing.
The shared item has a reviewed split but no `lean` record. Its source statement
and proof are retained. This delivery does not resplit the reviewed node.

Hypotheses and objects, individually:

- The finite-field tuple `(p,a,q,k_0,k)` is the recorded `D : FiniteFieldDatum.{u}`.
  Its fields carry primality, positive exponent, cardinality and algebraic closure.
- `m : ℕ`, `hm : 1 ≤ m` is exactly the positive constant-extension degree.
- `X₀ : Over (Spec (.of D.k₀))` is the base scheme. `LocallyOfFiniteType X₀.hom`
  and `QuasiCompact X₀.hom` jointly mean finite type. `hsep : IsSeparated X₀.hom`
  is explicitly included in the main theorem.
- `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p` give the coefficient prime.
- `Ω : Type v`, `[Field Ω]`, `[Algebra (Padic l) Ω]`,
  `[IsAlgClosure (Padic l) Ω]` give the fixed coefficient closure. Its universe
  is independent of the scheme universe. `iota : Ω ≃+* ℂ` is the specified realization.
- `constantExtensionDatum D m hm` has `p=D.p`, exponent `D.a*m`, cardinality
  `D.q^m`, base field exactly `D.extensionSubfield m hm`, and closure exactly `D.k`.
  Only its finite-field and algebraic-closure proof fields are postponed.
- `constantExtensionModel` is the actual pullback of `X₀` to this subfield.
  `constantExtensionOriginalModel` is that same scheme with the composite
  structure map to `Spec k₀`. `constantExtensionProjection` is its first projection.
- `sfCommonStageWeilSheaf` is used in all three hearts. Its carrier is a fixed
  pair in the actual common-stage constructible derived category, in the recorded
  standard heart. There is no lissity, irreducibility or semisimplicity binder.

Clauses, individually:

- (a), unchanged underlying object on `X`: `constantExtensionFiberIso` is the
  canonical base-change identification, obtained from the distinguished sheet
  followed by the actual base-changed projection. `constantExtensionFiberPull`
  uses the recorded derived inverse image of this isomorphism.
  `ConstantExtensionRestrictionSpec` supplies the natural carrier comparison for
  restriction, including its action on every arrow.
- (a), iterated Weil map: `constantExtensionWeilIterate` has base case `K.str`
  and the recurrence with the prescribed `zlPullComp` and pulled-back `K.str`.
  The structure equation of `ConstantExtensionRestrictionSpec` equates the
  new Weil map, under the natural carrier comparison, with this actual iterate
  at index `m-1`. `constantExtensionFiber_return` identifies q^m-Frobenius
  with the mth power of the old geometric Frobenius.
- (a), exactness: both `PreservesFiniteLimits` and `PreservesFiniteColimits`
  are asserted for `constantExtensionRestriction`. On these abelian hearts
  this is exactness, including preservation of zero, kernels and cokernels.
- (a), closed-point image: `constantExtensionClosedImage` uses the actual
  point map of the finite projection and its named closed-image theorem.
- (a), residue degree: `constantExtensionResidueDegree` is `Module.finrank`
  along the actual `Scheme.Hom.residueFieldMap`, with the induced algebra
  explicitly installed. It is not replaced by the total extension degree.
- (a), arithmetic formula: the closed-point conjunct asserts
  `f = m / Nat.gcd (localClosedPointDegree D X₀ x) m` and
  `Nat.card κ(z) = (Nat.card κ(x)) ^ f`.
- (a), local operator: `ConstantExtensionLocalConjugacy` is asserted for every
  constructible input and every closed `z`, with this same `f`. For every common
  finite Weil presentation and every compatible residue-field embedding, it
  gives an isomorphism of the actual scalar-extended degree-zero point modules
  intertwining `localClosedFrobeniusCohomology` at `z` with the fth power of
  that at `x`. These are the specified iterated point transports, not an
  arbitrary Frobenius endomorphism. Common coefficient stages exist because
  a fixed pair and its inverse involve only a finite diagram of common-stage
  morphisms; enlarging once represents the whole diagram.
- (b), m cyclic sheets: `constantExtensionCyclicSheets` asserts that the
  translates `constantExtensionCyclicSheet i`, `i : Fin m`, are open and closed
  immersions and give an `IsColimit` coproduct cocone onto the k₀-geometric
  fibre. The final equation states the m-step return with geometric q^m-Frobenius.
  Their definition uses precisely the distinguished embedding k_m into k.
- (b), canonical restriction and return: the main theorem supplies an
  equivalence `e` satisfying `ConstantExtensionSheetSpec`. The natural
  carrier comparison is sheet restriction, and its displayed structure
  equation is the actual return around the entire m-cycle.
  `constantExtensionReturnComparison` is constructed from `zlPullComp`,
  the sheet-return equality, and `zlPullComp` again; it is not freely chosen.
- (b), inverse: equivalence unit and counit give the inverse, and the
  `constantExtensionSheetPullAt` clause identifies its carrier on every
  semilinear sheet with the given k_m-carrier. In these coordinates the
  successive Frobenius translates have identical carriers. The SheetSpec
  return equation and equivalence inverse identities impose the given
  q^m-Weil map as the return. This is the normalized cyclic tuple, with
  identities on intermediate arrows, up to its canonical isomorphism.
- (b), exactness in both directions: the main theorem asserts finite-limit
  and finite-colimit preservation for both `e.functor` and `e.inverse`.
  An equivalence identifies subobjects; these exact functors also identify
  their cokernel quotients and arbitrary finite chains. Thus the statement
  includes all subobjects, quotients and finite filtrations, not just a
  numerical consequence of mixedness.
- (b), local operators: the same `ConstantExtensionLocalConjugacy` clause
  is asserted with exponent `1`, at the same underlying closed point `z`
  for `N` and `e.functor.obj N`.
- (b), absolute residue size: the two models have definitionally identical
  underlying schemes, so `κ(z)` and its `Nat.card` are literally the same
  terms. No new relative degree or cardinality convention is introduced.
- (b), pure quotients and mixed filtrations: for every `N` and real `w`,
  the main theorem gives both directions of the recorded
  `SfIsPunctuallyPureOfWeight` and `SfIsMixedOfWeightsAtMost` predicates.
  Exactness transports the actual cokernel quotients, so the purity
  equivalence applies to every corresponding quotient as well.
- (b), final pullback clause: restriction is explicitly the canonical
  `zlWeilPull g_m` followed by `e.functor`. The main theorem states the
  natural isomorphism from this restriction followed by `e.inverse`
  back to `zlWeilPull g_m`. There is no pushforward in this construction.

Recorded dependency declarations used, with sources read:

- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum`, `extensionSubfield`,
  `extensionEmbedding`, `geometricFiber` and their docstrings. The unique
  subfield theorem is reused for the datum; no field is independently chosen.
- `Sheaf.Paper.SfWeilSheafComplex`: `sfWeilComplex`,
  `sfCommonStageWeilSheaf`, `sfCommonStageWeilForget`,
  `sfCommonStageWeilFrobeniusPullback`, `sfWeilPrimeInvertible`,
  `sfWeilStageObject`; the fixed-pair and finite-stage signatures were read.
- `Sheaf.Paper.SfConstructibleHeart`: `sfCommonStageHeartProperty`,
  its standard-class definition, heart construction and abelianity interface.
- `Sheaf.Paper.LocalFrobeniusTrace`: `localPositivePower`,
  `localClosedPointDegree`, `localClosedPoint`, `localPointComplex`,
  `localClosedFrobeniusCohomology`; its full definitions of the iterate,
  point transport, return comparison and local operator were inspected.
- `Sheaf.Paper.AdicPunctualWeights`: `SfPunctualEigenvalue`,
  `SfIsPunctuallyPureOfWeight`, `SfIsMixedOfWeightsAtMost`.
  These predicates include the actual scalar extension and finite filtrations.
- `Sheaf.AlgebraicGeometry.FrobeniusDetailed`:
  `FiniteFieldDatum.geometricFrobenius`, its coefficient map, inverse and
  projection docstrings. The automorphism is semilinear geometric Frobenius.
- Added already-landed dependency `def-zl-weil-ind-sheaf-category`, module
  `Sheaf.Paper.WeilIndSheafCategory`: `zlFiberMap`, `zlPullComp`,
  `zlWeilPull`, and their canonical finite-stage normalization and heart lift.
  These avoid duplicate definitions of Weil pullback and common-stage composition.
- Mathlib: `Over.pullback`, `pullback.lift`, `asIso`, `Cofan`, `IsColimit`,
  `PreservesFiniteLimits`, `PreservesFiniteColimits`, `Module.finrank`,
  `ModuleCat.extendScalars`, and `CategoryTheory.End` powers.

Edge cases checked mathematically: m=1 (one sheet, original Weil map and degree
one); empty scheme (empty carriers and the coproduct of m empty schemes); zero
sheaf (all local modules zero and length-zero mixed filtration); nonsemisimple
Jordan blocks (power/conjugacy is an operator statement); closed degree d=2,
m=2 (f=1, not 2); d=2, m=3 (f=3); d divisible by m (f=1); several components;
arbitrary coefficient-closure universe. No statement correction or dispute.

Searches made:

- `msearch.py ... leanfinder`: "An exact equivalence between constructible Weil
  sheaves after finite extension of the finite base field, by cyclic geometric
  sheets". Eight hits (isocrystals, profinite Galois groups, coherent sheaf
  comparison, condensed locally constant sheaves); none is this statement.
- `msearch.py ... loogle`: "CategoryTheory.IsoAlgebra, CategoryTheory.Equivalence".
  Zero hits; IsoAlgebra is an upstream extension, not a Mathlib identifier.
- `msearch.py ... grep`: "IsoAlgebra|WeilSheaf", subdirectory CategoryTheory.
  Zero Mathlib hits. The exact fixed-pair construction was found upstream
  and is reused through the recorded modules.
- Further Loogle query "CategoryTheory.Equivalence" and LeanSearch query
  "Constructible Weil sheaves on a finite extension of a finite field are
  equivalent to Weil sheaves on cyclic geometric sheets" were run through
  the prescribed wrapper. Loogle returned 12 general equivalence declarations;
  LeanSearch returned 8 general sheaf-comparison and finite-field Galois hits.
  None is the constructible cyclic-sheet theorem.
- `rg` of all upstream `WeilConjectures` for constant extension and cyclic
  sheets found only reduction commentary and representation constituents.
  `grep -rn` for this exact node id found no declaration.
- `rg` of project `lean/Sheaf` found finite coefficient extension constructions
  and geometric descent statements, but no such equivalence. The canonical
  `zlWeilPull` and `zlPullComp` helpers were found and reused.
- DAG search and `tools/blueprint_refs.py search 'constant extension Weil'`
  found no alternative owning node for this two-heart equivalence. Existing
  lisse constant-extension and Weil-group nodes do not state its constructible
  cyclic-sheet conclusion. No new notion node or dependency repair is needed.

The module and statement were reread against the entire node, the current
blueprint proof (paragraphs 1 and 5), and the six dependency signatures.
An initial missing explicit separatedness binder was corrected using
`include hsep in`. Elaborator issues in the induced residue-field algebra
and parentheses around an operator power were repaired. This is a worker
self-check; the maintainer's independent review remains the second reading.

## Second reading by Q06

Independent maintainer reading of immutable delivery
`ab8de972fcdc90080cf653b925472aa2adc9cf6c`, 2026-10-18. I did not author or
previously second-read this delivery. Read packet.md, the full check-brief2.md,
the stage-2 contract, delivery-errors H, all seven statement-dependency nodes,
their recorded declarations and docstrings, the delivered module and worker report.

Sources inspected: the named main-20261015 blueprint proof of
thm-zl-real-mixed-by-curves, including constant-field restriction and descent;
Deligne, Weil II, (1.1.8), (1.1.10), the change-of-base-field paragraph on p.152,
(1.1.14), and (1.2.6); Stacks sites.tex, lemma-mapping-property-glue (04TS).
The source supports constructible sheaves, rather than only lisse or semisimple
ones. The blueprint's lisse opening is an application, not a restriction on the
change-of-base-field equivalence.

Hypotheses and objects checked individually:

- `D : FiniteFieldDatum.{u}` supplies p prime, a positive, q=p^a, the finite base
  and fixed closure. `m`, `hm : 1 ≤ m` give exactly the extension degrees allowed.
  The new datum uses the existing unique `extensionSubfield` and its inclusion,
  with q^m and the same closure; no arbitrary replacement field is introduced.
- `X₀ : Over (Spec (.of D.k₀))`, locally finite type and quasi-compact, is exactly
  a finite-type scheme. `include hsep in` retains separatedness in the main
  theorem. The auxiliary constructions need fewer assumptions, legitimately.
- `l`, primality, `hl : l ≠ D.p`, `Ω : Type v` with its field, algebra and
  algebraic-closure instances, and `iota : Ω ≃+* ℂ` match the coefficient datum.
  Scheme universe u and closure universe v remain independent. autoImplicit is
  false; all variables are bound. No additional Noetherian, properness, lissity,
  irreducibility or semisimplicity binder appears.
- The two models are the actual pullback and the very same underlying scheme
  with composite k₀-structure map. Projection, sheet inclusion and fibre
  isomorphism are constructed with pullback maps and universal properties.
  `sfCommonStageWeilSheaf` is the recorded full heart-carrier fixed-pair category,
  not the older derived category of Weil sheaves or a discrete sheaf substitute.

Conclusion clauses checked individually:

- (a) `ConstantExtensionRestrictionSpec` naturally identifies the carrier with
  pullback by the canonical fibre isomorphism and specifies the new Weil map.
  `constantExtensionWeilIterate` starts with theta and recurs using the specified
  `zlPullComp`; localPositivePower index m-1 means exponent m, including m=1.
  `constantExtensionFiber_return` supplies the geometric q^m comparison.
- Finite-limit and finite-colimit preservation assert exactness of restriction
  on the abelian hearts. The closed image is the actual projection of z;
  residue degree is finrank for its induced residue-field algebra. The formula
  uses the actual degree d over k₀ and asserts f=m/gcd(d,m) and q_z=q_x^f.
- `ConstantExtensionLocalConjugacy` uses the recorded degree-zero
  `localClosedFrobeniusCohomology`, including its iterated point transports and
  normalized integral composition. It quantifies over finite Weil presentations
  and compatible residue embeddings, and compares the scalar-extended operators
  by an isomorphism intertwining with the fth power. Common-stage descent of
  the finite diagram supplies such presentations; this is not a fixed-field or
  eigenvalue-only substitute for operator conjugacy.
- (b) The separately recorded `constantExtensionCyclicSheets` states clopen
  immersions, the coproduct universal property for all m sheets, and the return
  equation. `ConstantExtensionSheetSpec` specifies the equivalence's underlying
  functor on arrows and the full Weil return; it is not an unconstrained map.
- The inverse-sheet carrier clause, the equivalence unit/counit and SheetSpec
  specify successive translates with the prescribed return, up to isomorphism.
  Both directions preserve finite limits and colimits. Equivalences identify
  subobjects, and exactness identifies their cokernel quotients and finite
  filtrations, so separate redundant filtration clauses are unnecessary.
- For the same z in both interpretations the local conjugacy exponent is 1.
  Their underlying schemes are definitionally the same, hence so are residue
  fields and absolute cardinalities. The purity and mixedness equivalences
  quantify over every N and every real weight. Exactness applies these to all
  corresponding quotients and transports actual finite filtrations.
- Restriction is defined as `zlWeilPull g_m` followed by the equivalence; its
  composite with the inverse is naturally isomorphic to `zlWeilPull g_m`.
  This is the stated pullback before direct image.

Dependency/interface and pilot checks:

Read FiniteFieldFiber, SfWeilSheafComplex, SfConstructibleHeart,
LocalFrobeniusTrace, AdicPunctualWeights, FrobeniusDetailed, and the used portion
of WeilIndSheafCategory. In particular `zlPullComp` is chosen from its uniquely
integral-normalized specification; `zlWeilPull` has explicit carriers, arrows and
Frobenius square. The finite-stage local operator composes point transport,
return comparison and the iterated Weil map in the required order. The weight
predicates extend scalars before testing eigenvalues and use finite mono chains
and cokernels. Existing notions are reused; the common-stage iterate is a
necessary extension of the finite-stage iterate, not a second definition on the
same category. Independent rg searches of Mathlib, upstream WeilConjectures and
project Sheaf found no existing two-heart cyclic-sheet theorem. An independent
LeanFinder search returned eight finite-field/Galois facts, no matching theorem;
the worker also records LeanSearch and Loogle searches.

All definitions contain real data. The fibre isomorphism uses asIso of a specified
map with a named IsIso theorem; no data is chosen from bare existence. Every
postponed theorem has a source/blueprint docstring and sorry-only proof. Helpers
belong to the owning node's constructions/clauses and are listed in
lean.declarations. Module/declaration docstrings and the main theorem's nine
proof steps agree with the node's argument. Imports are used, all lines have at
most 100 characters, and there are no private copies or name conflicts found.

Compared the node to the immutable commit's parent: only lean and stmt_deps
change; the latter adds the already-landed def-zl-weil-ind-sheaf-category. No
new node, dependency module, statement correction or citer audit is needed.
The lean.statement field equals the file's main theorem signature verbatim.
The current route-pivot dropped list has no intersection with this item's
statement/proof dependencies. No item-specific repair note exists at the named
origin/newtargets-dag path. The proof uses ordinary derived pullback, finite
clopen decomposition and fixed pairs; it reintroduces none of the dropped
infinity/dg/model-category machinery. The side framework manifest was read;
recorded side sources, rather than an older pro-etale API substitute, were used.

Edge cases: m=1 gives the original one-step theta and one sheet; m=0 is excluded
by the node itself. The empty scheme gives a coproduct of empty sheets and
vacuous local assertions. The zero sheaf has zero local modules and a length-zero
filtration. Nonsemisimple Jordan blocks are allowed because conjugacy is an
operator assertion. d=2,m=2 gives f=1, whereas d=2,m=3 gives f=3; if m divides d,
f=1. Nonconnected schemes and arbitrary real weight bounds are included.

Compiler evidence: the original worker report records no per-file compile result,
so I supplied a fresh immutable-file check with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q06
lem-zl-constant-extension-weil-heart-equivalence
snapshot/lean/Sheaf/Paper/ConstantExtensionWeilHeartEquivalence.lean`
(the displayed command is wrapped here for readability). Exit status 0:
sandbox Sheaf/Stage2/Sandbox0.lean, 22.0 s, and library
Sheaf/Paper/ConstantExtensionWeilHeartEquivalence.lean, 20.2 s; no Lean errors or
warning diagnostics. The installed wrapper runs a server-hosted private side
overlay; its output identifies /dev/shm/nt-tmp/.../.lbuild. Thus this is evidence
for the actual installed wrapper, not a claim that its older local-only
implementation was used. No direct SSH command, lake/global build, direct live
Lean edit, delivery, claim, merge or Git mutation was performed by this review.

Findings and corrections: H11/H1 report defect only. The delivered second-reading
section was an explicit placeholder, not an independent reading, and omitted
compiler evidence. This complete replacement retains the Worker report and
supplies this actual independent reading and compiler result. No mathematical,
Lean, dependency or statement-field correction is needed. All three delivered
files were verified byte-for-byte against the named immutable commit. The
review does not change that delivery commit or branch.

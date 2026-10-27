## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.NormalExtensionTorsorReduction`
states `AlgebraicGeometry.normal_extension_torsor_reduction`, with proof `sorry`.
The four auxiliary declarations `NormalTorsorReduction.Data`, `Data.map`,
`SectionFiber` and `BaseChange` spell out this theorem's own conclusions and actual
quotient morphism. They are recorded in `lean.declarations`. The structures have
real fields, and `Data.map` is the explicit composite of the identification inverse
and N-torsor projection. No object or map is chosen using a postponed existence
proof. There is no other postponed theorem. No natural-language statement correction
and no dependency interface repair was needed.

Sources opened: Milne, Algebraic Groups (2017), printed pp.60--61 (Definition 2.66,
Examples 2.67--2.68, Proposition 2.69 and Exercise 2-1), p.344 (Proposition 16.55 and
Corollary 16.56), and pp.584--585 (Appendix A.80--A.81). These are PDF pages 72--73,
356 and 596--597. The item is an extracted supporting lemma, not a blueprint unit
statement. `tools/blueprint_refs.py ancestor` reports None; the latest blueprint
search for `normal extension torsor` gives no matching node.

Hypothesis correspondence:

| Node | Lean |
| --- | --- |
| A field k | `{k : Type u} [Field k]` |
| N, G, Q are k-group schemes | `N G Q : Grp (Over (Spec (.of k)))`; the recorded internal group objects, with actual multiplication, unit and inverse |
| Each is affine | `[IsAffine N.X.left]`, and the analogous G and Q binders |
| Each has finite type | `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]` for each H=N,G,Q, following the finite-type dependency |
| Closed normal subgroup i:N→G | `i : N ⟶ G`, `[IsClosedSubgroupScheme i.hom.hom] [IsNormalSubgroupScheme i.hom.hom]` |
| Homomorphism q:G→Q | `q : G ⟶ Q` in the category of group objects |
| q faithfully flat and surjective | `[Flat q.hom.hom.left] [Surjective q.hom.hom.left]`; for an affine map this is faithful flatness of its coordinate-ring map |
| q finitely presented | `[LocallyOfFinitePresentation q.hom.hom.left] [QuasiCompact q.hom.hom.left] [QuasiSeparated q.hom.hom.left]` |
| Scheme-theoretic kernel i(N) and Q=G/N as fppf sheaves | `_hquot : IsFppfGroupQuotient i q`; its `IsPullback i ... q η` is the scheme-theoretic kernel square; its orbit coequalizer, specified quotient arrow and universal property identify the sheaf quotient |
| Arbitrary k-scheme S | `S : Over (Spec (.of k))` with no affineness, reducedness or finite-type restriction |
| Any represented right G-torsor P→S | `P : RepresentedRightTorsor G S`, the landed definition, including all five morphism-property fields, right action laws on all test schemes, and the cartesian torsor square |

`IsFppfGroupQuotient` also records local surjectivity, that h_Q is a sheaf and
the N-torsor comparison for q. These are precisely the existing quotient-presentation
interface: under the stated flat surjective kernel hypotheses, the comparison inverse
is (g,h)↦(g,g⁻¹h), and local lifts along the fppf q give local surjectivity. Thus the
interface introduces no extra mathematical restriction or pointwise-surjectivity
assumption. Its coequalizer/universal property is the recorded sheafification notion,
not a private quotient definition.

Conclusion correspondence:

| Node clause | Lean |
| --- | --- |
| P/N represented by R over S | `d : NormalTorsorReduction.Data i q P`, with `d.quotient.space`, `.projection`, `.isSheaf`, `.orbitMap`, `.orbitMap_quotient`, `.universal` |
| The quotient is the sheafification of the restricted-N orbit presheaf | The presheaf `coequalizer (yoneda.map (fst P.space N.X)) (yoneda.map ((𝟙 P.space ⊗ₘ i.hom.hom) ≫ P.action))` is pointwise the orbit quotient; `.universal` asserts bijectivity of precomposition into every fppf sheaf `Z : Sheaf (Scheme.fppfTopology.over B) (Type u)`, and `.orbitMap_quotient` fixes its unit on representatives |
| R→S is a Q-torsor for the induced action | `d.quotient : RepresentedRightTorsor Q S`; `.quotient_action` says exactly r(pg)=r(p)q(g) |
| The quotient map P→R is an N-torsor | `d.kernelTorsor : RepresentedRightTorsor N d.quotient.space`, with `.identification : d.kernelTorsor.space ≅ P.space`; `d.map` is the actual quotient arrow through this identification |
| Its action is the original restricted action | `.restricted_action` identifies N-action followed by `.identification.hom` with the original action after the pair `(identification.hom, i)` |
| Both projections agree over S | `.over_base` identifies the composite N-torsor/Q-torsor projection with the original P→S via the same identification |
| Every S-section a gives P_a=P×[R]S as N-torsor | The first universal clause gives `Nonempty (SectionFiber d a)` for every `a` with `a ≫ d.quotient.projection = 𝟙 S`. `F.torsor` is the N-torsor and `.cartesian : IsPullback F.inclusion F.torsor.projection d.map a` identifies precisely that fibre product |
| The fibre has its induced N-action | `SectionFiber.action` fixes it by the actual inclusion into P and subgroup inclusion i |
| Every section b of P_a composes to a section e of P | `.section_lift` says `(b ≫ inclusion) ≫ P.projection = 𝟙 S` whenever a and b are sections |
| Arbitrary base change of P | For every `S'` and `f : S' ⟶ S`, existential `P'`, `j` have the cartesian square `IsPullback j P'.projection P.projection f` and the exact equivariance equation `P'.action ≫ j = (j ⊗ₘ 𝟙 G.X) ≫ P.action` |
| Quotient formation, quotient action and N-torsor commute with base change | The same full `Data i q P'` is required, so it represents exactly the sheafified orbit quotient of P'. `BaseChange.quotientMap`, `.quotient_cartesian`, `.quotient_action`, and `.kernel_cartesian` identify it with R×_S S', its Q-action and quotient morphism. The kernel square includes r' followed by quotientMap = j followed by r |
| All section reductions and section composites commute with base change | The primed section-fibre existence clause and `BaseChange.section_fibers` apply to every pair of compatible sections and every pair of their fibres. The unique comparison t is cartesian over f, commutes with both actual projections, preserves N-action and identifies the lifted composites of any compatible sections b,b' |
| Identity and iterated pullbacks | Each quotient arrow is fixed on orbit representatives. Each fibre comparison is unique with its pullback projections; identity and composites have those same projections. Cartesian universal properties therefore give precisely their canonical coherence, without a choice of unrelated isomorphisms |

The quotients are stated on the big fppf site over the ground scheme, as in the
landed group-quotient interface. The invariant projection to S is retained in
`over_base`; its slice is the same quotient over S. All test schemes and base
changes are in the fixed project universe u. There is no independent smaller
universe of test schemes or any collapse between object and morphism universes.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `Grp`, `GrpObj`; imported through the group-scheme and quotient modules. `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme` (including the injective algebra-valued subgroup maps and normal range).
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`; `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`; `.QuasiCompact`: `QuasiCompact`; `.QuasiSeparated`: `QuasiSeparated`; `.Flat`: `Flat`; `.UnderlyingMap`: `Surjective`; `.FinitePresentation`: `LocallyOfFinitePresentation`. These are used with the recorded dependency meanings, not alternative predicates.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`, `Scheme.fppfPrecoverage`, `Scheme.fppfPrecoverage_le_fpqcPrecoverage`, the subcanonical fpqc topology. `Mathlib.CategoryTheory.Sites.Over`: `GrothendieckTopology.over`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`, `sheafificationAdjunction`; the quotient conclusion uses their defining universal property (the node's equivalently clause) so it needs no extra `HasSheafify` hypothesis on this large site.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its projections and universal property; `.IsPullback.Defs`: `IsPullback`. The records use a cartesian square, which identifies the displayed spaces with precisely the chosen fibre product up to its unique comparison.
- Newly cited landed node `def-sfb-split-solvable-right-torsors`, module `Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions`: `RepresentedRightTorsor`. Its general represented-right-torsor component is used; neither split solvability nor smoothness of the group is assumed.
- Newly cited landed definition node `def-sfb-fppf-group-quotient-presentation` (existing:true, Q95), module `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`: `IsFppfGroupQuotient`.

The two existing landed nodes above are added to `stmt_deps` under the standing
STMT_DEPS MAY GAIN LANDED NODES rule. All original dependencies remain. There are
no new independent definitions: the four auxiliary declarations only expose the
data and canonical map of this item's own reduction assertion, under the authorized
owning-node helper rule. Every one has its source and this item's blueprint tag.

Stated proof dependencies are imported as ordinary, non-public imports where they
are not already public statement dependencies: `Noetherian` for the finite-type/lfp
comparison, `PullbackCarrier` for surjective base change, `Morphisms.QuasiSeparated`
for qc/qs permanence, `AffineFpqcDescent` (including `Over.DescentDatum` and
`Over.DescentDatum.isEffective_of_isAffineHom_fpqc`), `FpqcAffineDescent`
(`isAffineHom_of_fpqc_cover`), `FlatOfFpqcCover` (`flat_of_fpqc_cover`),
`LocallyOfFinitePresentationFpqcDescent`
(`locallyOfFinitePresentation_of_fpqc_cover`) and `Sites.LocallyBijective`
(`GrothendieckTopology.W_iff_isLocallyBijective`). Flat-field, affine permanence,
fppf-to-fpqc, representable descent and Yoneda declarations are already imported
through the public quotient module. No proof prerequisite creates an import cycle.

Edge cases checked before writing and again against the final statement:

- Empty S and empty pullbacks: no nonempty total-space hypothesis; the empty torsor and its cartesian squares are allowed.
- N=1 and N=G (Q=1): respectively r is an isomorphism and R≅S; the two torsor structures and section fibres have the expected meanings.
- Trivial G-torsor: the quotient is locally and globally S×Q with r=id×q, and section reductions are pullbacks of q.
- Nonsmooth and nonreduced kernel: Frobenius G_m→G_m in characteristic p with kernel μ_p is allowed. No smoothness, etaleness, perfectness or characteristic restriction occurs.
- P(T) or G(T)→Q(T) may lack lifts on a test scheme: only the orbit presheaf is formed pointwise and then sheafified; no global test-point surjectivity is assumed or concluded.
- Non-affine, nonreduced and non-Noetherian S and S', and arbitrary f: all are allowed; only the group schemes are affine of finite type.
- A quotient torsor need not have a global section: the reduction conclusion quantifies over sections that actually exist; it does not assert their existence.
- Arbitrary compatible choices of representatives for cartesian fibres: the unique t in `.section_fibers` compares all such choices, preserving both projections and the actions.

Searches performed for an existing statement (using prescribed msearch.py):

- LeanFinder: `quotient of a represented group scheme torsor by a normal subgroup is a torsor under the quotient group scheme` returned eight abstract representation/group-quotient results (`Rep.quotientToCoinvariants`, `Rep.ofQuotient`, etc.), none the scheme-torsor theorem.
- Loogle: `CategoryTheory.GrpObj, AlgebraicGeometry.IsNormalSubgroupScheme` returned no hits, noting the latter project name is unknown to the remote Mathlib index.
- LeanSearch: `represented right torsor group scheme` returned eight set/additive-torsor results, none this theorem.
- Mathlib grep: `torsor|Torsor` in `AlgebraicGeometry` returned zero hits; `RightModObj|RModObj|RightTorsor|IsRightTorsor` globally returned zero hits.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for `normal_extension_torsor_reduction|NormalTorsorReduction|lem-sfb-normal-extension-torsor-reduction` found no existing theorem or namespace, only the consumer's proof-docstring mention of this item.
- Direct concept searches `torsor|orbit.*presheaf|sheaf.*quotient` and `right.*torsor|right.*action` in project group-scheme modules found the existing group-quotient interface and then `def-sfb-split-solvable-right-torsors` with its landed `RepresentedRightTorsor`. Both are reused. The action-groupoid torsor interface uses left actions and extra equivariant-map data, so is not substituted for the recorded right torsor.
- DAG concept search found `def-sfb-split-solvable-right-torsors`; blueprint_refs ancestor/search returned None/no duplicate, respectively.

No STATEMENT-DISPUTED flag: the source, explicit local quotient coordinates and the
edge-case tests agree with the node. The node's statement, proof, proof_deps and all
other fields are unchanged, apart from `lean` and the two additional landed stmt_deps.

Validation: prescribed scompile.py compiled the only delivered module on the server
against the published live library, exit 0, without errors or warnings. No local
compile, global build, direct repository edit or direct git mutation was performed.

The prescribed deliver2.py --no-push dry run also passed server preflight and
compilation (`OK (dry run)`), staging exactly this module, the item node and report.


## Returned delivery repair

H2, returned head 5bb0cd6bc6ad: replaced the statement dependency
`lem-sfb-affine-normal-quotient-geometry` with the landed definition node
`def-sfb-fppf-group-quotient-presentation`, which owns the existing plain definition
`AlgebraicGeometry.IsFppfGroupQuotient`. Its recorded module is still
`Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`. Read the owning
node, its existing:true Lean record and the full definition: its kernel square,
local surjectivity, represented sheaf, torsor comparison and sheafification
universal arrow are exactly the interface used in `_hquot`. Updated the dependency
list above. The affine-normal-quotient theorem's conclusion is not used.

The sandbox item was compared with current main and refreshed from its node,
retaining the delivered Lean record and the two authorized additional definition
dependencies. The Lean module is unchanged from the returned delivery, as requested;
its signature, structures, proof plan and sorry proof are preserved.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

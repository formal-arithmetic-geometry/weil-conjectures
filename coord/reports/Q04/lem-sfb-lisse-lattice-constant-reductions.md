## Worker report

The delivery states `AlgebraicGeometry.ProEtale.lisseLattice_constant_reductions` in
`Sheaf.Paper.LisseLatticeConstantReductions`, with a single `sorry` and the six-step
natural-language proof from the node. No theorem is proved. The repair additionally records ownership of five existing definitions; no definition is duplicated.
There is no statement correction and no STATEMENT-DISPUTED issue.

The node expressly permits the equivalent sheaf-module encoding. I use the existing
continuous-function coefficient sheaves of `IntegralLisseReductionData` and
`LisseLatticeCoefficientsSized`. These are the canonical realizations of the pulled-back
condensed rings, by `lem-sfb-totally-disconnected-coefficient-realization`; its naturality
and preservation of finite products retain ring operations, scalar maps and finite free
modules. Thus this is the continuous sheaf-module presentation of the same assertion,
not a discrete constant replacement of A_X or E_X.

Hypotheses and clauses:

| Node | Lean |
| --- | --- |
| Prime ell | `(l : ℕ) [Fact l.Prime]` |
| Finite field extension of Q_l | `(E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]` |
| Norm topology, valuation ring, chosen uniformizer and positive quotients | The recorded `lisseIntegerSheafSized`, `lisseFieldSheafSized`, `Padic.coefficientExtensionIntegers` and `Padic.coefficientExtensionUniformizer`; coefficient constructors install the spectral norm; cokernel index n denotes exponent n+1. |
| Any scheme and its small pro-etale site | `(X : Scheme.{u})`, with `X.ProEt` and `Scheme.ProEt.topology X`; there is no connectedness, qcqs or Noetherian assumption. |
| Lisse A_X-module, allowing rank zero and locally varying finite rank | `(N : IntegralLisseModule l E X)`, the full subcategory defined by `SheafOfModules.isFiniteLocallyFree`. This is the sheaf-module form of `IsLisseCoefficientModule`. |
| Actual scalar quotient F_n | `integralLisseCokernel l E X N.obj n`, the cokernel of multiplication by the recorded uniformizer to power n+1. |
| Actual quotient transitions | `integralLisseCokernelTower`, defined from `integralLisseCokernelTransition`, induced by the identity on N; the existing normalization theorem says each transition is the smaller scalar quotient. |
| Fixed d >= 0 | `(d : ℕ)`, with the standard module `SheafOfModules.free (ULift.{u + 1} (Fin d))`; ULift changes only size. |
| Each finite reduction is individually free of rank d, no supplied compatibility | `hconstant : ∀ n : ℕ, Nonempty (cokernel N n ≅ cokernel freeA n)`; these existential isomorphisms are independent. |
| Every prescribed residue basis | The unrestricted binder `b1 : cokernel N 0 ≅ cokernel freeA 0`. |
| Compatible b_n on X itself | `∃ B : integralLisseCokernelTower ... N.obj ≅ integralLisseCokernelTower ... freeA`; `B.app (op n)` is b_(n+1). The naturality of this isomorphism includes all transitions, not just adjacent ones. |
| Extends the prescribed b_1 | `B.app (op 0) = b1`. |
| Global integral basis | `∃ b : N.obj ≅ SheafOfModules.free ...`. |
| Its reduction is b_n for every n | `∀ n, ((integralLisseCokernelFunctor l E X).mapIso b).app (op n) = B.app (op n)`. The functor acts by the actual cokernel map induced by b. |
| Inclusion A_X -> E_X | Exactly `lisseIntegerToFieldSized l E X`, postcomposition with the recorded valuation-subring inclusion. |
| Ordinary tensor scalar extension | `SheafOfModules.changeOfRingsOfUniverses` along this inclusion; this is sheafification of the sectionwise balanced tensor product, not a derived or completed extension. |
| Rational basis E_X tensor N -> E_X^d | The existential `bE` is an isomorphism to the standard free sheaf over `lisseFieldSheafSized`. |
| It is the rationalization of the same b | The last equation, for every U, s, x and coordinate i, sends the image of s tensor x under the actual module-sheafification unit to s times the image under A(U)->E(U) of the i-th coordinate of b(x). Pure tensors generate the tensor presheaf locally and the sheafification universal property determines the morphism, so bE is canonically normalized rather than an unrelated isomorphism. |
| Global assertion, empty scheme and d=0 included | All isomorphisms are in the original site of X, with no cover binder, nonemptiness, positive-rank or point hypothesis. |

Why the finite free target is exactly `(A_n)_X^d`: the cokernel of varpi^(n+1)
on the standard integral free sheaf is canonically the restriction of the standard
rank-d free finite-coefficient sheaf. Cokernels commute with the finite coproduct and
the coefficient quotient is the actual scalar quotient. In the continuous presentation,
the finite coefficient ring is the constant sheaf of the finite discrete ring, as in
`IntegralLisseReductionEquivalence.finiteConstant`. These canonical identifications
commute with the quotient projections and transitions. Restriction of scalars along
the surjective quotient is fully faithful: integral-linear maps are quotient-linear,
as can be checked after locally lifting a coefficient to the integral ring. Consequently
both the individual trivializations and the arbitrary prescribed b1 in the Lean statement
are precisely the A_n-linear trivializations in the node, in equivalent canonical models.
No hypothesis that such a compatible family is already supplied has been added.

Dependency declarations read and reused:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its public import of
  `Sheaf.NumberTheory.Padics.CoefficientExtension` for the integer ring, uniformizer,
  finite quotients and coefficient transitions.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt` and `ProEt.topology`.
- `Sheaf.Topology.ContinuousMapCondensedRing`:
  `Profinite.continuousMapRingSheafOfUniverse`, its abelian sheaf and ring structure;
  `Sheaf.Topology.ContinuousMapCondensedRingMap`:
  `Profinite.continuousMapRingSheafMapOfUniverse` and its ring-object morphism.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`, and the strong
  monoidal point pullback used in the realization interpretation.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, `ModObj`, and `Mod.regular`;
  `Sheaf.Paper.CoefficientHeartStratificationDefs`: `IsLisseCoefficientModule`.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`;
  `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.SixFunctors.IntegralLisseReductionData`: `IntegralLisseModule`,
  `integralLisseRing`, `integralLisseScalar`, and the canonical coefficient interfaces.
- `Sheaf.SixFunctors.IntegralLisseReductionConstruction`: `integralLisseCokernel`,
  `integralLisseCokernelTransition`, `integralLisseCokernelTower`, and
  `integralLisseCokernelFunctor`, including its actual cokernel action on maps.
- `Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized`: `lisseFieldSheafSized`,
  `lisseIntegerSheafSized`, and `lisseIntegerToFieldSized`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free`:
  `SheafOfModules.freeπ`; `Mathlib...Sheaf.Free`: `SheafOfModules.free`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`:
  `SheafOfModules.changeOfRingsOfUniverses` and
  `changeOfRingsPresheafOfUniverses`; Mathlib's
  `PresheafOfModules.sheafificationAdjunction` supplies the actual tensor unit.
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, the tensor node's
  current recorded module, remains a proof import.
- Proof imports preserve the node's other recorded proof dependencies:
  `TotallyDisconnectedCoefficientRealization`, `IntegralSquareZeroMatrixLift`,
  `IntegralLisseReductionComplete`, and `IntegralLisseCoefficientLimit`.

The already-landed nodes `def-per-integral-lisse-reduction-data`,
`def-weil-pbc-lisse-lattice-coefficients`,
`def-sfb-integral-lisse-cokernel-tower`, and
`def-pur-sheaf-tensor-product` are additionally cited in stmt_deps because their existing
interfaces appear directly in the signature. No dependency record is repaired.

Source read: the local Bhatt--Scholze PDF, printed pages 58--60, Definition 6.8.1,
Lemma 6.8.2, Definition 6.8.3 and Proposition 6.8.4(1). The source explicitly begins
with any scheme and adds qcqs only in later clauses (3), (4). Clause (1) leaves its
proof to the reader, so the node's global-basis supplement is retained in the docstring.

Edge cases checked before drafting: d=0 gives an empty finite basis and zero free sheaf;
the tensor coordinate equation is vacuous but both zero objects are retained. The empty
scheme imposes no spurious point, residue-field or nonzero-ring assumption. Disconnected,
non-quasi-compact and non-Noetherian schemes are permitted: global automorphisms are
locally constant matrices, whose lifts are obtained by a discrete set section, so no
connectedness assumption or finite open-cover gluing is needed. Positive exponents start
at n=0 (exponent 1), and square-zero kernels have 2(n+1) >= n+2. The original module may
have locally varying rank before the individual constant-rank trivializations are assumed.
The pro-etale site retains object universe u+1 and morphism universe u; scalar extension's
four universe parameters were specified explicitly rather than equating site universes.

Searches (2026-10-22):

- msearch LeanFinder: `Individually constant reductions of a lisse integral sheaf admit
  compatible global bases extending any residue basis`. Eight results concerned ordinary
  algebraic module bases/finite-presentation loci; none is the global sheaf statement.
- msearch Loogle: `SheafOfModules.free, IsAdicComplete`. No hits.
- msearch grep: `compatible.*(basis|bases|trivialization)|constant.*reductions|reductions.*constant`.
  Eight displayed hits concerned topological bases and manifold local frames, no match.
- msearch LeanSearch: `Global compatible bases of individually constant finite reductions
  of a lisse integral sheaf extending a prescribed residue basis`. Eight hits included
  `IsLocalRing.basisQuotient.congr_simp`, `NumberField.integralBasis`, and algebraic basis
  localization lemmas, no matching sheaf theorem.
- rg in `lean/WeilConjectures` and `lean/Sheaf` for the item id and compatible bases / constant
  reductions: no existing declaration of the item. Relevant reusable results are the
  actual scalar-cokernel construction and completeness modules used above.
- rg for the proposed name in both source roots and `dag/lean_names_upstream.json`: no clash.

Validation: prescribed `scompile.py` compiled the final file as both its sandbox module
and its actual library module, cleanly (6.5 s and 8.3 s). All theorem variables and the
single universe are explicit, with `autoImplicit false`. Only the requested theorem has
`sorry`; there are no helper definitions, axioms or diagnostic commands.

## Second reading by Q04

I reread the node and final module directly, in a separate pass. This is the dispatcher's
single-worker workflow; no second agent was started, and the maintainer supplies the
independent delivery review.

I checked the two presentation changes explicitly: finite free targets are the canonical
scalar cokernels of the standard integral free module, not arbitrary tower objects;
and the continuous coefficient presentation is the one identified with the pulled-back
rings by the recorded realization theorem. Quotient-linearity follows from the actual
surjective coefficient quotient, so the arbitrary b1 is not restricted. The hconstant
binder is pointwise Nonempty, and imposes no compatibility. B is a genuine natural
isomorphism on the entire opposite natural-number indexing category, so all transitions
are covered. Its first component is exactly b1, and mapIso b gives every component.

I checked the rationalization equation against its domain: a pure tensor first enters
the actual scalar-extension sheaf through the sheafification adjunction unit, then bE
is applied, and the i-th target coordinate is compared with s times the scalar image of
the i-th coordinate of b(x). This fixes the same b and uses ordinary tensors. Earlier
elaboration failures were repaired only by explicit scalar-extension universe arguments
and explicit target-ring inference for freeπ. There was no mathematical statement change.
The explicit empty-index, empty-base, nonconnected and unrestricted-scheme cases agree
with the node. No omitted hypothesis or conclusion was found in this pass.

## New nodes

`def-sfb-integral-lisse-cokernel-tower` records the five existing declarations in
`Sheaf.SixFunctors.IntegralLisseReductionConstruction`, with `existing: true` and
branch `sheaf-dag`. Its source is Bhatt--Scholze Proposition 6.8.4(1), p.59, whose
functor is the actual quotient tower. The ambient construction needs no local freeness.
The primary declaration is `AlgebraicGeometry.ProEtale.integralLisseCokernelFunctor`;
its declarations list additionally owns `integralLisseCokernel`,
`integralLisseCokernelTransition`, `integralLisseCokernelTower` and
`integralLisseCokernelMap` in the same namespace. These are exactly the five definitions
requested by the return; no source file needs moving or duplicating.

The node's first clause is the actual `cokernel (integralLisseScalar ... (varpi ^ (n+1)))`.
Its transition is `cokernel.desc` of the smaller quotient projection, hence is induced by
the identity of M, rather than an arbitrary compatible map. `Functor.ofOpSequence`
supplies all composites and identities. `integralLisseCokernelMap` is a
`NatTrans.ofOpSequence` with components `cokernel.map ... f f ...`;
`integralLisseCokernelFunctor` uses precisely these object and morphism assignments.
The source's positive levels are reindexed by n+1. M is an arbitrary module sheaf, so
zero objects, the empty scheme and modules not locally free are included.

Searches for this definition node: LeanSearch's canonical uniformizer-cokernel inverse
system query returned eight generic cokernel/sheafification lemmas; LeanFinder's quotient
tower functor query returned eight tilde/local-cohomology constructions. Loogle returned
zero hits (unknown identifier `cokernel`). Mathlib grep returned only the two generic
`ofOpSequence` constructors. Source and DAG grep found these exact five definitions,
but no definition node owning them. Blueprint search `integral lisse cokernel` returned
zero matches. The similarly titled `def-trf-integral-scalar-tower-functors` defines a
tensor tower of complexes over completed rings and does not own these declarations.
The new node records these searches in `mathlib_searches` without introducing a copy.

## Repair of independent return 31c1e4f8f38e (B3/H2)

The previous statement dependency named the theorem
`lem-sfb-integral-lisse-cokernel-transition-quotient`, but its theorem declaration is
not used to form the signature. I replaced that added dependency by the new definition
node above. The item thus cites the owner of the actual quotient, transition, tower,
map and functor definitions. The existing public import of their module remains correct.
The theorem node is not needed in proof_deps either: the original proof plan is unchanged.
No statement, hypothesis, conclusion or proof step has been changed. The item JSON
changes only `lean` and `stmt_deps` relative to the shared base.

I compared the retained packet with current shared source through the required dry run,
and read the live construction again using `scompile.py --source`. Its five definition
bodies agree with the local source and use no `.choose` of the transition-quotient theorem.
I reread the new node and the item's signature separately: all five ownership clauses
match their definitions, and the item continues to express independent Nonempty bases,
an arbitrary residue basis, a tower iso, reduction of one integral basis and its normalized
ordinary rationalization, including X empty and rank zero. This is the required self-check
of the repair; no additional agent was started under the dispatcher's explicit instruction.

Repair validation: `scompile.py` compiled the retained theorem file as sandbox and library
modules in 4.1 s and 3.6 s, without errors or unexpected warnings. The revised
`deliver2.py --no-push` classified and checked the existing definition binding plus the
theorem module, then printed OK after preflight and per-file compilation.

## Repair self-check of independent return 4a561903c2e3

On 2026-10-23 the prescribed first dry run of the retained packet passed preflight
and per-file compilation, producing dry-run commit 06ed91110b3 with nothing pushed.
The return's incremental reachability finding does not reproduce on the current base.
I retained the statement and definition ownership records rather than inventing an
unreachable flag or changing the source assertion.

I checked the current target route directly from the node records, including every
intermediate node's status. The route is:

thm-weil-final → thm-weil-final-rh → prop-arithmetic-roots →
lem-weil-smooth-proper-purity-hypotheses → sk-thm-sf-package →
det-thm-sf-ctf-stability-adjunctions → det-thm-sf-ctf-stability-direct-images →
lem-sfb-admissible-direct-image → lem-sfb-continuous-algcl-open-finiteness →
lem-sfb-continuous-algcl-open-scalar-comparison → lem-sfb-tame-pair-proper-generators →
lem-sfb-tame-pair-lattice-realization → lem-sfb-lisse-lattice-potential-kummer-tameness →
lem-sfb-lisse-lattice-constant-reductions → def-sfb-integral-lisse-cokernel-tower.

Every node through the item on this route currently has status split and none is
merged. Thus no unsplit-node traversal cutoff interrupts the route. The final edge
is the item's explicit stmt_deps entry in this packet. The new definition is reached
and must not be marked unreachable. No unrelated node was edited.

For the required second reading I reopened the full theorem signature and the existing
IntegralLisseReductionConstruction source. The five owned definitions still construct
the actual cokernels, identity-induced transitions, tower, induced maps and functor;
they do not choose data from the transition-quotient theorem. Independent finite-level
trivializations remain pointwise Nonempty, b1 remains arbitrary, B covers all transitions,
and b induces its every component. The rationalization equation still specifies the
same integral basis on local pure tensors. Rank zero, the empty scheme, varying local
rank before hconstant, and arbitrary schemes remain included. No Lean change was needed.

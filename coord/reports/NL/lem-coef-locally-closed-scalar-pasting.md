## Worker report

The delivery states `WeilConjectures.LocallyClosedScalarPasting.locallyClosedScalarPasting`
in `Sheaf.Paper.LocallyClosedScalarPasting`. It has one postponed proof, `sorry`.
The other fifteen declarations are structures or definitions with real data; they
package the supplied families, their hypotheses, their specified composites and the
four clauses of the conclusion. There is no proof of a mathematical theorem here.
The item's JSON differs only in `lean`. There are no new nodes, dependency-node
repairs, statement corrections or disputed statements.

The prior NO delivery was a stage-1 split: `reviewed` is present, but both `lean`
and `reviewed_lean` were absent. A clearly marked unpublished diagnostic dry run
established that the previously reported already-merged rejection does not occur
in the current stage-2 tools. That diagnostic binding was removed before writing
the actual delivery; it is not part of this packet.

### Each hypothesis and convention

| Node text | Lean rendering |
| --- | --- |
| Fixed algebraic closure of a finite field | `D : FiniteFieldDatum.{u}`; its `k`, `p` and finite-field datum are reused unchanged. |
| Prime ell different from the characteristic | `l : ℕ`, `[Fact l.Prime]`, `hl : l ≠ D.p`. The explicitly included `hl` retains this hypothesis even though the calculation is formal. |
| Finite extensions E and L of Q_l | `E L : Type u`, their `Field`, `Algebra (Padic l)` and `FiniteDimensional` instances. The third field `F` has precisely the same binders. |
| Positive exponents m,n,s | Indices `m n s : ℕ` denote exponents `m+1`, `n+1`, `s+1` in the existing `finiteClosedCoefficient`. This is a bijective reindexing of every positive exponent, including one. |
| A, B and C are the specified quotient rings | `finiteClosedCoefficient l E m`, `finiteClosedCoefficient l L n`, `finiteClosedCoefficient l F s` reuse the actual `Padic.coefficientExtensionRing`. |
| Any unital A-to-B and B-to-C maps | `φ` and `ψ` are arbitrary `→+*` maps of their canonical `ULift` rings. The lift is the existing fixed-coefficient module convention, canonically ring-isomorphic to the original quotient. There is no flatness, field embedding or coefficient-linearity restriction. |
| Small pro-etale constant module sheaves | The existing `finiteClosedDerived T A` is `DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat (ULift A)))`. No alternate site or module category is introduced. |
| Ordinary uncompleted derived scalar extension | `finiteClosedScalar φ T` is the existing `ProEtale.pbcFixedScalarExtension`, left adjoint to actual exact derived scalar restriction. No completion or substitute functor is used. |
| The notation D^b_ctf | The imported `finiteTorConstructibleProEtaleModule` is the existing fixed-coefficient realization of the recorded finite-Tor predicate. The node does not impose a separate D^b_ctf condition on M or Q after introducing this notation: it explicitly specifies chosen bounded constructible etale-origin domains. `Domains` follows that scope, and may in particular be instantiated on a finite-Tor subdomain when the operations preserve it. |
| Separated finite-type schemes over k, and k-maps | `X V W W' : Over (Spec (CommRingCat.of D.k))`, with named `IsSeparated`, `LocallyOfFiniteType` and `QuasiCompact` structure-map instances. All twelve instances are explicitly included in the theorem. `t`, `j` and `u` are morphisms in this over category, so they already are k-maps. |
| t closed, j open, further u closed | `[IsClosedImmersion t.left]`, `[IsOpenImmersion j.left]`, `[IsClosedImmersion u.left]`. |
| All operations defined on chosen full bounded constructible domains of etale origin | `Domains` records object properties `onX`, `onV`, `onW` of the actual ambient categories; their full subcategories are inherited, not new categories. `boundedX/V/W` use the published `ProEtale.DerivedCategory.boundedConstructible`, whose definition is the comparison-pullback essential image of bounded constructible etale complexes. The four closure fields express the indicated operations on those domains. `Comparison.scalarX/V/W` are the needed scalar-domain conditions. `ClosedCocycle` records the corresponding source and target domains on W', with their closure and scalar conditions. |
| Closed exceptional and ordinary direct-image operations | The existing `finiteClosedExceptional` is the specified transported etale exceptional functor; `finiteClosedPush` is ordinary derived direct image. They are not arbitrary supplied functors. |
| Natural closed b_t and ordinary isomorphism c_t | `Comparison.b`, `Comparison.c`, `bNatural`, `cNatural`, `cIso`. They have exactly the source and target displayed in the node. |
| Closed counit normalization | `Comparison.closedCounit` is `c_t ≫ t_*(b_t) ≫ epsilon_t,B = S_V(epsilon_t,A)`, using the actual `finiteClosedCounit`. Lean composition is left to right, the reverse of the paper's juxtaposition convention. |
| Canonical natural open restriction comparison | `(finiteClosedScalarPullIso φ j).inv` is the existing canonical conjugate of scalar restriction/direct-image comparison; it has direction `S_V j_A^* -> j_B^* S_X`. Its global naturality is already part of its `NatIso` type. |
| Natural B-linear open isomorphism e_j with open counit normalization | `Comparison.e`, `eIso`, `eNatural`, `openCounit`. Each component is an actual morphism in the B-linear ambient derived category. The latter field is exactly `e_j ≫ j_!(r_j) ≫ epsilon_j,B = S_X(epsilon_j,A)`. |
| Identity coefficient normalizations | `qid` and `_hi : IdentityCocycle qid`; the record includes the closed, ordinary, restriction and open identities. `unitIso` reuses `normalizedOriginScalarUnit`, so identity scalar extension is never silently replaced by a definitionally equal identity functor. |
| Successive-scalar cocycles for the corresponding families | `r`, `z` and `_hc : ScalarCocycle q r z`; the record retains all four closed, ordinary, restriction and open equations, with the published actual tensor associators. |
| Composition-of-closed-immersions cocycles using chained adjunctions | `cu : ClosedCocycle u.left q` provides the natural b_u, b_tu, c_u, c_tu families, ordinary invertibility, their closed counit normalizations, and both ordinary and exceptional composition equations. The tu functors are explicitly the chained `Ru^! Rt^!` and `t_*u_*` of the node, not an independently chosen composite adjoint. |
| No invertibility of b | No structure or hypothesis contains `IsIso` for `b`, `b_u`, `b_tu`, `pastedB` or `pastedTripleB`; the conclusion asserts none. Only the ordinary c and open e have isomorphism hypotheses. |

### Each construction and conclusion

`pastedB q M hM` is exactly `q.b (j_A^* M) ≫ Rt_B^!(r_j,M)`.
`pastedC q Q hQ` is exactly `q.e (t_*,A Q) ≫ j_!,B(q.c Q)`.
Their domain proofs are supplied by the closure fields, with no default zero
values or hidden choices for the supplied comparisons.

The theorem concludes the conjunction of the following four fully expanded
Prop-valued definitions:

1. `PastingStatement q` contains both input-morphism naturality equations,
   `∀ Q hQ, IsIso (pastedC q Q hQ)`, and the precise pasted counit equation.
   In its last clause `N` is literally
   `(finiteLocallyClosedExceptional A t j).obj M`; the domain proof is
   `dA.closedExceptional _ (dA.openPull M hM)`. The last arrow is the actual
   `finiteLocallyClosedCounit B t j (S_X M)`, and the right side is scalar
   extension of the actual A-counit.
2. `ScalarStatement q r z` says
   `S_W(ψ).map (pastedB q M) ≫ pastedB r (S_X(φ) M) ≫ h_C^!(alpha_X)`
   equals `alpha_W ≫ pastedB z M`. Thus the B-to-C factor is evaluated at M_B,
   as required. Both tensor associators are present, so there is no false
   definitional identification of composed scalar functors.
3. `ClosedStatement cu` says
   `pastedTripleB cu M = b_u (Rh_A^! M) ≫ Ru_B^!(pastedB q M)`.
   `pastedTripleB` first applies the supplied b_tu at j_A^*M and then
   `Ru_B^! Rt_B^!(r_j)`, exactly the definition for j(tu) in the chosen
   chained-adjunction coordinates.
4. `TripleCounitStatement u dA` and `TripleCounitStatement u dB` state the
   formula at both coefficient stages. Each identifies `tripleCounit` with
   `j_!t_*(epsilon_u) ≫ finiteLocallyClosedCounit A t j M`.
   The definition of `tripleCounit` composes u_* with t_* first; the right side
   composes t_* with j_! first. Expanding the existing locally closed counit
   gives exactly epsilon_j after j_!epsilon_t after j_!t_*epsilon_u.

The identity normalization remains a hypothesis, as written in the node; no
additional identity conclusion is added beyond the node's stated conclusions.
The theorem docstring carries all six natural-language proof steps. The helper
Prop definitions merely spell out its clauses; they are not extra theorem claims.
The notation h denotes t.left followed by j.left; its exceptional and compact-support
operations are exactly the existing factorized functors above, without an independent h.

### Dependency declarations and existing definitions reused

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing` and the unchanged `Padic.coefficientExtensionRing` construction from its public dependency.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`, `ProEt.topology`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`: the recorded `SheafOfModules.DerivedChangeOfRingsCochainModel` / `nonempty_derivedChangeOfRingsCochainModel` interface. The scalar functor reused here is the published fixed-module realization `ProEtale.pbcFixedScalarExtension` from `Sheaf.Paper.WitnessCompatibility`, with its actual scalar adjunction and its canonical compositor.
- `Sheaf.Paper.FiniteTorAmplitudeSites` and `Sheaf.Paper.FiniteTorAmplitudeProEtaleModule`: the existing intrinsic and fixed-module finite-Tor predicates; no new Tor definition.
- `def-weil-scheme-morphism-properties` is a convention node; its prescribed Mathlib `IsSeparated`, `LocallyOfFiniteType`, `QuasiCompact`, `IsClosedImmersion`, `IsOpenImmersion` and `Over` are used.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`: the recorded constructible exceptional framework. Its actual finite exceptional construction is `ProEtale.sfFiniteExceptionalFixed` from `Sheaf.AlgebraicGeometry.SfFiniteExceptionalInverseImage`, reused through `finiteClosedExceptional`.
- `Sheaf.Paper.SfDerivedDirectImage`: the recorded ordinary derived-image construction. In the same fixed-coefficient coordinates its ordinary finite direct image is the existing `finiteClosedPush`, namely `(ProEtale.lowerStar _ t).rightDerivedFunctor`.
- `Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`: the recorded compact-support realization. In the specified closed-then-open factorization the same operations are the existing `finiteLocallyClosedPush` and `finiteClosedOpenPush`.
- `Mathlib.CategoryTheory.Adjunction.Basic`: `CategoryTheory.Adjunction.comp` and `comp_counit_app`, which specify the chained double and triple counits.
- `Sheaf.Paper.FiniteClosedShriek`: reuse `finiteClosedDerived`, `finiteClosedCoefficient`, `finiteClosedScalar`, `finiteClosedPush`, `finiteClosedPull`, `finiteClosedExceptional`, `finiteClosedCounit`, `finiteClosedOpenPush`, `finiteClosedScalarPullIso`, `finiteLocallyClosedExceptional`, `finiteLocallyClosedPush`, `finiteLocallyClosedCounit`. The canonical `finiteClosedShriekMap` and its invertibility theorems are never used as supplied b_t.
- `Sheaf.Paper.NormalizedOriginScalarComparisons`: `ProEtale.normalizedOriginScalarUnit` for the canonical identity normalization.

### Import-cycle note for maintenance

`Sheaf.Paper.FiniteClosedShriek` already owns the shared operational definitions
above, and its DAG node `lem-coef-finite-closed-shriek` now lists this item as a
proof dependency. This delivery reuses those definitions instead of copying them.
Its automatic proof-dependency import into that parent must therefore be omitted:
it would form a Lean import cycle. This is the explicit exception in
`stages/2-statements.md` section 3, rule 7. No current import cycle is added. Before
the parent is proved using this lemma, its existing definitions can be moved by the
maintainer into a common data module; no shared file is edited in this delivery.
The parent theorems are not used in this item's statement or its proof plan.

### Edge cases checked

- Level one is `m = 0`; every positive exponent occurs. No zero-exponent quotient is introduced.
- Empty schemes and empty chosen domains are allowed. Universal naturality and counit clauses remain well typed, and no nonempty-domain assumption is made.
- Zero objects and zero component comparisons are not excluded by an invertibility requirement on b. The normalization equations retain whatever restriction the actual supplied counits impose.
- Quotient coefficient maps, nonflat maps, ramified extensions and arbitrary unital maps are all admitted by the bare `RingHom` binders.
- Identity changes use the actual self-extension unit. Successive changes retain the two canonical tensor associators rather than equating scalar functors definitionally.
- The further closed immersion can be the identity. Both parenthesizations of the triple counit have the same actual source and target.
- All sites have their existing object/morphism universes; module values are in `u+1`. No extra equality of site or coefficient universes is assumed.
- The full domains carry component families only on objects in their predicates; no global natural transformation on an unrestricted pro-etale category is assumed.

### Searches made

- `msearch.py ... leanfinder`: “Pasting scalar change comparisons for a closed immersion followed by an open immersion preserves adjunction counits and scalar cocycles”. Eight hits, including ordinary scheme restriction adjunctions; none is this conditional finite-coefficient pasting theorem.
- `msearch.py ... loogle`: `CategoryTheory.Adjunction.comp, CategoryTheory.Adjunction.comp_counit_app`. One hit, `comp_counit_app`, gives only the generic composite-counit formula.
- `msearch.py ... grep`: `pasting|comp_counit_app` in `CategoryTheory/Adjunction`. Three hits: `comp_counit_app` and its uses in Mates. None gives this assertion on the actual coefficient and exceptional operations.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for `locallyClosedScalarPasting|LocallyClosedScalarPasting|finiteLocallyClosed`. No existing declaration has the new name; the locally closed hits are the canonical constructions and theorems in `Sheaf.Paper.FiniteClosedShriek`. Those theorems fix the canonical b_t and assert its invertibility, unlike the present conditional theorem for supplied families. Their shared operations are reused verbatim.
- `rg` for the item id in `lean/WeilConjectures`, `lean/Sheaf` and coordination records found the stage-1 split but no existing Lean statement of the item.

### Validation

Standalone checks through the prescribed `scompile.py` against the published
live library passed without errors or warnings. The prescribed `deliver2.py --no-push`
also passed its server compilation and preflight. The final packet is checked again
by that dry-run wrapper and by the delivery wrapper before publication. Only the node's
`lean` field changes; its signature is copied verbatim from the file. The module has
one `sorry`, every variable is explicitly bound with `autoImplicit false`, no line
exceeds 100 characters, and every helper has a source/blueprint docstring.

## Second reading by NL

No second worker was started, as the dispatch brief prohibits other agents and
specifies that the maintainer supplies the independent review. This section does
not claim an independent reading by a worker.

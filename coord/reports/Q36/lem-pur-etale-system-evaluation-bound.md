## Worker report

The module `Sheaf.Paper.EtaleSystemEvaluationBound` states
`AlgebraicGeometry.etaleSystemEvaluationBound`. Its sole theorem proof is `sorry`.
The record `StrictEtaleEvaluationBound` packages the conclusions; it is not an
assumed exceptional-adjoint package. Three auxiliary definitions build the
specified Hom equivalence, coefficient mate, and finite-level transition word
from the recorded adjunctions and comparisons, with real data and no `sorry`.
No node statement, dependency, proof, or source was changed.

I read Zheng, arXiv:1006.3810, printed pp. 35–36, using the local PDF:
Construction 5.15 gives the ordinary system functor and its amplitude; (5.16.2)
gives the insertion comparison; Lemma 5.22 gives the evaluated right adjoint by
adjunction. I also read the current blueprint's
`sec-six-functors-basics/sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md`.
This item is an ordinary strict-system lemma, not a definition of the condensed
exceptional functor (which the current blueprint explicitly constructs separately).
The node's five proof steps are reproduced as a complete proof plan in the theorem
docstring, including the nonflat transition transpose and the truncation argument.

Hypothesis-by-hypothesis correspondence:

| Node hypothesis or object | Lean rendering |
| --- | --- |
| Algebraic closure of a finite field, characteristic p | `D : WeilConjectures.FiniteFieldDatum.{u}` supplies its finite field, algebraic closure, and prime `D.p`. |
| Prime ell different from p | `(l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)`. |
| Finite extension E/Q_ell and its integer ring | `(E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`; the ring is the recorded `Padic.coefficientExtensionIntegers l E`. |
| Arbitrary nonzero nonunit t | `(t : Padic.coefficientExtensionIntegers l E) (_ht : t ≠ 0) (_hunit : ¬ IsUnit t)`; it is not restricted to a uniformizer. |
| X,Y finite-type k-schemes | `X.Over`, `Y.Over` and `LocallyOfFiniteType` plus `QuasiCompact` on their structure morphisms to `Spec (.of D.k)`. |
| f a separated finite-type k-morphism | `(f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]`. |
| No separatedness hypothesis on Y | There is no `IsSeparated` assumption on either structure morphism; only f is separated. |
| Fixed compactification | `(c : Compactification f)` uses its actual open immersion `c.i`, proper map `c.g`, ambient `c.Z`, and factorization. |
| A_n=O/(t^n), n positive | Existing `strictEtaleLevel W O t n` has ring `O ⧸ (Ideal.span {t})^(n+1)`; n in Lean denotes the paper's n+1, so every positive index occurs. |
| Strict systems and ordinary unbounded derived categories | Existing `strictEtaleCoefficientSystem` and `DerivedCategory`, without a normalization or constructibility restriction. |
| F_A=Rp_*j_! and F_n | `(S : StrictEtaleCompactSupport O t c)`; `S.functor` and `S.levelFunctor n` are the actual composites of the open extension and proper derived direct image. |
| Canonical evaluation and left-extension comparisons from Brown | `S.evaluation n` and `(B : StrictEtaleBrownConstruction O t c S).leftExtension n`. Brown's `projection_recorded_q` fixes its quotient projection by the recorded compact-support coefficient map. B is the existing presentation of those canonical comparisons, provided for every S by the dependency theorem, not an assumption about the new chosen G or g. |
| Fixed system adjunction | Arbitrary `(G : D(system Y) ⥤ D(system X))` and `(adj : S.functor ⊣ G)`; G is not required to equal B.right. |
| Fixed finite adjunctions and units/counits | Arbitrary `g n` and `(adjN : ∀ n, S.levelFunctor n ⊣ g n)`, with `(adjN n).unit` and `.counit`. The canonical realization `B.levelComparison n` identifies this fixed-ring-sheaf encoding with the recorded ordinary etale module-sheaf compact support. |

Clause-by-clause correspondence (fields of the conclusion record):

| Node conclusion | Lean rendering |
| --- | --- |
| Natural isomorphism e_n G_A ≅ g_n e_n | `theta : ∀ n, G ⋙ S.PX.evaluation n ≅ S.PY.evaluation n ⋙ g n`. This is a derived natural isomorphism, not merely a collection of cohomology isomorphisms. |
| Exact six-bijection Hom chain | `strictEtaleEvaluationHomChain` is the composite of inverse X insertion adjunction, inverse system adjunction, `Iso.homCongr ((B.leftExtension n).app P) (Iso.refl M)`, Y insertion adjunction, and finite adjunction. The `Iso.homCongr` precomposes by the inverse left-extension comparison, in the required direction. `hom_chain` equates this equivalence applied to h with postcomposition by theta. |
| Uniquely specified by the Hom chain | `unique` says every other family of natural isomorphisms with precisely this Hom-chain equation equals `theta`. All test objects P and M are unbounded. |
| Evaluated counit | `counit` states `F_n(theta_M);epsilon_n = c_n^{-1};e_n(epsilon_M)` on the actual maps. |
| Evaluated unit, using c_n | `unit` states `e_n(eta_K);theta_(F_A K);g_n(c_n,K) = eta_n,e_nK`. |
| T^W_(m,n) is derived coefficient tensor | Exactly `(S.PX.scalar h).derived` and `(S.PY.scalar h).derived`, for `h : n ≤ m`, with their existing derived scalar adjunctions. |
| q coefficient projection and b its specified transpose | `strictEtaleBrownQuotientMate B adjN h` is `mateEquiv (adjN m) (adjN n)` of `(B.projection h).hom`, i.e. q inverse. `coefficient_transpose` explicitly states its finite Hom transpose is `q^{-1};T_Y(epsilon_m)`. No arbitrary coefficient map is substituted. |
| Actual transition of G_A M under theta | `transition` equates `tr_X(G M);theta_n` with `T_X(theta_m);b_(M_m);g_n(tr_Y M)`. The actual `tr_W` is the inverse Hom image of `(P.transition h).app M` under `(P.scalar h).derivedAdj`. The helper `strictEtaleBrownRightSystemTransition` is exactly the last two arrows. |
| Three-index compatibility and identities | `coefficient_composition` gives the b cocycle with both canonical `derivedAssoc` maps; `coefficient_identity` uses `derivedUnit`. `transition_composition` states `T_(m,n)(h_(r,m));h_(m,n) = assoc_X;h_(r,n)` for the actual identified transition words. `transition_identity` is the canonical tensor unit at repeated indices. |
| N ≥ 0, same N for every finite level and every b | `lower_bound : ∀ N : ℕ, (∀ n b P, P.IsLE b → (F_n P).IsLE (b + (N : ℤ))) → ...`. |
| G_A(D≥a) ⊆ D≥a−N for every integer a | The same field concludes `∀ a M, M.IsGE a → (G.obj M).IsGE (a - (N : ℤ))`. The cast and subtraction preserve the stated sign and constant. |

Recorded dependencies used/read:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` (full fields and instances read).
- `def-weil-scheme-morphism-properties` is a convention node; its real finite-type and separated predicates are the existing `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, and `Scheme.Over` interfaces. No convention was redefined.
- `WeilConjectures.Compactification.RefinementCategory` and its `Defs` import: `AlgebraicGeometry.Compactification`, `Compactification.Refinement`; full signatures and docstrings read.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: `Padic.finite_coefficientExtensionRing`; its dependency `CoefficientExtension` gives the actual integer ring, not a newly chosen coefficient ring. The theorem at arbitrary t uses the Brown dependency's arbitrary-parameter quotient interface rather than specializing t to its uniformizer.
- `Sheaf.Paper.CoefficientSystemDerivedComparison`: `SheafOfModules.coefficientSystemDerivedComparison`, its full signature, the `CoefficientEvaluationDerivedPackage` fields, and the strict category were read. These are used through `StrictEtaleEvaluation` and S's components.
- `Sheaf.CategoryTheory.SystemLevelLeftExtension`: `SheafOfModules.systemLevelLeftExtensionTheory`, including exact evaluations and the derived tensor/left-extension adjunctions. The constant-quotient package reused by Brown is `CoefficientEvaluationDerivedPackage`; no second strict-system category is introduced.
- `Sheaf.Paper.EtaleSystemBrownConstruction`: `StrictEtaleBrownConstruction`, `StrictEtaleBrownComponents`, `etaleSystemBrownConstruction`; full structure and theorem read. In particular, `leftExtension_below`, `projection_recorded_q`, and the exact `bounds` field were checked.
- `Sheaf.Paper.EtaleSystemCoefficientProjection`: `AlgebraicGeometry.Etale.SystemProjection.etaleSystemCoefficientProjection`; its canonical single coefficient map and mate normalization are realized by B's `projection_recorded_q` and the existing `Etale.compactScalarMap`. The theorem signature and the projection data definitions were read.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`: `AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification`; full actual source signature and docstring read. Here the finite-level adjunctions are fixed inputs, so no new adjoint is selected from its existence theorem.
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`: `DerivedCategory.TStructure.t`, `IsLE`, `IsGE`; the published cohomological bounds are reused unchanged.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`: `SheafOfModules.sheafRingDerivedCoefficientAdjunction`; full signature/docstring read, including its K-flat representative normalization. The evaluated strict system package supplies this normalized scalar adjunction directly. It does not require quotient flatness.
- Proof plan also reuses `CategoryTheory.Yoneda.fullyFaithful`, `CategoryTheory.mateEquiv`, `CategoryTheory.mateEquiv_vcomp`, `CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE`, and `CochainComplex.quasiIsoAt_ιTruncLE` from their recorded Mathlib matches, whose relevant source was opened.

The module's public imports are the Brown dependency and the finite-field and coefficient-extension interfaces. Brown publicly exposes the strict-system, coefficient-projection, derived-comparison and left-extension interfaces needed in the signature. No dependency module was repaired. The remaining existence/proof declarations are not needed as extra inputs: the adjunctions are fixed in this node.

Edge cases checked before/following transcription:

- Level n=0 in Lean is O/(t), never the zero-exponent ring. Natural-number indices include all positive paper levels.
- h reflexive, r=m and m=n are allowed. Derived tensor identities use `derivedUnit`, not a definitional equality of tensor with identity; the two associators occur explicitly in the composition equation.
- Quotient A_m→A_n may be nonflat. Actual transitions are transposed through the *derived* scalar adjunction; no ordinary tensor or flatness assumption occurs.
- N=0 gives exactly a, with no off-by-one loss. Arbitrary negative a and b are included. In the proof, the test truncation is at a−N−1, whose image lies at most a−1.
- Zero objects and empty X/Y need no exclusion. For arbitrary unbounded M the evaluation and transition clauses hold before any amplitude implication is used.
- Y may be nonseparated over k. No Noetherian, smoothness, constructibility or normalization hypothesis was silently added; the requisite Noetherian facts for compact support follow from the original finite-type geometry, as in Brown.
- O is allowed in Type (u+1), the etale-site objects in Type (u+1), morphisms in Type u, and ordinary derived localizations use the existing u+2 instance. No equality between site object and morphism universes was imposed.

Searches actually performed:

1. `msearch.py ... leanfinder "Evaluation of right adjoint on strict coefficient systems, adjunction mates and uniform lower cohomological bound"`: OK, 8 hits. These are generic truncation/factorization declarations such as `DerivedCategory.right_fac_of_isStrictlyLE`, not this system theorem.
2. `msearch.py ... loogle "CategoryTheory.conjugateEquiv, CategoryTheory.mateEquiv"`: OK, 4 hits, including `conjugateEquiv_mateEquiv_vcomp` and `iterated_mateEquiv_conjugateEquiv`. These are the reusable formal mate machinery, not an existing ordinary strict-etale evaluation/bound theorem.
3. `msearch.py ... grep "conjugateEquiv|mateEquiv" CategoryTheory/Adjunction`: OK, 12 hits; opened `Mathlib/CategoryTheory/Adjunction/Mates.lean` and used its `mateEquiv`.
4. `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and `evaluation.*[Rr]ight|[Rr]ight.*evaluation`: no declaration of this full statement. The downstream `FreeInsertionCompactSupportCoherence` cites this node and has a specialized insertion/evaluation theorem, but requires a uniformizer, separated X,Y and an already-constructed exceptional-adjoint package, omits this uniform-bound implication, and depends mathematically on the present node. It is not imported or restated. Its scalar-adjoint-transition helper is not copied: the present record uses the existing scalar Hom equivalence inline.
5. Read the node records for every statement dependency and the full canonical Brown and strict-evaluation interfaces; searched the current library before choosing all new names. There is no existing full match and no new independent notion requiring a definition node.

Validation: `scompile.py Q36 lem-pur-etale-system-evaluation-bound <module>` succeeded, compiling the Brown overlay and this module in sandbox and library modes. No errors or unexpected warnings. No `#check` probes remain. Only the main theorem is postponed. There are no disputed statements or source corrections.

## Second reading by Q36

This is a second pass by the same dispatcher-started worker; the brief forbids
starting another agent. The maintainer's independent review remains independent
of this report.

I reopened the node and checked the five groups of clauses against the record.
The Hom-chain direction is correct: `Iso.homCongr` precomposes with the inverse
of `F_A L_X ≅ L_Y F_n`. The finite Hom transpose used in
`coefficient_transpose` has domain `F_n(T_X(g_m M))` and target `T_Y M`, so
`B.projection.hom` is precisely q inverse, not q. The unit equation includes
`g_n(c_n)` after theta and the evaluated system unit. The transition equation
begins with the adjoint of the actual derived strict transition, so it makes a
claim about maps, not just evaluated objects. Both tensor associators in the
b-cocycle have the directions required to compare the direct and pasted maps.
The right-system composition uses one associator on its actual common source.
The bound is conditional, universally quantifies every b and n, and concludes
a−N with exactly that same N. Neither X nor Y is assumed separated over k.
No mismatch or additional change was needed after the clean compile.

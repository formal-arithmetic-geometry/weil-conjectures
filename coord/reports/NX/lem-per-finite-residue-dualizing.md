## Worker report

This repairs H13/H4 on immutable head ca455f296d6d using the reviewer's second
permitted route: leave N6's constructibility dependency record unchanged and own
the fixed-coefficient interface in this delivery. The item now declares
`finiteResidueProConstructibleSheaf`, a transparent alias to the published
`Scheme.IsConstructibleProEtaleFixedModuleSheaf`. Its bounded-constructibility
helper uses that alias. The full mathematical condition is definitionally the
same, and the theorem signature and assertion fields are unchanged. The new
alias is listed in this item's `lean.declarations` with a source docstring.
The dependency node is restored byte-for-byte from the current server record,
including N6's module, primary declaration, signature, declarations and note;
it contributes no dependency-record change to the delivery.

`Sheaf.Paper.FiniteResidueDualizing` states `AlgebraicGeometry.Etale.finite_residue_dualizing`. Its only postponed proof is the whole named theorem, with all eight DAG proof steps in its docstring. All helper definitions contain real data. The following matches every hypothesis and clause of the node:

- The base is any `k : Type u` with `[Field k]`. `ell : ℕ`, `hℓ : Nat.Prime ell`, and `hℓk : IsUnit (ell : k)` impose exactly a prime invertible in the base. `A : Type (u + 1)`, `[Field A]`, `[Finite A]`, and `[CharP A ell]` specify the finite residue-field coefficients. No characteristic, perfectness, separable closedness, or cohomological-dimension restriction is imposed on k.
- `a : T ⟶ Spec (.of k)` with `[IsSeparated a]`, `[LocallyOfFiniteType a]`, and `[QuasiCompact a]` is the separated finite-type structure map. The genuine Nagata compactification supplies the existing compact-support and exceptional functors; no extra compactification is assumed.
- `finiteResidueLowerShriek`, `finiteResidueExceptional`, and `finiteResidueOmega` specialize the existing ordinary etale `rightDerivedLowerShriek`, `rightDerivedUpperShriek`, and `dualizingComplex`. In particular Omega is precisely the exceptional image of the coefficient unit, not an arbitrary dualizing candidate. `adjunction` supplies the stated adjunction. `omega_bounded` uses the recorded etale bounded-constructibility predicate. `hom_preserves` states preservation of that predicate by the actual etale derived internal Hom into Omega.
- `evaluation_pairing` is `Etale.AmbientDualityPairing` at this Omega, and `biduality` is `IsIso` of its specified `bidualityMap` for every bounded constructible P. The pairing's defining equations identify evaluation as the adjunct of the identity and biduality as its transpose, including naturality, shifts and triangles.
- The dimension function is the real construction `finiteResidueTranscendenceDegree a t`, namely `Algebra.trdeg` for the field map `Scheme.Hom.residueFieldMap a t`. The image residue field is canonically k. Following the review's explicit “drop or pin” instruction, the tautological `∀ t, ∃ δ, δ = trdeg` field is dropped. No pinning theorem is simulated by an existential equality. The normalization of the dualizing object is fixed by its definition as `a^! A_s`; the docstring records the potential-pinning argument for this object and the displayed dimension function.
- `finiteResidueProDerivedCategory` is the actual unbounded pro-etale derived category in the fixed-ModuleCat presentation. `finiteResidueProEtaleComparison` is exactly `(ProEtale.comparisonUpperStar (ModuleCat A) T).mapDerivedCategory`. This is the first, explicitly requested presentation from the return. The canonical coefficient realization of `def-weil-pbc-proetale-modules` identifies it with that node's constant-coefficient ring-module presentation.
- `hom_comparison` is `IsIso (ProEtale.siteComparisonEvaluationHom (ModuleCat A) T P Q)`, with BOTH P and Q required to be bounded constructible. Its imported construction is the transpose of pulled-back evaluation using the canonical derived tensor comparison. There is no arbitrary Hom functor, bare existence of an isomorphism, or assertion for unrestricted unbounded pairs. `def-sf-evaluation-hom-site-comparison` has been added to `stmt_deps` as the return expressly requests.
- `finiteResidueProOmega a A` is definitionally comparison inverse image of the actual etale Omega. No unused existential Omega remains.
- `finiteResidueProBoundedConstructible T A K` requires the existing intrinsic finite-stratification constructibility predicate on EVERY cohomology sheaf, and vanishing outside some finite interval `[a,b]`. `intrinsic_eq_origin` states that this condition holds if and only if K is isomorphic to comparison inverse image of a bounded constructible etale object. Thus the intrinsic category and its equality with the etale-origin category are explicitly asserted. The etale-origin predicate is written out using the specified functor and an actual etale bounded constructible witness, not substituted for the intrinsic predicate.
- `pro_omega_bounded` and `pro_hom_preserves` state bounded constructibility of the specified pro-etale Omega and preservation by the ACTUAL ambient `ProEtale.derivedHom` into it. `pro_evaluation_pairing` is `ProEtale.AmbientDualityPairing` at that Omega, and `pro_biduality` is `IsIso` of `ProEtale.AmbientDualityPairing.bidualityMap` for every intrinsically bounded constructible P. This quantifies over all intrinsic objects, rather than only objects with chosen etale representatives. Naturality and the evaluation normalization are part of the existing pairing predicate.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`: `Etale.DerivedCategory.isBoundedConstructible`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`: the recorded generic internal-Hom interface and its public ordinary-etale `Etale.derivedHom` specialization. `WeilConjectures.SixFunctors.Etale.Derived.Tensor` provides `Etale.derivedTensor` through the duality pairing import.
- `Sheaf.Paper.DualityPairing`: both `Etale.AmbientDualityPairing` and `ProEtale.AmbientDualityPairing`, and their canonical `bidualityMap` extractors. These choices extract uniquely normalized data.
- `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` and its imports: the compact-support functor, its exceptional right adjoint, and `dualizingComplex`; `WeilConjectures.Compactification.NagataCompactification`: the actual compactification.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`; `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and `Scheme.Hom.residueFieldMap`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`: the canonical fixed-coefficient comparison and coefficient realization vocabulary of the pro-etale module node. Its public comparison-site interface supplies the exact comparison inverse image used here.
- `Sheaf.AlgebraicGeometry.EvaluationHomSiteComparison`: `ProEtale.siteComparisonEvaluationHom`. Its published finite-coefficient imports provide `ProEtale.derivedHom`, definitionally the internal Hom of the ambient derived monoidal closed structure. The source of the latter module was read via `scompile.py --source WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom` because it was absent from the older local checkout.
- `Sheaf.Paper.ProEtaleFixedModuleConstructible`: the existing `Scheme.IsConstructibleProEtaleFixedModuleSheaf`, the same intrinsic constructibility in the fixed-ModuleCat presentation. The item owns a transparent fixed-coefficient alias, as explained below. The published module publicly imports the original intrinsic constant-ring module; neither predicate is copied.

Edge cases checked: zero P or Q is allowed; zero objects fit every suitable cohomological bound and the specified maps have the appropriate zero endpoints. The empty scheme is allowed by the intrinsic definition (one empty stratum meets its positive-stratum convention). A finite FIELD is nonzero by `Field`, exactly as the item requires; this item does not claim a zero coefficient ring. Bounded constructibility uses a degreewise predicate with no fixed common stratification, and a witness interval including single-degree and zero complexes. Non-equidimensional T retains the pointwise residue transcendence degree. The identity structure map fixes Omega from the coefficient unit through the identity adjunction. Imperfect fields and fields of infinite ell-cohomological dimension remain included. Comparison invertibility is restricted to bounded constructible pairs, so the old unbounded overstatement is removed.

Searches: the saved report recorded LeanFinder and LeanSearch searches for finite-coefficient duality, Loogle `dualizing`, and Mathlib/source/project grep, with no exact duplicate theorem. In this repair, `msearch.py ... leanfinder "finite coefficient etale dualizing complex canonical pro-etale biduality"` returned eight unrelated etale-algebra results; `msearch.py ... loogle "Algebra.trdeg"` returned the existing transcendence-degree definition and its lemmas; `msearch.py ... grep "finiteResidue|finite_residue_dualizing|IsConstructibleProEtaleFixedModuleSheaf"` returned seven unrelated Mathlib finite-residue-field references. `rg` of the read-only upstream `WeilConjectures` found no finiteResidue/finite_residue_dualizing match. Project `rg` found and led to reuse of `DualityPairing`, `EvaluationHomSiteComparison`, `ProEtaleFixedModuleConstructible` and its existing consumers (including `EtaleProEtaleExceptionalTransport`). No new independent notion or definition node is introduced.

No mathematical node statement was changed. No `STATEMENT-DISPUTED:` remains. The only item dependency addition is the review-requested, already recorded canonical evaluation-comparison node.

## Dependency modules

None. The sandbox copy of `def-weil-proetale-constructible-sheaf` equals the
current server node, including its complete `lean` record. The delivery leaves
N6's `Sheaf.Paper.ProEtaleConstructibleSheaf` /
`AlgebraicGeometry.Scheme.IsConstructibleProEtaleModuleSheaf` binding intact.
The published fixed-ModuleCat predicate remains unchanged in
`Sheaf.Paper.ProEtaleFixedModuleConstructible`.

The item-owned `AlgebraicGeometry.Etale.finiteResidueProConstructibleSheaf`
reuses that published fixed-ModuleCat predicate through an `abbrev`; it defines
no independent stratification or constructibility condition. The bounded
predicate uses the alias at each cohomology sheaf. This takes the reviewer's
explicit second route and keeps both shared encodings and their consumers
intact. It requires no public-import-aware change to the delivery validator.

## Second reading by NX

I reopened the node and repaired Lean file for a separate clause-by-clause self-check; no additional agent was started, as instructed. The old dry-run success was only mechanical and did not address H3/H5. The arbitrary H, unrestricted pair comparison, arbitrary existential biduality arrow, existential unused Omega, and tautological normalization field are all absent. Each replacement uses the canonical declaration specifically named by the return. Both comparison inputs carry etale bounded-constructibility hypotheses. The pro-etale biduality conclusion uses the pairing at the defined inverse-image Omega and covers every intrinsically bounded constructible pro-etale object. Intrinsic constructibility is degreewise on cohomology, with finite bounds, and `intrinsic_eq_origin` explicitly states the equivalence with the etale-origin condition. For the present H13/H4 repair, the dependency record is restored exactly to
the current N6 record. The fixed-coefficient interface is a transparent alias
owned and recorded by the item. Unfolding it recovers precisely the published
predicate used before this repair, so the bounded predicate and all assertion
clauses have the same mathematical content. No shared source declaration or
existing consumer changes. The etale clauses that the reviewer accepted remain unchanged. The source-based normalization convention is the actual a^! unit definition plus the real dimension-function definition, with the tautology removed as requested. The theorem docstring now gives the eight proof steps and names their DAG dependencies. Every definition has real data and only the final theorem is sorry.


## Maintenance handoff (2026-10-19)

The previous superset packet repeatedly failed `deliver2.py --no-push` because
`tools/stage2_delivery.py:check_existing` searches only the named module's
source, although the reviewer-requested primary declaration was publicly
imported. The existing-declaration export probe and item compilation passed.
This is a mismatch between the first suggested repair and the validator, not
a mathematical failure. The shared landing validator is protected from
maintenance edits, so the permitted second repair route above is used.

Maintenance validation: the complete isolated packet passed the prescribed
`deliver2.py NX lem-per-finite-residue-dualizing --no-push` (candidate b129300b22).
Only the item module, item JSON and report were staged; the dependency node was
absent from the delivery delta. A separate full-module equality probe passed
`tools/lean_file.sh` in 4.6 seconds with nice 19, two threads and a 60-second
limit: `rfl` proves the entire new bounded predicate equal to its original
body. The theorem signature and every assertion field remain verbatim.
No protected launcher, review or landing tool was edited.
The next worker must retain this route, run the prescribed no-push delivery
check, then deliver normally. Do not replace N6's dependency record with a
fixed-predicate-only or public-import-superset record. All earlier accepted
H3/H5 repairs and the added evaluation-comparison statement dependency remain.

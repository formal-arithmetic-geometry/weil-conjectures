## Worker report

Stage 2, Q125: `lem-sfb-normalized-dualizing-depth-detection`.

Files: `lean/Sheaf/Algebra/Homology/NormalizedDualizingDepthDetection.lean` and the item's node copy. The only changed DAG field is `lean`. The accepted stage-1 statement, dependencies and fourteen-step proof remain verbatim. There are no new nodes or dependency repairs. The single theorem has proof `sorry`, as required in stage 2. The helper `DerivedCategory.moduleDualCohomology` is a transparent abbreviation with actual data, naming exactly the expression E^i introduced by this item; it constructs no new duality functor.

I read Stacks `dualizing.tex`, Definition 0A7B, the opening normalization paragraph of section-dualizing-local, and Lemma 0A7U with its proof. This item asserts parts (1) and (3), not the additional support-dimension assertion (2) of Stacks. It excludes the zero module, whose depth is infinite. I read all eight statement-dependency nodes and their recorded declaration signatures/docstrings. The dependency module `OrdinaryModuleDerivedInternalHom` already supplies precisely the ordinary-module presentation required here; its abbreviation is the existing closed internal-Hom bifunctor, derived through K-injectives. Thus there is no second ringed-site or module RHom definition.

Hypothesis and object correspondence:

- A nonzero commutative Noetherian local ring is `(A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]`. Mathlib's `IsLocalRing` extends `Nontrivial`, so the nonzero condition is present without a redundant instance. The unique maximal ideal is `IsLocalRing.maximalIdeal A`; its quotient `A ⧸ IsLocalRing.maximalIdeal A` is the stated residue field, viewed as an A-module.
- K in D(A) is `K : DerivedCategory (ModuleCat.{u} A)`. The localization is the dependency's `DerivedCategory`, with the already supplied Grothendieck-module localization instance. There is no independent arbitrary derived category or monoidal structure hypothesis.
- A bounded injective representative is `hKinjective`: an integer-indexed module complex J, integers a,b outside of which its terms are zero, termwise `CategoryTheory.Injective`, and an actual derived isomorphism `Q.obj J ≅ K` under `Nonempty`. This is exactly finite injective dimension as stated inline in the node, not merely cohomological boundedness.
- Finite cohomology is `hKfinite`, with the recorded `Module.Finite A` in every integer degree.
- The canonical scalar-action isomorphism is `hKscalar : IsIso (MonoidalClosed.id K)`. The source of this map is the canonical derived tensor unit, representing A[0]. In `Closed.Basic`, `MonoidalClosed.id K` is `curry (ρ_ K).hom`, the transpose of the right unitor under the tensor-Hom adjunction. It sends the unit scalar to the identity endomorphism, exactly the homothety map of 0A7B. Replacing the source by its canonical A[0] presentation leaves IsIso equivalent; no arbitrary endomorphism or existence of an unspecified isomorphism substitutes for this condition.
- Normalization is `hKnormalized`, a derived isomorphism from the existing `ordinaryModuleDerivedInternalHom A` applied to κ[0],K to κ[0]. Each κ[0] uses `DerivedCategory.singleFunctor` in degree zero and the actual residue-field quotient. It is an isomorphism in D(A), with no replacement by degreewise identifications.
- The nonzero finite module is `(M : ModuleCat.{u} A) [Module.Finite A M] [Nontrivial M]`. The ring and its module objects are taken in a common ambient universe, which is arbitrary; any larger given module universe can be included by enlarging that ambient universe. No finite-dimensional, free, Cohen-Macaulay or regularity condition is added.
- E^i is `moduleDualCohomology A M K i`, definitionally the dependency's RHom followed by `DerivedCategory.homologyFunctor` in integer degree i. The source module is M[0], not a shifted object or an Ext group in only nonnegative degrees.
- Support dimension is Mathlib's `Module.supportDim A M`, defined as `Order.krullDim (Module.support A M)`. I read its definition and `Module.support`, which uses nontriviality of localization at each prime, so this is the same strict-prime-chain dimension as in the node. Its `WithBot ℕ∞` codomain includes empty and unbounded cases.

Conclusion correspondence:

1. For every natural d with `Module.supportDim A M = (d : WithBot ℕ∞)`, every integer i satisfying `i < -(d : ℤ) ∨ 0 < i` has `IsZero (moduleDualCohomology A M K i)`. Quantifying over d with this equality is precisely the node's conditional assertion when its nonempty support dimension is finite. It does not assume finite support dimension globally or drop the positive-degree vanishing case. `IsZero` is applied to an object of ModuleCat, not to a bare type.
2. There exists a natural n with `IsLocalRing.depth (R := A) M = (n : ℕ∞)`, nonzero E^(-n), and zero E^(-t) for every natural t<n. The existence of a natural witness states finiteness of depth; its nonvanishing and the quantified earlier vanishing state exactly that n is the least nonnegative integer with nonvanishing dual cohomology. Natural t encodes the integer condition t≥0. These are the two explicit 'in particular' consequences too; no converse or extra support assertion is added.

The theorem docstring contains all fourteen accepted proof steps, with every cited node, as the stage-3 plan. Every recorded proof-dependency module is imported normally; statement-dependency modules are public imports. The helper and theorem each have the source and blueprint docstring. There are no file-local notations/instances, hidden `let` binders, auto-implicit variables, new axioms, or proofs besides the mandated `sorry`.

Dependency declarations used for the statement:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`.
- `def-sp-injective-resolutions`: `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, `CategoryTheory.Injective`.
- `def-pur-derived-internal-hom`: `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`, `CategoryTheory.ordinaryModuleDerivedInternalHom`.
- `def-weil-finitely-generated-module`: `Mathlib.RingTheory.Finiteness.Defs`, `Module.Finite`.
- `def-weil-pbc-localization-at-prime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`.
- `def-weil-pbc-depth`: `WeilConjectures.RingTheory.Depth`, `Ideal.depth`.

Edge cases checked: over a field with K=A[0] every nonzero finite module has support dimension/depth zero and E^0 nonzero, with all other degrees zero. Over a DVR with normalized K=A[1], M=A gives degree -1 and depth one, while M=κ gives degree zero and depth zero; this checks the sign of both casts. For A=k[ε]/(ε²) and K=A[0], M=κ is the depth-zero case. M=A⊕κ over a DVR has depth zero, consistent with the least-degree statement even though E^-1 may also be nonzero. The zero module is excluded exactly as in the node. Neither conclusion asserts E^-d is nonzero for every module. The degree-bound formulation keeps its conditional finite-dimension hypothesis. No source correction was needed.

Searches for an existing exact statement (all through msearch.py, with the actual responses read):

- leanfinder: `Normalized dualizing complex cohomology bounds detect depth of a finite module over a Noetherian local ring`. Eight hits, all about Module.supportDim and quotients by regular elements; no dualizing/depth theorem.
- loogle: `Module.supportDim, IsLocalRing.depth`. Zero hits.
- grep: `dualizing|semidualizing|normalizedDual`. Ten incidental prose hits (ToDual, categorical dualization, etc.); none is an algebraic dualizing theorem.
- leansearch: `Cohomology of derived Hom into a normalized dualizing complex detects depth`. Eight Hom-complex/cohomology-class and ordinary Ext hits, none the requested normalized-dualizing assertion.
- Project source searches: the item tag and normalized-dualizing/depth variants in both WeilConjectures and Sheaf; no exact declaration. The existing coherent-RHom, semidualizing-conservativity and complete-local-duality statements have different conclusions. The new helper and theorem names also have no existing source occurrence. Search logs remain in the prescribed sandboxes.

Validation: the first server check exposed a nonexistent Mathlib import, which was removed. The next check elaborated both declarations and reported only an overlapping Nontrivial/IsLocalRing instance; the redundant Nontrivial binder was removed because IsLocalRing already includes it. The final prescribed dry run compiles the resulting module and checks the node/packet.

## Review by Q125

This is the author's self-check, with the source, node and Lean open. I checked the four inline dualizing conditions separately: termwise injectivity is retained rather than inferred from cohomology; homothety is the canonical enriched identity rather than an arbitrary map; normalization uses the module quotient residue field and a derived isomorphism. I checked that the cohomological sign convention sends depth n to degree -n, and that a natural witness for the extended-natural depth states finite depth, rather than silently converting infinity with toNat. I checked the conditional degree bound using supportDim's actual chain definition. The accepted source proof is retained in the docstring, including dimension induction before depth induction; no clause is replaced by a newly postulated helper. The two compiler diagnostics were corrected as described above. No statement change, new node, or independent second reading is claimed.

## Second reading by Q125

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

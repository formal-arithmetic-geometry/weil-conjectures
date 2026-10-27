## Worker report

The module `Sheaf.Algebra.Homology.FiniteMapDualizingTransfer` states
`DerivedCategory.finite_map_dualizing_transfer`, with its whole proof `sorry`.
The proof docstring records all five steps of the node. The only helper,
`DerivedCategory.finiteMapDualizingComplex`, constructs the particular B-object
RHom_A(B,L); its data contain no sorry and no choice of an arbitrary B-action.
No mathematical statement correction, dependency module, or new DAG node is needed.
This packet repairs the return on immutable head `2011bef2e601`; see the repair
account and second reading below.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- A and B are commutative Noetherian rings: `{A B : Type u}` with `[CommRing A]`,
  `[CommRing B]`, `[IsNoetherianRing A]`, `[IsNoetherianRing B]`.
- The specified homomorphism is `(f : A →+* B)`. Finiteness as an A-module is
  `hfinite : Module.Finite A ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))`.
  This uses precisely the A-action through f; no separate algebra structure,
  injectivity, surjectivity, flatness, or nonzero-ring hypothesis is imposed.
- D(A) and D(B) on the one-object ringed sites are
  `DerivedCategory (RingSiteModules A)` and `DerivedCategory (RingSiteModules B)`.
  The `HasDerivedCategory.{u}` binders are the existing small Hom size convention.
  The one-object site and its arrows have universe u, with module carriers in u;
  no equality between originally independent site universes is being imposed.
- L is `(L : DerivedCategory (RingSiteModules A))`.
- Finite cohomology in every degree is `hL : ∀ i : ℤ, Module.Finite A (...)`,
  evaluating `homologyFunctor` at the unique site object `op ⟨PUnit.unit⟩`.
  There is no boundedness assumption on this cohomology in addition to hI.
- A bounded injective representative is hI: an existential complex I, integers
  a,b with `IsZero (I.X q)` outside [a,b], `∀ q, Injective (I.X q)`, and
  `Nonempty (Q.obj I ≅ L)`. These are actual term bounds, not cohomology bounds.
- The scalar-action hypothesis is `hscalar : IsIso (...)`, where the arrow is
  `(SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf A) L).homEquiv
  _ _ (λ_ L).hom`. The adjunction is normalized by the ordinary signed evaluation;
  transposing the unitor sends a scalar a to multiplication by a. Its source is
  the existing derived tensor unit, canonically A[0]. Thus this asserts the
  specified scalar-action map is invertible, not just existence of some iso.
- Omega_B is the actual helper `finiteMapDualizingComplex f L`. It applies the
  existing K-injective replacement to `Q.objPreimage L`, evaluates at the point,
  applies `(ModuleCat.coextendScalars f).mapHomologicalComplex (.up ℤ)` and the existing constant-module
  embedding, then localizes. The unique-object evaluation and constant embedding
  are inverse exact equivalences (the unit uses the unique object's identity).
  In particular evaluation carries K-injectives to K-injectives. The resulting
  complex is Hom_A(B,I), whose B-action is the existing Mathlib coextension action
  `(b • h)(x) = h(x*b)`. Since B is commutative, this is exactly h(bx) in the node.
  Its underlying A-object is the recorded K-injective derived Hom of B[0] and L.
- Conclusion 1 is `∀ i : ℤ, Module.Finite B (...)` for the cohomology of that
  exact helper, evaluated at the unique object of the B-site.
- Conclusion 2 existentially supplies a complex J on the B-site, zero outside a
  finite term interval, injective in every degree, with
  `Nonempty (Q.obj J ≅ finiteMapDualizingComplex f L)`.
- Conclusion 3 uses the identical evaluation-normalized transpose over B, at
  `finiteMapDualizingComplex f L`, and asserts `IsIso` of that actual arrow.

Definitions and dependency declarations reused:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, `DerivedCategory.Q`, `Q.objPreimage`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`:
  `DerivedCategory.homologyFunctor`.
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `CategoryTheory.Injective`;
  its `Adjunction.map_injective` is the proof's injective-transfer input.
  The other recorded declaration `InjectiveResolution` was read in
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`; this statement needs
  only the general Injective notion, not an object resolution concentrated at 0.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`. Its actual specialization is
  `SignedRingedHom.homFunctor`, not a newly defined derived Hom.
- `Sheaf.Algebra.Homology.RingHomExtensionDefs`: `CategoryTheory.RingSiteModules`,
  built from `CochainComplex.onePointRingSheaf` in the upstream
  `WeilConjectures.Algebra.Homology.KFlatTensorQuasiIso` module.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses` publicly reexports
  the existing `CategoryTheory.SignedRingedHom.adjunction` and its derived tensor.
  The original `RingedInternalHomSignedCalculus` definition was read directly.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`:
  `ModuleCat.coextendScalars`, applied degreewise by `mapHomologicalComplex`,
  supplies the helper's actual Hom modules, precomposition action, and differential.
  `ModuleCat.restrictCoextendScalarsAdj` and
  `Mathlib.CategoryTheory.Adjunction.Additive` supply its additivity.
- `Sheaf.Algebra.Homology.DerivedCoinductionAdjunction` is now a plain proof import:
  `ModuleCat.derivedCoinductionAdjunction_spec` supplies the proof's canonical
  comparison, evaluation-at-one counit, and conservative restriction. It is not
  used to define the transferred object and is not a statement dependency.
- `Sheaf.Paper.RingComplexGodementConstruction`:
  `AlgebraicGeometry.ringComplexConstant` and `ringComplexConstant_additive`.
  The latter is supplied explicitly in the helper's definition for elaboration.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`:
  `CochainComplex.kInjectiveResolutionFunctor`, the actual functorial factorization,
  with the existing ringed-site Grothendieck instances. Its universe is explicitly u.
- All already-stated proof-dependency modules are imported: the coherent RHom
  finiteness theorem, finite-injective evaluation, the ordinary enriched
  coinduction adjunction, the Noetherian pseudo-coherence criterion, and Mathlib
  K-injectivity of bounded-below injective complexes. Dependencies already used
  publicly for the constructions are public imports; the remaining proof imports
  are plain imports. No proof import closes a cycle.

The three added stmt_deps are already-landed nodes: the shared ring-site definitions,
ringed internal Hom calculus, and the existing constant-module embedding's owning
Godement-construction node. Ordinary coinduction is used directly from Mathlib.
`lem-trf-derived-coinduction-adjunction` remains in proof_deps only; the original
five statement dependencies are retained. The statement, proof, proof_deps and all
other node fields outside lean and stmt_deps are unchanged.

Edge cases checked before drafting: identity A→A recovers L; A→0 gives the zero
complex over the zero ring and an invertible map between zero objects; A=0 forces
B=0 and is also included. Finite field extensions give the usual coinduced dual
module. For a DVR and its residue field, the transferred object has the Ext shift;
there is no false concentration-at-zero or flatness assumption. L=0 over a nonzero
ring fails the scalar-action hypothesis as required. Outside-interval IsZero
permits the zero complex and does not require a nonempty support interval.

Searches for an existing statement or construction:

- `msearch.py ... leanfinder "finite ring map transfers a dualizing complex by
  derived Hom"`: eight hits including `IsBaseChange.dual`, `Module.dual_finite`,
  and exact derived functor infrastructure, but no dualizing transfer theorem.
- `msearch.py ... loogle "ModuleCat.coextendScalars"`: twelve hits, including the
  actual `ModuleCat.coextendScalars`, its linear-equivalence presentation,
  `restrictCoextendScalarsAdj`, and the evaluation-at-one counit. Reused these
  directly from Mathlib after the return, rather than through a theorem-owned helper.
- `msearch.py ... grep "dualizing|semidualizing" Algebra`: one unrelated path-object
  docstring in `Mathlib/Algebra/Homology/HomotopyFiber.lean`; no matching theorem.
- `msearch.py ... leansearch "For a finite algebra B over a Noetherian ring A and
  a dualizing complex L, derived Hom from B to L is a dualizing complex over B"`:
  eight ordinary finite-map and dual-base-change hits, no derived transfer theorem.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for dualizing, semidualizing,
  coinduction, point equivalences, and constant-module embeddings found the reused
  APIs above and the existing complete-local-duality consumer, but no transfer.
  Searching upstream for the exact item id and the proposed declaration names
  yielded no declaration; `dag/lean_names_upstream.json` likewise has no match.
- The site's evaluation/constant equivalence already appears as private helpers
  in `NilpotentDerivedUpperBound`; no copy of it or of its definitions is added.
  The public constant-module embedding was located and reused instead.
- `scompile.py --source Sheaf.Paper.RingComplexGodementConstruction` confirmed its
  live source and existing additivity declaration.

## Repair of immutable head 2011bef2e601

H2/H4: I read `coinductionComplexFunctor` and its body in the live
`DerivedCoinductionAdjunction.lean`, and `coextendScalars`, `CoextendScalars.hasSMul`,
`CoextendScalars.smul_apply`, and `CoextendScalars.map_apply` in Mathlib's
`ChangeOfRings.lean` (lines 455–555). The helper was only the degreewise application
of Mathlib's existing functor, with additivity supplied by the ordinary adjunction.
I now use that Mathlib expression directly inside `finiteMapDualizingComplex`, with
the identical additive instance. I removed `lem-trf-derived-coinduction-adjunction`
from stmt_deps and changed its module import from public to plain. It stays a
proof dependency for steps 2 and 5. This is the return's inline-Mathlib repair;
no additional ownership record or duplicate coinduction definition is needed.

The accepted `lem-weil-pbc-ringed-internal-hom-exact-restriction` dependency is
retained. I reread `SignedRingedHom.adjunction`: it uses the `.choose` of
`normalizedAdjunction_existsUnique`, whose representative normalization fixes the
closed structure. This is substantive statement data, unlike the ordinary
coinduction wrapper, and the return explicitly accepts it.

H11: I replaced the former generic second-reading paragraph with the actual
binder-by-binder and conclusion-by-conclusion reading below. No other agent was
launched. No theorem signature, mathematical hypothesis, conclusion, or proof
plan changed. Compared with the current shared node, the only changed fields
are lean and stmt_deps; the first saved-packet dry run rebased the packet through
the delivery wrapper and passed at `6499de21930` before these repairs.

## Second reading by Q40

I reopened the node, the full delivered Lean file, and Stacks `dualizing.tex`
`lemma-dualizing-finite` (Tag 0AX0, lines 2808ff.), `definition-dualizing`
(Tag 0A7B, lines 2557ff.), and `more-algebra.tex`
`definition-injective-dimension` (Tag 0A5S, lines 17510ff.). This is my second
reading; the maintainer will independently review the delivered head.

1. The node's commutative Noetherian rings are `{A B : Type u}` with
   `[CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]`.
   `(f : A →+* B)` is the specified map, and `hfinite` is `Module.Finite A`
   on B restricted along that exact map. This matches “finite ring map” in 0AX0;
   it assumes neither flatness nor injectivity nor surjectivity.
2. The node explicitly asks for the one-object ringed-site presentations of
   D(A) and D(B). The two `HasDerivedCategory.{u} (RingSiteModules ...)` binders
   and `L : DerivedCategory (RingSiteModules A)` use those shared presentations,
   not a different derived category or an arbitrary supplied Hom operation.
   Each site has its unique object and identity morphism in universe u. All
   mathematical rings and modules of this size are included; there is no
   nontriviality or finite-dimensionality restriction.
3. “Finitely generated cohomology in every degree” is precisely `hL : ∀ i : ℤ,
   Module.Finite A (...)`, with `homologyFunctor` evaluated at the unique object
   `op ⟨PUnit.unit⟩`. The quantifier ranges over every integer. The evaluation
   recovers the underlying A-module, so no sheaf-coherence substitute is used.
4. “Isomorphic to a bounded complex of injective A-modules” is hI's existential
   complex I, term bounds `∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero (I.X q)`,
   termwise `∀ q, Injective (I.X q)`, and `Nonempty (Q.obj I ≅ L)`.
   These are term bounds as required by 0A5S, not just vanishing cohomology.
   No particular resolution, nonempty support, or bounds a ≤ b are required.
5. The node's specified scalar-action map is hscalar, the `IsIso` of
   `(SignedRingedHom.adjunction ... L).homEquiv _ _ (λ_ L).hom`.
   Transposing the left unitor under the normalized tensor–Hom adjunction
   sends a scalar a to multiplication by a on L. Its source is the tensor
   unit A[0]. Thus the hypothesis is the actual homothety map of 0A7B,
   rather than existence of an unrelated isomorphism A[0] ≅ RHom(L,L).
6. The node's Omega_B is `finiteMapDualizingComplex f L`. Reading its body:
   `Q.objPreimage L` supplies a representative, the existing functorial
   K-injective replacement supplies I, and evaluation at the unique object
   gives its A-module complex. Mathlib `coextendScalars f`, applied by
   `mapHomologicalComplex (.up ℤ)`, then gives Hom_A(B,I) degree by degree;
   its maps postcompose with the differential. The existing constant embedding
   returns this to the B-site, and Q localizes. Evaluation and the constant
   embedding are inverse exact equivalences on this one-object category,
   so the evaluated replacement is K-injective. This computes RHom_A(B,L).
   Mathlib's actual action is `(b • h)(x) = h(x*b)`, equal to h(b*x) by
   commutativity of B, exactly the action in the node. It is never chosen
   arbitrarily. The body now uses Mathlib directly; the theorem node removed
   from stmt_deps supplies no part of these definition data.
7. The first conclusion is `∀ i : ℤ, Module.Finite B (...)` on the evaluated
   homology of that exact Omega_B. It matches finite B-cohomology in every
   degree, without demanding finite projective terms or concentration at zero.
8. The second conclusion existentially supplies J with finite term bounds,
   injectivity in every degree, and `Nonempty (Q.obj J ≅
   finiteMapDualizingComplex f L)`. It is exactly 0A5S over B and the node's
   second clause, retaining arbitrary integer bounds and the zero-complex case.
9. The third conclusion is `IsIso` of the same normalized transpose of the
   left unitor, now at Omega_B over B. Its source is B[0], its target is
   RHom_B(Omega_B,Omega_B), and it is the scalar-action arrow. The final
   connective is the conjunction of exactly these three conclusions.
10. I retested the semantic edge cases. For f = id the coinduced object is L;
    for B = 0 it is the zero B-complex and homothety is an isomorphism of zero
    objects. A = 0 forces B = 0, which is allowed. L = 0 over a nonzero A
    fails hscalar, as it must. A DVR mapping to its residue field retains the
    Ext shift, since the helper uses a K-injective complex and is not ordinary
    Hom of cohomology. Finite field extensions have the usual dual module.
    None of these checks required changing the mathematical statement.

The reading found the reported ownership defect, repaired by inlining the
existing Mathlib functor and keeping the coinduction theorem only in the proof
plan. It found no missing hypothesis or clause and no statement fault.

## Validation

The retained packet first passed `deliver2.py --no-push` at `6499de21930`.
The revised Lean module passed scompile.py in sandbox mode (7.1 s) and library
mode (2.6 s), with no errors or warnings. Final dry-run and delivery results are
recorded by the wrapper.

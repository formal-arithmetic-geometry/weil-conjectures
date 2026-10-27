## Worker report

The module `Sheaf.Algebra.Homology.DerivedEvaluationResolvedModel` states
`DerivedCategory.derived_evaluation_resolved_model`, with its proof `sorry`.
It has no new definitions and no postponed helper theorem. The node statement,
proof and proof dependencies are unchanged. Five already landed ownership nodes
are added to statement dependencies for the concrete interfaces used below.

Source checked: `literature/stacks-project/more-algebra.tex`,
`lemma-evaluate-and-more` (0A60), `remark-sign-explanation` (0A61), and
`lemma-internal-hom-evaluate` (0A67). The tags table confirms these labels.
The component sign in 0A61 is the Koszul swap of the P and Hom(P,J) factors.
The theorem docstring carries all six DAG proof steps, including the counit
normalization for an arbitrary first Hom argument. In particular it never
requires the complex Hom(P,J) to be K-flat.

Hypotheses and clauses, checked against the unchanged node:

| Node | Lean |
| --- | --- |
| Commutative ring R | `(R : Type u) [CommRing R]` |
| D(R) on the one-object trivial-topology site | `DerivedCategory (RingSiteModules R)`, with the chosen small-Hom localization `[HasDerivedCategory.{u} (RingSiteModules R)]` |
| Arbitrary K,L,M | `(K L M : DerivedCategory (RingSiteModules R))` |
| Chosen complexes representing them | `(P J I : CochainComplex (RingSiteModules R) ℤ)` and arbitrary `(eP : Q.obj P ≅ K) (eJ : Q.obj J ≅ L) (eI : Q.obj I ≅ M)` |
| P K-flat | `hP : (HomologicalComplex.quasiIso (RingSiteModules R) (.up ℤ)).kFlat P`; the recorded dependency also publicly exposes this tensor-quasi-isomorphism formulation, equivalent to acyclic-test K-flatness |
| J and I K-injective | `[J.IsKInjective] [I.IsKInjective]`, Mathlib's homotopy-zero definition |
| Product Hom A=Hom(J,I), B=Hom(P,J), outer Hom(B,I) | The existing `CategoryTheory.homComplex.{u,u,u,u}` at `CochainComplex.onePointRingSheaf R`, written explicitly throughout |
| Direct-sum total tensor Tot(A tensor P) | The existing `coefficientTotalTensor.{u,u,u} ⊥ (CochainComplex.onePointRingSheaf R)` |
| E is a chain map | `∃ E : Tot(A tensor P) ⟶ Hom(B,I)` in the category of cochain complexes |
| Homogeneous h in A^a, x in P^b, f in B^c | The universally quantified `a b n c j i : ℤ`, degree equalities `a+b=n`, `b+c=j`, `j+a=i`, `c+n=i`, and actual section binders `h x f` |
| E(h tensor x)(f)=(-1)^(bc)h(f(x)) | The first conjunct uses `coefficientTensorGenerator`, all three `coefficientHomComponent` projections, identity-object slice evaluation, and `(b*c).negOnePow • ...` |
| Canonical Hom comparison for A | Existential iso `a`, with its `hom` prescribed as `ringedHomRepresentativeMap J I` followed by `H(eJ.inv,eI.hom)` |
| Canonical Hom comparison for B | Existential iso `b`, normalized by `ringedHomRepresentativeMap P J` followed by `H(eP.inv,eJ.hom)` |
| Canonical outer Hom comparison | Existential iso `c`, normalized by `ringedHomRepresentativeMap B I` followed by `H(id,eI.hom)` |
| Canonical one-K-flat tensor comparison | Iso `t : Q Tot(A tensor P) ≅ QA tensor QP`, with `t.inv = μ Q A P ≫ Q.map totalTensorNativeIso.inv`; the latter is the actual identification of the two existing total tensor presentations |
| lambda_P has the stated endpoint | Iso `lambda : Q Tot(A tensor P) ≅ H(L,M) tensor K` |
| lambda_P is the canonical composite | `lambda.hom = t.hom ≫ (a.hom ⊗ₘ eP.hom)` |
| rho_P has the stated endpoint | Iso `rho : Q Hom(B,I) ≅ H(H(K,L),M)` |
| rho_P is the canonical contravariant transport | `rho.hom = c.hom ≫ H.map (b.inv.op, id M)` |
| e is exactly the iterated closed evaluation transpose | The final RHS applies the existing normalized `SignedRingedHom.adjunction` Hom equivalence to the associator, the single braiding of K past H(K,L), then the two specified counits. This is the expanded defining term of `closedIteratedEvaluation`, with the adjunction oriented as `tensorRight ⊣ H` |
| rho_P Q(E)=e lambda_P | `Q.map E ≫ rho.hom = lambda.hom ≫ ...` (Lean's composition is left to right) |
| No boundedness, degreewise flatness or finite-generation condition | No such binder occurs; every degree variable is an integer |

The three intermediate Hom isomorphisms and tensor isomorphism specify the
canonical normalizations, rather than imposing extra hypotheses. They are
existential conclusions, and their hom/inv equations fix their data uniquely.
Thus the conclusions include actual derived isomorphisms, not just cohomology
isomorphisms. Arbitrary representatives, including arbitrary automorphisms of
those representatives, are retained in eP, eJ and eI.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`: the recorded
  dependency publicly retains `CategoryTheory.derivedInternalHomOfUniverses`
  and its localization construction. On this ringed-site presentation,
  `SignedRingedHom.homFunctor` is precisely its `{u,u,u,u}` specialization.
  The ordinary ModuleCat abbreviation is not used as a competing encoding.
- `WeilConjectures.Algebra.Homology.HomComplex`: `CategoryTheory.homComplex`,
  the shared product-total Hom with differential d_M f-(-1)^n f d_L.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor`;
  `coefficientTotalTensor` is its existing curried-sheaf-tensor presentation.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`: the recorded
  independent-coefficient predicates and public `MorphismProperty.kFlat`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`.
- `Sheaf.CategoryTheory.ClosedEvaluationNaturality`:
  `closedRightEvaluation`, `closedIteratedEvaluationUncurried`,
  `closedIteratedEvaluation`, `closed_evaluation_naturality`; the final term
  spells out the defining transpose without introducing another map definition.
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`:
  `ringedDerived_closed_symmetric_monoidal` and its representative coherence.
- `Sheaf.Algebra.Homology.RingHomExtensionDefs`: `RingSiteModules` (owning node
  `def-pc-ring-hom-extension-shared-definitions`, added to stmt_deps).
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses` publicly reexports
  `RingedInternalHomSignedCalculus`: `SignedRingedHom.hom`, `homFunctor`,
  `adjunction`, `totalTensorNativeIso`, and the native derived monoidal and
  Koszul braiding instances (owning node
  `lem-weil-pbc-ringed-internal-hom-exact-restriction`, added to stmt_deps).
- `Sheaf.Algebra.Homology.RingedHomCompositionModel`:
  `ringedHomRepresentativeMap` (owning definition node
  `def-trf-ringed-hom-representative-comparison`, added to stmt_deps).
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`:
  `coefficientHomComponent` (owning node
  `def-coef-hom-representative-evaluation`, added to stmt_deps).
- `Sheaf.Paper.CoefficientRingedTensorHomModel`: `coefficientTotalTensor`,
  `coefficientTensorGenerator` (owning node
  `def-coef-ringed-tensor-hom-model`, added to stmt_deps).

Plain proof imports retain the already stated proof dependencies:
`QuasiIsoHomComplexMap` (`quasiIso_homComplex_map`),
`RingedDerivedTensorNative` (localization tensorator/coherence),
`KFlatResolutionIndependentCoefficients`
(`exists_isKFlatResolutionIndependentCoefficients`), and
`OneKFlatChainTranspose` (`oneKFlatChainTranspose`). Other proof dependencies
are already public statement imports. No import of the downstream
`DerivedEvaluationCanonicalMap` is added.

Edge cases checked before and after writing:

- R the zero ring, or any of P,J,I the zero complex: tensor/Hom maps and
  normalization equations have the indicated endpoints and become zero maps
  or the unique isomorphisms of zero objects. No nontrivial-ring assumption.
- Negative degrees: b*c is an integer exponent, encoded with `Int.negOnePow`.
  No natural-degree restriction or truncation is used.
- Unbounded P,J,I: all Hom coordinates are product projections; each input
  generator lies in a direct-sum summand. No target coordinate sums over f.
- P K-flat without flat individual terms: hP only states K-flatness and is
  sufficient for mu at (A,P); no termwise flatness assumption.
- B=Hom(P,J) need not be K-flat. Neither mu at (Hom(B,I),B) nor a second
  K-flat representative is required by the statement.
- Identity representative isomorphisms recover the QP,QJ,QI formula. Arbitrary
  isomorphisms are transported contravariantly with inverses in the first
  Hom variable and covariantly in the second. The rho transport uses b.inv,
  whose opposite points from op QB to op H(K,L).
- E and Q(E) are not asserted invertible; only the representative comparisons
  lambda and rho are isomorphisms.

Searches (all before the statement was written):

1. `msearch.py ... leanfinder` query
   "For unbounded module complexes identify the signed double evaluation map
   on K-flat and K-injective representatives with derived closed evaluation
   transpose": eight hits, including generic HomologicalComplex evaluation
   and tensor existence declarations; no matching derived comparison.
2. `msearch.py ... loogle '"HomComplex", "tensor"'`: zero hits.
3. `msearch.py ... leansearch` query
   "Signed unbounded double Hom evaluation chain map on K-flat and K-injective
   derived representatives": eight generic complex-map/evaluation hits, no match.
4. `msearch.py ... grep 'evaluation|uncurry|curry'
   Algebra/Homology/DerivedCategory`: four hits in `SingleTriangle` and
   `FullyFaithful`; no resolved double evaluation statement.
5. `rg` on the shared `lean/WeilConjectures`, `lean/Sheaf` and
   `dag/lean_names_upstream.json` found no declaration with the item's id or
   the proposed name. Concept search found
   `DoubleEvaluationSignedDerivedModel.doubleEvaluation_signed_derived_model`:
   it supplies the QP,QJ,QI representative statement, with component sign
   identities as a separate theorem. Its signature does not bind arbitrary
   K,L,M and arbitrary eP,eJ,eI or expose lambda/rho with those endpoints.
   This delivery uses the same existing Hom/tensor/projection/comparison
   constructions and writes that explicit arbitrary-representative interface.
   It does not import that module, which imports the downstream canonical-map
   theorem. No duplicate Hom, total tensor, K-flat, or comparison definition.

Validation: the prescribed `scompile.py` first identified underconstrained Hom
universes and two product-morphism endpoint inferences. Explicit Hom universes
and explicit functor-map X/Y endpoints repaired them. Final server confirmation:
exit 0, 2.7 seconds, nice 19, two threads, default 60-second limit, no warnings.
The local compiler's full temporary filesystem was handled successfully by
scompile.py's automatic server fallback. No library file or launcher tool edited.
There is no statement correction and no disputed statement.

## Second reading by Q30

I reread the node, source and final module as a separate author check; this was
not a second agent (the dispatcher expressly prohibits starting agents).
Independent delivery review remains with the maintainer as specified in the brief.

The check matched every hypothesis and clause in the table above. In particular,
a transports J→L contravariantly by eJ.inv and I→M covariantly by eI.hom;
b uses eP.inv and eJ.hom; c leaves QB fixed and transports only I→M.
The inverse of t has orientation QA tensor QP→Q Tot(A tensor P).
Thus lambda points Q Tot(A tensor P)→H(L,M) tensor K, and rho points
Q Hom(B,I)→H(H(K,L),M). The final equality is Q(E) then rho, versus
lambda then the required transpose. Its uncurried composite has exactly one
swap, so the component coefficient is (-1)^(bc), with no extra evaluation sign.
All seven normalization/equality conjuncts are substantive, and each intermediate
isomorphism is a conclusion, not a new hypothesis. No mathematical mismatch was
found in this pass. The compiler-driven changes only made universes and product
morphism endpoints explicit; they did not change the statement.

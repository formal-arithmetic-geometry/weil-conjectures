## Worker report

Repaired the returned immutable head 2baa3170a3b4. The saved packet was first
inspected and dry-run as requested: it passed mechanical preflight at 7671c7c37a,
but still had the mathematical defects in the return. Those defects are repaired
in the retained module `Sheaf.SixFunctors.EtaleHomThickLocus`.

The node statement, statement dependencies, proof and proof dependencies are
unchanged. The item now imports the published `Etale.derivedHom` directly. The
returned adapter module and its dependency-node specialization are removed; the
record for `def-pur-derived-internal-hom` is restored to its original general
`CategoryTheory.derivedInternalHomOfUniverses` interface.

Hypothesis and clause correspondence:

- Scheme X: `(X : Scheme.{u})`. Commutative rings: the explicitly bound
  `{A B : Type (u + 1)} [CommRing A] [CommRing B]`. Coefficient homomorphism:
  `(φ : A →+* B)`. There are no flatness, boundedness, finiteness, or
  constructibility assumptions.
- Small étale site and ordinary unbounded categories:
  `DerivedCategoryModule A X` and `DerivedCategoryModule B X`, namely the
  existing derived categories of ModuleCat-valued sheaves on
  `X.smallEtaleTopology`. The scheme universe is u and the module/ring universe
  is u+1, as required by the published presentation.
- F is the existing `scalarExtension φ X`, the chosen left adjoint to actual
  derived restriction of scalars. H_A and H_B are the published `derivedHom`.
  `EtaleHomLeft` is H_A(-,M) followed by F. `EtaleHomRight` is F.op followed by
  H_B(-,FM). Both have source `(DerivedCategoryModule A X)ᵒᵖ`.
- Canonical tensor comparison: `IsEtaleHomTensorCanonical` requires the two
  naturality equations, for every derived morphism in either variable, and
  `EtaleHomTensorModelNormalization`. The normalization uses the fixed
  `etaleSheafExtendScalarsAdjunction.leftAdjointOplaxMonoidal`, derived counit
  maps `scalarExtensionRepresentative`, and the lax tensorators of Q. On
  flat-term K-flat P,Q it requires
  `F(Qμ_A) ≫ r(P⊗Q) ≫ Q(δ_E) = μ.inv ≫ (rP ⊗ₘ rQ) ≫ Qμ_B`.
  Here δ_E is the ordinary adjunction mate, inverse to coefficient multiplication
  `(x⊗b)⊗(y⊗c) ↦ (x⊗y)⊗bc`. Thus the equation fixes the actual comparison,
  rather than an arbitrary natural family of isomorphisms.
  `etaleHomTensorComparison_existsUnique` states existence AND uniqueness of
  the normalized family; `etaleHomTensorComparison` takes its unique witness.
  This is a choice from a theorem determining the object, not a Nonempty choice.
  Its source and full natural-language proof are in its docstring and in node
  proof step 1. No theorem outside this node's construction is introduced.
- Evaluation-defined v: `IsEtaleHomTranspose` uses that fixed canonical μ,
  without a free μ parameter. Its left side is μ followed by F of the
  A tensor-Hom counit. Its right side is the inverse B tensor-Hom adjunction
  image of `v.app (op K)`. The library uses K⊗H for evaluation; symmetry gives
  exactly the node's H⊗K convention, with its Koszul signs.
- Naturality in K: `v M` is a natural transformation. Naturality in M is the
  explicit square `IsEtaleHomNaturalInM`, for every g and K.
- Canonical shifts: `etaleHomScalarCommShift` is the canonical left-adjoint
  mate of the exact restriction shift. `EtaleHomShiftNormalization` fixes s_A
  and s_B by requiring evaluation after the explicit signed map
  `n.negOnePow • s_R` and the canonical cancellation of the two tensor shifts to
  equal evaluation at the shifted K. The factor is forced by the order of the
  two tensor shifts and the opposite triangulated convention; it is the Hom
  reindexing sign on the cone connecting map.
- In `IsEtaleHomReversedExact`, the chosen chiPhi and chiPsi are explicitly
  constrained, for every K and integer n, to `F(s_A) ≫ sigma` and
  `H_B(sigma.inv,1) ≫ s_B`, respectively. The same existentially bound
  structures are used for BOTH `.IsTriangulated` propositions AND
  `NatTrans.CommShift v ℤ`. Thus the assertion includes the shift square for v,
  hence the third square of the reversed triangle, its connecting map and sign.
  They are not independent shift structures on the two functors.
- Thick locus: `IsEtaleHomThickIsoLocus` has its five conjuncts in the node's
  order: every `IsZero K`; invariance under `K ≅ L`; every integer shift;
  the third vertex of a distinguished triangle when the first two components
  are invertible; and retracts `i ≫ r = 𝟙 K`. Integer shift and rotation yield
  the other positions of two-out-of-three. Retracts require no idempotent
  completeness hypothesis.

Return point 1 is repaired by the uniquely normalized μ, its explicit two-variable
naturality, and the removal of the free μ from both the theorem and transpose.
Return point 2 is repaired by the fixed scalar mate, evaluation-normalized Hom
shifts with the `n.negOnePow` correction for both s_A and s_B, both chi equations,
and the shared IsTriangulated/NatTrans.CommShift clauses.
H8 is repaired for every helper, including `EtaleHomRight`: each declaration now
names its source place and blueprint id; both postponed theorems have complete
proof docstrings corresponding to the node's steps. H4/H9 is repaired by removing the unused generic-Hom import and using the
published `Etale.derivedHom` import directly.
The previous H11 second reading is superseded by the explicit checks below.

Dependency declarations read and used:

- `def-weil-pbc-derived-categories`: `AlgebraicGeometry.Etale.DerivedCategoryModule`
  in `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, publicly available
  through the recorded derived-category module.
- `def-pur-derived-internal-hom`: `CategoryTheory.derivedInternalHomOfUniverses`
  and its three comparison declarations from
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`. The concrete étale
  Hom used by this item is the published `AlgebraicGeometry.Etale.derivedHom`
  and `derivedTensorHomAdjunction` from
  `WeilConjectures.SixFunctors.Etale.Derived.Hom`, imported directly in the item;
  this preserves the general dependency record and its independent universe note.
- `lem-pur-derived-change-of-rings`: the existing general
  `SheafOfModules.derivedChangeOfRingsIndependentCoefficients`, reexported by
  `Sheaf.Paper.EtaleDerivedScalarTensor`; the latter supplies `scalarExtension`
  and the explicitly normalized `scalarExtensionRepresentative`.
- `def-weil-triangulated-category`: Mathlib `Pretriangulated`,
  `Functor.IsTriangulated`, the opposite triangulated shift, and
  `NatTrans.CommShift`. The derived tensor shift is the existing structure from
  `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift`.

Edge cases checked against the signatures and equations: zero objects; empty
scheme; A=B with identity coefficient map (the prescribed tensor balancing and
shift are the canonical ones); the zero ring as target; the nonflat Z→Z/2 case;
all positive, zero and negative shifts; cone triangles including their last
arrow; and nonsplit idempotents versus actual retracts. None is excluded. In
particular flat-term K-flat hypotheses occur only in the characterization of μ,
not as assumptions on φ or on K,M. The cancellation equation gives the usual
source Hom sign (-1)^a in shift one; keeping the opposite shift n as original
shift -n makes the two chi equations type correctly.

Searches, retained and repeated during repair:

- `msearch.py ... leanfinder` with query `canonical derived extension of scalars
  tensor comparison natural normalized K flat complexes`: eight hits, headed
  by Module.Flat.lTensor_shortComplex_exact and the analogous rTensor results;
  these do not supply the derived comparison or its normalization.
- `msearch.py ... loogle '"NatTrans", "CommShift"'`: twelve generic hits,
  including `CategoryTheory.NatTrans.CommShift`, its core, and identity/iso
  transfer results. This existing predicate is used directly in the repair.
- `msearch.py ... grep 'internalHom.*CommShift|scalar.*tensor.*comparison'
  CategoryTheory`: zero hits.
- `rg` for `lem-coef-etale-hom-thick-locus`, `etaleHomComparison_thickLocus`,
  `etaleHomTensorComparison`, and `EtaleHomShiftNormalization` in the source
  WeilConjectures and shared lean/Sheaf trees: no existing statement or helper.
- Targeted `rg` and full source reads found the existing scalar/tensor unique
  normalization, actual derived restriction/extension, closed internal Hom,
  ordinary adjunction-mate oplax tensorator, and derived tensor shift instances.
  Those are reused; no second tensor, Hom, or scalar-extension construction is made.

The actual source places were read locally: Stacks sites-cohomology.tex,
lemma-pullback-tensor-product (07A4), lemma-RHom-triangulated (08JC), and the
blueprint thm-coef-finite-hom proof's evaluation and localization paragraphs.
The current main-20261015 snapshot's target statement was also read.

Validation: `scompile.py NC lem-coef-etale-hom-thick-locus`
`lean/Sheaf/SixFunctors/EtaleHomThickLocus.lean` completed cleanly in the
sandbox and library (12.6 s and 14.4 s in the final run), with no errors or
warnings. The signed normalization elaborates directly against the published
Hom and tensor-shift APIs. No adapter or extra dependency module is delivered.
No timeout limit was raised. No proofs were filled: the only `sorry`s are the
two named theorems, each owned by this node and carrying its proof docstring.

## Dependency modules

None. The returned `Sheaf.Algebra.Homology.DerivedInternalHomEtale` adapter was
removed as requested. The dependency node is restored unchanged to its general
`Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses` declaration record, while
the item imports and uses the existing published `Etale.derivedHom` directly.

## Second reading by NC

This is the required self-check in this dispatcher repair: the brief prohibits
starting another agent. I reopened the node, its proof steps, the corrected Lean,
and the dependency record after compilation. Unlike the returned reading, this
check tests the two precise failure modes.

First, a per-object twist of μ must preserve both derived naturality equations
AND the flat-term K-flat counit equation. The latter fixes every model component;
naturality through resolutions fixes all other components. The exists-unique
statement consequently excludes the twist, and the transpose has no free μ.
Second, the comparison v appears in the exactness predicate and specifically in
`NatTrans.CommShift v ℤ`. The structures used there are the same chiPhi/chiPsi
bound alongside both triangulatedness assertions, and their component formulas
are fixed by sigma and the evaluation-normalized s_A/s_B. An independent pair of
unrelated shift structures no longer satisfies this predicate merely by existing.

I checked each hypothesis and clause against the list above, including the scalar
shift at -n in the right-hand formula, the tensor order in the adjunction, the
negative shift on the original category induced by the opposite category, the
`n.negOnePow` factor in both Hom shift normalizations, and all five thick-locus
conjuncts. The main theorem signature now has only the
coefficient map and scheme as explicit inputs, then its canonical v family; it
has no μ input or existential μ. All variables and universes are explicitly bound.
The helper/source docstrings and recorded declarations were checked individually;
the unused adapter import and file are absent, and the dependency record is back
to its general interface. No statement correction is needed.

## Reviewer fix (maintainer review of 6ce2b6e277d0)

The Hom shift normalization `EtaleHomShiftNormalization` used the factor
`n.negOnePow`. That sign is correct for n = 1, which is what the cone triangle's
connecting morphism needs in the opposite triangulated convention. It is wrong for
the other n. The tensor cancellations satisfy c(a+b) = (-1)^(a*b) c(a) c(b). On Hom
complexes the normalized shift is s_n = ε(n) (-1)^(n*j) in degree j. The CommShift
addition axiom then forces ε(a+b) = (-1)^(a*b) ε(a) ε(b). With ε(n) = (-1)^n this
fails at a = b = 1, and also at a = 1, b = -1 against the zero axiom. So no
`CommShift` satisfied the delivered normalization, and the main theorem was false
for any nonempty X.

The factor is replaced by `((n * (n + 1)) / 2).negOnePow`:
- it agrees with the delivered sign at n = 1;
- it satisfies the cocycle identity;
- it is Mathlib's `Cochain.leftShift` sign for the shift by -n.

The docstrings of the normalization and of proof step 4, and the record note, are
updated to match. Nothing else changed. The fixed file compiles cleanly with
`nt_compile.py`.

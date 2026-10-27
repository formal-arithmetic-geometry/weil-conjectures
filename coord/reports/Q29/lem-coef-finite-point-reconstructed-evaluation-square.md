## Worker report

Item: `lem-coef-finite-point-reconstructed-evaluation-square`, Q29, stage 2.
Module: `Sheaf.Paper.FinitePointReconstructedEvaluationSquare`.
Main declaration:
`WeilConjectures.FinitePointEvaluation.finite_point_reconstructed_evaluation_square`.
The only postponed proof is this theorem, whose docstring contains the node's six-step
proof. All four helper definitions contain their actual composites. The repository
was read only; source and node writes are confined to this item's sandbox. All
compilation used the prescribed `scompile.py` wrapper.

The node's statement, source, dependencies and proof are unchanged. No new node or
dependency module is required. The source was read in
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/lem-pod-point-dualizing-complex.proof.md`:
its second sentence computes point internal Hom over the coefficient ring. The
node's refined proof supplies the reconstruction, evaluation and naturality details.

Hypotheses and objects, individually:

- The global finite-field tuple is `D : FiniteFieldDatum.{u}`. This includes the
  prime characteristic, positive exponent, finite base field with the specified
  cardinality and its algebraic closure. The point is `Spec (.of D.k)` throughout.
- The coefficient prime is `l : ℕ`, `[Fact l.Prime]`, `_hl : l ≠ D.p`.
- The finite coefficient extension is `E : Type u`, `[Field E]`,
  `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`.
  Its valuation ring and selected uniformizer are those of the recorded
  coefficient-extension construction. No different DVR or quotient is supplied.
- A positive exponent is written `n + 1` with `n : ℕ`, covering every exponent
  at least one, including one. The positivity proof everywhere is
  `Nat.succ_le_succ (Nat.zero_le n)`. This matches the index of the already
  recorded point tensor comparison; it is not a restriction of the statement.
- The coefficient ring is `FinitePointHom.A l E (n + 1)`, namely the canonical
  `ULift` of `Padic.coefficientExtensionRing l E (n + 1)`.
- The small-site ring sheaf is `FinitePointHom.B D l E (n + 1)`; modules are
  `FinitePointHom.Mod D l E (n + 1)`. The coefficient object in the tensor
  category is `(finiteIntrinsicClosed l E (Spec (.of D.k)) n).monoidal.tensorUnit`,
  exactly the coefficient object fixed by `PointFiniteTensorData`. Thus `α` is
  specified, with arbitrary domain `V` in the ambient sheaf derived category.
- The source object is `C : finiteTorConstructibleCategory ...`: its `.obj`
  is an ambient derived object, and `.property` includes bounded
  constructibility AND finite Tor amplitude. The latter is not inferred merely
  from bounded constructibility.
- Sections are `FinitePointHom.G ...`, the same final-object evaluation and
  restriction along the actual constant-section map as `pointFiniteSections`.
  Its derived functor is the ambient part of `pointFiniteFibre`; no alternative
  point-fibre functor is defined. The ordinary derived source is its value at C.
- Internal Hom is `FinitePointHom.H ...`, the recorded
  `derivedInternalHomOfUniverses` on the same site and coefficient sheaf.
  Ordinary RHom is `ordinaryModuleDerivedInternalHom`, the recorded ordinary
  module presentation of the closed derived Hom functor.
- `L`, `hobj`, `_hmap`, `adj`, `_hex`, `hr`, `q`, `_hq`, `_hrec` are the
  witnesses supplied by `finite_point_reconstructed_hom_model`. The object and
  arrow equations specify actual extension of constant modules; `_hex` fixes
  its adjunction by evaluation at `1 tensor x`; `hr` is the actual-counit
  reconstruction/triangle assertion; `_hq : Comparison ...` fixes q on
  flat-term K-flat/K-injective models and requires derived naturality.
  `_hrec` retains the recorded reconstructed comparison. These are not
  unconstrained Hom arrows or a replacement reconstruction. Exactness and
  additivity instance binders expose the derived functors of these already
  exact dependencies; their existence is not an additional mathematical claim.
- `S : PointFiniteTensorData ...`, `_hsource` and `_hcanonical` are the fixed
  finite-stage witnesses from `pointFibreDerivedTensor` (also supplied by
  `pointFiniteTensorComparisons`). The canonical predicate fixes the
  comparison on actual K-flat tensor generators. No arbitrary tensor isomorphism
  is used. The coefficient comparison is `S.unitIso` throughout.

Conclusions and formulas, individually:

- `reconstructedMap` is exactly `Gamma Hom(e_C,V)` followed by `q`. Its first
  factor uses `adj.mapDerivedCategoryAdjunction.counit.app C.obj`, not an
  independently chosen isomorphism `L(Gamma C) ≅ C`. The finite-cohomology
  witness needed by q is `(hr C.obj C.property.1).1`.
- `beta` first applies `Gamma Hom(C,α)`, then `reconstructedMap` at the
  coefficient unit, then RHom applied to `S.unitIso.hom`. Thus its order is
  exactly the node's beta formula, with the stipulated constant-value unit
  identification made explicit at the target.
- The existential family `hH` asserts that `H(C,V)` belongs to the SAME
  `finiteTorConstructible` predicate, including its bounded constructibility
  and Tor condition, for each C. This provides the witness required to apply
  the tensorator to `(H,C)`; no such witness is an input assumption.
- `pairing` is `(pointFiniteTensorComparison ... S ⟨H,hH⟩ C).inv`, followed by
  `Gamma (finiteIntrinsicEvaluation ... C V ≫ α.hom)`, then `S.unitIso.hom`.
  Hence this is precisely the specified right-hand side with mu the INVERSE
  tensor comparison and the same coefficient unit.
- The first conjunct after `hH` is `(beta ▷ c) ≫ perfectTraceEvaluation c =
  pairing ...`. `perfectTraceEvaluation` is the Hom-first coefficient
  evaluation, obtained from the ordinary counit using the recorded Koszul
  braiding. Composition `≫` reads left to right, so this is the displayed
  evaluation square in the node.
- The next conjunct identifies beta with `pairingTranspose`. This helper
  braids `c tensor Gamma H` to `Gamma H tensor c` using
  `pointModuleDerivedBraiding`, then applies `MonoidalClosed.curry` to the
  specified pairing. It is the coefficient closed tensor-Hom transpose,
  rather than a new map asserted to have the desired properties.
- The separate naturality conjunct quantifies every derived `f : C ⟶ C'`
  in the full finite-Tor subcategory. Its equation reads
  `Gamma Hom(f,V) ≫ beta_C = beta_C' ≫ RHom(Gamma f,A)`, exactly the node's
  displayed contravariant square with the composition convention reversed.
  It does not require a chain representative of f. Inverted
  quasi-isomorphisms and compositions of derived roofs are included.
- The final conjunct quantifies a representative `P` of `Gamma C` through
  `_eP : DerivedCategory.Q.obj P ≅ Gamma C`, the acyclic-test definition of
  K-flatness, and termwise flatness. It quantifies a K-injective `J` with an
  actual quasi-isomorphism from the constant coefficient module in degree
  zero. The comparison `qPJ` is required to satisfy the existing
  `PointDerivedHom.IsComparison` formula `q(h)(x)=h(1 tensor x)`.
- Its conclusion is the EXISTING `PointDerivedHom.EvaluationCompatible`.
  I read that definition in full: it provides the sheaf input-first evaluation,
  the balancing map and the ordinary input-first evaluation. The first and
  third clauses explicitly give `(-1)^(p*j)` times the Hom component value;
  its second clause fixes the balancing map on the actual local tensor
  generator; its last clause equates the two chain-map composites. Substituting
  `1 tensor x` gives `(-1)^(p*j) h(1 tensor x)` on BOTH sides. Thus the
  signed clause is an actual formula and equality, not just a prose comment.
  The Hom-first convention is recorded by the braiding in the pairing and
  transpose clauses above. No copy of the signed-Hom notion was introduced.

Recorded dependency declarations read and reused:

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: coefficient-extension
  ring/finiteness, with the coefficient construction it imports.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`;
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`: `CategoryTheory.constantSheaf`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `Scheme.intrinsicFiniteTorsionConstructible`; `Sheaf.Paper.FiniteTorAmplitudeSites`
  and `Sheaf.Paper.FiniteTorAmplitude`: `finiteTorConstructible` and its full category.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointFiniteFibre`, whose ambient functor
  is the recorded `pointFiniteSections` used here.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `ordinaryModuleDerivedInternalHom`, `derivedInternalHomOfUniverses`.
- `WeilConjectures.Algebra.Homology.HomComplex`: `homComplex`, used through
  `PointDerivedHom.sheafHom` and the recorded signed comparison predicates.
- `Sheaf.Paper.FinitePointReconstructedHomModel`: all of `FinitePointHom.A`,
  `B`, `Mod`, `G`, `H`, `Reconstruction`, `Comparison`, `ReconstructedComparison`,
  `qSource`, `qTarget` and `finite_point_reconstructed_hom_model`.
- `Sheaf.Paper.PointFibreDerivedTensor`: `PointFibreDerivedTensorCanonical`,
  its finite-model and finite-source fields, `PointFiniteTensorData`,
  `pointFiniteTensorComparison`, `S.unitIso`, `pointModuleDerivedBraiding`.
- `Sheaf.Paper.CoefficientRingedTensorHomModel`: the recorded closed structure's
  evaluation/transpose, used through the fixed `finiteIntrinsic...` operations.
- Proof imports include `FiniteConstructibleHom`, `PointDerivedHomEvaluation`,
  `PointRingedEvaluationModel` and `RingedDerivedTensorHomAdjunction`. The
  finite K-flat model node is publicly reexported by `PointFibreDerivedTensor`.

Edge cases checked before finalizing the statement:

The smallest positive level is n=0, i.e. quotient exponent one. No zero level
is silently substituted. C may be the zero derived object, any shift, or any
finite-Tor object with negative cohomological degrees. The formula's p,j range
is all integers; signs are the existing `negOnePow` convention, including
negative degrees and characteristic two. V is arbitrary ambient derived data
with the specified α, rather than a complex assumed bounded termwise. The
identity f, zero f and inverses of quasi-isomorphisms are all derived morphisms
in the quantified full subcategory. Small-site objects have universe u+1 and
arrows universe u; coefficients and module carriers have the prescribed u+1
lift, with the recorded standard sheaf derived universe u+2. No equality of
site object and morphism universes is imposed.

Searches performed via the prescribed `msearch.py` wrapper:

- LeanFinder: `signed evaluation square derived internal Hom reconstructed
  constant sheaf at algebraically closed point`. Eight hits, mostly smooth
  evaluation plus `LightCondensed.ihomPoints[_apply]`; none states the
  reconstructed finite-coefficient pro-etale derived square.
- Loogle: `CategoryTheory.MonoidalClosed.curry`. Twelve hits, including the
  generic curry/uncurry identities and naturality. These give the coefficient
  transposition operation, but not the point comparison theorem.
- Grep of Mathlib/CategoryTheory: `reconstruct.*[Ee]valuation|[Ee]valuation.*reconstruct`.
  Zero hits.
- LeanSearch: `Derived internal Hom comparison from reconstructed constant
  sheaves on a point preserves signed evaluation and is natural for derived
  morphisms`. Eight hits, including `ihom.ev`, `constantSheafAdj`, generic
  sheaf sections and Day convolution evaluation. No exact match.
- `rg` of project `lean/WeilConjectures` and `lean/Sheaf` for
  `reconstruct.*[Ee]valuation|[Ee]valuation.*reconstruct|finite_point_reconstructed_evaluation`.
  The relevant existing result is the predecessor reconstructed-Hom module,
  whose statement stops before this evaluation square; other hits are
  unrelated reconstruction/evaluation comments. Searching the exact item id
  in `lean/WeilConjectures` gave no match. The sibling
  `FinitePointInternalHomEvaluation` specializes V to the exceptional object
  and defines a transpose directly; it does not identify the predecessor's Q
  with this pairing for arbitrary specified `(V,α)`, so is not an existing match.

Validation: `scompile.py Q29 lem-coef-finite-point-reconstructed-evaluation-square
<module>` compiled both sandbox and actual module cleanly, with no errors or
unexpected warnings. Auto-implicit variables are disabled. No proof was attempted.

## Second reading by Q29

Author's second reading, performed with the node, its six proof steps and the
final module open; the maintainer supplies the independent review for this
self-delivered task. I checked the two directions of the Hom comparisons, the
contravariance of the actual reconstruction counit, the order of α and Q in
beta, the inverse direction of the tensorator in pairing, and the target unit
map. The derived naturality equation has beta_C after precomposition and
beta_C' before coefficient precomposition, as required. The final representative
clause was restricted to representatives of Gamma C, so it does not add an
unrequested result for arbitrary nonconstructible source complexes. Its
K-flat test is acyclicity of `F tensor P`, not a vacuous test. The full
`EvaluationCompatible` definition was reopened to verify both signs and the
balancing-map equation. Every helper is a concrete composite of recorded maps.
No mathematical mismatch or statement correction remains; no
STATEMENT-DISPUTED flag is asserted.

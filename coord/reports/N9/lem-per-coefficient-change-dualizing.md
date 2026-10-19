## Worker report

Module: `Sheaf.Paper.CoefficientChangeDualizing`. Main declaration:
`AlgebraicGeometry.Etale.CoefficientChangeDualizing.coefficient_change_dualizing`.
The sole postponed theorem is the item, with all eight DAG proof steps in its docstring.
The helpers `dual`, `biduality`, and `homComparison` have real data and source docstrings.
No statement correction, dependency replacement, or new definition node is needed.

Source checked: the local ILO Travaux de Gabber PDF, Expose XVII, Definition 7.1.1,
Theorems 7.1.3 and 7.6.1 and the deduction on printed p. 311. Definition 7.1.1's
printed `RHom(K,-)` is the known typographical reversal: its biduality and subsequent
proof use `RHom(-,K)`, as the DAG already states. The Noetherian hypotheses, general
Noetherian coefficient algebra, finite-Tor domain and canonical coefficient comparison
are retained. No invertibility of ell on X or finite type over a field is assumed.

Hypotheses and clauses, individually:

- Prime ell: `(ℓ : ℕ) [Fact ℓ.Prime]`. Lambda is the actual prime field
  `ULift.{u + 1} (ZMod ℓ)`, a size lift, not an arbitrary finite coefficient ring.
- X Noetherian: `(X : Scheme.{u}) [IsNoetherian X]`.
- K in the original finite-coefficient Dbc: `K : DerivedCategoryModule ... X` and `hK`
  using the dependency's `DerivedCategory.isBoundedConstructible`.
- Original duality preserves this category and its biduality is invertible: `hdual`
  quantifies over every bounded constructible N and gives both the constructibility
  of `(dual _ X K).obj (op N)` and `IsIso (biduality _ X K N)`.
- Every commutative Noetherian Lambda-algebra: `(A : Type (u + 1)) [CommRing A]
  [IsNoetherianRing A] [Algebra (ULift ... (ZMod ℓ)) A]`. There is no finiteness,
  flatness or nonzero-ring hypothesis on A.
- K_A: everywhere the actual object is `(scalarExtension (algebraMap ... A) X).obj K`.
  This is the existing ordinary derived left adjoint of exact restriction. Its
  `scalarTensorIso` in `Sheaf.Paper.EtaleDerivedScalarTensor` identifies its underlying
  Lambda-complex with tensor by A_X, normalized on K-flat representatives.
- K_A bounded constructible: the first conjunct uses upstream
  `DerivedCategory.boundedConstructible (ModuleCat A) X`.
  This combines bounded cohomology with `Scheme.IsConstructibleSheaf` for every
  cohomology sheaf. The latter uses finite `Scheme.Stratification`, with locally closed
  constructible strata, and `IsFiniteLocallyConstantSheaf`. Here “finite” means
  finitely generated MODULE stalks (`IsFiniteSheaf`, `ModuleCat.isFinitelyGenerated_iff`),
  so infinite coefficient algebras are not excluded. On Noetherian X the strata's
  constructibility is automatic; boundedness permits a finite common refinement for
  the finitely many relevant cohomology sheaves.
- Preservation of the finite-Tor bounded constructible category: the second conjunct
  quantifies over every M with `DerivedCategory.boundedConstructibleFiniteTor A X M`
  and gives the same predicate on its actual internal-Hom dual.
  This existing predicate is the preceding bounded constructible predicate intersected
  with `DerivedCategory.finiteTorAmplitude (ModuleCat A) X`, which tests tensor against
  EVERY module sheaf placed in degree zero with one common finite interval.
- Evaluation-transpose biduality isomorphisms: this same conjunct gives `IsIso` of
  `biduality A X K_A M`. This helper is the explicit transpose, under
  `derivedTensorHomAdjunction`, of the counit after `derivedTensorSymmetry`. The latter
  is the descended Koszul symmetry, not an arbitrary braiding witness.
- Naturality: the next conjunct is the naturality equation for those same components
  on every arrow between finite-Tor bounded constructible objects. The double-dual
  functor is `(dual A X K_A).rightOp ⋙ dual A X K_A`; invertibility above therefore
  yields the asserted natural isomorphism on that category.
- Finite field: the next conjunct assumes `IsField A` and quantifies over `[Finite A]`.
  It gives preservation and invertible evaluation biduality for ALL objects satisfying
  the dependency's original `isBoundedConstructible A X`, without a Tor hypothesis.
- Extended input N: the final conjunct quantifies over every original bounded
  constructible N. It supplies both Hom comparisons as isomorphisms alpha and beta,
  with their homs EQUATED to the components of `homComparison` at N and D_K N.
  `homComparison` extracts the natural transformation of the landed
  `etaleHomComparison_thickLocus`; its evaluation-transpose normalization uniquely
  fixes every component. Thus neither isomorphism is arbitrary.
- Compatibility of biduality: the final equation is
  `T.map delta_N ≫ beta.hom ≫ D_A.map alpha.inv.op = delta_(T N)`.
  Its direction agrees with the DAG formula beta_total = Hom(alpha_inverse,1)
  composed with alpha_(D N). Contravariance requires exactly `alpha.inv.op`.
  The comparisons are natural by their existing natural transformation interface.

Dependency declarations read and used:

- `def-kun-derived-tensor`: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor`; its full signature has arbitrary monoidal
  Grothendieck coefficients, specialized here to `ModuleCat.{u+1} R`.
- `def-pur-derived-internal-hom`:
  `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`; the recorded declarations
  include its public `Etale.derivedHom` and `Etale.derivedTensorHomAdjunction`.
  The generic ringed-site module and its independent universes are not replaced.
  The current source was also checked with `scompile.py --source`.
- `def-weil-pbc-constructible-complexes`:
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `Etale.DerivedCategory.isBoundedConstructible`, for the finite-ring hypothesis
  and finite-field conclusion. General A uses the existing upstream general-ring
  `boundedConstructible` and `boundedConstructibleFiniteTor` from Constructible and
  Derived.Coefficients; these are not the finite-value predicate at infinite A.
- Added already-landed statement dependencies `lem-kun-tensor-sym` and
  `lem-coef-etale-hom-thick-locus`, respectively modules
  `Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry` and
  `Sheaf.SixFunctors.EtaleHomThickLocus`, expose the canonical symmetry and the
  evaluation-normalized coefficient comparison. The latter also exposes the existing
  `scalarExtension` and normalized binary tensor comparison.
- All available proof-dependency modules are imported non-publicly: tensor
  triangulatedness, internal-Hom triangulatedness, tensor/stalk comparison,
  Noetherian pseudo-coherence and maximal-fibre perfectness, conservative stalks,
  derived homology long exact sequences and exact stalks. The two proof-only nodes
  `lem-per-ctf-hom-coefficient-comparison` and `lem-per-prime-field-tensor-devissage`
  have no Lean record yet; their imports are consequently omitted. They are not needed
  for elaborating this statement, and are named explicitly in its proof docstring.

Edge cases checked: X empty, K=0 when it can satisfy the duality hypothesis, M=0,
ell=2 (the actual signed symmetry specializes correctly), identity algebra extension,
an infinite Noetherian algebra A, the zero algebra A, and finite fields with extension
degree greater than one. A is not forced finite or a field except in the stated
finite-field implication. General coefficient categories have the same object and
morphism size convention as the recorded derived module categories; no site-universe
equality or smallness assumption was added. In particular no assumption that every
A-complex descends to the prime field appears.

Searches:

- msearch LeanFinder: “Extension of coefficients preserves dualizing complexes and
  evaluation biduality on constructible etale complexes of finite Tor amplitude”.
  Eight hits on `HomologicalComplex.extend`, none on coefficient duality.
- msearch Loogle: `DerivedCategory`. Twelve generic derived-category hits, no match.
- msearch LeanSearch: “Dualizing complexes remain dualizing under extension from a
  prime field to a noetherian algebra”. Eight ordinary dual/base-change hits, no match.
- msearch grep: `dualizing|biduality|constructible.*tensor`. Ten unrelated dualizing-word
  hits, no etale coefficient-extension theorem.
- rg of Mathlib via msearch, upstream WeilConjectures and side lean/Sheaf for
  `biduality`, `dualizing`, `scalarExtension`, `etaleSheafExtendScalars`, `finiteTor`,
  `EtaleHomTranspose`, and the exact item id. The exact id has no upstream declaration;
  existing derived tensor/Hom, constructible predicates, scalar extension, symmetry
  and normalized comparison were reused. The ordinary perfect-complex biduality and
  finite-field-over-a-geometric-base Verdier declarations have different hypotheses.
- `tools/lean_names_upstream.py show lem-per-coefficient-change-dualizing`: no binding.

Validation: the module passed scompile.py in both its sandbox and library names, with
no diagnostics. The final packet is checked again by deliver2.py --no-push.

## Second reading by N9

Author self-reading, as required by the dispatcher brief forbidding additional agents;
the maintainer supplies the independent review. Reopened the full node and final Lean.
Checked every binder and all five conclusion conjuncts against the statement as listed
above. Checked that the output predicate at infinite A uses finite MODULE stalks;
using the finite-ring predicate there would have been wrong. Checked that the finite
field clause includes all original Dbc objects and imposes no Tor input. Recomputed the
last comparison's direction: alpha inverse goes from D_A(TN) to T(D_K N), so its op
under D_A gives the desired final target. Restricted the explicit naturality clause
to the stated finite-Tor subcategory during self-reading. No statement correction or
unresolved dispute remains. All helper data is constructed from canonical existing
interfaces; only the item's theorem uses sorry.

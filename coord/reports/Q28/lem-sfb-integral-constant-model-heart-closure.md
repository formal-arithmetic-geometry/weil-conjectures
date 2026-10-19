## Worker report

This delivery adds `Sheaf.Paper.IntegralConstantModelHeartClosure` and records its
statement as `AlgebraicGeometry.ProEtale.isConstantModelConstructible_serre_padicIntegers`.
The theorem is statement-only, with `sorry` as its proof.  The node copy changes its
`lean` field and adds the already-landed finite-subextension dependency
`def-weil-finite-subextension-directed-set`, because the Lean binder for a finite
subextension is `Padic.FiniteCoefficientFields`.

The module uses `IsNoetherian X`, whose Mathlib class extends exactly
`IsLocallyNoetherian X` and `CompactSpace X`, rendering the node's quasi-compact and
locally Noetherian hypotheses without adding separatedness, finite type, dimension, or
invertibility assumptions.  The prime is `[Fact ℓ.Prime]`, and
`E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)` is a finite intermediate field in
the fixed algebraic closure `PadicAlgCl ℓ`.  Its coefficient ring is
`Profinite.padicIntegersRingObj ℓ E.val`, the condensed ring of integers with its
valuation topology, and `condensedRingObj ... X` is its canonical pullback to
`X.ProEt`.

Hypothesis-by-hypothesis and clause-by-clause rendering:

| Node clause | Lean rendering |
| --- | --- |
| Noetherian scheme | `(X : Scheme.{u}) [IsNoetherian X]`; the class is locally Noetherian plus compact. |
| Prime `ℓ` | `(ℓ : ℕ) [Fact ℓ.Prime]`. |
| Fixed algebraic closure and finite subextension `E` | `E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)`, whose value is an intermediate field with `FiniteDimensional ℚ_[ℓ] E.val`. |
| Pulled-back integral condensed coefficient ring | `condensedRingObj (Profinite.padicIntegersRingObj ℓ E.val) X`. |
| Ambient module category | `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (...)`, with the existing module-sheaf category and its ambient abelian kernels/cokernels. |
| Kernel/cokernel hypotheses | `∀ (M N : ...) (f : M ⟶ N), IsConstantModelConstructible ... M → IsConstantModelConstructible ... N`. |
| Kernel conclusion | `IsConstantModelConstructible ... (kernel f)`. |
| Cokernel conclusion | `IsConstantModelConstructible ... (cokernel f)`. |
| Short exact extension hypothesis | `∀ S : ShortComplex (...), S.ShortExact → ... S.X₁ → ... S.X₃`. |
| Extension conclusion | `IsConstantModelConstructible ... S.X₂`. |

The finite constant local model predicate is the recorded
`AlgebraicGeometry.ProEtale.IsConstantModelConstructible`; it includes finite
stratifications by locally closed subschemes and finite scalar presentations over the
condensed ring on the point.  Thus the theorem does not replace scalar matrices by
arbitrary coefficient sections.  `kernel` and `cokernel` are the categorical operations
in the displayed `Mod` category, and `S.ShortExact` is the existing short-exact notion.

Dependency declarations read and used:

* `Mathlib.Topology.Defs.Filter.CompactSpace` (`CompactSpace`) gives the
  quasi-compact component of `IsNoetherian`.
* `Mathlib.AlgebraicGeometry.Noetherian` (`AlgebraicGeometry.IsLocallyNoetherian` and
  `AlgebraicGeometry.IsNoetherian`) gives the local Noetherian component and their
  combined class.
* `Sheaf.NumberTheory.Padics.FiniteCoefficientFields` (`Padic.FiniteCoefficientFields`)
  is the finite intermediate-field subtype used for `E`; its docstring records the
  fixed algebraic closure, finite-dimensionality, composita, base and exhaustion.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
  (`Padic.finite_coefficientExtensionRing`) is the recorded coefficient-extension
  interface.  The condensed integral ring used here is the canonical
  `Profinite.padicIntegersRingObj` rather than a second ring construction.
* `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`
  (`Profinite.padicIntegersRingObj` and
  `Profinite.isCommMonObj_padicIntegersRingObj`) gives the continuous condensed ring of
  `PadicAlgCl.integers ℓ E.val` and its commutative ring-object structure.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
  (`AlgebraicGeometry.ProEtale.condensedRingObj` and
  `isCommMonObj_condensedRingObj`) gives the canonical inverse-image coefficient object.
* `Mathlib.AlgebraicGeometry.Sites.Proetale` (`Scheme.ProEt` and
  `Scheme.ProEt.topology`) supplies the small pro-étale site.
* `Sheaf.CategoryTheory.RingedSiteModules` (`CategoryTheory.ringedSiteModules`) is the
  general ringed-site module category underlying the displayed `Mod` encoding.
* `Sheaf.Paper.CondensedConstantConstructibility`
  (`AlgebraicGeometry.ProEtale.IsConstantModelConstructible`) supplies the exact finite
  constant scalar-model constructibility notion.
* `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`
  (`AlgebraicGeometry.Scheme.FiniteLocallyClosedStratification`) supplies the finite
  locally closed stratum data used by that predicate.

The proof is postponed exactly as required by the node.  Its documented route is the
coefficient comparison with the completed adic model, the adic stratified-perfect
two-out-of-three criterion for cones, and the degree-zero triangle for short exact
sequences; no proof dependency is imported as a theorem in this stage-2 statement.

Edge cases checked: `X` may be empty; `E` may be the base field `ℚ_ℓ`; the index of a
stratification may be empty; the zero module and zero morphism give zero kernels and
cokernels; the identity morphism gives zero kernel and itself as cokernel; multiplication
by a uniformizer gives the residue-field cokernel; and a nonsplit short exact sequence is
allowed because only `S.ShortExact` is assumed.  No connectedness, separatedness,
finite-type, dimension, or coefficient-invertibility condition is introduced.

Searches made:

* `msearch.py ... leanfinder "integral scalar constant model constructible module
  sheaves on Noetherian schemes closed under kernels cokernels and extensions"` returned
  generic scheme-module, finite-presentation, and locally Noetherian declarations, with
  no exact closure theorem.
* `msearch.py ... loogle "IsConstantModelConstructible kernel cokernel ShortExact"`
  returned zero hits and reported `IsConstantModelConstructible` unknown to Loogle.
* `msearch.py ... grep "IsConstantModelConstructible|constant.*constructible.*kernel|
  integral.*heart" CategoryTheory` returned zero hits.
* The same grep over the upstream `WeilConjectures` tree found only an unrelated
  constructible-cokernel mention; direct `rg` for the proposed theorem and for the node
  id found no existing declaration in the source tree or shared `lean/Sheaf`.
* The existing project module `Sheaf.Paper.CondensedConstantConstructibility` was read
  in full.  It defines the required finite constant scalar-model notion but contains no
  weak-Serre closure statement, so no duplicate declaration exists.

No statement correction or `STATEMENT-DISPUTED` flag is needed.  No new definition node
or dependency repair module was added.

## Second reading by Q28

I reread the copied node, the complete theorem signature, and the imported dependency
declarations.  The first conjunct has exactly the two constructible hypotheses and the
kernel and cokernel conclusions for an arbitrary ambient morphism.  The second conjunct
has exactly the short-exact hypothesis and constructibility of the middle object.  The
coefficient object is the pulled-back condensed ring of integers, and the finite field
parameter is the recorded finite-intermediate-field subtype.  `IsNoetherian` contributes
only the two stated Noetherian conditions.  No mismatch was found.

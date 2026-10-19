## Worker report

The module `Sheaf.Paper.Pur9Invertible` records the finite-level tensor-invertibility
notion on both the small pro-etale and small etale sites.  The main declarations are
`AlgebraicGeometry.Scheme.IsProEtaleInvertibleAtLevel` and
`AlgebraicGeometry.Etale.DerivedCategory.IsEtaleInvertibleAtLevel`; the module also
records the shared chosen-data structure and the site-specific derived-tensor and
constant-complex helpers.  There are no theorem proofs or postponed data.

The Lean rendering follows every clause of the node statement.

* The prime `l`, finite extension `E`, field/algebra and finite-dimensional
  hypotheses are explicit in both `IsProEtaleInvertibleAtLevel` and
  `IsEtaleInvertibleAtLevel`.  The positive level hypothesis is the explicit
  `_hn : 1 ≤ n`.  The coefficient ring is
  `Padic.coefficientExtensionRing l E n`, the construction supplied by
  `Padic.coefficientExtensionRing`.
* `proEtaleDerivedCategory X ...` is the unbounded derived category of modules on
  the recorded small pro-etale site.  Its complex presentation is
  `Scheme.proEtaleComplex`; `proEtaleQuotient` is its localization functor.
  The etale side is `DerivedCategoryModule Λ X`, the recorded unbounded derived
  category on `X.smallEtaleTopology`.  At the finite level its coefficient is
  `ULift (Padic.coefficientExtensionRing l E n)`, the standard size lift used by
  `DerivedCategoryModule`.
* `proEtaleConstantComplex` is the sheafification of the constant commutative-ring
  sheaf, restricted to modules and placed in degree zero.  The etale counterpart is
  `etaleConstantComplex`, which is the existing
  `AlgebraicGeometry.Etale.constantComplex`.
* On the pro-etale site, `ProEtaleInvertibleData` supplies objects `L` and
  `inverse`, representatives `K₁,K₂`, a K-flat resolution
  `f : P ⟶ K₁` with `QuasiIso f`, the identifications of the representatives with
  `L` and `inverse`, and the displayed isomorphism
  `derivedTensor X A K₁ K₂ P f hf hP ≅ proEtaleConstantComplex X A`.
  This is the recorded K-flat-resolution computation of
  `L ⊗ᴸ_{A_X} inverse`; all resolution data are existentially supplied rather than
  chosen from a mere existence theorem.
* `IsProEtaleInvertible` is the existence of that chosen inverse data, and its
  finite-level specialization is exactly the node's pro-etale definition.
  `IsEtaleInvertible` uses the existing etale derived tensor bifunctor and asserts
  the same chosen inverse and one displayed tensor-unit isomorphism.  Its finite-level
  specialization is the node's etale definition.  No second inverse isomorphism,
  boundedness, constructibility, connectedness, or nonzero-object hypothesis is added.

The dependency declarations used are:

* `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`;
* `Sheaf.Algebra.Homology.DerivedTensor`,
  `AlgebraicGeometry.Scheme.derivedTensor`;
* `Sheaf.Algebra.Homology.KFlatResolutionGeneral`,
  `CochainComplex.exists_isKFlatResolutionGeneral`;
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
  `Padic.coefficientExtensionRing`;
* `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.Etale`;
* `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`;
* `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`,
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and
  `AlgebraicGeometry.Etale.constantComplex`;
* `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor`.

Edge cases checked: `n = 1` leaves the quotient coefficient ring and degree-zero
constant complex well-defined; the empty scheme and disconnected schemes impose no
extra condition; the zero object on a nonempty site cannot satisfy the displayed
isomorphism, while the unit object can; and no connectedness, finiteness of `X`, or
invertibility of `l` on `X` is silently assumed.  The inverse is one chosen object
and one displayed isomorphism exactly as in the source.

Existing-definition searches:

* `msearch.py ... leanfinder "tensor-invertible object in a derived category with a
  chosen inverse and isomorphism to the tensor unit"`: eight hits, all generic
  homological tensor-unit or localization declarations; no matching definition.
* `msearch.py ... loogle "IsInvertible, TensorInvertibleData, derivedTensor"`: zero
  hits; the service reported `IsInvertible` as unknown.
* `msearch.py ... grep "IsInvertible|TensorInvertibleData|proEtaleDerivedTensor"
  CategoryTheory/Monoidal`: zero hits.
* `rg` over the upstream `WeilConjectures/` and project `lean/Sheaf` found only
  unrelated ordinary-module, rigid-category, and etale two-sided predicates; no
  declaration for this two-site finite-level notion.  The stage-1 node's recorded
  searches (LeanFinder, LeanSearch, Loogle, and Mathlib/source greps) likewise found
  no exact match.

The module compiles cleanly with `scompile.py`; no warnings remain beyond the
expected declaration-sorry warning (there are no sorry declarations in this
definition module).


## Earlier second reading (a previous round; superseded)

I independently reread the node, the source definition, and the compiled module. The finite-level
pro-etale declaration binds the prime, finite extension, positive level, scheme, coefficient ring,
and object exactly as stated. Its chosen-data structure makes the K-flat first-factor resolution
explicit and supplies the single displayed isomorphism to the degree-zero constant sheaf; this
introduces no extra geometric or boundedness hypothesis. The etale declaration uses the existing
derived tensor and constant complex with the standard ULift coefficient encoding. The generic helper
declarations are implementation interfaces for those two clauses, and all declarations carry the
blueprint identifier in their module or docstrings. No mismatch was found.

## Second reading by Q35

I read the node copy, the exact blueprint source
`literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-coprojection/pur9-cs-def-invertible.md`
(order 2349), and the dependency nodes and their recorded declarations. This source is a
blueprint definition, not a Stacks tag. The definition introduces exactly the triple and
existence condition, with the same definition on the etale site.

Clause-by-clause list and verdict:

* Objects and hypotheses: `l : ℕ`, `[Fact l.Prime]`, `E : Type u`, `[Field E]`,
  `[Algebra (Padic l) E]`, `[FiniteDimensional (Padic l) E]`, `n : ℕ`, `_hn : 1 ≤ n`,
  and `X : Scheme.{u}` in both `IsProEtaleInvertibleAtLevel` and
  `IsEtaleInvertibleAtLevel`. These give the prime, finite extension, positive level,
  and arbitrary scheme with no extra geometric hypotheses. Verdict: exact.
* Coefficient ring: `Padic.coefficientExtensionRing l E n` is the recorded quotient
  of `Padic.coefficientExtensionIntegers l E` by the nth power of the ideal generated
  by `Padic.coefficientExtensionUniformizer l E`. I opened those constructions in
  `CoefficientExtension.lean` and the finiteness interface in
  `CoefficientExtensionFinite.lean`. Verdict: the node's chosen coefficient datum,
  not a different finite ring or a residue-field specialization.
* Pro-etale site and unbounded category: `proEtaleDerivedCategory X A`, and the
  definitionally matching `proEtaleComplex X A` and `proEtaleQuotient X A`.
  I opened `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: it uses
  `ProEt.topology X`, the intrinsic constant-ring `SheafOfModules` category, and
  `HasDerivedCategory.standard`. Site object universe is `u+1`, morphism universe
  is `u`, coefficient and module values are canonically lifted to `u+1`.
  Verdict: same recorded category and size convention.
* Constant coefficient sheaf in degree zero: `proEtaleConstantComplex X A` forms
  the recorded `constantSheaf` in commutative rings, forgets to rings, uses its
  unit module, and applies the single complex at 0 and the localization functor.
  On the etale side the final file directly uses the existing
  `AlgebraicGeometry.Etale.constantComplex Λ X`, whose source identifies it as the
  derived tensor unit and constant coefficient complex. Verdict: exact.
* Pro-etale chosen inverse triple: `L` is a parameter of
  `Scheme.ProEtaleInvertibleData X A L`, `inverse` is `L'`, and `iso` is the one
  displayed isomorphism to `proEtaleConstantComplex`. Fields `K₁`, `K₂`, `P`, `f`,
  `hP`, `hf`, `iso₁`, and `iso₂` expose the representatives and K-flat first-factor
  resolution required by the recorded `Scheme.derivedTensor` interface. I opened
  that definition: it is `Q(P tensor K₂)` with the signed total tensor complex.
  These are presentation data, not boundedness or constructibility assumptions.
  Verdict: the specified derived tensor and single evaluation isomorphism.
* Pro-etale existence condition: `IsProEtaleInvertible` is precisely
  `Nonempty (ProEtaleInvertibleData X A L)` and the finite-level wrapper specializes
  it. The inverse, representatives and displayed isomorphisms are all under this
  existential, after `L`. Verdict: correct quantifier order.
* Etale category and tensor: `DerivedCategoryModule Λ X` is the recorded
  `DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u+1} Λ))`, read in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`. `etaleDerivedTensor`
  applies the recorded `AlgebraicGeometry.Etale.derivedTensor` bifunctor to `L,M`.
  I opened `Derived.Tensor`: it is the unbounded K-flat-derived monoidal tensor.
  Verdict: the recorded etale category and construction, using its standard ULift
  of the finite coefficient ring, not another site or bounded subcategory.
* Etale chosen inverse and existence: `TensorInvertibleData` has fields `inverse`
  and `iso`, with `L` fixed; its total family is the chosen triple. `IsEtaleInvertible`
  specializes `IsTensorInvertible`, the `Nonempty` of this family, to the etale
  tensor and existing constant complex. `IsEtaleInvertibleAtLevel` supplies the
  exact finite coefficient specialization. Verdict: both clauses are present;
  no second evaluation isomorphism is required.

Edge cases: there is no index family. Empty and disconnected schemes are admitted;
there is no nonempty, connected, finite-type, Noetherian or separated assumption.
The zero object is not excluded by a binder: it can satisfy the predicate exactly
when its tensor is isomorphic to the unit (in particular in the degenerate empty-site
case). The tensor unit and its shifts are covered. Level 1 is included; level 0 is
excluded only by the source's explicit positivity hypothesis. No condition on the
characteristic of X or invertibility of l on X has been added. Universes are bound
and the larger site-value universe is retained; there is no new equality of site
object and morphism universes. The finite extension and scheme share the recorded
coefficient/site size convention; the general predicates retain every object of
those recorded categories.

Independent duplicate searches used different words as well as direct names:

* `msearch.py ... leanfinder "Picard groupoid objects in a monoidal category admitting
  an inverse under tensor product"`: eight hits, including `RigidCategory`, `Center`,
  and `CommRing.Pic`, none gives these two site-specific chosen triples.
* `msearch.py ... loogle '"Pic"'`: twelve unrelated pick/pickle/PiBase hits.
* `msearch.py ... grep "TensorInvertible|HasTensorInverse|InvertibleObject|Picard"
  CategoryTheory`: one comment referring to the ordinary-module Picard group.
* Direct `rg` searches of Mathlib/CategoryTheory, upstream WeilConjectures, and
  the project's lean/Sheaf covered those terms and `isInvertible|IsInvertible`.
  I opened the upstream etale `DerivedCategory.isInvertible`: it asks for two
  displayed isomorphisms, not the source's one-isomorphism chosen data; it also
  does not give the pro-etale clause. Ordinary locally free rank-one module and
  scheme-module predicates are different categories. No exact existing declaration
  replaces this node.

Mismatches repaired: H8, most helper docstrings had neither the exact source place
nor the required blueprint identifier, and the remaining docstrings gave only the
identifier. Every retained declaration now has both. H4, the `etaleConstantComplex`
wrapper repeated the existing `Etale.constantComplex` verbatim; I removed the wrapper,
used the existing declaration directly, and removed its name from `lean.declarations`.
H9, removed the unused `KFlatResolution` and `KFlatResolutionGeneral` imports: the
module asserts no existence theorem and needs no choice of resolutions. No Lean
signature or mathematical definition was weakened, and no node statement was
corrected. There are no new nodes, dependency modules, postponed theorem proofs,
or hollow definitions.

Validation: all declarations were checked for bound variables and universes and
all lines are at most 100 characters. The node's `lean.statement` remains verbatim
the main signature. The single delivered module compiled cleanly through
`scompile.py Q35 pur9-cs-def-invertible lean/Sheaf/Paper/Pur9Invertible.lean`, with
no errors or warnings. The final file supersedes the wrapper and import inventory
in the earlier worker report.

## Worker report

The delivery states `AlgebraicGeometry.Etale.isIso_projectionMap_finiteConstant_of_preservesCountableCoproducts`
in `Sheaf.AlgebraicGeometry.ExceptionalConstantTensor`. Its sole proof is `sorry`.
No definition, additional theorem, dependency record, natural-language statement,
or statement dependency is changed. No statement dispute was found.

The previous worker's diagnosis confused stages: NJ's merged work is the reviewed
stage-1 split. The current node has no `lean` or `reviewed_lean` record. This delivery
supplies the missing stage-2 statement instead of resubmitting that unchanged split.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The finite commutative ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  There is no nonzero-ring, characteristic, invertibility, or Noetherian hypothesis.
- The schemes are `{U T : Scheme.{u}}`; the open immersion is
  `(j : U ⟶ T) [IsOpenImmersion j]`.
- The size convention is the explicit universe `u`, the ordinary small etale sites
  `U.smallEtaleTopology` and `T.smallEtaleTopology`, and coefficients and module
  carriers in `Type (u + 1)`. This is exactly the recorded six-functor encoding of
  `def-weil-pbc-derived-categories`; no additional equality between site object
  and morphism universes is imposed. A finite coefficient ring or module can be
  represented at this size without restricting its isomorphism class.
- The ordinary unbounded category is `DerivedCategoryModule A U` for `K`.
  There is no bounded-above, bounded-below, constructibility, flatness, perfectness,
  finite Tor amplitude, or finite projective dimension assumption.
- `Rj_*` is `(lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor`.
  `lowerStar` is the canonical etale sheaf direct image, and its existing total
  right derived functor is the unbounded K-injective derived direct image.
- Countable coproduct preservation is exactly
  `[PreservesColimitsOfShape (Discrete ℕ)
    (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor]`.
  This requires no preservation of arbitrary coproducts. Enumerating a countable
  index set reduces its coproducts to this shape (and summands may be zero).
- The arbitrary derived object is `(K : DerivedCategoryModule A U)` and the finite
  module is `(N : ModuleCat.{u + 1} A) [Finite N]`. `Finite N` means finite underlying
  set, as the node explicitly requests, rather than just finite presentation.
- `N_T` is `((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N)`:
  the sheafification of the constant presheaf. Applying
  `(_root_.DerivedCategory.singleFunctor _ 0).obj` places it in degree zero.
- The displayed canonical map is
  `((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app K).app (N_T[0])`.
  By the defining bifunctors its source is precisely
  `((derivedTensor (ModuleCat.{u + 1} A) T).obj (Rj_*.obj K)).obj (N_T[0])`;
  its target is `Rj_*.obj (((derivedTensor (ModuleCat.{u + 1} A) U).obj K).obj
  (Lj^*.obj (N_T[0])))`. The existing `leftDerivedUpperStarIsoMapDerivedCategory`
  identifies `Lj^*` with the exact termwise inverse image, and
  `singleFunctorCompLeftDerivedUpperStarIso` followed by
  `Scheme.upperStarConstantSheafIso` identifies the last argument with `N_U[0]`.
  This is the node's explicit last sentence: state invertibility of `PF_j(K,N_T)`
  under this canonical identification. It neither picks an arbitrary comparison
  nor asserts existence of an unspecified isomorphism. Postcomposing by that
  canonical target isomorphism preserves and reflects `IsIso`.
- The conclusion is `IsIso` of that very canonical morphism, exactly the assertion
  that the displayed tensor comparison is an isomorphism. All tensors are the
  recorded uncompleted K-flat derived tensor bifunctors.

Recorded statement dependency declarations used (their complete signatures and
source docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (`def-pc-scheme`), imported through the etale framework.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`
  (`def-weil-open-immersion`).
- `def-weil-size-convention` is a recorded metatheoretic convention, with no module
  or declaration; its content is represented by explicit universe annotations.
- `Sheaf.AlgebraicGeometry.DerivedCategories`: the recorded
  `AlgebraicGeometry.Etale.DerivedCategoryModule` from
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
  (`def-weil-pbc-derived-categories`).
- `WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection`:
  `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap`, with its
  `rightDerivedLowerStarProjectionMap_app_app` and
  `homEquiv_symm_rightDerivedLowerStarProjectionMap` descriptions
  (`def-kun-projection-formula-map`). `FlatModuleCat` supplies the existing
  `upperStarPreservesFlat_moduleCat` instance, without a new hypothesis.
- `Mathlib.Algebra.Homology.Additive`:
  `CategoryTheory.Functor.mapHomologicalComplex` (`def-kun-constant-sheaf`).
  The degree-zero specialization uses `CategoryTheory.constantSheaf` from
  `Mathlib.CategoryTheory.Sites.ConstantSheaf` and `DerivedCategory.singleFunctor`.
  It agrees with the termwise constant-complex construction in that record.
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`:
  `AlgebraicGeometry.Etale.derivedTensor` (`def-kun-derived-tensor`), used by the
  existing projection map's source and target, imported through its recorded module.

The already stated proof dependencies are imported without `public` (except the
ones that are also statement dependencies): constant-module pullback, exact etale
module inverse image, sheafification, the exact projection mate, short-exact-sequence
triangles, the complex-colimit telescope, and derived-tensor direct sums. The triangle
isomorphism and left-adjoint-colimit Mathlib interfaces are already available through
these imports. No unstated proof prerequisite is restated in the delivery.
The theorem docstring records all eight steps of the node's proof, including the
canonical connecting square in the telescope argument and augmentation naturality.

Edge cases checked before writing:

- The zero ring is allowed; all its modules, and the comparison, are zero.
- The zero module, zero `K`, and the empty source or target scheme are included.
  There is no `Nonempty`, nontriviality, or quasi-compactness binder.
- Identity open immersions are included; the mate becomes the tensor comparison for
  the identity derived adjunction.
- Modules of infinite projective dimension over a finite ring, e.g. the residue field
  over `Z/4Z`, remain included: no dualizability or perfectness hypothesis is imposed.
- Arbitrarily unbounded `K` is included. The proof uses countably many finite brutal
  truncations, with the `m = 0` case a finite free module in degree zero.
- Countability concerns the coproduct shape `Discrete ℕ`, not the sequential-colimit
  shape `ℕ`. No assumption of preservation of filtered or arbitrary colimits is added.

Searches made (the launcher tools also saved their exact results in `searches.jsonl`):

- `msearch.py`, LeanFinder: "For an open immersion with countable coproduct preserving
  derived direct image, the projection formula for a finite constant module is an
  isomorphism". Eight hits about ordinary scheme restriction/open-immersion functors;
  none is the unbounded derived finite-constant comparison.
- `msearch.py`, Loogle: `rightDerivedLowerStarProjectionMap, PreservesColimitsOfShape`.
  Zero hits; the project-specific projection-map identifier is unknown to Loogle.
- `msearch.py`, grep in Mathlib CategoryTheory:
  `constant.*[Pp]rojection|[Pp]rojection.*constant`. Zero hits.
- `msearch.py`, LeanSearch: "Projection formula for a finite constant module when
  unbounded derived direct image preserves countable coproducts". Eight hits on module
  products, countable AB4*, module-sheaf finite limits, and projective resolutions;
  no matching theorem.
- `rg` in upstream `WeilConjectures` and project `lean/Sheaf`:
  `constant.*[Tt]ensor|constantTensor|constant_tensor`, then
  `rightDerivedLowerStar.*Projection`, countable-coproduct signatures, and
  constant-sheaf/single-functor expressions. No exact existing statement found.
- `rg` for `lem-exc-constant-tensor` in upstream `WeilConjectures`: no hits.
- Read `Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula`: its theorem
  `isIso_finiteConstantProjectionMap` assumes a uniform cohomological dimension bound
  and bounded-above `K`, with Noetherian coefficients and a finitely presented module.
  It is a different statement, so it is not re-recorded as this node.
- Read upstream `Derived.ProjectionFormula`: the dualizable-object theorem requires
  dualizability, and the finite-coefficient theorem requires a proper morphism.
  Neither states this open-immersion/countable-coproduct assertion.

Validation: the prescribed `scompile.py ND lem-exc-constant-tensor` compiled the
sandbox file and its library-module form cleanly (3.3 s and 2.5 s). Only the expected
`sorry` is present. The file sets `autoImplicit false`, binds its universe explicitly,
and contains no file-local notation, private declaration, or local instance.

## Second reading by ND

I independently read the sandbox node and module, the blueprint source
`sec-smooth-purity/sk-prop-a1-kummer/lem-exc-constant-tensor.md`, all seven statement
dependency records, and the declarations they designate. The source has no standing
Noetherian, quasi-compactness, separatedness, boundedness, constructibility, perfectness,
or finite-projective-dimension assumption. Its use of Noetherianity in the proof follows
from finiteness of the coefficient ring. The node explicitly specifies commutative
coefficients, as required by its derived-tensor dependency. I also read the Stacks
passages defining the canonical projection map (sites-cohomology.tex,
`equation-projection-formula-map`, Tag 0B56), its finite-complex argument
(`lemma-projection-formula`, Tag 0944), constant sheaves and their exactness
(sites-modules.tex, `section-constant`, Tag 093I), inverse image of locally constant
modules (`lemma-pullback-locally-constant`, Tag 093R), and the sequential telescope
(derived.tex, `lemma-colim-hocolim`, Tag 0949). These impose no additional hypothesis
on this node; in particular the perfectness assumption in Tag 0944 belongs to that
lemma's conclusion and is not an assumption on the present countable-telescope result.

The independent list of objects, hypotheses, and conclusion clauses, matched to Lean:

- Finite commutative coefficient ring: `(A : Type (u + 1)) [CommRing A] [Finite A]`.
  Verdict: exact; neither a field nor a nontrivial ring is required.
- Schemes and open immersion: `{U T : Scheme.{u}} (j : U ⟶ T)
  [IsOpenImmersion j]`. I opened Mathlib's `Scheme` structure and `IsOpenImmersion`
  abbreviation: they are respectively the locally affine locally ringed space and
  open immersion of locally ringed spaces recorded by the two dependency nodes.
  Verdict: exact, with no extra geometric condition.
- Small etale sites and ordinary unbounded categories: `DerivedCategoryModule A U`
  expands, in `Derived.Coefficients`, to
  `DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))`.
  The target uses the same encoding on `T`. I read the recorded
  `Sheaf.AlgebraicGeometry.DerivedCategories` module as well. The explicit `u` and
  `u + 1` implement the recorded size convention and existing dependency interface;
  no site object/morphism universe equality is added. Verdict: exact.
- Unbounded K-injective direct image and its inverse-image adjunction:
  `(lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor`. The upstream
  `Derived.UpperLowerStar` declarations give this unbounded right derived functor and
  `derivedUpperStarLowerStarAdjunction`; `leftDerivedUpperStarIsoMapDerivedCategory`
  identifies its left adjoint with the exact inverse image on complexes.
  Verdict: the specified functors, not a bounded-category substitute.
- Countable coproduct hypothesis:
  `[PreservesColimitsOfShape (Discrete ℕ)
    (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor]`.
  This is preservation of countable sums, not sequential colimits. Sums on smaller
  countable index sets are obtained by reindexing and padding with zero objects;
  the derived direct image is additive and preserves zero. Verdict: exact.
- Every unbounded derived object and finite module:
  `(K : DerivedCategoryModule A U) (N : ModuleCat.{u + 1} A) [Finite N]`.
  `Finite N` concerns its underlying set. The preservation hypothesis precedes both
  objects, just as in the node. There is no flatness, projectivity, or amplitude
  condition on either object. Verdict: exact.
- Constant module on the target in degree zero:
  `(_root_.DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N)`.
  I opened `constantSheaf`: its data is `Functor.const ⋙ presheafToSheaf`.
  `singleFunctor` puts that sheaf in degree zero, and the recorded
  `Functor.mapHomologicalComplex` is its termwise complex version.
  Verdict: exactly `N_T[0]`, not a constant presheaf or a derived coefficient object
  with unspecified realization.
- Ordinary derived tensors and the actual comparison:
  `((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app K).app (N_T[0])`.
  I read both defining bifunctors and the projection map in `Derived.LowerStarProjection`.
  Their source is `Rj_*K tensor^L N_T[0]` and their target is
  `Rj_*(K tensor^L Lj^*(N_T[0]))`. The map is the adjunction mate of the pullback
  tensor comparison followed by tensoring the counit with the identity, agreeing
  with Tag 0B56. `Derived.Tensor.derivedTensor` is `curriedTensor` on the ordinary
  K-flat derived category. The global `upperStarPreservesFlat_moduleCat` instance
  supplies the needed flat-pullback interface for every commutative ring.
  Verdict: the recorded uncompleted derived tensor and canonical map, with no
  additional instance hypothesis.
- Canonical identification with the source constant module: I opened
  `singleFunctorCompLeftDerivedUpperStarIso` and `Scheme.upperStarConstantSheafIso`.
  Evaluating the former on `N_T` and then applying the degree-zero functor to the
  latter at `N` gives `Lj^*(N_T[0]) ≅ N_U[0]`. Applying tensor with `K` and then
  `Rj_*` gives precisely the target identification allowed in the node's final
  sentence. Verdict: exact; the conclusion need not replace this canonical mate
  by a separately defined postcomposition.
- Isomorphism assertion: `IsIso` of that specific component. Verdict: the entire
  conclusion, not existence of some isomorphism between its endpoints.

Edge cases: zero rings of characteristic one, arbitrary finite-ring characteristics,
zero modules, zero `K`, empty source or target schemes, and identity immersions are
all admitted by the binders. A module has a zero element, so an empty coefficient
module carrier is not a missing mathematical case. No finiteness condition is put
on the schemes. Infinite projective dimension (for example the residue module over
`Z/4Z`) and arbitrary unbounded `K` remain allowed. There is no finite-resolution
length or positive truncation parameter in the signature; proof step 4 includes
the base truncation `m = 0`. Empty and finite coproducts follow from additivity;
the assumption addresses the countably infinite case. The coefficient and module
universe is the one recorded for this six-functor encoding; finite carriers in
other universes have equivalent representatives here. No universe or variable
is unbound: `autoImplicit false` is set and `u` is explicitly declared.

Independent H4 searches (not only the first worker's recorded searches):

- `msearch.py ND lem-exc-constant-tensor leanfinder` with
  "A right derived sheaf direct image preserving countable sums commutes with derived
  tensor by a finite constant coefficient module": eight hits about monoidal
  structures on light condensed sheaves and general sheaf categories; no theorem
  about this derived direct image.
- `msearch.py ... leansearch` with
  "If Rj_* commutes with countable direct sums then the canonical map from Rj_*K
  tensor N to Rj_*(K tensor j* N) is an isomorphism for finite constant N": eight
  ordinary tensor/direct-sum or direct-limit identities; no matching statement.
- `msearch.py ... loogle` with `PreservesColimitsOfShape, IsIso` rejected the
  first identifier, so that query is not evidence of absence. The replacement
  `"IsIso", "tensor"` returned five generic monoidal tensor-isomorphism,
  distributivity, reflective-monoidal, and sifted-colimit facts; none matches.
- Independent `rg` across Mathlib's CategoryTheory and Algebra/Homology,
  upstream `WeilConjectures/SixFunctors`, project `lean/Sheaf/AlgebraicGeometry`,
  and the upstream-name inventory, using `preserves.*[Cc]ountable`,
  `countable.*[Pp]rojection`, `finiteConstant`, and `finite_constant`, found no
  exact existing theorem. I read `FiniteConstantProjectionFormula.lean`:
  `isIso_finiteConstantProjectionMap` assumes a uniform cohomological-dimension
  bound and bounded-above `K`, and so cannot serve this node. Its canonical-map
  definition uses exactly the two target-identification isomorphisms checked above.
  The upstream proper projection theorem requires properness, and the dualizable
  theorem requires dualizability; neither states this result.

No new definition nodes or dependency modules occur in this delivery, and there is
no `statement_change`. Comparison with the shared base found only the item's
`lean` record changed. The module contains no definitions or other theorem:
the named theorem has exactly one `sorry`, and its source/blueprint docstring
records all eight proof steps, including augmentation naturality and the actual
connecting square in the telescope argument. Imports retain the available proof
dependencies. There is no hollow definition, private copy, local notation, local
instance, or proved lemma. Every Lean line is at most 100 characters, and a direct
text comparison confirms that `lean.statement` is verbatim the signature before
`:= by`.

Mismatches found: none. I preserved the correct Lean module and node record and
added this independent second reading. The prescribed `scompile.py` compiled both
the sandbox and library-module forms cleanly (2.2 s and 2.4 s), with no errors or
unexpected warnings.

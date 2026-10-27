## Worker report

Existing attachment; no new module or theorem. Read the full item, its six proof steps,
all five statement-dependency nodes, their recorded declarations and docstrings, and the
source modules `WeilConjectures.WeilSheaf.LowerShriek` and
`WeilConjectures.WeilSheaf.Category`. The four existing declarations recorded in
`lean.declarations` jointly express the node. The primary signature is copied verbatim
from the theorem keyword up to its `:=` in `LowerShriek.lean`.

Hypotheses and clauses:

- A finite field is `{k₀ : Type u} [Field k₀] [Finite k₀]`; the coefficient prime and
  characteristic restriction are `{l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]`.
  Coefficients are the framework's `PadicAlgCl l`; this attachment uses that exact
  framework, its pro-etale module sheaves and Frobenius-equivariant derived categories.
- The two schemes are `{X Y : Scheme.{u}}` with their respective
  `[X.Over (Spec (CommRingCat.of k₀))]` and
  `[Y.Over (Spec (CommRingCat.of k₀))]`. The morphism is `(f : X ⟶ Y)` with
  `[f.IsOver (Spec (CommRingCat.of k₀))]`.
- Separated, quasi-compact, locally finite type are respectively `[IsSeparated f]`,
  `[QuasiCompact f]`, `[LocallyOfFiniteType f]` in the restricted functor and its
  shift/triangulated instances. The target hypotheses are
  `[QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]`,
  `[QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]`, and
  `[LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]`.
  Over the affine field spectrum the first two are equivalent to the absolute
  quasi-compactness and quasi-separatedness required in the statement. No absolute
  separatedness of either scheme is assumed.
- Ambient preservation is
  `AlgebraicGeometry.WeilComplex.objectProperty_rightDerivedLowerShriek`
  (`WeilConjectures.WeilSheaf.LowerShriek`, lines 115–142): for an arbitrary
  `K : DerivedCategory (ProEtaleWeilSheaf k₀ l X)`, the hypothesis
  `WeilComplex.objectProperty k₀ l X K` implies the same property on its actual
  `ProEtaleWeilSheaf.rightDerivedLowerShriek` image. `objectProperty` is literally
  `DerivedCategory.TStructure.t.bounded ⊓ DerivedCategory.homologyProperty
  (WeilSheaf.objectProperty k₀ l X)`, and the latter property forgets Frobenius
  to the framework's constructible sheaves. Thus both boundedness and constructibility
  in every degree occur in the conclusion. The theorem's `[HasCompactification f]`
  is supplied by `hasCompactification_of_over (k₀ := k₀) f`, using the stated
  geometric hypotheses. Its chosen compactification is exactly the one used by
  `WeilComplex.derivedLowerShriek`, not an arbitrary replacement operation.
- Inherited triangulation on each of X and Y is
  `AlgebraicGeometry.instIsTriangulatedWeilComplex`
  (`WeilConjectures.WeilSheaf.Category`, lines 243–247). The preceding inherited
  `Pretriangulated` instance, shift and additive-shift instances are those of
  `(WeilComplex.objectProperty k₀ l X).FullSubcategory`. Its distinguished triangles
  are the inverse image of ambient distinguished triangles under the full inclusion
  (`Mathlib.CategoryTheory.Triangulated.Subcategory`, line 694).
- The source-local-finite-type instance needed for triangulation follows from the
  original assumptions, without adding a hypothesis: rewrite its structure map by
  `← comp_over f (Spec (CommRingCat.of k₀))` and apply the locally-finite-type
  composition instance. The server probe checked this derivation and then synthesized
  both category-triangulation instances and the restricted functor instance.
- The restricted functor is the framework's `WeilComplex.derivedLowerShriek k₀ l f`.
  Its canonical shift comparison is
  `AlgebraicGeometry.instCommShiftWeilComplexDerivedLowerShriekInt`
  (`WeilConjectures.WeilSheaf.LowerShriek`, lines 201–207), constructed by
  `ObjectProperty.commShiftLiftFullSubcategory` from the actual ambient composite's
  shift comparison. For `F := WeilComplex.derivedLowerShriek k₀ l f`, the required
  component is `(F.commShiftIso (1 : ℤ)).app L`.
- Triangle preservation is
  `AlgebraicGeometry.instIsTriangulatedWeilComplexDerivedLowerShriek`
  (`WeilConjectures.WeilSheaf.LowerShriek`, lines 210–217). This is the
  `ObjectProperty.isTriangulated_liftFullSubcategory` instance for the same ambient
  composite. `Functor.IsTriangulated.map_distinguished` asserts precisely that
  `F.mapTriangle.obj T` is distinguished whenever T is. The third arrow of that
  triangle is definitionally
  `F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁`
  (`Mathlib.CategoryTheory.Triangulated.Functor`, lines 42–44), so the last-arrow
  requirement is included, with the specified comparison.

Dependency declarations used:

- `def-sf-native-weil-derived-framework`:
  `WeilConjectures.WeilSheaf.LowerShriek`,
  `AlgebraicGeometry.WeilComplex.derivedLowerShriek`, its actual ambient
  `ProEtaleWeilSheaf.rightDerivedLowerShriek`, and the publicly imported
  `WeilComplex`, `WeilComplex.objectProperty`, `WeilSheaf.objectProperty` and
  `ProEtaleWeilSheaf` from `WeilConjectures.WeilSheaf.Category`.
  Also read the recorded coefficient/constructibility definitions in
  `SixFunctors.ProEtale.Adic.ConstantSheaf`, `.Module`, `.Constructible` and the
  inverse/direct/open-extension operations in `WeilSheaf.Category`, `.LowerStar`,
  `.OpenImmersion`. The finite rank is allowed to depend on the covering member:
  `IsAdicLisseSheaf` quantifies over the covering arrow before `∃ n : ℕ`.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`, `IsSeparated`, `UniversallyClosed`; properness
  belongs to the chosen compactification's proper leg, while f is only separated.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`,
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`.
- `def-weil-triangulated-category` (Mathlib match):
  `Mathlib.CategoryTheory.Triangulated.Pretriangulated`, `CategoryTheory.Pretriangulated`;
  `.Triangulated`, `CategoryTheory.IsTriangulated`; `.Functor`,
  `CategoryTheory.Functor.IsTriangulated`; and `Functor.CommShift` with its canonical
  coherent comparison. These are the classes used by the recorded native instances.
- `def-weil-quasi-separated-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`, `AlgebraicGeometry.QuasiSeparated`.

No missing notion or unusable dependency interface was found. No statement correction,
new node, dependency module, or disputed statement is needed. This records existing
statements; it does not claim their transitive axioms have been eliminated. In particular,
the source-place phrase about proofs being present is not an assertion that all of their
prerequisites are sorry-free. The existing declarations are reused rather than restated.

Edge cases checked against the definitions and hypotheses: the zero complex and empty
scheme/open are included; boundedness permits zero cohomology in every degree and
constructibility allows rank zero (`Fin 0`). Identity morphisms meet the same geometry.
No cohomological degree or shift is excluded, and all integer shifts are supplied by
CommShift. The unbounded-dimension disjoint union of projective spaces over a disjoint
union of field spectra is excluded by the necessary target quasi-compactness, which was
retained. No additional source separatedness, source properness, constant rank across
covering members, or Frobenius splitting is imposed. Universes use exactly the native
framework's common scheme/field universe u, with larger sheaf/derived universes inferred
by its existing definitions, without introducing a new size restriction.

Searches made on 2026-10-22:

- `msearch.py ... leanfinder`: “compactly supported direct image preserves bounded
  constructible Weil complexes and is triangulated”; eight hits including
  `HomologicalComplex.map_isStrictlySupported`, constructible-image topology results,
  and generic triangulated-functor facts. No native Weil specialization in Mathlib.
- `msearch.py ... loogle '"IsTriangulated"'`: twelve hits including the category and
  functor classes; supplies the generic meanings, not the native finiteness theorem.
- `msearch.py ... leansearch`: “derived direct image with compact support Weil sheaves
  triangulated functor”; eight generic site/derived-functor hits, no native match.
- `msearch.py ... grep 'rightDerivedLowerShriek|WeilComplex'`: zero Mathlib hits.
- `rg -n 'lem-sf-native-weil-shriek-triangulated' lean/WeilConjectures`: no label hit.
  Searching `objectProperty_rightDerivedLowerShriek` and reading
  `lean/WeilConjectures/WeilSheaf/LowerShriek.lean` finds the exact native theorem at
  line 115 and all restricted-functor instances at lines 201–217. Reading
  `WeilSheaf/Category.lean` finds the inherited triangulation at lines 217–247.
- `rg` for `objectProperty_rightDerivedLowerShriek`, triangulated derivedLowerShriek,
  and native-shriek terminology under `lean/Sheaf`: no competing statement found.

Validation: module-mode scratch probe `ExistingChecks.lean` was compiled by the prescribed
`scompile.py ND lem-sf-native-weil-shriek-triangulated .../ExistingChecks.lean` against the
live published library. Final probe passed both sandbox and library compilation with no
errors or warnings. It checked all four fully qualified declaration names and the
specialization under exactly the node's geometric assumptions. The scratch probe is
outside `lean/` and is not delivered. The delivery wrapper also independently checks all
four existing declarations and runs the maintainer's preflight.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

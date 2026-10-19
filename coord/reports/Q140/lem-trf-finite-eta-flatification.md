## Worker report

The module `Sheaf.TraceFormula.FiniteEtaFlatification` states
`AlgebraicGeometry.exists_finite_eta_flatification`, with proof `sorry` only. It
uses the canonical `Scheme.fromSpecFunctionField` map and canonical pullback
maps. The theorem binds schemes `S` and `X` in one universe, assumes an
integral, quasi-compact, quasi-separated base (`[IsIntegral S]`,
`[CompactSpace S]`, `[QuasiSeparatedSpace S]`), and assumes that `f : X ⟶ S`
is dominant, locally of finite presentation, quasi-compact, and
quasi-separated (`[IsDominant f]`, `[LocallyOfFinitePresentation f]`,
`[QuasiCompact f]`, `[QuasiSeparated f]`). These four classes render the
node's dominant finitely presented hypothesis, while the two space classes
render the node's qcqs hypothesis.

The conclusion is rendered clause by clause as follows.

* `∃ (S₁ : Scheme.{u}) (b : S₁ ⟶ S), IsIntegral S₁` introduces the integral
  modified base.
* `IsProper b ∧ Surjective b` gives the proper surjective base morphism.
* `IsIso (pullback.snd b S.fromSpecFunctionField)` says that the base change
  over the generic point `S.fromSpecFunctionField : Spec S.functionField ⟶ S`
  has projection to `Spec S.functionField` an isomorphism, i.e. its generic
  fibre is `Spec K` for `K = S.functionField`.
* `∃ (X₁ : Scheme.{u}) (a : X₁ ⟶ pullback f b), IsFinite a` introduces the
  finite morphism to the canonical base change `X ×_S S₁`. `IsFinite` is the
  finite part of the recorded finite/integral-morphism notion.
* The following `IsIso (pullback.map ...)` is the actual generic-fibre map of
  `a`. Its source is the pullback of
  `a ≫ pullback.snd f b ≫ b` along the generic-point map, its target is the
  corresponding pullback of `pullback.snd f b ≫ b`, and the identity maps and
  the two `by simp` equations make it the canonical base-change map. Thus it
  renders `a_η` is an isomorphism.
* `∃ U₁ : (pullback f b).Opens` introduces the open in the base-change target.
  `IsIso (a ∣_ U₁)` says that `a` is an isomorphism over this open, and
  `SchematicallyDenseOpen (a ⁻¹ᵁ U₁)` says that its inverse-image open is
  schematically dense in `X₁` by injectivity of every restriction map.
* `Flat (a ≫ pullback.snd f b)` and
  `LocallyOfFinitePresentation (a ≫ pullback.snd f b)` state that
  `X₁ → S₁` is flat and finitely presented.
* `IsSchemeTheoreticallyDominant (pullback.fst
  (a ≫ pullback.snd f b ≫ b) S.fromSpecFunctionField)` states that the generic
  fibre morphism into `X₁` is scheme-theoretically dominant, which is the
  stated schematic density of the generic fibre (sections on opens are
  determined by their generic restrictions).

The statement dependencies and declarations used are:

* `def-pc-integral-scheme`: Mathlib `AlgebraicGeometry.IsIntegral` from
  `Mathlib.AlgebraicGeometry.Properties`.
* `def-sbc-locally-finite-presentation`: Mathlib
  `AlgebraicGeometry.LocallyOfFinitePresentation` from
  `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`.
* `def-sc-generic-point`: Mathlib `IsGenericPoint` from
  `Mathlib.Topology.Sober`; the canonical generic-point map is the upstream
  `AlgebraicGeometry.Scheme.fromSpecFunctionField` from
  `WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField`.
* `def-weil-proper-morphism`: Mathlib `AlgebraicGeometry.IsProper` (with its
  `IsSeparated` and `UniversallyClosed` declarations) from
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
* `def-weil-surjective-morphism`: Mathlib `AlgebraicGeometry.Surjective` from
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
* `def-weil-finite-integral-morphism`: Mathlib `AlgebraicGeometry.IsFinite` from
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.
* `def-pc-base-change`: upstream `AlgebraicGeometry.Scheme.Modules.moduleBaseChange`
  and its base-change conventions from
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`; the scheme fibre
  itself is Mathlib's `Limits.pullback`.
* `def-weil-flat-morphism`: Mathlib `AlgebraicGeometry.Flat` from
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`.
* `def-trf-schematically-dense-open`: landed
  `AlgebraicGeometry.SchematicallyDenseOpen` from
  `Sheaf.TraceFormula.SchematicallyDenseOpen`.
* `lem-sc-integral-function-field-affine-fraction`: Mathlib's
  `AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen` from
  `Mathlib.AlgebraicGeometry.FunctionField`; the theorem uses the associated
  `S.functionField` object and canonical generic-point map.

Edge cases checked before writing: the empty family of affine charts is covered
by the intrinsic `IsIntegral` and qcqs classes; no nonempty index type is
introduced. The zero polynomial and zero-generator cases remain in the finite
presentation notion. Empty schemes are excluded only where the node's integral
base hypothesis excludes them; `X` itself is otherwise unrestricted, so an
empty fibre is allowed. The generic point and function field are canonical for
an integral scheme, and no Noetherian, separated, or flatness hypothesis on
`X` or `f` was added. The generic-isomorphism map is a pullback map, rather than
an arbitrary isomorphism. The density predicate on `a ⁻¹ᵁ U₁` is only on the
flat source, and the generic-fibre density is expressed by the canonical
scheme-theoretic dominance predicate.

Searches for an existing declaration: `msearch.py Q140 lem-trf-finite-eta-flatification
leanfinder "A dominant finitely presented morphism admits a base modification and
finite eta modification whose source is flat finitely presented"` returned only
flatness and generic morphism-property declarations, with no flattening theorem;
`msearch.py ... loogle "AlgebraicGeometry.IsFinite, AlgebraicGeometry.Flat"`
returned no matching existence statement; `msearch.py ... grep
"strictTransform|flattening|blowup"` returned no hits in Mathlib's
AlgebraicGeometry; and `rg -n "flattening|finite eta|strict transform"` in
`WeilConjectures/` and `lean/Sheaf/` found no duplicate theorem. The recorded
node mathlib searches were also reviewed and all report no exact match.

## Second reading by Q140

I reread the node statement, its corrected split report, and the complete Lean
signature. The four morphism-property typeclass binders exactly render
"dominant and finitely presented" (locally finite presentation plus qcqs), and
`CompactSpace`/`QuasiSeparatedSpace` render the integral qcqs base without
introducing a Noetherian or separated assumption. The witnesses occur in the
same order as the node: integral `S₁`, proper surjective `b`, generic-fibre
isomorphism, finite `a`, generic-fibre isomorphism, target open `U₁`, source
schematic-density and open isomorphism, flat finite-presentation source map,
and generic-fibre schematic density. The pullback map has the canonical
identity comparison maps and no arbitrary choice. `IsIso (a ∣_ U₁)` is the
restriction of `a` to exactly `U₁`; `SchematicallyDenseOpen (a ⁻¹ᵁ U₁)` is on
its inverse image in `X₁`, matching the corrected source-side clause. The last
predicate is on the generic-fibre projection into `X₁`, so it does not assert
schematic density in the possibly nonflat target. No hypothesis or conclusion
from the node is omitted, strengthened, or weakened, and the only proof term is
`sorry`.

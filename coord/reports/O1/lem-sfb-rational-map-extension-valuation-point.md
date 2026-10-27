## Worker report

The module `Sheaf.AlgebraicGeometry.RationalMapExtensionValuationPoint` states
`AlgebraicGeometry.exists_extension_at_valuation_stalk`. Its only theorem has proof
`sorry`; it introduces no definitions, additional nodes, or dependency repairs.
The item's node is unchanged outside `lean`.

The previous worker's superseded-assignment diagnosis confused the completed stage-1
split with this stage-2 assignment. The live node is split and reviewed by Q36, but
has no `lean` record. This delivery states that already reviewed node without
re-splitting it or changing its mathematical statement.

Source read: `literature/stacks-project/morphisms.tex`, Tag 0BX7,
`lemma-extend-across`, statement and complete proof, lines 10424–10479.
The item is its integral Noetherian specialization. Density supplies closure at x;
the source's valuative lift, spreading, relative equalizer, and final gluing give
exactly the five steps already in the node, reproduced in the theorem docstring.

Hypothesis and conclusion correspondence:

- Schemes S, X, Y: `(S X Y : Scheme.{u})`, using the recorded scheme definition.
  The explicit universe `u` is arbitrary. All objects and universes are bound;
  `set_option autoImplicit false` also enforces this.
- X and Y over S: `(a : X ⟶ S) (b : Y ⟶ S)` are their specified structure maps.
  These encode exactly `Scheme.Over`'s data, without selecting a field base.
- Integral X: `[IsIntegral X]`. This includes nonemptiness, reducedness, and
  irreducibility; no extra integral or reduced hypothesis is placed on Y or S.
- Noetherian X: `[IsNoetherian X]`, whose fields are precisely
  `IsLocallyNoetherian X` and `CompactSpace X`, i.e. local Noetherianity and
  quasi-compactness as spelled out in the node.
- Proper Y → S: `[IsProper b]`. The existing Mathlib class gives relative
  separatedness, universally closedness, and local finite type; universally
  closedness also gives quasi-compactness, hence the stated finite type.
- Dense open U of X: `(U : X.Opens) (hU : Dense (U : Set X))`.
  `U.toScheme` is the restriction with its canonical open immersion `U.ι`.
- S-morphism f: `(f : U.toScheme ⟶ Y)` with
  `(hf : f ≫ b = U.ι ≫ a)` is precisely commutation with the structure maps.
- Point x with valuation local ring: `(x : X)` and
  `[ValuationRing (X.presheaf.stalk x)]`. Integrality supplies the stalk-domain
  instance from FunctionField. `ValuationRing.TFAE` identifies this recorded
  class with the fraction-field condition in the node; fields are allowed.
- Open extension domain containing U: `∃ (V : X.Opens) (hUV : U ≤ V)`.
  The whole original U is retained, with no shrinking of that domain.
- The domain contains x: the conjunct `x ∈ V`.
- Extension F: `∃ F : V.toScheme ⟶ Y`.
- F is an S-morphism: `F ≫ b = V.ι ≫ a`.
- F restricts to f: `X.homOfLE hUV ≫ F = f`, using Mathlib's canonical
  inclusion of open subschemes. No uniqueness or further conclusion is added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.Over`: `Scheme.Over`, `Scheme.Hom.IsOver`, and
  `Scheme.Hom.isOver_iff` (the explicit structure-map form used here).
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`;
  `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
  Mathlib's `Restrict` supplies `Scheme.Opens.toScheme`, `Scheme.Opens.ι`,
  its open-immersion instance, `Scheme.homOfLE` and `Scheme.homOfLE_ι`.
- `Mathlib.RingTheory.Valuation.ValuationRing`: `ValuationRing` and
  `ValuationRing.TFAE`, the dependency's recorded Mathlib match.
- `Mathlib.AlgebraicGeometry.FunctionField`: the integral-stalk `IsDomain`
  instance, required publicly to type the valuation-ring hypothesis;
  `germ_injective_of_isIntegral`, `stalkFunctionFieldAlgebra`, the `IsFractionRing`
  instance on the generic stalk, and `Scheme.functionField` are the recorded
  proof dependency's exact objects.
- The remaining proof dependencies are imported privately:
  `WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`
  (`Scheme.fromSpecStalk_affine_description`, `Scheme.fromSpecStalk_local_properties`);
  `Mathlib.AlgebraicGeometry.ValuativeCriterion`
  (`UniversallyClosed.eq_valuativeCriterion`);
  `Mathlib.AlgebraicGeometry.SpreadingOut`
  (`spread_out_of_isGermInjective'`);
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`
  (`ext_of_isDominant_of_isSeparated`);
  `Mathlib.AlgebraicGeometry.Gluing`
  (`Scheme.Cover.glueMorphisms`, `ι_glueMorphisms`, `hom_ext`).
  Sobriety for schemes and generic-point uniqueness are in Properties and Sober,
  already imported through these modules. Every recorded interface is usable.

Edge cases checked before writing:

- x already in U, including U = X: V = U and F = f is permitted.
- x the generic point, so its local ring is a field: `ValuationRing` allows fields;
  a dense open in integral X contains that point, and the same trivial extension applies.
- U empty: excluded by density and the nonemptiness already inherent in integral X,
  rather than an added nonemptiness hypothesis. Empty X is excluded by the node itself.
- S may be non-separated, non-reduced, or non-Noetherian. Only b is proper;
  no absolute separatedness of Y is imposed. The equalizer argument is relative.
- Only the chosen stalk is a valuation ring; no condition is made at other points.
- Arbitrary characteristic and arbitrary scheme universe are retained.

Searches actually run through `msearch.py` for this group and item:

1. LeanFinder: “A map from a dense open of an integral Noetherian scheme to a
   proper scheme over a base extends to an open containing a point with valuation stalk”.
   Eight hits: function-field rational maps, normalization dominance, and
   `PartialMap.ofFromSpecStalk`, `mem_domain_ofFromSpecStalk` and its stalk restriction.
   None gives an extension retaining the original full U from only a valuation hypothesis.
2. Loogle: `"ValuativeCriterion", "Existence"`. Nine hits, all valuative existence
   properties, their functoriality, or projective-spectrum valuative criteria.
   These give the local lift, not the open extension with the prescribed restriction.
3. Mathlib grep: `extend.*across|valuation.*stalk|stalk.*valuation|ofFromSpecStalk`
   in AlgebraicGeometry. Seven hits, in ValuativeCriterion, OrderOfVanishing,
   and Birational/RationalMap. The latter definitions were opened: they spread a
   supplied stalk morphism and do not state the complete item.
4. LeanSearch: “Extend a morphism from a dense open to a proper scheme across a
   point whose local ring is a valuation ring”. Eight hits: valuative criteria,
   dense-function extensions, and dominance of open inclusions; no exact match.
5. Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` by the node id,
   valuation/stalk extension words, proposed theorem name and module name.
   The node id occurs only in SurfaceRationalMapPointResolution's proof docstring;
   the proposed name and module do not occur. Other keyword hits concern different
   stalk/module extension constructions. No existing statement of this item was found.

Validation: the required `scompile.py O1 lem-sfb-rational-map-extension-valuation-point`
compiled this file both as a sandbox module and under its final library module name,
with exit status 0 and no warnings or errors (7.9 s and 6.3 s respectively).
No statement dispute or source fault was found.

## Second reading by O1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

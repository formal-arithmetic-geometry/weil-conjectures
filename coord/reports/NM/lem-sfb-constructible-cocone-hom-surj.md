## Worker report

Record the exact existing declaration
`AlgebraicGeometry.ProEtale.constructibleCocone_homSurj` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`.
No module is delivered: the one-definition-per-notion rule requires reuse.
The signature copied verbatim from the live source is:

```lean
theorem constructibleCocone_homSurj : (constructibleCocone X ℓ).HomSurj
```

Read the complete theorem docstring and its surrounding module documentation, the
constructible cocone definition, and the full signatures and docstrings of both
statement dependencies. Verified the current server source with
`scompile.py --source WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`.
The server source agrees with the read clone. The declaration already has a proof;
this delivery only attaches its statement and makes no claim that its transitive
proof dependencies are all closed.

Hypothesis and clause correspondence:

- A scheme X is the section parameter `(X : Scheme.{u})`, for arbitrary universe u.
- A prime ℓ is `(ℓ : ℕ) [Fact ℓ.Prime]`.
- Noetherianity of the underlying topological space is the section instance
  `[TopologicalSpace.NoetherianSpace X]` in `section TwoColimit`.
  No locally Noetherian scheme hypothesis is imposed.
- The cocone is exactly `constructibleCocone X ℓ`, the declaration recorded by
  `def-sfb-constructible-cocone`. Its index type is
  `PadicAlgCl.FiniteIntermediateField ℓ`, finite intermediate fields of the fixed
  algebraic closure over ℚ_ℓ, ordered by inclusion. Thus arbitrary finite E,F in
  the statement are the `i j` quantified by `CategoryCocone.HomSurj`.
- `x : C i` and `y : C j` in `HomSurj` are respectively objects of
  `PadicSubfieldConstructible X ℓ E` and `PadicSubfieldConstructible X ℓ F`.
  These abbreviate `BoundedConstructible (padicSubfieldRingObj X ℓ E)` and its F
  analogue. `BoundedConstructible` is the full subcategory on complexes with
  bounded cohomology and constructible cohomology sheaves. Constructibility uses
  finite stratifications and local finite presentations, exactly as the source.
- The arbitrary morphism φ is `f : (c.Φ i).obj x ⟶ (c.Φ j).obj y`.
  The cocone has `Φ E := constructibleToPadicAlgCl X ℓ E`, namely the restriction
  of derived scalar extension to the bounded constructible full subcategory.
  Fullness ensures these are the ambient derived morphisms as well.
- The conclusion `∃ (k : I) (hi : i ≤ k) (hj : j ≤ k)` supplies the required
  finite field H containing E,F. There is no strict-containment restriction.
- The existential `g : (c.T hi).obj x ⟶ (c.T hj).obj y` is a morphism in the
  bounded constructible H-category, because
  `T h := constructibleExtendScalars X ℓ h`.
- The final equality is exactly
  `f = (c.iso hi).inv.app x ≫ (c.Φ k).map g ≫ (c.iso hj).hom.app y`.
  Here `iso h := constructibleToPadicAlgClCompIso X ℓ h`, the restriction of the
  derived tensor transitivity comparison. With Lean's left-to-right `≫`, this is
  precisely θ_F ∘ T_H,Ω(g) ∘ θ_E⁻¹. There is no untransported equality of
  morphisms with different endpoints.

Dependency declarations used:

- `def-sfb-constructible-cocone`:
  `AlgebraicGeometry.ProEtale.constructibleCocone`, in
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit`.
  Read its fields and the definitions of `constructibleExtendScalars`,
  `constructibleToPadicAlgCl`, and `constructibleToPadicAlgClCompIso` there.
- `sk-def-sfb-filtered-two-colimit`:
  `CategoryTheory.CategoryCocone.IsFilteredTwoColimit`, in
  `WeilConjectures.CategoryTheory.FilteredTwoColimit`. Read its three fields;
  the `homSurj` field uses `CategoryTheory.CategoryCocone.HomSurj`, whose full
  quantifiers and equation were matched above. The general category cocone
  imposes no transition coherence or additional directedness hypothesis.

Also read the coefficient and category definitions in
`WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension` and
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory`. The algebraic
closure coefficient sheaf is the finite-subextension-valued condensed ring,
not all continuous functions into the algebraic closure. This matches the
blueprint and the actual cocone.

Edge cases checked: the empty scheme is permitted; zero complexes and zero
morphisms remain in the full subcategories; E=F and H=E are permitted by ≤;
complexes supported in one degree and arbitrary bounded shifts are included;
topologically Noetherian schemes which are not locally Noetherian are not
excluded. The index is nonempty (the base field belongs) and directed by finite
composita, so no empty-index exception is introduced. No independent site or
coefficient universe restriction is added by this record.

Searches made:

- msearch leanfinder, query “Every morphism between bounded constructible complexes
  over finite l-adic coefficient fields after scalar extension to Qbar_l descends
  to a common finite coefficient field”: eight Mathlib hits, including
  `ComplexShape.Embedding.homRestrict_hasLift`, `Condensed.profiniteSolid`, and
  `InfiniteGalois.finGaloisGroupFunctor_map_proj_eq_proj`; none states this theorem.
- msearch loogle, query `CategoryTheory.CategoryCocone.HomSurj`: no hit; unknown
  identifier, because this is an upstream project declaration rather than Mathlib.
- msearch grep, query `constructibleCocone_homSurj|Hom.*filtered.*colimit`: thirteen
  Mathlib hits on finite presentability and ordinary filtered colimits; no exact
  constructible coefficient-descent theorem.
- rg in both project roots, query
  `constructibleCocone_homSurj|constructible.*[Hh]om[Ss]urj`: found the exact
  theorem in `TwoColimit.lean` and its consumers, including
  `Sheaf.Paper.CoefficientFiniteDescentHom`. The declaration's docstring explicitly
  states the finite-common-field descent claimed by this node.
- grep of `lem-sfb-constructible-cocone-hom-surj` in upstream Lean found no literal
  blueprint marker. The current blueprint node itself names the exact theorem in
  its `lean` metadata; its statement agrees word for word with the DAG statement.

No statement correction, new node, dependency repair, or disputed statement is
needed. The existing-declaration probe and server preflight are run by deliver2.py
for both the required dry run and final delivery.

## Second reading by NM

No second reading by a worker: the dispatcher forbids starting other agents and
the worker delivers directly. The maintainer's independent review reads this
existing-declaration attachment. The clause correspondence above records the
worker's own reading, not an independent review.

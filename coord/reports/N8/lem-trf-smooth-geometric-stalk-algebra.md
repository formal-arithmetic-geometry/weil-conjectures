## Worker report

The delivery repairs the already published `Sheaf.TraceFormula.SmoothGeometricStalkAlgebra`
statement to match the current node. It retains the published strict-local ring-map and
coordinate constructions. The only postponed theorem is
`AlgebraicGeometry.smooth_geometric_stalk_algebra`, with proof `sorry` and the complete
node proof plan in its docstring. No node statement or dependency list changes.

Hypothesis and clause comparison (A and B below abbreviate the actual explicitly written
`Scheme.strictHenselizationRing s` and `Scheme.strictHenselizationRing v`):

- Schemes `S,V`, the morphism `f`, both `IsLocallyNoetherian` instances, and `[Smooth f]`
  render smoothness between locally Noetherian schemes.
- `Ω : Type u`, `[Field Ω]`, `[IsAlgClosed Ω]`, and `s,v : Spec (.of Ω) ⟶ ...`
  render the common-field geometric points. `hv : v ≫ f = s` is compatibility.
- `strictHenselizationRingMapAlong f s v hv` is the map induced by
  `Scheme.strictHenselizationMap f v`, on global sections through `ΓSpecIso`, transported
  along `hv`. No arbitrary ring map is quantified over.
- `IsNoetherianRing A ∧ IsNoetherianRing B ∧ IsLocalRing A ∧ IsLocalRing B`
  is exactly the Noetherian-local assertion. Maximal ideals throughout are
  `IsLocalRing.maximalIdeal` of these actual rings. The old redundant assertions that
  these maximal ideals are maximal were removed.
- `RingHom.Flat φ ∧ IsLocalHom φ` is flatness and locality; the next `IsRegularRing`
  is regularity of `B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)`.
- `∀ I, ∀ _hI : I ≤ maximalIdeal A` is every indicated ideal, including zero and
  the maximal ideal. `Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map`
  is the canonical map `A/I → B/IB`; its flatness and locality are asserted.
- The first fibre equivalence has source `B/(IB + mA B)` and target `B/mA B`.
  Its equation on every `b : B`, `E (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ b`,
  uniquely specifies the canonical identification. It is not a bare isomorphism choice.
- `∀ r`, `e : V ≅ 𝔸(ULift.{u} (Fin r); S)` and `_he` render the affine-space
  isomorphism over S. `K : Finset (ULift.{u} (Fin r))` is any finite coordinate subset.
- `strictHenselizationAffineCoordinate v r e i` is precisely `AffineSpace.coord S i`
  pulled back by `strictHenselizationStructuralMap v ≫ e.hom` and `ΓSpecIso`.
  `_hK` says that each selected coordinate belongs to the actual maximal ideal of B.
- The ideal of selected coordinates is `Ideal.span (Set.range (fun i : K ↦ ... i.1))`.
  The final universally quantified I again satisfies exactly `I ≤ maximalIdeal A`.
- The coordinate quotient has `IsNoetherianRing`, `IsLocalRing`, and flat canonical
  `Ideal.quotientMap` from `A/I`. No locality hypothesis on that quotient is added.
- Its closed fibre is the displayed quotient by `(IB + coordinateIdeal) + mA B`,
  canonically identified with `F_K = B/(mA B + coordinateIdeal)` by the second ring
  equivalence, again characterized on every quotient class. `IsRegularRing F_K` asserts
  regularity, and `ringKrullDim F = ringKrullDim F_K + K.card` is the dimension formula.

Dependency declarations read and used: Mathlib `Smooth` in
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`; `IsLocallyNoetherian` in
`Mathlib.AlgebraicGeometry.Noetherian`; `IsAlgClosed` and the geometric-point
morphism convention; `pointSmallEtale` in `Mathlib.AlgebraicGeometry.Sites.EtalePoint`
and `Point.sheafFiber` in `Mathlib.CategoryTheory.Sites.Point.Basic` (the general
geometric stalk is not separately constructed here); `Scheme.strictHenselizationRing`
and `strictHenselizationScheme` in `Sheaf.AlgebraicGeometry.StrictHenselization`;
`RingHom.Flat` in `Mathlib.RingTheory.RingHom.Flat`; `IsRegularRing` and
`IsRegularLocalRing` in `Mathlib.RingTheory.RegularLocalRing.Defs`; `AffineSpace`
and `AffineSpace.coord` in `Mathlib.AlgebraicGeometry.AffineSpace`; `ringKrullDim`
in `Mathlib.RingTheory.KrullDimension.Basic`. The canonical scheme map comes from
`Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap`; its structural map from
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`, and the local structure
from `Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`. The stated proof
nodes' modules are imported without `public`; there are no import cycles involving
this module in the read sources.

Sources read: morphisms.tex, labels lemma-smooth-flat and lemma-base-change-smooth;
algebra.tex, lemma-quotient-strict-henselization and
lemma-dimension-height-polynomial-ring; more-algebra.tex,
lemma-henselization-dimension and lemma-henselization-regular. These give the
individual inputs, as the node says, rather than a single purported Stacks theorem.

Edge cases checked: `I = 0` and `I = mA`, `K = ∅`, all coordinates selected, and
`r = 0`. No nonempty K or positive r is assumed. Geometric points exclude the zero
strict-local ring and empty source; empty schemes therefore make the point binders
uninhabited as intended. The coordinate prime need not be maximal; the dimension
argument uses its localization. There is no characteristic restriction or assumption
that the base is regular. All universes and variables are explicit, and the point
and ring universes follow the recorded strict-henselization API without added equality.

Searches actually run:

- `msearch.py ... leanfinder "Smooth geometric strict local rings flat regular closed
  fibre coordinate quotient dimension"`: eight hits on standard smoothness and smooth
  loci; none state the strict-local or coordinate-quotient theorem.
- `msearch.py ... loogle "RingHom.Flat, IsRegularRing"`: zero hits.
- `msearch.py ... grep "strictHenselization|strictLocalization|AffineSpace.coord"
  AlgebraicGeometry`: AffineSpace.lean's coordinate declaration documentation.
- `rg` of `lean/Sheaf` found the already published item module and a separate global
  strict-local ring-map helper in StrictHenselizationTensorFinite.lean. The item retains
  its own already published API; no new version of those constructions is introduced.
- `rg` in the named slopmaster2 `WeilConjectures` tree and the required item-id grep
  found no upstream copy. `rg` of `dag/lean_names_upstream.json` found no matching name.

No STATEMENT-DISPUTED flag or mathematical node correction is needed. The prior Lean
signature's `let` binders, redundant maximality conjuncts, and uncharacterized fibre
isomorphisms were interface defects; the mathematical node is unchanged.

Compilation: `scompile.py N8 lem-trf-smooth-geometric-stalk-algebra` compiled the
sandbox and library module cleanly (3.2 s and 4.4 s). The final dry run repeats the
check after the proof-plan/docstring and import completion.

## Second reading by N8

This is the author's final self-check; the dispatcher forbids starting other agents,
and the maintainer provides the independent review. Re-read the node beside the
complete module. Every hypothesis and each conclusion is matched above. In particular,
checked that the base ring is not assumed regular, that `e` commutes with projection,
that the coordinate values use the strict-local structural map, and that each fibre
isomorphism fixes the image of B. Removed all theorem-local `let` bindings, the two
redundant maximality conjuncts, and the two unused equivalence-helper definitions;
retained the actual canonical ring-map and coordinate definitions. Checked there is
one theorem with `sorry`, no data containing `sorry`, and no extra hypothesis.

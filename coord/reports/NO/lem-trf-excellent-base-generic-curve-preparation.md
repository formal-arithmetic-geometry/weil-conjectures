## Worker report

The module `Sheaf.AlgebraicGeometry.ExcellentBaseGenericCurvePreparation` states
`AlgebraicGeometry.exists_excellentBaseGenericCurvePreparation`. Its only proof is `sorry`.
No definitions or additional theorems are introduced. The item retains its statement,
proof and proof dependencies. Its statement dependencies gain the already landed
`def-trf-orgogozo-induction-data` to reuse its alteration and excellence predicates.

The node is rendered hypothesis by hypothesis and clause by clause as follows.

- Schemes C and B: `{C B : Scheme.{u}}`, with one explicit arbitrary universe.
- Integral C and B: `[IsIntegral C] [IsIntegral B]`; these include nonemptiness.
- Noetherian C and B: `[IsLocallyNoetherian C] [CompactSpace C]` and the same for B.
  This is exactly Mathlib's `IsNoetherian`, whose fields are those two properties.
- Excellent C and B: `hC : IsExcellentScheme C`, `hB : IsExcellentScheme B`.
  The existing definition tests `IsExcellent` on every affine coordinate ring.
- Proper dominant f: `(f : C ⟶ B) [IsProper f] [IsDominant f]`.
- Generic fibre of dimension one: `hdim : topologicalKrullDim
  (f.fiber (genericPoint B)) = 1`. An integral scheme is irreducible and sober, so
  this is its genuine generic point and the fibre is over its residue field.
- Proper closed subset Z: `(Z : Closeds C) (hZ : Z ≠ ⊤)`. This does not select or
  require a particular thickening of the subset and permits the empty subset.
- The output schemes and maps: existential `C₀ B₀`, `a : C₀ ⟶ C`, `b : B₀ ⟶ B`,
  and `f₀ : C₀ ⟶ B₀`.
- Each output is integral, excellent and Noetherian: the four conjuncts
  `IsIntegral`, `IsExcellentScheme`, `IsLocallyNoetherian`, `CompactSpace`, for each.
- Alterations a and b: `IsAlteration a ∧ IsAlteration b`. The reused predicate says
  proper, surjective, finite after pullback to some dense open, and componentwise
  dominance. The last condition adds nothing here: an integral scheme has only
  its whole space as irreducible component, and a surjection maps it onto the
  whole integral target. Thus it is precisely the item's alteration definition.
- Proper dominant f₀: `IsProper f₀ ∧ IsDominant f₀`.
- Commutativity: `a ≫ f = f₀ ≫ b`, the categorical ordering of `f ∘ a = b ∘ f₀`.
- Generic point of B₀: `∃ η₀ : B₀, IsGenericPoint η₀ Set.univ ∧ ...`.
  This avoids requiring a Lean instance from an earlier conjunct; it adds no
  mathematical choice of extra data, since B₀ is integral and has a unique generic point.
- Smooth generic curve: `Smooth (f₀.fiberToSpecResidueField η₀)`.
- Geometrically integral generic curve: `GeometricallyIntegral
  (f₀.fiberToSpecResidueField η₀)`. This includes geometric reducedness and
  irreducibility, rather than only ordinary irreducibility.
- Curve dimension: `topologicalKrullDim (f₀.fiber η₀) = 1`.
- Reduced inverse image: `Scheme.IdealSheafData.vanishingIdeal
  (Z.preimage a.continuous)` is the radical ideal sheaf defining precisely the
  closed subset `a ⁻¹' (Z : Set C)`. Its `.subscheme` is Z₀ and `.subschemeι`
  is its canonical closed inclusion. This is the reduced induced structure,
  equivalently the reduction of any scheme-theoretic inverse image of a closed
  structure with support Z. Mathlib documents `vanishingIdeal` in these terms;
  the imported reduced-induced-closed-subscheme theorem supplies uniqueness.
- Nowhere dense Z₀: `IsNowhereDense (a ⁻¹' (Z : Set C))`, its underlying subset of C₀.
- Finite generic boundary: `IsFinite (((vanishingIdeal
  (Z.preimage a.continuous)).subschemeι ≫ f₀).fiberToSpecResidueField η₀)`.
- Étale generic boundary: `Etale` of that identical morphism. The codomain is
  `Spec (B₀.residueField η₀)`, exactly Spec κ(B₀).

Dependency declarations read and used (possibly publicly reexported by the landed
Orgogozo module):

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`.
- `Sheaf.RingTheory.ExcellentRing`: `IsExcellent`, through `IsExcellentScheme`.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`.
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber` and
  `Scheme.Hom.fiberToSpecResidueField`, canonical pullback and second projection.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`,
  the property of the canonical reduced closed inclusion used here.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Geometrically.Integral`: `GeometricallyIntegral`, the
  geometric integrality notion explicitly supplied by the geometric-properties
  dependency's `mathlib_match` (its primary name is `GeometricallyIrreducible`).
- `Mathlib.AlgebraicGeometry.IdealSheaf.Basic` and `.Subscheme`:
  `Scheme.IdealSheafData.vanishingIdeal`, `.subscheme`, `.subschemeι`.
  The reduction dependency supplies these subscheme declarations; vanishingIdeal
  gives the reduced induced structure without choosing an auxiliary thickening.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `IsFinite`.
- `Mathlib.Topology.Sober`: `IsGenericPoint`, `genericPoint` and its specification.
- `Sheaf.Paper.OrgogozoInductionData`: `AlgebraicGeometry.Orgogozo.IsAlteration`,
  `AlgebraicGeometry.Orgogozo.IsExcellentScheme` (the added landed dependency).

All recorded proof-dependency modules with a `lean` record are imported without
`public`, except those already publicly imported for statement notions. Duplicate
module paths are imported once. Unstated proof lemmas are not needed to elaborate
this statement and are not restated here. There is no dependency module or new node.

Source reading: the local Travaux de Gabber PDF, Exposé IX §1.3, printed p.132,
explicitly makes a finite radicial extension of the generic point, normalizes
source and base, replaces the boundary by its reduced inverse image, and then
uses Stein factorization to obtain a smooth geometrically connected generic
curve with étale generic boundary. The item's sixteen-step proof supplies the
arbitrary-base affine gluing and boundary arguments; the declaration docstring
records all sixteen steps, including the generic-boundary identification after
Stein. The de Jong PDF is not locally archived, as its source record already says.

Edge cases checked: Z empty gives the empty reduced subscheme and a finite étale
empty generic boundary, without a nonemptiness condition. Z = C is excluded
explicitly. Empty C or B is already excluded by integrality, exactly as in the node.
Vertical boundary components are allowed. Positive characteristic and imperfect
function fields are allowed; no separability is imposed on the alteration degree.
Nontrivial separable constant extensions are allowed by the existential B₀.
The base can be nonseparated, nonprojective, and of unbounded finite chain length:
no finite-dimensionality or absolute finite-type assumption occurs. A field base
is allowed. Dimension is the full topological Krull dimension, not a fibrewise
upper bound. No data definitions, hidden choices of maps, or additional assertions
of finite alterations have been added.

Searches performed:

- `msearch.py ... leansearch "Proper family of integral curves over an excellent
  base admits alterations with smooth geometrically integral generic fibre and
  finite etale boundary"`: eight hits concerning smoothness, properness, and
  étale morphisms; no alteration-preparation theorem.
- `msearch.py ... leanfinder "Proper dominant curve over an excellent base admits
  alterations with smooth geometrically integral generic fibre and finite etale
  boundary"`: eight hits on smooth relative dimension, normalization dominance,
  smooth algebra descent and étale objects; no matching theorem.
- `msearch.py ... loogle "AlgebraicGeometry.IsProper, AlgebraicGeometry.Smooth"`:
  zero hits.
- `msearch.py ... grep "alteration|generic.*preparation|preparation.*generic"
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` in upstream `WeilConjectures` for alteration/Alteration, the item id and the
  proposed declaration: no match. `rg` in `dag/lean_names_upstream.json` for the
  proposed declaration: no match.
- `rg` in `lean/Sheaf`: found `GenericSmoothBoundaryPreparation` and
  `AlterationRelativeCurvePreparation`; their signatures were read. They assume
  additional field/trait/projective preparation data and do not state this theorem
  over an arbitrary excellent base. Found `OrgogozoInductionData`'s existing
  `IsAlteration` and `IsExcellentScheme`; reused both. Found the existing canonical
  Mathlib closed-set vanishing ideal construction, so no helper definition is needed.

No statement dispute or source-based correction is needed.

## Second reading by NO

Author's second reading against the node and the complete file; the maintainer's
independent review is separate. Checked each hypothesis and clause against the
mapping above. In particular, the output says *geometrically integral*, retains
exact dimension one, and uses the boundary's own induced map to B₀ before taking
its generic fibre. It never replaces that fibre by an unrelated scalar extension.
The boundary support is the preimage of the actual input closed subset; its
vanishing ideal supplies the reduced scheme structure canonically. The alteration
predicate's extra component clause is automatic on these integral schemes, and
Noetherianity includes quasi-compactness on all four schemes. The statement gains
no affine, separated, projective or finite-dimensional hypothesis. The declaration
has exactly one `sorry`, in its theorem proof. Every variable and universe is
explicit, the signature is copied verbatim into `lean.statement`, and no line
exceeds 100 characters. No mathematical mismatch was found in this reading.

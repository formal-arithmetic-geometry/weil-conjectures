## Worker report

The module `Sheaf.AlgebraicGeometry.ProperFieldAlgebraicDualizing` states
`AlgebraicGeometry.proper_field_algebraic_dualizing`, with one `sorry` and no new
definitions. The node's mathematical statement, proof and proof dependencies are
unchanged. Its statement dependencies gain three already-landed definition nodes
for the global-sections, stalk and derived-Hom interfaces used in the signature.

Hypothesis and clause correspondence:

- A field k: `(k : Type u) [Field k]`, with no characteristic or perfection restriction.
- A scheme C and proper f to Spec k: `(X : Scheme.{u})`,
  `(f : X ⟶ Spec (.of k)) [IsProper f]`. Properness supplies finite type;
  Noetherian, flat, connected, smooth and equidimensional assumptions are not added.
- The derived categories are the recorded `schemeDerivedCategory` and its
  quasi-coherent full subcategory `schemeDerivedQCohCategory`. The two explicit
  `HasDerivedCategory` binders retain independently chosen localization hom universes
  `wX` and `wS`, exactly as the recorded interface requires. Ordinary module derived
  categories use the existing standard instance. There is no equality of universes
  imposed on the two scheme localizations.
- The given right adjoint: `a : DerivedCategory (ModuleCat.{u} k) ⥤
  schemeDerivedQCohCategory X`, and `_adj` is an adjunction from the recorded
  derived pushforward restricted by `(schemeDerivedQCohProperty X).ι`, followed
  by the existing right-derived global-sections functor on Spec k and restriction
  of scalars along `(Scheme.ΓSpecIso (.of k)).inv.hom`. This is the canonical
  affine identification of the target with D(k), not an arbitrary comparison.
- K=a(k[0]): every occurrence is exactly
  `(a.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
  (ModuleCat.of k k))).obj`. The final `.obj` forgets the full-subcategory witness.
- Coherent cohomology: the first conjunct is `∀ j : ℤ,
  RingedSpace.IsCoherent X.toRingedSpace (H^j K)`, with the actual finite-type
  kernel coherence predicate of `pqf-def-coherent`, not merely finite type.
- Bounded cohomology: the second conjunct gives `∃ p q : ℤ` such that `H^j K`
  is `IsZero` whenever `j < p ∨ q < j`. The same bounds work on the entire scheme.
- Every stalk: the final conjunction starts `∀ x : X`. The stalk object is
  `DerivedCategory.Q.obj` of the complex obtained by
  `(RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex (.up ℤ)`
  applied to `DerivedCategory.Q.objPreimage K`. The recorded stalk functor is
  exact, so this is the derived stalk with its actual local-ring action. These
  terms are definitionally the downstream convenience `properDualizingStalk`.
- Noetherian local ring: `IsNoetherianRing (X.presheaf.stalk x)` is asserted,
  not assumed. The local-ring structure is already carried by scheme stalks.
- Finite injective dimension, in precisely the node's stated sense: there is
  `I : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ`, with bounded terms,
  every term `Injective`, and `Nonempty (DerivedCategory.Q.obj I ≅ K_x)`.
  The isomorphism expresses existence of a representative; no preferred one is
  claimed. Bounds may depend on x. No bounded complex is replaced by a one-sided
  bounded complex.
- Scalar homothety is an isomorphism: `IsIso (MonoidalClosed.curry' (𝟙 K_x))`.
  The imported ordinary-module derived closed structure identifies this map as
  O_{X,x}[0] → RHom(K_x,K_x). Currying the identity gives scalar multiplication,
  rather than selecting an arbitrary isomorphism. Stalk cohomology is finite by
  the global coherence conjunct and exactness of stalks, so the full algebraic
  dualizing condition is present.
- Arbitrary dimensions, disconnected schemes and arbitrary fields: no dimension,
  connectedness, nonemptiness, separability, reducedness or regularity binders occur.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (via the public proper-scheme imports).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Spec` and
  `Scheme.Hom`; `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `IsProper`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`: `schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: publicly exposes
  `AlgebraicGeometry.RingedSpace.IsCoherent` from
  `WeilConjectures.AlgebraicGeometry.Coherent`; its full defining signature and
  finite-type-kernel clause were read. The finite-type conjunction alone is not used.
- `WeilConjectures.Topology.RingedSpaceModuleCohomology`:
  `AlgebraicGeometry.RingedSpace.globalSectionsFunctor`.
- `WeilConjectures.Algebra.Homology.ModuleStalkFunctor`:
  `AlgebraicGeometry.RingedSpace.moduleStalkFunctor`.
- `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`:
  `CategoryTheory.ordinaryModuleDerivedInternalHom`, the recorded abbreviation
  for the derived closed bifunctor. Its public derived closed structure supplies
  `MonoidalClosed.curry'`. No second RHom is constructed.

All recorded proof-dependency modules are plain imports, while the interfaces
appearing in the signature are public imports. Mathlib proof leaves are imported
from the files in their records. `lem-trf-flat-coherent-homothety-base-change` has
no recorded Lean module or Mathlib match and hence no import yet; the docstring
retains this planned proof step. `ProperDualizingClosedStalkNormalized` was read
but intentionally is not imported: it is a downstream consumer of this item and
contains convenience abbreviations of the very expressions used here. Importing
its theorem would close a mathematical import cycle. No copied definition is made.

Sources read: `literature/stacks-project/duality.tex`, `lemma-shriek-dualizing`
(Tag 0AA3), `example-proper-over-local` (0AWI), and
`example-equidimensional-over-field`. The theorem docstring carries all ten
accepted proof steps, including local regular rings, polynomial differential
trivialization, finite-free resolutions, maximal localization bounds, finite-cover
gluing, and finite-map transfer at each localized quotient.

Edge cases checked before writing and again against the signature: the empty
scheme has no stalk obligations and zero cohomology with bounds [0,0]; Spec k has
K=k[0] and identity scalar map; finite nonreduced proper schemes are allowed;
disconnected unions of components of differing dimensions use common global
bounds but independent stalk models; arbitrary imperfect fields are allowed;
polynomial charts with zero variables use zeroth exterior power in the proof.
The canonical scalar map, not mere existence of an iso to RHom, is required.

Searches made (2026-10-24; wrapper outputs retained in `searches.jsonl`):

- `msearch.py ... leanfinder "For a proper scheme over a field, the right adjoint
  of derived pushforward applied to the field has bounded coherent cohomology
  and algebraic dualizing stalks"`: 8 hits, ordinary module-sheaf pushforward
  adjunctions only; no theorem matching this node.
- `msearch.py ... leansearch "Proper scheme over a field has a dualizing complex
  given by the right adjoint of derived direct image"`: 8 hits, ordinary
  pushforward adjunctions and proper global-section algebra finiteness; no match.
- `msearch.py ... loogle "AlgebraicGeometry.IsProper, DerivedCategory"`: 0 hits.
- `msearch.py ... grep "dualizing|Dualizing" AlgebraicGeometry`: 0 Mathlib hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for absolute/algebraic dualizing,
  proper-field and derived-stalk spellings found downstream
  `ProperDualizingClosedStalkNormalized` and `ReducedCurveDualizingModule`, and
  the polynomial model. None states bounded coherent cohomology with dualizing
  stalks at every point for a proper field-scheme right adjoint. Exact searches
  for `proper_field_algebraic_dualizing` and `ProperFieldAlgebraicDualizing` were
  empty before writing; searching the item id upstream also gave no match.

No STATEMENT-DISPUTED issue, correction, dependency repair or new definition node.
Validation: `scompile.py Q06 lem-sfb-proper-field-algebraic-dualizing <module>`
compiled both the sandbox and library module, in 3.6 s and 4.0 s respectively,
with no errors or unexpected warnings.

## Second reading by Q06

A separate self-audit was performed with both the JSON statement and Lean module
open; no second agent was started, following the dispatcher's explicit instruction.
The maintainer's independent review remains the independent reading.

The audit checked the field/scheme/proper binders, the domain and codomain of a,
the canonical affine coefficient transport, and each occurrence of a(k[0]). It
checked genuine coherence rather than the quasi-coherent finite-type shorthand,
global two-sided cohomology bounds, all points rather than only closed points,
the Noetherian conclusion, two-sided bounded injective representatives, and the
specific identity-transpose scalar map. It checked the absence of connectedness,
dimension, smoothness and field restrictions. The stalk expressions on the two
clauses are identical. No mismatch was found and no mathematical statement changed.
The only DAG additions are the three already-landed definition dependencies whose
recorded declarations actually appear in the signature.

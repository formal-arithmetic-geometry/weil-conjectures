## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeWeilCodimensionExtension` states
`AlgebraicGeometry.exists_extension_of_fiberwise_dense_of_codimension_two` with its entire
proof postponed by `sorry`. No definition or other theorem is introduced. Only the item's
`lean` field changes; no statement correction, dependency repair, or new node is needed.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| Noetherian integrally closed domain D | `(D : Type u) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsIntegrallyClosed D]` |
| Krull dimension one | `(hD : ringKrullDim D = 1)` |
| Fraction field E | `(E : Type u) [Field E] [Algebra D E] [IsFractionRing D E]` |
| Nonempty open subscheme T of Spec D | `(T : (Spec (CommRingCat.of D)).Opens) [Nonempty T]`, with scheme `T.toScheme` |
| Schemes X and G with structure maps to T | `(X G : Scheme.{u}) (f : X ⟶ T.toScheme) (g : G ⟶ T.toScheme)` |
| Smoothness of both structure maps | `[Smooth f] [Smooth g]` |
| Separatedness of G over T | `[IsSeparated g]`, the closed-immersion diagonal predicate |
| Group scheme structure, including multiplication, inverse and identity and their diagrams | `[GrpObj (Over.mk g)]`; this is a group object in schemes over T, with no commutativity condition |
| Open V in X | `(V : X.Opens)` and its scheme `V.toScheme`, inclusion `V.ι` |
| T-morphism u from V to G | `(u : V.toScheme ⟶ G) (hu : u ≫ g = V.ι ≫ f)` |
| Density of V_t in X_t for every t | `(hdense : ∀ t : T.toScheme, Dense ((f.fiberι t) ⁻¹' (V : Set X)))` |
| V contains every point whose local ring has dimension at most one | `(hcodim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ V)` |
| Existence of an extension | `∃ ubar : X ⟶ G, ...` |
| Extension is over T | `ubar ≫ g = f` |
| Restriction equals u | `V.ι ≫ ubar = u` |
| No quasi-compactness or separatedness condition on X, no properness or commutativity of G | No such instance or hypothesis occurs |

The fibre `f.fiber t` is literally the pullback along `T.toScheme.fromSpecResidueField t`
to `Spec (T.toScheme.residueField t)`. The inverse image of V under its projection
`f.fiberι t` is precisely the open underlying the base change V_t. Its density therefore
expresses the node's fibrewise density, without introducing a substitute notion of fibre.
All variables and the universe `u` are explicitly bound. The common scheme universe follows
Mathlib's category of schemes and imposes no finite-dimensionality or smallness hypothesis.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map`; these supply def-pc-scheme and def-weil-affine-spectrum.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, for the base and stalk dimensions
  (def-weil-pbc-krull-dimension-ring).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`
  (def-sbc-smooth-morphisms).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its public dependency Separated:
  `AlgebraicGeometry.IsSeparated` (the separatedness clause of def-weil-proper-morphism).
  Properness itself is deliberately not assumed.
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: the recorded base-change module
  (def-pc-base-change). Its documented scheme base change reuses Mathlib pullbacks; its
  `moduleBaseChange` declaration is for modules and is not used as a scheme construction.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` (def-weil-residue-field). `Mathlib.AlgebraicGeometry.Fiber`,
  publicly imported through BaseChangeConventions, gives `Scheme.Hom.fiber` and `fiberι`.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`: `CategoryTheory.GrpObj`, whose underlying
  class in `Mathlib.CategoryTheory.Monoidal.Grp` extends `MonObj` with inverse and inverse
  laws. In `Over T.toScheme` this supplies exactly the group diagrams already spelled out
  in the node; no new definition node is required.
- Ring hypotheses additionally reuse Mathlib `IsNoetherianRing`, `IsIntegrallyClosed` and
  `IsFractionRing`; no private definitions are introduced.

The proof plan is copied into the theorem docstring. Proof dependencies with existing
interfaces are imported: Noetherian definitions, open immersions and principal-localization
open immersion through the public modules, `IsLocalization.isNoetherianRing` through
`Mathlib.RingTheory.Localization.Submodule`, normal localization through
`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` and
`Mathlib.RingTheory.Localization.LocalizationLocalization`, and
`Scheme.fromSpecStalk_affine_description` / `fromSpecStalk_local_properties` through
`WeilConjectures.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`.
The general theorem lem-sfb-relative-group-weil-extension currently has neither a Lean record
nor a Mathlib match. It is only a proof dependency, not needed to type this statement, so
there is no import for it and its future formalization is referenced in the proof docstring.

Source check: read the primary scan of BLR Néron Models, PDF pp.115--116, printed pp.109--110,
4.4 Theorem 1 and its proof, at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf .
The theorem has a normal Noetherian base, smooth source, smooth separated group target,
and an S-rational map defined in codimension at most one. Its proof uses fibrewise density
of the domain. This delivery is exactly the node's stated Dedekind specialization, with
existence only (uniqueness from the general theorem is not added).

Edge cases checked before writing: X may be empty (the density and codimension conditions
are then vacuous and the unique empty-domain morphism extends); an empty V is permitted
syntactically, but fibrewise density rules it out whenever X is nonempty. Empty fibres do
not create extra restrictions. V = X gives the original morphism as extension. Local ring
dimension zero as well as one is included by `≤ 1`, whereas dimensions above one and
infinite dimension are not mistakenly forced into V. Fields are excluded as bases only by
the node's explicit dimension-one hypothesis. An empty T is excluded exactly by its
nonemptiness assumption; the generic-point open of a local Dedekind base remains allowed.
There is no restriction on characteristic, connected components, commutativity, affine or
proper targets, quasi-compactness, or separatedness of X.

Searches (msearch.py, group Q12, this item; raw responses are in the sandbox searches.jsonl):

- LeanFinder: “A morphism on a fibrewise dense open containing all points of local ring
  dimension at most one of a smooth scheme over a Dedekind base extends to a smooth
  separated group scheme”. Eight hits, principally smoothness and separated-target
  extensionality, none the required extension theorem.
- Loogle: `"AlgebraicGeometry", "GrpObj"`. Five hits: group-object base change, affine
  Hopf algebra instances and smoothness of reduced group schemes. These confirm the
  existing group-object interface but do not state the extension theorem.
- Mathlib grep: `Weil.*extension|codimension.*extend|relative.*weil` in AlgebraicGeometry.
  No hits.
- LeanSearch: “A fibrewise dense partial map to a smooth separated group scheme over a
  normal Noetherian base extends if defined at all codimension one points”. Eight hits:
  partial-map constructors, representatives and restriction, and topological Dense.extend;
  none states the algebraic extension theorem.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf`, and in the upstream name index:
  `lem-sfb-relative-weil-codimension-extension|relativeWeil|relative_weil|codimension_extension`.
  No hits. Broader group-scheme search found the upstream GroupScheme.Defs documentation
  and Mathlib GrpObj, which are reused rather than copied.

Validation: prescribed scompile.py compiled both sandbox and library forms without any
error or warning (1.7 s and 1.8 s). The proof is intentionally `sorry`, as stage 2 requires.
No statement dispute or node fault was found.

## Second reading by Q12

A separate second pass in this worker session reread the node and final signature side by
side; no other agent was started, as the dispatcher brief prohibits that. The maintainer's
independent review remains the independent review for this delivery.

The pass checked that E is present with its fraction-field structure, that nonempty T is an
actual open of Spec D, and that the group structure lives over exactly the map g used for
smoothness and separatedness. In particular, `GrpObj (Over.mk g)` is not a group structure
on an unrelated scheme. It checked the inverse-image description of V_t using the actual
residue-field fibre, and that the stalk dimension predicate includes every point of height
zero or one. It checked both equations of the conclusion: the first says the extension is
over T and the second says it agrees on the specified V. No uniqueness, group-homomorphism
condition on u, or quasi-compactness/separatedness assumption on X was added. No mismatch
was found, and no signature change was required after the successful compile.

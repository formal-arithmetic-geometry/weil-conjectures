## Worker report

The module `Sheaf.TraceFormula.AmpleNeighbourhood` states
`AlgebraicGeometry.exists_ample_neighbourhood`.  It introduces schemes `X` and `Y` in one
explicit universe, a proper morphism `f : Y ⟶ X`, an invertible module `L : Y.Modules`, and
a point `x : X`.  Its hypothesis is absolute ampleness of the pullback of `L` along the
fibre inclusion `f.fiberι x` on the scheme `f.fiber x`.  Its conclusion supplies an open
`U : X.Opens` containing `x`, compactness (quasi-compactness) of the inverse-image scheme
`(f ⁻¹ᵁ U).toScheme`, and ampleness of the pullback of `L` to every inverse image of an
affine open `V : X.Opens` with `V ≤ U`.

The Lean rendering of each clause is:

* “`f : Y → X` is proper” is `(f : Y ⟶ X) [IsProper f]`, using
  `AlgebraicGeometry.IsProper`.
* “`L` is invertible” is `(L : Y.Modules) [L.IsInvertible]`, using
  `AlgebraicGeometry.Scheme.Modules.IsInvertible`.
* “the restriction to the fibre over `x` is ample” is
  `Scheme.Modules.IsAmple (f.fiber x)
  ((Scheme.Modules.pullback (f.fiberι x)).obj L)`; `Scheme.Hom.fiber` and
  `Scheme.Hom.fiberι` are Mathlib's fibre and fibre inclusion, and `Scheme.Modules.pullback`
  is the recorded module pullback.
* “there is an open neighbourhood” is `∃ U : X.Opens, x ∈ U`.
* “the inverse image is quasi-compact” is
  `CompactSpace ((f ⁻¹ᵁ U).toScheme)`.
* “ample on every inverse image of an affine open of `U`” is
  `∀ V : X.Opens, V ≤ U → IsAffineOpen V →
  Scheme.Modules.IsAmple ((f ⁻¹ᵁ V).toScheme)
  ((Scheme.Modules.pullback ((f ⁻¹ᵁ V).ι)).obj L)`.
  An affine open of the open subscheme `U` is represented canonically by an affine open
  `V` of `X` with `V ≤ U`; `(f ⁻¹ᵁ V).ι` is the corresponding restriction map to `Y`.

The statement imports `WeilConjectures.AlgebraicGeometry.Ample` for the project's absolute
ampleness predicate and invertible-module API, and Mathlib's proper-morphism and fibre APIs.
The dependency declarations read were:

* `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper` in
  `Mathlib.AlgebraicGeometry.Morphisms.Proper`; its class extends separated, universally
  closed, and locally finite type.
* `def-sc-invertible-module`:
  `AlgebraicGeometry.Scheme.Modules.IsInvertible` in
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`; it requires local triviality on
  open neighbourhoods.
* `def-weil-pbc-ample-invertible-module`:
  `AlgebraicGeometry.Scheme.Modules.IsAmple` and
  `AlgebraicGeometry.Scheme.Modules.nonvanishingLocus` in
  `WeilConjectures.AlgebraicGeometry.Ample`; this is the absolute Stacks 01PS notion.
* `def-pc-fibre-product`: Mathlib's `CategoryTheory.Limits.pullback` with its projections;
  the fibre API is Mathlib's `Scheme.Hom.fiber`/`fiberι` built from this pullback.
* `def-pc-scheme`: Mathlib's `AlgebraicGeometry.Scheme` and `Scheme.Hom`.

I checked that the source repository's `AlgebraicGeometry.IsAmple` is a different
relative-to-a-field, projective notion and therefore is not reused.  The target's recorded
searches were also repeated: `msearch.py` leanfinder/leansearch queries for ampleness near a
proper fibre, Loogle queries `IsAmple, IsProper, neighbourhood` and `"IsAmple"`, and grep
queries for `ample-in-neighbourhood|relatively ample|IsAmple` in Mathlib and the project.
They found no exact theorem or Mathlib declaration.  The existing project declaration of
absolute `Scheme.Modules.IsAmple` is used instead of defining a duplicate notion.

Edge cases checked before writing include an empty fibre (the hypothesis remains the stated
absolute predicate), the zero tensor power (excluded by `0 < n` inside `IsAmple`), empty
schemes, and the necessity of `x ∈ U`.  The source does not require `U` itself to be affine;
the statement therefore only requires `V` to be affine and contained in `U`.  The theorem
compiled cleanly with `scompile.py`; the sole expected warning is the theorem's `sorry`.

## Second reading by Q78

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

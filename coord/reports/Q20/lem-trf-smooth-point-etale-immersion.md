## Worker report

The module `Sheaf.AlgebraicGeometry.SmoothPointEtaleImmersion` states
`AlgebraicGeometry.Smooth.exists_etale_immersion_slice` for a smooth morphism
`f : X ⟶ S`, a point `x`, and the hypotheses that `x` is closed in the fibre,
that the residue-field extension is finite dimensional, and that it is separable.
The conclusion introduces a scheme `Z`, an immersion `i : Z ⟶ X`, and `z : Z`;
it states `i z = x`, that `i ≫ f` is étale, and that the range of the fibre
projection over `f x` is exactly `Set.singleton z`, i.e. the underlying fibre has
one point.

The `letI := (f.residueFieldMap x).hom.toAlgebra` binder gives the canonical
residue-field algebra structure. The `Module.Finite` conjunct renders “finite
(finite-dimensional as a vector space)”; `Algebra.IsSeparable` renders the
separable algebraic extension. `IsClosed {f.asFiber x}` is the closedness of
`x` in the scheme-theoretic fibre via the fibre projection. `IsImmersion i` is
Mathlib's closed-then-open immersion notion, and `Etale (i ≫ f)` is the
structural morphism's étaleness. `Set.range ((i ≫ f).fiberι (f x)) =
Set.singleton z` is the set-theoretic singleton fibre clause.

The source is Stacks Project, `more-morphisms.tex`, Tag 057G (lemma-slice-smooth),
including its immersion conclusion and singleton fibre. The docstring records the
four proof steps from the node: finite fibre dimension and strong induction;
the zero-dimensional étale neighbourhood and isolated fibre point; a smooth
hypersurface dimension-lowering slice with residue-field/closedness checks; and
composition of the induced immersion with the closed-open immersion into `X`.

Dependencies used as recorded declarations:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme`.
- `def-sbc-smooth-morphisms`: Mathlib `AlgebraicGeometry.Smooth` and `SmoothOfRelativeDimension`.
- `def-pc-scheme-fibre`: Mathlib `AlgebraicGeometry.Scheme.Hom.fiber`, with `fiberι` and `fiberToSpecResidueField`.
- `def-weil-residue-field`: Mathlib `AlgebraicGeometry.Scheme.residueField` and `Scheme.Hom.residueFieldMap`.
- `def-pc-field-extension`: Mathlib `Algebra` / `RingHom.toAlgebra`.
- `def-weil-pbc-separable-algebraic-extension`: Mathlib `Algebra.IsSeparable`.
- `def-weil-etale-morphism`: Mathlib `AlgebraicGeometry.Etale`.
- `def-weil-closed-immersion`: Mathlib `AlgebraicGeometry.IsImmersion`.

The module imports only Mathlib modules providing these declarations. No project
notion was duplicated and no new definition or dependency repair was needed.

Edge cases checked: the fibre point is represented by `f.asFiber x`, so the
closedness hypothesis is in the actual scheme-theoretic fibre; the singleton is
set-theoretic and permits the fibre to have its induced scheme structure; the
finite-dimensional and separability hypotheses use the canonical residue-field
map and do not impose a field-universe restriction beyond the common scheme
universe; and the theorem allows arbitrary schemes, including empty fibres away
from the designated point.

Searches made (all on the pinned slopmaster2/Mathlib sources):

- `leanfinder`: “smooth morphism closed fibre point finite separable residue field immersion etale slice singleton fibre” — returned smooth/étale infrastructure and no slice theorem.
- `loogle`: `Scheme.Hom, IsEtale, closed point fibre` — query failed to parse (unavailable; not a negative result).
- `grep`: `057G|lemma-slice-smooth|etale.*slice` in Mathlib/AlgebraicGeometry — no hits.
- `leansearch`: “immersion through a closed point of a smooth fibre with separable residue field that is etale over the base and has singleton fibre” — no Tag 057G theorem.
- `leanfinder`: “A closed point with finite separable residue field in a smooth fibre admits an immersion from an etale scheme with singleton fibre” — only smooth/étale chart and residue-field preimmersion declarations.
- `loogle`: `"Smooth", "Etale"` — smooth/étale algebraic declarations, no slice theorem.
- `grep`: `slice.smooth|057G|etale.*slice|slice.*etale` in Mathlib/AlgebraicGeometry — no hits.

No `STATEMENT-DISPUTED` issue or node correction was found.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

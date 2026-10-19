## Worker report

The delivery adds the general-base reduced dominant-part construction and states
`AlgebraicGeometry.dominantPart_coreflection` with a `sorry` proof.  The new definition
module `Sheaf.AlgebraicGeometry.DominantPart` defines `dominantPartClosed` as the closure
of `p ⁻¹' genericPoints S`, `dominantPart` as the vanishing-ideal subscheme of that closed
set, and `dominantPartι` as its canonical closed immersion.  The item module
`Sheaf.DeligneLaumon.DominantPartCoreflection` states reducedness and closed immersion,
the reduced maximally-dominant Hom bijection, unique induced maps, identity and
composition, the generic-fibre reduction isomorphism, the étale pullback isomorphism,
and proper-surjective preservation.

Hypothesis and clause rendering:

- `S` is a scheme with the finite-affine-cover Noetherian condition as
  `[AlgebraicGeometry.IsNoetherian S]`; `p : X ⟶ S` is finite type as the two
  recorded Mathlib classes `[LocallyOfFiniteType p] [QuasiCompact p]`.
- The first conjunction is `IsReduced (dominantPart X S p)` and
  `IsClosedImmersion (dominantPartι X S p)`, with the actual reduced induced
  construction supplied by `dominantPart` and `dominantPartι`.
- The equality for `dominantPartClosed` identifies its support with the union of
  `closure {ξ}` for `ξ ∈ genericPoints X` whose image lies in `genericPoints S`,
  rendering the reduced union of the dominant irreducible components.
- For `q : T ⟶ S`, `[IsReduced T]`, and the same finite-type classes, the condition
  on every generic point is `(∀ t ∈ genericPoints T, q t ∈ genericPoints S)`.  The
  displayed `Function.Bijective` maps a subtype of `S`-morphisms into the dominant
  part to a subtype of `S`-morphisms into `X` by composition with `dominantPartι`.
- For an `S`-morphism `f : X ⟶ Y`, the equation `f ≫ r = p` is explicit and the
  induced map is rendered by `∃! fmd` with
  `fmd ≫ dominantPartι Y S r = dominantPartι X S p ≫ f`.
  The next clause gives the corresponding equation for `hmd` and proves the
  composition law `hmd = fmd ≫ gmd`; the following clause gives the identity law.
- For every `s ∈ genericPoints S`, the fibre clause is an existential scheme
  isomorphism between `(dominantPartι X S p ≫ p).fiber s` and
  `(p.fiber s).nilradical.subscheme`, with both projection compatibilities written.
- For an étale `f` (the class binder `[Etale f]`), the canonical pullback map is
  `pullback.lift (dominantPartι X S p) fmd hcomp`, where `hcomp` is its pullback
  commutativity equation; `IsIso` states the required isomorphism.
- For proper and surjective `f`, the same induced map satisfies
  `IsProper fmd ∧ Surjective fmd`.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (the ring-level
  Noetherian dependency; the scheme-level hypothesis is Mathlib's
  `AlgebraicGeometry.IsNoetherian`).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`
  and `AlgebraicGeometry.QuasiCompact`.
- `Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme`:
  `AlgebraicGeometry.Scheme.IdealSheafData.reduced_induced_closed_subscheme`.
- `Mathlib.Topology.Irreducible`: `irreducibleComponents`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and its `fst`, `snd`, and `lift` maps.
- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsReduced` and
  `AlgebraicGeometry.Scheme.nilradical`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`.
- `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.Topology.Sober`: `IsGenericPoint` and `genericPoints`.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`,
  `fiberι`, and `fiberToSpecResidueField`.

The recorded dependency declarations and their full signatures/docstrings were opened.
The theorem module also imports the already stated
`Sheaf.AlgebraicGeometry.ReductionGenericFibre` declaration
`AlgebraicGeometry.Scheme.Hom.reduction_generic_fibre` for the generic-fibre clause and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale` declaration
`AlgebraicGeometry.isReduced_of_etale` for the étale clause's proof plan.

Edge cases checked: an empty inverse image of generic points gives the vanishing-ideal
subscheme on the empty closed set; an empty scheme `X` is admitted; a base with several
irreducible components and a nonreduced base is admitted by `genericPoints S`; vertical
components are excluded from the closure; `T` may be empty and the Hom subtype then has
its ordinary empty/zero behaviour; the generic-fibre quantifier includes every generic
point and does not assume `S` reduced or integral; identity maps and length-zero
compositions are covered by the explicit identity clause; proper-surjective maps retain
both hypotheses.  The existing `def-per-dominant-reduced-part` was checked and is only
an integral-base ideal specialization, so it does not state this general-base notion.

Searches made: `msearch.py NU def-per-dominant-part leanfinder "reduced induced closed
subscheme on closure of inverse image of generic points of base scheme"` returned only
`IdealSheafData.subscheme` and unrelated image declarations; `msearch.py ... loogle
"genericPoints, vanishingIdeal, IdealSheafData.subscheme"` returned zero hits (the
service reported `vanishingIdeal` as an unknown identifier); `msearch.py ... grep
"dominantPart|dominantPartClosed|genericPoints" Mathlib/` returned no dominant-part
match.  `rg` over `WeilConjectures` and `lean/Sheaf` found only the integral-base
`dominantReducedPartIdeal` specialization and generic-point utilities.  No exact
Mathlib, source, or project declaration exists.

No `STATEMENT-DISPUTED` flag or node fault was found.

## Second reading by NU

I reread the item node, the new definition node, the two modules, and every recorded
statement dependency.  The Lean uses exactly the same objects as the node: a Noetherian
base, finite-type `S`-schemes, closure of inverse images of generic points, reduced
induced structure, and the canonical closed immersions.  The Hom assertion retains the
reducedness and generic-point hypotheses and states a bijection of precisely the two
subtypes of `S`-morphisms.  Functoriality is rendered by unique induced maps together
with explicit identity and composition equations.  The generic-fibre clause includes
both scheme-over-residue-field projection equations.  The étale clause uses the actual
canonical pullback lift and its commutativity witness, while the proper-surjective clause
retains both properties.  No hypothesis or conclusion was added or dropped.  Both files
compile cleanly with `scompile.py`; all lines are at most 100 characters.

## New nodes

`def-per-dominant-part` is the missing general-base notion.  Its source is ILO Exposé II
1.2.5, and its module constructs the closed subset and reduced induced subscheme using
the real `vanishingIdeal` construction.  The three searches above found no exact
existing declaration.  The existing `def-per-dominant-reduced-part` node was rejected as
an exact match because it assumes an integral base and records only its ideal.

## Recovery self-check

Retained the saved packet and repaired the dry-run diagnostics: the recorded theorem
signature excludes the terminating `:=`; the new definition node has the full blueprint
ancestry and separately bracketed dependency citations. The clause-by-clause reading
found the dominant-component support identification was missing from the theorem and
added its explicit equality. No natural-language node statement changed.

LeanSearch recovery search: `Reduced induced closed subscheme on the closure of inverse images of generic points of a base scheme` returned genericPoints, its component
correspondence, open-immersion generic-point compatibility, reducedness constructors,
and the closed-immersion-to-immersion instance; no dominant-part construction.
The full tool output is recorded in the new node.

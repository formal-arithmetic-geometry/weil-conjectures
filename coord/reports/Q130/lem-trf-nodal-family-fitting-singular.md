## Worker report

The module `Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular` states
`AlgebraicGeometry.nodal_family_fitting_singular` with one `sorry` proof.  It uses
the existing first-Fitting singular subscheme construction and gives the canonical
base-change map directly as `CategoryTheory.Limits.pullback.map`; no arbitrary map or
choice is introduced.

The hypotheses are rendered as follows.  The morphism is
`{X S : Scheme.{u}} (f : X ⟶ S)` with typeclass hypotheses `[Flat f]` and
`[LocallyOfFinitePresentation f]`.  For every algebraically closed field
`Ω : Type u`, every `[Field Ω] [IsAlgClosed Ω]`, and every geometric-point map
`g : Spec (.of Ω) ⟶ S`, the hypothesis
`Nonempty (pullback (C := Scheme.{u}) f g) → ...` permits empty fibres and requires
`(pullback f g).IsPureDimension 1`; for every point `x` outside
`(pullback.snd f g).smoothLocus`, it requires
`IsGeometricOrdinaryDoublePoint Ω (pullback f g) x`, which is the completed-local-ring
condition `Ω[[u,v]]/(uv)`.

The conclusion clauses are:

* `IsOpen (f.smoothLocus : Set X)` says the relative smooth locus is open.
* `Set.range (Scheme.firstFittingSingularSubscheme f) = (f.smoothLocus : Set X)ᶜ`
  identifies the underlying set of the first-Fitting singular subscheme with the
  nonsmooth locus.
* `(LocallyOfFiniteType (Scheme.firstFittingSingularSubscheme f ≫ f) ∧
  IsOpenImmersion (pullback.diagonal (Scheme.firstFittingSingularSubscheme f ≫ f)))`
  is the recorded Mathlib form of unramifiedness over `S`.
* For every `S' : Scheme.{u}` and `g : S' ⟶ S`, the `Nonempty` isomorphism in
  `Over` is between the explicit canonical map
  `pullback.map (Scheme.firstFittingSingularSubscheme f ≫ f) g f g
  (Scheme.firstFittingSingularSubscheme f) (𝟙 S') (𝟙 S) ...` and
  `Scheme.firstFittingSingularSubscheme (pullback.snd f g)`, so it states canonical
  formation under arbitrary base change.  The final range equality identifies the
  base-changed singular subscheme with the nonsmooth locus of the base-changed map.

The statement dependencies and declarations used are:

* `def-trf-first-fitting-singular-subscheme`:
  `Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme`,
  `AlgebraicGeometry.Scheme.firstFittingSingularSubscheme`.
* `def-weil-flat-morphism` (Mathlib match `AlgebraicGeometry.Flat`) and
  `def-sbc-locally-finite-presentation` (Mathlib
  `AlgebraicGeometry.LocallyOfFinitePresentation`).
* `def-kun-dimension` is rendered through the existing
  `Sheaf.AlgebraicGeometry.PureDimension` declaration
  `AlgebraicGeometry.Scheme.IsPureDimension`.
* `def-weil-unramified-morphism` is rendered inline as
  `LocallyOfFiniteType h ∧ IsOpenImmersion (pullback.diagonal h)`.
* `def-pc-fibre-product` is Mathlib's
  `CategoryTheory.Limits.pullback`, with `pullback.map`, `pullback.snd`, and
  `CategoryTheory.Over.mk` for the canonical base-change square.
* `def-sbc-smooth-morphisms` is Mathlib's `AlgebraicGeometry.Smooth` API and
  `Scheme.Hom.smoothLocus`.
* `def-weil-geometric-fibre` is represented by the explicit geometric pullback
  `pullback f g` with `g : Spec (.of Ω) ⟶ S`.
* The completed local-ring clause reuses
  `AlgebraicGeometry.IsGeometricOrdinaryDoublePoint` from
  `Sheaf.AlgebraicGeometry.ProjectiveNodalTower`.

Edge cases checked: empty geometric fibres satisfy the implication vacuously;
the pure-dimension predicate is vacuous on an empty scheme; smooth fibres have no
points outside the smooth locus; the first-Fitting construction allows the unit ideal
convention; arbitrary base changes include identity, empty, and non-flat bases; and
the singular subscheme is not reduced in the statement.

Searches made: `msearch.py ... leanfinder "first Fitting singular subscheme"` found
only generic ideal-sheaf declarations and no nodal theorem; analogous searches for
flat morphisms and locally finite presentation found the Mathlib classes used above.
`msearch.py ... loogle` for `AlgebraicGeometry.Flat,
AlgebraicGeometry.LocallyOfFinitePresentation, AlgebraicGeometry.FormallyUnramified`
found only generic etale/unramified APIs.  `msearch.py ... grep
"IsStableUnderBaseChange|FormallyUnramified|smoothLocus|Fitting"` found no
Fitting/nodal-family theorem.  Searches of `WeilConjectures/` and `lean/Sheaf/`
found no declaration of this theorem; the only reusable completed-node helper was
`IsGeometricOrdinaryDoublePoint`, which was inspected in full.  The DAG search found
no node restating this item.

No statement correction, new definition node, dependency module, or
`STATEMENT-DISPUTED` issue was needed.

## Second reading by Q130

I reread the node and the complete module.  The two hypotheses (flat/LFP and the
empty-or-pure-one-dimensional nodal geometric-fibre condition) and all four
conclusion clauses (open smooth locus, support equality, unramifiedness, and the
canonical arbitrary-base-change isomorphism plus support equality) are present with
the same objects and no added finiteness or connectedness assumption.  The explicit
`pullback.map` uses the canonical universal-property map and avoids an import of the
downstream projective-family theorem, so there is no dependency cycle.

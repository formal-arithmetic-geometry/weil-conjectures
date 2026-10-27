## What changed

The only edited Lean module is Sheaf.Paper.CondensedTateRealization. Four existing theorem bodies
are filled, with proved private helpers for the lift/down coefficient isomorphism,
the bottom finite-field isomorphism, restriction of tensor products, and the tensor
projection equation. Existing imports and theorem statements are preserved. Three public construction
interfaces name the existing derived-limit functor, its projection, and the
composition with an exact functor's degree-zero comparison.

Exactness factors the rational-to-closure map through the bottom finite subfield:
the first map is an isomorphism, and the second uses the source library's proved
finite-extension filtered-colimit flatness theorem. Tensor projection compatibility
is induction using the cokernel map in degree zero and the Tate-limit cone equation
at successors. Applying the integral encoding functor proves augmentation naturality.
The balanced family starts with the coefficient map on the unit, and recursively
descends the tensor of the previous map and the scalar-extension unit through the
balanced coequalizer. The projection is epic, so the same equations prove uniqueness.

The canonical scalar/shift elaboration changes and consumer audit are recorded in
coord/changes/A2-condensed-tate-scalar-shift-elaboration.md. The node's proof-origin
note and proof-step additions record these proved parts. The original proof plan
and unit route remain in place; the auxiliary exactness proof additionally cites
the already proved lem-sfb-qlbar-flat, whose declaration was already imported.

The main theorem statement is unchanged, and exactly three original sorry tokens
remain. The complete production source and its artifact-producing build both
passed lcompile.py under its 60-second per-file limit. No profiling options are
present. A separate check importing the newly built module proves by rfl that
the scalar/shift structure, rational derived scalar functor and scalar adjunction
are definitionally equal to the original constructions. Generic checks compare
the named limit and projection interfaces and the exact-functor projection
composition with their defining formulas, and compare the reconstructed object
with its original formula. All six unchanged downstream modules listed in the
change record compile against this build. No consumer adaptation is needed.

## Proved and sorry left

Four of the seven original proof holes are closed:

- AlgebraicGeometry.ProEtale.CondensedTateRealization.rationalToQbar_preservesFiniteLimits
- AlgebraicGeometry.ProEtale.CondensedTateRealization.powerProjection_compatible
- AlgebraicGeometry.ProEtale.CondensedTateRealization.augmentation_compatible
- AlgebraicGeometry.ProEtale.CondensedTateRealization.balancedPower_existsUnique

Zero holes are added or split off. The three remaining original holes are:

- AlgebraicGeometry.ProEtale.CondensedTateRealization.integralComparison_existsUnique
- AlgebraicGeometry.ProEtale.CondensedTateRealization.encodedBalancedPower_existsUnique
- AlgebraicGeometry.ProEtale.CondensedTateRealization.condensed_tate_realization

All seven declarations are attached to lem-pur-condensed-tate-realization. The
remaining holes keep their existing complete proof docstrings and statements.
The current compiled module reports only propext, Classical.choice and Quot.sound
for rationalToQbar_preservesFiniteLimits, powerProjection_compatible and
balancedPower_existsUnique. augmentation_compatible has a complete proof but its
type uses integralEncoding, whose integralComparison_existsUnique dependency is
still sorry; its axiom report therefore still includes sorryAx.
Degree zero is proved explicitly in both inductions. The arguments are uniform in
the scheme, including the empty scheme, and use no odd-prime hypothesis or chosen
root of unity.

## No longer needed

None. No original import, node, module, declaration or unit step is withdrawn. The
retained definitions and three remaining proofs still need the existing plan.
The existing tensor coequalizer lemmas and scalar-composition isomorphisms are
already available through the retained imports, so no extra proof import is needed.

## Where the brief, the DAG or earlier work was wrong

The existing docstring of rationalToQbar_preservesFiniteLimits says the map is a
field extension on every pro-etale section. Section rings need not be fields (for
example on a disconnected scheme). The proof instead uses the valid internal
flatness theorem: the finite-extension-valued closure is a filtered colimit of
finite free modules over a finite intermediate field. Suggested replacement for
the last two docstring lines: "The lift-down and bottom-field maps are isomorphisms.
The finite-extension-valued closure is a filtered colimit of finite free modules,
so its scalar extension preserves finite limits."

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

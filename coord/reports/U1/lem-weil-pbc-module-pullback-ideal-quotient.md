## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient` as
`AlgebraicGeometry.modulePullbackIdealQuotient`.  The binders `X Y` and `f` render a
morphism of schemes, and `J : Y.IdealSheafData` renders the quasi-coherent ideal sheaf.
The first conjunct states the affine-open formula using the range of the inclusion of
`Scheme.extendedIdeal f J` and `Ideal.map` along the induced ring map.  The second conjunct
states extension commutes with every positive power.  The third conjunct quantifies a
quasi-coherent `G`; `Epi` and the `kernel` equality render the epimorphism and kernel clause.
The displayed existential family `σ` consists of the quotient isomorphisms, its first
equation is `σ_G ∘ p_G = f^*q_G`, and its second equation is naturality for every
quasi-coherent `G'` and map `u`.  Quotients and their induced maps are the definitions
`formalModuleQuotient`, `formalModuleQuotientπ`, and `formalModuleQuotientMap` from
`Sheaf.AlgebraicGeometry.CoherentFormalModule`.

The module imports `Sheaf.AlgebraicGeometry.ExtendedIdeal`,
`Sheaf.AlgebraicGeometry.CoherentFormalModule`, and `Sheaf.AlgebraicGeometry.Coherent`.
The dependency declarations used are `AlgebraicGeometry.Scheme.extendedIdeal`,
`AlgebraicGeometry.Scheme.extendedIdealModule`, and
`AlgebraicGeometry.Scheme.extendedIdealModuleι` from `ExtendedIdeal.lean`,
`AlgebraicGeometry.Scheme.Modules.tensorPullback` and
`AlgebraicGeometry.Scheme.Modules.tensorPullbackObjUnitToUnit` from
`Sheaf.AlgebraicGeometry.TensorPullback`, and the formal quotient declarations listed
above from `CoherentFormalModule.lean`.

Edge cases checked before writing were `n = 1` (the first power), the zero ideal and unit
ideal (the range and `Ideal.map` formulations remain meaningful), the zero module, and
empty affine opens.  No nonemptiness or flatness hypothesis is added; the pullback is
right exact without flatness, as in the source.

Searches made: LeanFinder for “pullback of a quasi coherent module quotient by an ideal
sheaf is naturally isomorphic to pullback module modulo extended ideal” returned
`Scheme.IdealSheafData.comap`, `Scheme.Modules.pullback`, and `Scheme.Hom.liftQuotient`,
but no matching quotient theorem (2026-10-11).  LeanSearch for “pullback of quasi
coherent module modulo ideal sheaf is naturally isomorphic to pullback module modulo the
extended ideal” was unavailable (HTTP 500; recorded as unavailable).  Loogle queried
`IdealSheafData.comap` and returned no hit because of an unknown identifier.  Grep over
Mathlib found only `Scheme.IdealSheafData.comap` and quotient-lifting declarations, with
no module-quotient compatibility.  Grep over the project found no existing declaration
for this item.  The source declaration search found no matching item declaration.

## Dependency modules

`def-nagata-extended-ideal` required a dependency module because its recorded
`AlgebraicGeometry.Scheme.IdealSheafData.comap` is only the scheme-theoretic kernel
representation and does not state the node's image-of-pullback module notion.  The new
`ExtendedIdeal.lean` module states `extendedIdeal` using that representation and defines
the corresponding image module and inclusion as the image of the tensor pullback of
`J.toModulesι` followed by `tensorPullbackObjUnitToUnit`.

## Earlier second reading (a previous round; superseded)

I reread the node and both modules line by line.  The scheme morphism, ideal sheaf,
affine-open formula, positive-power clause, quasi-coherent module hypothesis, epimorphism,
kernel, quotient isomorphism, and naturality map all occur in the theorem in that order.
The quotient maps are exactly the formal-module cokernel maps, and the induced maps are
`formalModuleQuotientMap`; no flatness, nonemptiness, or characteristic hypothesis was
introduced.  The dependency module records both the comap representation and the image
module/inclusion used by the statement.  Compilation on the server succeeds with only the
expected `sorry` warning.

## Second reading by U1

I compared the node clause by clause with `modulePullbackIdealQuotient`. The binders
`X Y`, `f`, and `J` render a scheme morphism and an ideal sheaf. Clause (1) is rendered
by the affine-open quantifiers and `Set.range ((Scheme.extendedIdeal f J).toModulesι.app
U.1) = Ideal.map ...`; this is the affine generated-ideal formula. Clause (2) is the
positive-power equality `(J ^ n).comap f = (Scheme.extendedIdeal f J) ^ n`. Clause (3)
quantifies quasi-coherent `G`, gives `Epi`, the kernel as `idealModuleProduct`, and the
existential quotient isomorphisms with the unit equation and naturality equation. The
formal quotient maps are the declarations from `CoherentFormalModule`.

The first reading used `extendedIdealModuleι` in clauses (1) and (3), while clause (2)
used `extendedIdeal` (the `IdealSheafData.comap` representation). This mixed two
representations of the same ideal and did not render one object consistently. I changed
both occurrences to `(Scheme.extendedIdeal f J).toModulesι`, the inclusion belonging to
the dependency node's extended ideal object. The theorem still compiles cleanly.

Edge cases checked: `n = 1`, zero and unit ideals, zero modules, empty affine opens,
and no nonemptiness or flatness assumptions. The empty-index case is irrelevant here;
universes are shared by `Scheme.{v}` and all quantified objects. Searches in Mathlib,
the project, and the source found no existing quotient compatibility theorem; LeanSearch,
LeanFinder, Loogle, and grep results are recorded in the worker report.

## Reviewer fix (R-mpq)

- The delivered dependency module `Sheaf.AlgebraicGeometry.ExtendedIdeal` re-recorded
  def-nagata-extended-ideal at `Scheme.extendedIdeal := J.comap f` (an alias of the landed record)
  plus two unused image-module definitions: reverted (H13/H4); the item uses `J.comap f` directly.
- `kernel (…) = idealModuleProduct …` was an equality of objects: replaced by the kernel-fork form
  `∃ w, Nonempty (IsLimit (KernelFork.ofι (idealModuleProductι …) w))` (as ClosedImmersionUnitQuotient).
- σ was existential inside `∀ G`, so `σ G'` was not tied to the canonical map: the family σ is now
  quantified once, with the defining equation for every quasi-coherent G.
- Clause (1) written with `IdealSheafData.ideal` on affine opens.

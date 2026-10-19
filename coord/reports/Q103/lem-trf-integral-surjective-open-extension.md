## Worker report

The module `Sheaf/AlgebraicGeometry/IntegralSurjectiveOpenExtension.lean` states
`AlgebraicGeometry.exists_surjective_integral_extension`. It introduces schemes `S`, `U`,
and `V`, an open immersion `j : U ⟶ S`, and an integral surjective morphism
`g : V ⟶ U` through the typeclass hypotheses `[IsOpenImmersion j]`,
`[IsIntegralHom g]`, and `[Surjective g]`. Its conclusion is the existence of a scheme
`Vbar`, a morphism `q : Vbar ⟶ S`, the clauses `IsIntegralHom q` and `Surjective q`,
and an isomorphism `e : Limits.pullback q j ≅ V` satisfying
`e.hom ≫ g = Limits.pullback.snd q j`, which is the required isomorphism over `U`.
The theorem proof is `sorry`, as required for stage 2.

The dependency declarations used are `AlgebraicGeometry.Scheme` from
`Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.IsOpenImmersion` from
`Mathlib.AlgebraicGeometry.OpenImmersion`, `AlgebraicGeometry.Surjective` from
`Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, `AlgebraicGeometry.IsIntegralHom`
from `Mathlib.AlgebraicGeometry.Morphisms.Integral`, and
`CategoryTheory.Limits.pullback` from
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.

Edge cases checked: no nonemptiness, quasi-compactness, quasi-separatedness, or
nonempty open assumption is added; the open immersion may be empty, and `V` may be
empty only when allowed by the stated surjectivity instance. The pullback uses the same
scheme universe `u` as `S`, `U`, and `V`, and the conclusion retains all clauses of the
node statement.

Searches made before writing: `msearch.py ... leanfinder "surjective integral morphism
extension open scheme"` returned Mathlib notions `IsIntegralHom`, `Surjective`, and related
maps but no extension theorem; `msearch.py ... loogle "IsIntegralHom, Surjective,
IsOpenImmersion"` returned 0 hits; `msearch.py ... grep "integral.*surjective.*open"
AlgebraicGeometry` returned 0 hits; `rg` over `WeilConjectures` and project `lean/Sheaf`
found no declaration of this extension theorem. The dependency declarations were read in
full in the Mathlib source files listed above.

## Second reading by Q103

I reread the node and the generated Lean signature. The scheme objects correspond exactly
to `[def-pc-scheme]`; `j` and its open-immersion instance render the open inclusion;
`g` and its two instances render the integral and surjective hypotheses. The existential
`Vbar`, `q`, `IsIntegralHom q`, and `Surjective q` render the requested extension, while
the pullback isomorphism and equation render “isomorphic to `V` over `U`”. No hypothesis or
conclusion clause was added or omitted, and the source proof is recorded in the declaration
docstring. `scompile.py` compiled the module without errors or warnings.
